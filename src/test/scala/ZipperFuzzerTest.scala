package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.collection.mutable
import scala.util.Random
import scala.util.control.NonFatal
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path as NioPath, Paths}

object ZipperProgramFuzzer:
  trait Dist[+T]:
    self =>
    def sample(using rng: Random): T
    def map[S](f: T => S): Dist[S] = new Dist[S]:
      override def sample(using rng: Random): S = f(self.sample)
    def flatMap[S](f: T => Dist[S]): Dist[S] = new Dist[S]:
      override def sample(using rng: Random): S = f(self.sample).sample
    def filter(p: T => Boolean): Dist[T] = Filtered(self, p)

  case class Filtered[T](d: Dist[T], p: T => Boolean) extends Dist[T]:
    override def sample(using rng: Random): T =
      while true do
        val x = d.sample
        if p(x) then return x
      throw IllegalStateException("unreachable filtered sampler exit")

  case class Mapped[T, S](d: Dist[T], f: T => S) extends Dist[S]:
    override def sample(using rng: Random): S = f(d.sample)

  case class Product2[T0, T1, S](d0: Dist[T0], d1: Dist[T1], f: (T0, T1) => S) extends Dist[S]:
    override def sample(using rng: Random): S = f(d0.sample, d1.sample)

  case class Dep[X, Y](dx: Dist[X], fdy: X => Dist[Y]) extends Dist[Y]:
    override def sample(using rng: Random): Y = fdy(dx.sample).sample

  case class Concentrated[X, Y, A](dx: Dist[X], initial: A, fa: (A, X) => Either[A, Y]) extends Dist[Y]:
    override def sample(using rng: Random): Y =
      var a = initial
      while true do
        fa(a, dx.sample) match
          case Right(y) => return y
          case Left(next) => a = next
      throw IllegalStateException("unreachable concentrated sampler exit")

  case class Degenerate[T](t: T) extends Dist[T]:
    override def sample(using rng: Random): T = t

  case class Categorical[T](weighted: Vector[(Int, T)]) extends Dist[T]:
    private val total = weighted.map(_._1).sum
    require(total > 0, "categorical sampler needs positive total weight")
    override def sample(using rng: Random): T =
      var k = rng.nextInt(total)
      var i = 0
      while i < weighted.length do
        val (w, t) = weighted(i)
        if k < w then return t
        k -= w
        i += 1
      weighted.last._2

  case class Repeated[T](dlength: Dist[Int], ditem: Dist[T]) extends Dist[Vector[T]]:
    override def sample(using rng: Random): Vector[T] =
      Vector.fill(dlength.sample)(ditem.sample)

  object Dist:
    def uniformInt(lowInclusive: Int, highExclusive: Int): Dist[Int] =
      new Dist[Int]:
        override def sample(using rng: Random): Int =
          rng.nextInt(highExclusive - lowInclusive) + lowInclusive
    def choose[T](xs: IndexedSeq[T]): Dist[T] =
      new Dist[T]:
        override def sample(using rng: Random): T =
          xs(rng.nextInt(xs.length))
    def weighted[T](xs: (Int, T)*): Dist[T] = Categorical(xs.toVector)
    def uniqueVector[T](target: Int, item: Dist[T]): Dist[Vector[T]] =
      Concentrated(item, Vector.empty[T], (acc, x) =>
        val next = if acc.contains(x) then acc else acc :+ x
        if next.length >= target then Right(next) else Left(next)
      )

  final case class ZLoc(trie: TrieSpace):
    def isPath(segment: PathValue): Boolean =
      trie.contains(segment)

    def branches(segment: PathValue = PathValue(Nil)): Vector[PathItem] =
      trie.subtree(segment).toVector
        .flatMap(_.children.keysIterator.map(TrieSpace.item))
        .sortBy(_.show)

    def descend(segment: PathValue): Option[ZLoc] =
      trie.subtree(segment).map(ZLoc(_))

    def instantiate: SpaceValue =
      val out = Vector.newBuilder[List[Int]]
      def rec(node: TrieSpace, prefix: List[Int]): Unit =
        if node.terminal then out += prefix.reverse
        node.children.foreach((item, child) => rec(child, item :: prefix))
      rec(trie, Nil)
      SpaceValue(out.result().map(TrieSpace.decode).toSet)

    def paths: Vector[PathValue] = trie.paths
    def union(that: ZLoc): ZLoc = ZLoc(trie.union(that.trie))
    def intersect(that: ZLoc): ZLoc = ZLoc(trie.intersect(that.trie))
    def diff(that: ZLoc): ZLoc = ZLoc(trie.diff(that.trie))
    def restrictBy(prefixes: ZLoc): ZLoc = ZLoc(trie.restrictBy(prefixes.trie))
    def raffinate(prefixes: ZLoc): ZLoc = ZLoc(trie.raffinate(prefixes.trie))
    def concat(that: ZLoc): ZLoc = ZLoc(trie.concat(that.trie))
    def wrap(prefix: PathValue): ZLoc = ZLoc(trie.wrap(prefix))
    def unwrap(prefix: PathValue): ZLoc = ZLoc(trie.unwrap(prefix))
    def tailsUnion: ZLoc = ZLoc(trie.tailsUnion)
    def tailsIntersection: ZLoc = ZLoc(trie.tailsIntersection)
    def range(start: Int, end: Int): ZLoc = ZLoc(trie.range(start, end))
    def heads: ZLoc =
      ZLoc.literal(branches().map(item => PathValue(item :: Nil)))
    def headGroups: Vector[(PathValue, ZLoc)] =
      branches().flatMap(item => descend(PathValue(item :: Nil)).map(PathValue(item :: Nil) -> _))

  object ZLoc:
    val empty: ZLoc = ZLoc(TrieSpace.empty)
    def singleton(path: PathValue): ZLoc = ZLoc(TrieSpace.singleton(path))
    def literal(paths: Iterable[PathValue]): ZLoc = ZLoc(TrieSpace.fromPaths(paths))
    def strings(paths: Iterable[String]): ZLoc = literal(paths.map(path))
    def unionAll(xs: IterableOnce[ZLoc]): ZLoc =
      ZLoc(TrieSpace.joinAll(xs.iterator.map(_.trie)))

  final case class Arg(name: SpaceMention, loc: ZLoc):
    def expr: Space = Space.Mention(name)
    def value: SpaceValue = loc.instantiate

  final case class Term(expr: Space, loc: ZLoc)

  final case class FuzzCase(name: String, args: Vector[Arg], term: Term):
    def mentions: Vector[SpaceMention] = args.map(_.name)
    def context: SpaceContextMap = SpaceContextMap(args.map(a => a.name -> a.value).toMap)
    def trieContext: TrieSpaceContextMap = TrieSpaceContext.fromReference(context)
    def routine: Routine = Routine(RoutinePtr("zipper_fuzz_" + name), Vector.empty, mentions, term.expr)
    def expected: SpaceValue = term.loc.instantiate
    def renderExpression: String =
      s"""[$name]
         |${term.expr.show}
         |""".stripMargin
    def render: String =
      val argText = args.map(a => s"${a.name.s} = ${a.value.pretty}").mkString("\n")
      s"""[$name]
         |program:
         |${term.expr.show}
         |arguments:
         |$argText
         |result:
         |${expected.pretty}
         |""".stripMargin

  private val people = Vector("ann", "bob", "cora", "dan", "eli", "fay", "gia", "hal", "ivy", "jo")
  private val groups = Vector("red", "blue", "green", "ops", "ml", "db")
  private val skills = Vector("scala", "rust", "logic", "trie", "viz", "proof")
  private val tags = Vector("hot", "cold", "dense", "sparse", "north", "south", "east", "west")

  private def path(s: String): PathValue = Syntax.parse(s)
  private def arg(name: String, loc: ZLoc): Arg = Arg(SpaceMention(name), loc)
  private def pickSome[T](rng: Random, xs: Vector[T], n: Int): Vector[T] =
    rng.shuffle(xs).take(n.min(xs.length)).toVector

  private def uniqueEdges(nodes: Vector[String], count: Int)(using rng: Random): Vector[(String, String)] =
    val edge = Product2(Dist.choose(nodes), Dist.choose(nodes), (a, b) => a -> b).filter {
      case (a, b) => a != b
    }
    Dist.uniqueVector(count, edge).sample

  private def graphNeighbors(id: Int)(using rng: Random): FuzzCase =
    val nodes = pickSome(rng, people, 5 + rng.nextInt(4))
    val edges = uniqueEdges(nodes, 7 + rng.nextInt(8))
    val seeds = pickSome(rng, nodes, 1 + rng.nextInt(3))
    val edgesArg = arg("edges", ZLoc.strings(edges.map((a, b) => s"edge.$a.$b")))
    val seedsArg = arg("seeds", ZLoc.strings(seeds))
    val src = Term(S"edges"("edge"), edgesArg.loc.unwrap(path("edge")))
    val body = (S"seeds" /\ sP"from") x S"tos"
    val loc = ZLoc.unionAll(src.loc.headGroups.map { (headPath, tail) =>
      seedsArg.loc.intersect(ZLoc.singleton(headPath)).concat(tail)
    })
    FuzzCase(s"graph-neighbors-$id", Vector(edgesArg, seedsArg),
      Term(src.expr.iter(P"from", S"tos", body), loc))

  private def groupSkills(id: Int)(using rng: Random): FuzzCase =
    val selectedPeople = pickSome(rng, people, 5 + rng.nextInt(4))
    val selectedGroups = pickSome(rng, groups, 2 + rng.nextInt(3))
    val memberships =
      selectedGroups.flatMap(g => pickSome(rng, selectedPeople, 2 + rng.nextInt(3)).map(p => s"member.$g.$p")).distinct
    val skillFacts =
      selectedPeople.flatMap(p => pickSome(rng, skills, 1 + rng.nextInt(3)).map(s => s"$p.$s")).distinct
    val members = arg("members", ZLoc.strings(memberships))
    val skillArg = arg("skills", ZLoc.strings(skillFacts))
    val src = Term(S"members"("member"), members.loc.unwrap(path("member")))
    val body = P"g" x (S"skills" <| S"people")
    val loc = ZLoc.unionAll(src.loc.headGroups.map { (group, people) =>
      ZLoc.singleton(group).concat(skillArg.loc.restrictBy(people))
    })
    FuzzCase(s"group-skills-$id", Vector(members, skillArg),
      Term(src.expr.iter(P"g", S"people", body), loc))

  private def rangePodium(id: Int)(using rng: Random): FuzzCase =
    val ranked = pickSome(rng, people, 5 + rng.nextInt(4)).zipWithIndex.map { (p, i) =>
      f"score.${i + 1}%02d.$p"
    }
    val rankArg = arg("ranked", ZLoc.strings(ranked))
    val k = 2 + rng.nextInt(3)
    val unwrapped = Term(S"ranked"("score"), rankArg.loc.unwrap(path("score")))
    val ranged = Term(Space.Range(unwrapped.expr, 0, k), unwrapped.loc.range(0, k))
    val term = Term("podium" x ranged.expr,
      ZLoc.singleton(path("podium")).concat(ranged.loc))
    FuzzCase(s"range-podium-$id", Vector(rankArg), term)

  private def commonTags(id: Int)(using rng: Random): FuzzCase =
    val rows = pickSome(rng, groups, 3 + rng.nextInt(3))
    val common = pickSome(rng, tags, 1 + rng.nextInt(2))
    val rowFacts = rows.flatMap { row =>
      val extras = pickSome(rng, tags.filterNot(common.contains), rng.nextInt(3))
      (common ++ extras).map(t => s"$row.$t")
    }
    val matrix = arg("matrix", ZLoc.strings(rowFacts))
    val term = Term("common" x /\(S"matrix"),
      ZLoc.singleton(path("common")).concat(matrix.loc.tailsIntersection))
    FuzzCase(s"common-tags-$id", Vector(matrix), term)

  private def pairPipeline(id: Int)(using rng: Random): FuzzCase =
    val lefts = pickSome(rng, people, 4 + rng.nextInt(3))
    val rights = pickSome(rng, tags, 4 + rng.nextInt(3))
    val pairs = lefts.zip(rng.shuffle(rights)).map((a, b) => s"pair.$a.$b")
    val pairsArg = arg("pairs", ZLoc.strings(pairs))
    val unwrapped = Term(S"pairs"("pair"), pairsArg.loc.unwrap(path("pair")))
    val tails = Term("tails" x \/(unwrapped.expr),
      ZLoc.singleton(path("tails")).concat(unwrapped.loc.tailsUnion))
    val leftHeads = Term("left" x head(unwrapped.expr),
      ZLoc.singleton(path("left")).concat(unwrapped.loc.heads))
    val term = Term(tails.expr \/ leftHeads.expr, tails.loc.union(leftHeads.loc))
    FuzzCase(s"pair-pipeline-$id", Vector(pairsArg), term)

  private def permissionMashup(id: Int)(using rng: Random): FuzzCase =
    val selectedPeople = pickSome(rng, people, 5 + rng.nextInt(4))
    val selectedGroups = pickSome(rng, groups, 2 + rng.nextInt(3))
    val memberships = selectedGroups.flatMap(g =>
      pickSome(rng, selectedPeople, 2 + rng.nextInt(3)).map(p => s"group.$g.$p")
    ).distinct
    val grants = selectedGroups.flatMap(g =>
      pickSome(rng, tags, 1 + rng.nextInt(3)).map(t => s"$g.$t")
    ).distinct
    val blocked = pickSome(rng, selectedPeople, rng.nextInt(3))
    val members = arg("members", ZLoc.strings(memberships))
    val grantsArg = arg("grants", ZLoc.strings(grants))
    val blockedArg = arg("blocked", ZLoc.strings(blocked))
    val src = Term(S"members"("group"), members.loc.unwrap(path("group")))
    val body = P"team" x ((S"people" \ S"blocked") x (S"grants"(P"team")))
    val loc = ZLoc.unionAll(src.loc.headGroups.map { (teamPath, people) =>
      val team = ZLoc.singleton(teamPath)
      team.concat(people.diff(blockedArg.loc).concat(grantsArg.loc.unwrap(teamPath)))
    })
    FuzzCase(s"permission-mashup-$id", Vector(members, grantsArg, blockedArg),
      Term(src.expr.iter(P"team", S"people", body), loc))

  private def unionTerms(terms: Vector[Term]): Term =
    terms.reduceLeft((a, b) => Term(a.expr \/ b.expr, a.loc.union(b.loc)))

  private def tag(label: String, term: Term): Term =
    Term(label x term.expr, ZLoc.singleton(path(label)).concat(term.loc))

  private def nonEmpty(t: Term): Boolean =
    !t.loc.trie.isEmpty

  private def bounded(t: Term, maxPaths: Int = 260, maxNodes: Int = 2200): Boolean =
    t.loc.trie.pathCount <= maxPaths && t.loc.trie.nodeCount <= maxNodes

  private def pathConst(p: PathValue): Path =
    Path.Constant(p)

  private def spaceKind(s: Space): String = s match
    case Space.Empty => "Empty"
    case Space.Call(_, _, _) => "Call"
    case Space.Mention(_) => "Mention"
    case Space.Singleton(_) => "Singleton"
    case Space.Literal(_) => "Literal"
    case Space.Union(_, _) => "Union"
    case Space.Intersection(_, _) => "Intersection"
    case Space.Subtraction(_, _) => "Subtraction"
    case Space.Restriction(_, _) => "Restriction"
    case Space.Raffination(_, _) => "Raffination"
    case Space.Composition(_, _) => "Composition"
    case Space.Iteration(_, _, _, _) => "Iteration"
    case Space.Fold(_, _, _, _, _, _, _) => "Fold"
    case Space.Fixpoint(_, _, _) => "Fixpoint"
    case Space.Wrap(_, _) => "Wrap"
    case Space.Unwrap(_, _) => "Unwrap"
    case Space.TailsUnion(_) => "TailsUnion"
    case Space.TailsIntersection(_) => "TailsIntersection"
    case Space.PrefixClosure(_) => "PrefixClosure"
    case Space.SuffixClosure(_) => "SuffixClosure"
    case Space.TailsClosure(_) => "TailsClosure"
    case Space.GroundedPS(_, _) => "GroundedPS"
    case Space.GroundedSS(_, _) => "GroundedSS"
    case Space.Range(_, _, _) => "Range"

  private def argSeedTerms(args: Vector[Arg]): Vector[Term] =
    args.flatMap { a =>
      val whole = Term(a.expr, a.loc)
      val unwrapped = a.loc.branches().take(4).map { item =>
        val prefix = PathValue(item :: Nil)
        Term(a.expr(pathConst(prefix)), a.loc.unwrap(prefix))
      }
      whole +: unwrapped
    }

  private def coverageSeedTerms(base: Term, args: Vector[Arg]): Vector[Term] =
    val seeds = argSeedTerms(args)
    val a = seeds.headOption.getOrElse(base)
    val b = seeds.drop(1).headOption.getOrElse(base)
    val prefix = a.loc.branches().headOption.map(item => PathValue(item :: Nil)).getOrElse(path("cov"))
    val singleton = Term(Space.Singleton(Path.Constant(path("cov_single"))), ZLoc.singleton(path("cov_single")))
    val literalValue = SpaceValue(path("cov_lit.a"), path("cov_lit.b"))
    val literal = Term(Space.Literal(literalValue), ZLoc.literal(literalValue.paths))
    Vector(
      Term(Space.Empty, ZLoc.empty),
      singleton,
      literal,
      Term(a.expr \/ b.expr, a.loc.union(b.loc)),
      Term(a.expr /\ b.expr, a.loc.intersect(b.loc)),
      Term(a.expr \ b.expr, a.loc.diff(b.loc)),
      Term(a.expr <| b.expr, a.loc.restrictBy(b.loc)),
      Term(a.expr \| b.expr, a.loc.raffinate(b.loc)),
      Term(a.expr x b.expr, a.loc.concat(b.loc)),
      Term(Space.Iteration(a.expr, PathRef("cov_h").known(1), SpaceMention("cov_r"), Space.Mention(SpaceMention("cov_r"))), a.loc.tailsUnion),
      Term("cov_wrap" x a.expr, ZLoc.singleton(path("cov_wrap")).concat(a.loc)),
      Term(a.expr(pathConst(prefix)), a.loc.unwrap(prefix)),
      Term(\/(a.expr), a.loc.tailsUnion),
      Term(/\(a.expr), a.loc.tailsIntersection),
      Term(Space.Range(a.expr, 0, a.loc.trie.pathCount.min(3)), a.loc.range(0, a.loc.trie.pathCount.min(3)))
    )

  private def rangeTerm(t: Term, id: Int, step: Int)(using rng: Random): Term =
    val n = t.loc.trie.pathCount
    if n == 0 then tag(s"rng_$step", Term(Space.Range(t.expr, 0, 0), t.loc.range(0, 0)))
    else
      val mode = rng.nextInt(4)
      val out =
        mode match
          case 0 =>
            val k = 1 + rng.nextInt(n.min(6))
            Term(Space.Range(t.expr, 0, k), t.loc.range(0, k))
          case 1 =>
            val k = 1 + rng.nextInt(n.min(6))
            Term(Space.Range(t.expr, -k, 0), t.loc.range(-k, 0))
          case 2 =>
            val lo = rng.nextInt(n)
            val hi = (lo + 1 + rng.nextInt((n - lo).min(5))).min(n)
            Term(Space.Range(t.expr, lo + 1, hi + 1), t.loc.range(lo + 1, hi + 1))
          case _ =>
            Term(Space.Range(t.expr, 0, n), t.loc.range(0, n))
      tag(s"rng_$step", out)

  private def headsTerm(t: Term, id: Int, step: Int): Term =
    tag(s"heads_$step", Term(head(t.expr), t.loc.heads))

  private def tailsTerm(t: Term, id: Int, step: Int)(using rng: Random): Term =
    val tails = Term(\/(t.expr), t.loc.tailsUnion)
    if rng.nextBoolean() then tag(s"tails_$step", tails)
    else tag(s"tail_heads_$step", Term(head(tails.expr), tails.loc.heads))

  private def meetTailsTerm(t: Term, id: Int, step: Int): Term =
    tag(s"meet_$step", Term(/\(t.expr), t.loc.tailsIntersection))

  private def unwrapTerm(t: Term, id: Int, step: Int)(using rng: Random): Option[Term] =
    val branches = t.loc.branches()
    Option.when(branches.nonEmpty) {
      val prefix = PathValue(branches(rng.nextInt(branches.length)) :: Nil)
      tag(s"unwrap_$step", Term(t.expr(pathConst(prefix)), t.loc.unwrap(prefix)))
    }

  private def iterTerm(src: Term, id: Int, step: Int)(using rng: Random): Term =
    val h = PathRef(s"fh_$step").known(1)
    val r = SpaceMention(s"fr_$step")
    val ph = Path.Deref(h)
    val sr = Space.Mention(r)
    val mode = rng.nextInt(4)
    val (body, loc) =
      mode match
        case 0 =>
          val body = ph x sr
          val loc = ZLoc.unionAll(src.loc.headGroups.map { (headPath, tail) =>
            ZLoc.singleton(headPath).concat(tail)
          })
          body -> loc
        case 1 =>
          val k = 1 + rng.nextInt(4)
          val body = ph x Space.Range(sr, 0, k)
          val loc = ZLoc.unionAll(src.loc.headGroups.map { (headPath, tail) =>
            ZLoc.singleton(headPath).concat(tail.range(0, k))
          })
          body -> loc
        case 2 =>
          val label = s"iterhead_$step"
          val body = Space.Singleton(Path.Constant(path(label)) x ph)
          val loc = ZLoc.singleton(path(label)).concat(src.loc.heads)
          body -> loc
        case _ =>
          val label = s"itertail_$step"
          val body = Path.Constant(path(label)) x sr
          val loc = ZLoc.singleton(path(label)).concat(
            ZLoc.unionAll(src.loc.headGroups.map(_._2))
          )
          body -> loc
    tag(s"iter_$step", Term(Space.Iteration(src.expr, h, r, body), loc))

  private def combineTerms(a: Term, b: Term, id: Int, step: Int)(using rng: Random): Term =
    val label = s"op_$step"
    rng.nextInt(8) match
      case 0 => tag(label, Term(a.expr \/ b.expr, a.loc.union(b.loc)))
      case 1 => tag(label, Term(a.expr /\ b.expr, a.loc.intersect(b.loc)))
      case 2 => tag(label, Term(a.expr \ b.expr, a.loc.diff(b.loc)))
      case 3 => tag(label, Term(a.expr <| b.expr, a.loc.restrictBy(b.loc)))
      case 4 => tag(label, Term(a.expr \| b.expr, a.loc.raffinate(b.loc)))
      case 5 => tag(label, Term(a.expr x b.expr, a.loc.concat(b.loc)))
      case 6 => tag(label, Term((a.expr \/ b.expr) /\ a.expr, a.loc.union(b.loc).intersect(a.loc)))
      case _ =>
        val wrapped = tag(s"lhs_$step", a)
        val rhs = tag(s"rhs_$step", b)
        Term(wrapped.expr \/ rhs.expr, wrapped.loc.union(rhs.loc))

  private def coverageDerivedTerm(pool: Vector[Term], id: Int, step: Int)(using rng: Random): Term =
    val child = pool(rng.nextInt(pool.length))
    val other = pool(rng.nextInt(pool.length))
    val label = s"cov_${spaceKind(child.expr)}_$step"
    val variant = rng.nextInt(23)
    variant match
      case 0 => tag(label, Term(\/(child.expr), child.loc.tailsUnion))
      case 1 => tag(label, Term(/\(child.expr), child.loc.tailsIntersection))
      case 2 => rangeTerm(child, id, step)
      case 3 =>
        val prefix = child.loc.branches().headOption.map(item => PathValue(item :: Nil)).getOrElse(path("missing"))
        tag(label, Term(child.expr(pathConst(prefix)), child.loc.unwrap(prefix)))
      case 4 => tag(label, Term(child.expr \/ other.expr, child.loc.union(other.loc)))
      case 5 => tag(label, Term(other.expr \/ child.expr, other.loc.union(child.loc)))
      case 6 => tag(label, Term(child.expr /\ other.expr, child.loc.intersect(other.loc)))
      case 7 => tag(label, Term(other.expr /\ child.expr, other.loc.intersect(child.loc)))
      case 8 => tag(label, Term(child.expr \ other.expr, child.loc.diff(other.loc)))
      case 9 => tag(label, Term(other.expr \ child.expr, other.loc.diff(child.loc)))
      case 10 => tag(label, Term(child.expr <| other.expr, child.loc.restrictBy(other.loc)))
      case 11 => tag(label, Term(other.expr <| child.expr, other.loc.restrictBy(child.loc)))
      case 12 => tag(label, Term(child.expr \| other.expr, child.loc.raffinate(other.loc)))
      case 13 => tag(label, Term(other.expr \| child.expr, other.loc.raffinate(child.loc)))
      case 14 => tag(label, Term(child.expr x other.expr, child.loc.concat(other.loc)))
      case 15 => tag(label, Term(other.expr x child.expr, other.loc.concat(child.loc)))
      case 16 => tag(label, child)
      case 17 => tag(label, Term(Space.Empty \/ child.expr, child.loc))
      case 18 => iterTerm(child, id, step)
      case 19 =>
        val h = PathRef(s"cov_body_h_$step").known(1)
        val rest = SpaceMention(s"cov_body_r_$step")
        val loc = if other.loc.headGroups.nonEmpty then child.loc else ZLoc.empty
        tag(label, Term(Space.Iteration(other.expr, h, rest, child.expr), loc))
      case 20 => tag(label, Term(Space.Range(\/(child.expr), 0, child.loc.tailsUnion.trie.pathCount.min(3)), child.loc.tailsUnion.range(0, child.loc.tailsUnion.trie.pathCount.min(3))))
      case 21 => tag(label, Term(\/(\/(child.expr)), child.loc.tailsUnion.tailsUnion))
      case _ =>
        val sub = Term(child.expr \ other.expr, child.loc.diff(other.loc))
        tag(label, Term(/\(sub.expr), sub.loc.tailsIntersection))

  private def randomDerivedTerm(pool: Vector[Term], id: Int, step: Int)(using rng: Random): Term =
    val a = pool(rng.nextInt(pool.length))
    val b = pool(rng.nextInt(pool.length))
    val candidate =
      rng.nextInt(12) match
        case 0 => rangeTerm(a, id, step)
        case 1 => headsTerm(a, id, step)
        case 2 => tailsTerm(a, id, step)
        case 3 => meetTailsTerm(a, id, step)
        case 4 => unwrapTerm(a, id, step).getOrElse(headsTerm(a, id, step))
        case 5 => combineTerms(a, b, id, step)
        case 6 => iterTerm(a, id, step)
        case _ => combineTerms(a, b, id, step)
    if bounded(candidate) then candidate else rangeTerm(candidate, id, step)

  private def growExpression(base: FuzzCase, id: Int, minSteps: Int, maxSteps: Int, coverageBias: Boolean)(using rng: Random): FuzzCase =
    val steps = minSteps + rng.nextInt((maxSteps - minSteps + 1).max(1))
    val coverageSeeds = coverageSeedTerms(base.term, base.args)
    var pool = ((if coverageBias then argSeedTerms(base.args) ++ coverageSeeds else argSeedTerms(base.args)) :+ base.term).filter(bounded(_))
    if pool.isEmpty then pool = Vector(base.term)

    val forcedRange = rangeTerm(base.term, id, 0)
    val forcedIter = iterTerm(base.term, id, 1)
    val forcedTailsOverTails = tag("forced_tails_over_tails", Term(\/(\/(base.term.expr)), base.term.loc.tailsUnion.tailsUnion))
    val forcedMeetOverSub =
      val sub = Term(base.term.expr \ coverageSeeds.head.expr, base.term.loc.diff(coverageSeeds.head.loc))
      tag("forced_meet_over_sub", Term(/\(sub.expr), sub.loc.tailsIntersection))
    val forcedCoverage = Vector(forcedTailsOverTails, forcedMeetOverSub)
    pool = (pool ++ Vector(forcedRange, forcedIter) ++ (if coverageBias then forcedCoverage else Vector.empty)).filter(bounded(_))

    val selected = mutable.ArrayBuffer.empty[Term]
    selected += forcedRange
    selected += forcedIter
    if coverageBias then
      selected += forcedTailsOverTails
      selected += forcedMeetOverSub

    var step = 2
    while step < steps do
      val next =
        if coverageBias && rng.nextInt(100) < 55 then coverageDerivedTerm(pool, id, step)
        else randomDerivedTerm(pool, id, step)
      if bounded(next) then
        pool :+= next
        if selected.length < 14 || rng.nextBoolean() then selected += next
      step += 1

    val picked =
      rng.shuffle(selected.toVector.distinctBy(_.expr)).take(14)
    val enough =
      if picked.length >= 8 then picked
      else picked ++ rng.shuffle(pool).take(8 - picked.length)
    val finalTerm = unionTerms(enough.zipWithIndex.map((t, i) => tag(s"view_$i", t)))
    base.copy(name = s"expr-${base.name}", term = finalTerm)

  private type Scenario = (Int, Random) => FuzzCase

  private val scenarioPool: Vector[(Int, Scenario)] = Vector(
      4 -> ((id, r) => { given Random = r; graphNeighbors(id) }),
      4 -> ((id, r) => { given Random = r; groupSkills(id) }),
      3 -> ((id, r) => { given Random = r; rangePodium(id) }),
      3 -> ((id, r) => { given Random = r; commonTags(id) }),
      3 -> ((id, r) => { given Random = r; pairPipeline(id) }),
      2 -> ((id, r) => { given Random = r; permissionMashup(id) })
  )

  private val scenario: Dist[Scenario] =
    Dist.weighted(scenarioPool*)

  def sample(id: Int)(using rng: Random): FuzzCase =
    val build = scenario.sample
    growExpression(build(id, rng), id, minSteps = 8, maxSteps = 15, coverageBias = false)

  def samples(count: Int, seed: Long = 0x5157f0ffL): Vector[FuzzCase] =
    given Random = Random(seed)
    Vector.tabulate(count)(sample)

  def coverageSample(id: Int)(using rng: Random): FuzzCase =
    val build = scenario.sample
    growExpression(build(id, rng), id, minSteps = 8, maxSteps = 15, coverageBias = true)

  def coverageSamples(count: Int, seed: Long = 0x7a11cafeL): Vector[FuzzCase] =
    given Random = Random(seed)
    Vector.tabulate(count)(coverageSample)

  def showcase(count: Int = 10, seed: Long = 20260625L): Vector[FuzzCase] =
    given Random = Random(seed)
    Vector.tabulate(count) { i =>
      val build = scenario.sample
      growExpression(build(i, summon[Random]), i, minSteps = 24, maxSteps = 38, coverageBias = true)
    }

  def largeSample(id: Int)(using rng: Random): FuzzCase =
    val build = scenario.sample
    growExpression(build(id, rng), id, minSteps = 24, maxSteps = 38, coverageBias = true)

object ZipperFuzzerTermStats:
  case class EdgeKey(childType: String, parentType: String, position: String)

  final class Collector:
    val edges: mutable.HashMap[EdgeKey, Long] = mutable.HashMap.empty
    val nodeCounts: mutable.HashMap[String, Long] = mutable.HashMap.empty
    var programs: Long = 0L
    var totalNodes: Long = 0L
    var totalEdges: Long = 0L

    private def bump(map: mutable.HashMap[String, Long], key: String, n: Long = 1L): Unit =
      map.update(key, map.getOrElse(key, 0L) + n)

    private def bumpEdge(childType: String, parentType: String, position: String): Unit =
      val key = EdgeKey(childType, parentType, position)
      edges.update(key, edges.getOrElse(key, 0L) + 1L)
      totalEdges += 1L

    private def seeNode(termType: String): Unit =
      bump(nodeCounts, termType)
      totalNodes += 1L

    private def pathType(p: Path): String = p match
      case Path.Deref(_) => "Path.Deref"
      case Path.Constant(_) => "Path.Constant"
      case Path.Concat(_, _) => "Path.Concat"
      case Path.GroundedPP(_, _) => "Path.GroundedPP"
      case Path.GroundedSP(_, _) => "Path.GroundedSP"

    private def spaceType(s: Space): String = s match
      case Space.Empty => "Space.Empty"
      case Space.Call(_, _, _) => "Space.Call"
      case Space.Mention(_) => "Space.Mention"
      case Space.Singleton(_) => "Space.Singleton"
      case Space.Literal(_) => "Space.Literal"
      case Space.Union(_, _) => "Space.Union"
      case Space.Intersection(_, _) => "Space.Intersection"
      case Space.Subtraction(_, _) => "Space.Subtraction"
      case Space.Restriction(_, _) => "Space.Restriction"
      case Space.Raffination(_, _) => "Space.Raffination"
      case Space.Composition(_, _) => "Space.Composition"
      case Space.Iteration(_, _, _, _) => "Space.Iteration"
      case Space.Fold(_, _, _, _, _, _, _) => "Space.Fold"
      case Space.Fixpoint(_, _, _) => "Space.Fixpoint"
      case Space.Wrap(_, _) => "Space.Wrap"
      case Space.Unwrap(_, _) => "Space.Unwrap"
      case Space.TailsUnion(_) => "Space.TailsUnion"
      case Space.TailsIntersection(_) => "Space.TailsIntersection"
      case Space.PrefixClosure(_) => "Space.PrefixClosure"
      case Space.SuffixClosure(_) => "Space.SuffixClosure"
      case Space.TailsClosure(_) => "Space.TailsClosure"
      case Space.GroundedPS(_, _) => "Space.GroundedPS"
      case Space.GroundedSS(_, _) => "Space.GroundedSS"
      case Space.Range(_, _, _) => "Space.Range"

    private def edgePath(parentType: String, position: String, child: Path): Unit =
      bumpEdge(pathType(child), parentType, position)
      visitPath(child)

    private def edgeSpace(parentType: String, position: String, child: Space): Unit =
      bumpEdge(spaceType(child), parentType, position)
      visitSpace(child)

    def visitPath(p: Path): Unit =
      val parent = pathType(p)
      seeNode(parent)
      p match
        case Path.Deref(_) | Path.Constant(_) => ()
        case Path.Concat(l, r) =>
          edgePath(parent, "left", l)
          edgePath(parent, "right", r)
        case Path.GroundedPP(path, _) =>
          edgePath(parent, "path", path)
        case Path.GroundedSP(space, _) =>
          edgeSpace(parent, "space", space)

    def visitSpace(s: Space): Unit =
      val parent = spaceType(s)
      seeNode(parent)
      s match
        case Space.Empty | Space.Mention(_) | Space.Literal(_) => ()
        case Space.Call(_, refs, mentions) =>
          refs.zipWithIndex.foreach((p, i) => edgePath(parent, s"ref[$i]", p))
          mentions.zipWithIndex.foreach((m, i) => edgeSpace(parent, s"mention[$i]", m))
        case Space.Singleton(p) =>
          edgePath(parent, "path", p)
        case Space.Union(l, r) =>
          edgeSpace(parent, "left", l)
          edgeSpace(parent, "right", r)
        case Space.Intersection(l, r) =>
          edgeSpace(parent, "left", l)
          edgeSpace(parent, "right", r)
        case Space.Subtraction(l, r) =>
          edgeSpace(parent, "left", l)
          edgeSpace(parent, "right", r)
        case Space.Restriction(src, prefixes) =>
          edgeSpace(parent, "src", src)
          edgeSpace(parent, "prefixes", prefixes)
        case Space.Raffination(src, prefixes) =>
          edgeSpace(parent, "src", src)
          edgeSpace(parent, "prefixes", prefixes)
        case Space.Composition(l, r) =>
          edgeSpace(parent, "left", l)
          edgeSpace(parent, "right", r)
        case Space.Iteration(src, _, _, body) =>
          edgeSpace(parent, "src", src)
          edgeSpace(parent, "body", body)
        case Space.Fold(src, initial, _, _, _, body, update) =>
          edgeSpace(parent, "src", src)
          edgePath(parent, "initial", initial)
          edgeSpace(parent, "body", body)
          edgePath(parent, "update", update)
        case Space.Fixpoint(initial, _, step) =>
          edgeSpace(parent, "initial", initial)
          edgeSpace(parent, "step", step)
        case Space.Wrap(src, prefix) =>
          edgeSpace(parent, "src", src)
          edgePath(parent, "prefix", prefix)
        case Space.Unwrap(src, prefix) =>
          edgeSpace(parent, "src", src)
          edgePath(parent, "prefix", prefix)
        case Space.TailsUnion(src) =>
          edgeSpace(parent, "src", src)
        case Space.TailsIntersection(src) =>
          edgeSpace(parent, "src", src)
        case Space.PrefixClosure(src) =>
          edgeSpace(parent, "src", src)
        case Space.SuffixClosure(src) =>
          edgeSpace(parent, "src", src)
        case Space.TailsClosure(src) =>
          edgeSpace(parent, "src", src)
        case Space.GroundedPS(path, _) =>
          edgePath(parent, "path", path)
        case Space.GroundedSS(src, _) =>
          edgeSpace(parent, "src", src)
        case Space.Range(src, _, _) =>
          edgeSpace(parent, "src", src)

    def addProgram(s: Space): Unit =
      programs += 1L
      visitSpace(s)

  private def csvCell(s: String): String =
    if s.exists(ch => ch == ',' || ch == '"' || ch == '\n') then
      "\"" + s.replace("\"", "\"\"") + "\""
    else s

  private def xml(s: String): String =
    s.flatMap {
      case '&' => "&amp;"
      case '<' => "&lt;"
      case '>' => "&gt;"
      case '"' => "&quot;"
      case '\'' => "&apos;"
      case c => c.toString
    }

  private def short(n: Long): String =
    if n >= 1_000_000_000L then f"${n / 1_000_000_000.0}%.1fB"
    else if n >= 1_000_000L then f"${n / 1_000_000.0}%.1fM"
    else if n >= 10_000L then f"${n / 1_000.0}%.0fk"
    else n.toString

  private def heatColor(count: Long, max: Long): String =
    if count == 0L || max == 0L then "#ffffff"
    else
      val t = math.log1p(count.toDouble) / math.log1p(max.toDouble)
      val r = (247 - 180 * t).round.toInt
      val g = (251 - 190 * t).round.toInt
      val b = (255 - 225 * t).round.toInt
      f"#$r%02x$g%02x$b%02x"

  private def write(path: NioPath, text: String): Unit =
    Files.writeString(path, text, StandardCharsets.UTF_8)

  private def sortedRows(c: Collector): Vector[String] =
    c.nodeCounts.keys.toVector.sorted

  private def sortedColumns(c: Collector): Vector[(String, String)] =
    c.edges.keysIterator.map(k => k.parentType -> k.position).toSet.toVector
      .sortBy((parent, pos) => parent + "@" + pos)

  private def matrixCount(c: Collector, row: String, col: (String, String)): Long =
    c.edges.getOrElse(EdgeKey(row, col._1, col._2), 0L)

  def writeCsv(c: Collector, outDir: NioPath): Unit =
    val rows = sortedRows(c)
    val cols = sortedColumns(c)
    val matrix = new StringBuilder
    matrix.append(("child_type" +: cols.map((p, pos) => s"$p@$pos")).map(csvCell).mkString(",")).append('\n')
    rows.foreach { row =>
      matrix.append((row +: cols.map(col => matrixCount(c, row, col).toString)).map(csvCell).mkString(",")).append('\n')
    }
    write(outDir.resolve("fuzzer_term_matrix.csv"), matrix.result())

    val edges = new StringBuilder
    edges.append("child_type,parent_type,position,count\n")
    c.edges.toVector.sortBy((k, n) => (-n, k.childType, k.parentType, k.position)).foreach { (k, n) =>
      edges.append(Vector(k.childType, k.parentType, k.position, n.toString).map(csvCell).mkString(",")).append('\n')
    }
    write(outDir.resolve("fuzzer_term_edges.csv"), edges.result())

  def writeSvg(c: Collector, outDir: NioPath): Unit =
    val rows = sortedRows(c)
    val cols = sortedColumns(c)
    val cellW = 38
    val cellH = 24
    val left = 170
    val top = 210
    val width = left + cols.length * cellW + 40
    val height = top + rows.length * cellH + 70
    val max = c.edges.valuesIterator.foldLeft(0L)(_ max _)

    val b = new StringBuilder
    b.append(s"""<svg xmlns="http://www.w3.org/2000/svg" width="$width" height="$height" viewBox="0 0 $width $height">""").append('\n')
    b.append("""<style>text{font-family:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace;font-size:11px}.title{font-size:16px;font-weight:700}.small{font-size:10px}.axis{fill:#222}.zero{fill:#f8fafc}</style>""").append('\n')
    b.append(s"""<rect width="$width" height="$height" fill="white"/>""").append('\n')
    b.append(s"""<text x="20" y="28" class="title">MORKL zipper fuzzer term inclusion matrix</text>""").append('\n')
    b.append(s"""<text x="20" y="48" class="small">Programs: ${c.programs}; nodes: ${c.totalNodes}; edges: ${c.totalEdges}; cell color is log-scaled by count.</text>""").append('\n')
    b.append(s"""<text x="20" y="${top - 14}" class="axis">child term type X</text>""").append('\n')
    b.append(s"""<text x="$left" y="70" class="axis">parent term type Y @ position p</text>""").append('\n')

    cols.zipWithIndex.foreach { case ((parent, pos), i) =>
      val x = left + i * cellW + cellW / 2
      b.append(s"""<g transform="translate($x,${top - 18}) rotate(-58)"><text class="axis">${xml(parent + "@" + pos)}</text></g>""").append('\n')
    }

    rows.zipWithIndex.foreach { case (row, j) =>
      val y = top + j * cellH
      b.append(s"""<text x="${left - 8}" y="${y + 16}" text-anchor="end" class="axis">${xml(row)}</text>""").append('\n')
      cols.zipWithIndex.foreach { case (col, i) =>
        val x = left + i * cellW
        val n = matrixCount(c, row, col)
        val color = heatColor(n, max)
        b.append(s"""<rect x="$x" y="$y" width="$cellW" height="$cellH" fill="$color" stroke="#e5e7eb" stroke-width="0.5">""")
        b.append(s"""<title>${xml(row)} in ${xml(col._1)} @ ${xml(col._2)} = $n</title></rect>""").append('\n')
        if n > 0 then
          val textColor = if math.log1p(n.toDouble) / math.log1p(max.toDouble.max(1.0)) > 0.62 then "white" else "#111827"
          b.append(s"""<text x="${x + cellW / 2}" y="${y + 16}" text-anchor="middle" fill="$textColor" class="small">${short(n)}</text>""").append('\n')
      }
    }

    val legendX = left
    val legendY = height - 42
    val legendW = 220
    (0 until legendW).foreach { dx =>
      val t = dx.toDouble / (legendW - 1).toDouble
      val pseudo = math.expm1(t * math.log1p(max.toDouble)).round.max(1L)
      b.append(s"""<rect x="${legendX + dx}" y="$legendY" width="1" height="12" fill="${heatColor(pseudo, max)}"/>""")
    }
    b.append('\n')
    b.append(s"""<text x="$legendX" y="${legendY + 28}" class="small">1</text>""").append('\n')
    b.append(s"""<text x="${legendX + legendW}" y="${legendY + 28}" text-anchor="end" class="small">${short(max)}</text>""").append('\n')
    b.append("</svg>\n")
    write(outDir.resolve("fuzzer_term_matrix.svg"), b.result())

  def writeMarkdown(c: Collector, elapsedMs: Long, outDir: NioPath): Unit =
    val topEdges = c.edges.toVector.sortBy((k, n) => (-n, k.parentType, k.position, k.childType)).take(30)
    val rows = Vector.newBuilder[String]
    rows += "# Zipper Fuzzer Term Inclusion Matrix"
    rows += ""
    rows += s"- Programs: ${c.programs}"
    rows += s"- Total AST nodes: ${c.totalNodes}"
    rows += s"- Total child edges: ${c.totalEdges}"
    rows += f"- Average nodes/program: ${c.totalNodes.toDouble / c.programs.max(1)}%.2f"
    rows += f"- Average edges/program: ${c.totalEdges.toDouble / c.programs.max(1)}%.2f"
    rows += f"- Generation and counting time: ${elapsedMs / 1000.0}%.3f s"
    rows += "- Matrix CSV: `fuzzer_term_matrix.csv`"
    rows += "- Edge-list CSV: `fuzzer_term_edges.csv`"
    rows += "- Heatmap SVG: `fuzzer_term_matrix.svg`"
    rows += ""
    rows += "![Term inclusion heatmap](fuzzer_term_matrix.svg)"
    rows += ""
    rows += "## Top Edges"
    rows += ""
    rows += "| child type X | parent type Y | position p | count |"
    rows += "|---|---|---:|---:|"
    topEdges.foreach { (k, n) =>
      rows += s"| `${k.childType}` | `${k.parentType}` | `${k.position}` | $n |"
    }
    rows += ""
    write(outDir.resolve("FUZZER_TERM_MATRIX.md"), rows.result().mkString("\n"))

  def collect(count: Int, seed: Long, progressEvery: Int = 0): (Collector, Long) =
    given Random = Random(seed)
    val collector = Collector()
    val start = System.nanoTime()
    var i = 0
    while i < count do
      val c = ZipperProgramFuzzer.largeSample(i)
      collector.addProgram(c.term.expr)
      i += 1
      if progressEvery > 0 && i % progressEvery == 0 then
        val elapsed = (System.nanoTime() - start).toDouble / 1_000_000_000.0
        println(f"generated $i%,d / $count%,d programs in $elapsed%.1f s")
    val elapsedMs = ((System.nanoTime() - start) / 1_000_000L).max(0L)
    collector -> elapsedMs

  def run(count: Int, seed: Long, outDir: NioPath): Unit =
    Files.createDirectories(outDir)
    val progressEvery = math.max(1, count / 20)
    val (collector, elapsedMs) = collect(count, seed, progressEvery)
    writeCsv(collector, outDir)
    writeSvg(collector, outDir)
    writeMarkdown(collector, elapsedMs, outDir)
    println(s"wrote ${outDir.resolve("FUZZER_TERM_MATRIX.md")}")
    println(s"wrote ${outDir.resolve("fuzzer_term_matrix.svg")}")
    println(s"wrote ${outDir.resolve("fuzzer_term_matrix.csv")}")
    println(f"programs=${collector.programs}%,d nodes=${collector.totalNodes}%,d edges=${collector.totalEdges}%,d time=${elapsedMs / 1000.0}%.3f s")

object RejectionSamplingFilters:
  final case class EvalFrame(pc: PathContextMap, sc: TrieSpaceContextMap)

  final case class OutputMetrics(inputCount: Int,
                                 uniqueOutputs: Int,
                                 outputEntropy: Double,
                                 changedTransitions: Int,
                                 nonEmptyOutputs: Int,
                                 zeroOutputs: Int,
                                 minPaths: Int,
                                 maxPaths: Int,
                                 meanPaths: Double,
                                 pathCountStddev: Double,
                                 unionOutputPaths: Int,
                                 interestingness: Double)

  final case class SensitivityWitness(input: String, beforePaths: Int, afterPaths: Int)

  final case class Acceptance(metrics: OutputMetrics,
                              witnesses: Vector[SensitivityWitness],
                              outputs: Vector[TrieSpace])

  final case class InterestingnessConfig(minUniqueOutputs: Int = 3,
                                         minScore: Double = 35.0,
                                         minNonEmptyOutputs: Int = 1,
                                         maxOutputPaths: Int = 4096)

  private def entropy(freqs: Iterable[Int], total: Int): Double =
    if total <= 1 then 0.0
    else
      val h = freqs.foldLeft(0.0) { (acc, n) =>
        val p = n.toDouble / total.toDouble
        acc - p * (math.log(p) / math.log(2.0))
      }
      h / (math.log(total.toDouble) / math.log(2.0))

  private def score(unique: Int,
                    inputCount: Int,
                    ent: Double,
                    changes: Int,
                    nonEmpty: Int,
                    unionPaths: Int,
                    stddev: Double): Double =
    val uniqueNorm = (unique - 1).max(0).toDouble / (inputCount - 1).max(1).toDouble
    val changeNorm = changes.toDouble / (inputCount - 1).max(1).toDouble
    val nonEmptyNorm = nonEmpty.toDouble / inputCount.max(1).toDouble
    val unionNorm = (math.log1p(unionPaths.toDouble) / math.log1p(512.0)).min(1.0)
    val stdNorm = (math.log1p(stddev) / math.log1p(64.0)).min(1.0)
    100.0 * (0.34 * uniqueNorm + 0.22 * ent + 0.16 * changeNorm + 0.12 * nonEmptyNorm + 0.10 * unionNorm + 0.06 * stdNorm)

  def evalOutputs(expr: Space,
                  frames: Vector[EvalFrame],
                  maxOutputPaths: Int): Option[Vector[TrieSpace]] =
    try
      val out = Vector.newBuilder[TrieSpace]
      var ok = true
      val it = frames.iterator
      while ok && it.hasNext do
        val frame = it.next()
        val value = evalTrie(expr)(using frame.pc, frame.sc, PartialFunction.empty)
        if value.pathCount > maxOutputPaths then ok = false
        else out += value
      if ok then Some(out.result()) else None
    catch
      case NonFatal(_) => None

  def metrics(outputs: Vector[TrieSpace]): OutputMetrics =
    val inputCount = outputs.length
    val freqs = mutable.HashMap.empty[TrieSpace, Int]
    var unionOut = TrieSpace.empty
    var nonEmpty = 0
    var zero = 0
    var minPaths = Int.MaxValue
    var maxPaths = 0
    var sum = 0.0
    var sumSq = 0.0
    var changed = 0
    var prev: TrieSpace | Null = null
    outputs.foreach { out =>
      val n = out.pathCount
      freqs.update(out, freqs.getOrElse(out, 0) + 1)
      unionOut = unionOut.union(out)
      if out.isEmpty then zero += 1 else nonEmpty += 1
      minPaths = minPaths.min(n)
      maxPaths = maxPaths.max(n)
      sum += n
      sumSq += n.toDouble * n.toDouble
      if prev != null && out != prev then changed += 1
      prev = out
    }
    val mean = sum / inputCount.max(1).toDouble
    val variance = (sumSq / inputCount.max(1).toDouble - mean * mean).max(0.0)
    val ent = entropy(freqs.values, inputCount)
    val stddev = math.sqrt(variance)
    OutputMetrics(
      inputCount = inputCount,
      uniqueOutputs = freqs.size,
      outputEntropy = ent,
      changedTransitions = changed,
      nonEmptyOutputs = nonEmpty,
      zeroOutputs = zero,
      minPaths = if minPaths == Int.MaxValue then 0 else minPaths,
      maxPaths = maxPaths,
      meanPaths = mean,
      pathCountStddev = stddev,
      unionOutputPaths = unionOut.pathCount,
      interestingness = score(freqs.size, inputCount, ent, changed, nonEmpty, unionOut.pathCount, stddev)
    )

  def interestingness(expr: Space,
                      frames: Vector[EvalFrame],
                      config: InterestingnessConfig = InterestingnessConfig()): Option[(OutputMetrics, Vector[TrieSpace])] =
    evalOutputs(expr, frames, config.maxOutputPaths).flatMap { outputs =>
      val m = metrics(outputs)
      Option.when(
        m.uniqueOutputs >= config.minUniqueOutputs &&
          m.interestingness >= config.minScore &&
          m.nonEmptyOutputs >= config.minNonEmptyOutputs
      )(m -> outputs)
    }

  def sensitivity(expr: Space,
                  baseline: EvalFrame,
                  perturbations: Vector[(String, EvalFrame)],
                  requiredInputs: Vector[String],
                  maxOutputPaths: Int = 4096): Option[Vector[SensitivityWitness]] =
    evalOutputs(expr, Vector(baseline), maxOutputPaths).flatMap(_.headOption).flatMap { baseOut =>
      val seen = mutable.LinkedHashMap.empty[String, SensitivityWitness]
      var ok = true
      val it = perturbations.iterator
      while ok && it.hasNext do
        val (name, frame) = it.next()
        evalOutputs(expr, Vector(frame), maxOutputPaths).flatMap(_.headOption) match
          case Some(out) =>
            if out != baseOut then
              seen.update(name, SensitivityWitness(name, baseOut.pathCount, out.pathCount))
          case None =>
            ok = false
      Option.when(ok && requiredInputs.forall(seen.contains))(requiredInputs.flatMap(seen.get))
    }

  def accept(expr: Space,
             interestingFrames: Vector[EvalFrame],
             baseline: EvalFrame,
             perturbations: Vector[(String, EvalFrame)],
             requiredInputs: Vector[String],
             config: InterestingnessConfig = InterestingnessConfig()): Option[Acceptance] =
    for
      (m, outputs) <- interestingness(expr, interestingFrames, config)
      witnesses <- sensitivity(expr, baseline, perturbations, requiredInputs, config.maxOutputPaths)
    yield Acceptance(m, witnesses, outputs)

object ZipperFuzzerInterestingness:
  import ZipperProgramFuzzer.*

  private val prefixRef = PathRef("probe_prefix")
  private val payloadRef = PathRef("probe_payload")
  private val probeRefs = Vector(prefixRef, payloadRef)

  final case class ProbeProgram(name: String,
                                wrapper: String,
                                base: FuzzCase,
                                expr: Space,
                                mentions: Vector[SpaceMention],
                                refs: Vector[PathRef])

  final case class InputFrame(pc: PathContextMap, sc: TrieSpaceContextMap)

  final case class ProgramStats(programId: Int,
                                name: String,
                                wrapper: String,
                                argCount: Int,
                                inputCount: Int,
                                uniqueOutputs: Int,
                                outputEntropy: Double,
                                changedTransitions: Int,
                                nonEmptyOutputs: Int,
                                zeroOutputs: Int,
                                minPaths: Int,
                                maxPaths: Int,
                                meanPaths: Double,
                                pathCountStddev: Double,
                                unionOutputPaths: Int,
                                interestingness: Double,
                                elapsedMicros: Long)

  final case class Summary(count: Int,
                           inputsPerProgram: Int,
                           seed: Long,
                           elapsedMs: Long,
                           stats: Vector[ProgramStats])

  private val atoms = Vector("ann", "bob", "cora", "dan", "eli", "fay", "gia", "hal", "ivy", "jo",
    "red", "blue", "green", "ops", "ml", "db", "hot", "cold", "dense", "sparse", "north", "south")

  private def path(s: String): PathValue = Syntax.parse(s)
  private def pathFromItems(items: Iterable[PathItem]): PathValue = PathValue(items.toList)
  private def argExpr(a: Arg): Space = Space.Mention(a.name)

  private def pathChoices(base: FuzzCase): Vector[PathValue] =
    val args = base.args
    val fromArgs = args.flatMap(_.loc.paths).filter(_.items.nonEmpty)
    val fromResult = base.term.loc.paths.filter(_.items.nonEmpty)
    val prefixes = (fromArgs ++ fromResult).flatMap(_.prefixes)
    (Vector(path("probe")) ++ prefixes ++ fromArgs ++ fromResult ++ atoms.take(8).map(path)).distinctBy(_.show).take(160)

  private def instrument(base: FuzzCase, id: Int)(using rng: Random): ProbeProgram =
    val args = base.args
    val arg = args(rng.nextInt(args.length.max(1)))
    val mention = if args.nonEmpty then argExpr(arg) else Space.Empty
    val payload = Path.Deref(payloadRef)
    val prefix = Path.Deref(prefixRef)
    val (wrapper, expr) = rng.nextInt(7) match
      case 0 => "identity" -> base.term.expr
      case 1 => "wrap-by-path" -> Space.Wrap(base.term.expr, prefix)
      case 2 => "unwrap-arg-by-path" -> (Space.Unwrap(mention, prefix) \/ base.term.expr)
      case 3 => "singleton-payload-union" -> (base.term.expr \/ Space.Singleton(payload))
      case 4 => "path-prefix-product" -> (Space.Singleton(prefix) x base.term.expr)
      case 5 => "path-restrict-base" -> (base.term.expr <| Space.Singleton(prefix))
      case _ => "arg-diff-path-unwrap" -> (base.term.expr \ Space.Unwrap(mention, prefix))
    ProbeProgram(s"${base.name}#$id", wrapper, base, expr, base.mentions, probeRefs)

  private def randomPathLike(choices: Vector[PathValue], i: Int)(using rng: Random): PathValue =
    if choices.nonEmpty && rng.nextInt(100) < 75 then choices(rng.nextInt(choices.length))
    else
      val len = 1 + rng.nextInt(3)
      pathFromItems((0 until len).map(j => PathItem(atoms((i + j + rng.nextInt(atoms.length)) % atoms.length))))

  private def perturbPath(p: List[Int], choices: Vector[PathValue], i: Int)(using rng: Random): List[Int] =
    if p.isEmpty || rng.nextInt(100) < 25 then TrieSpace.intern(randomPathLike(choices, i))
    else
      val items = p.map(TrieSpace.item).toBuffer
      val j = rng.nextInt(items.length)
      items(j) = PathItem(atoms((i + j + rng.nextInt(atoms.length)) % atoms.length))
      TrieSpace.intern(pathFromItems(items))

  private def perturbTrie(base: TrieSpace, choices: Vector[PathValue], i: Int)(using rng: Random): TrieSpace =
    val paths = base.encodedPaths
    if paths.isEmpty then
      TrieSpace.fromEncodedPaths(Vector.fill(1 + rng.nextInt(4))(TrieSpace.intern(randomPathLike(choices, i))))
    else
      val kept = paths.filter(_ => rng.nextInt(100) >= (15 + (i % 17)))
      val mutated = paths.iterator.filter(_ => rng.nextInt(100) < 22).map(perturbPath(_, choices, i)).toVector
      val added = Vector.fill(rng.nextInt(5))(perturbPath(paths(rng.nextInt(paths.length)), choices, i))
      val rotated = if i % 11 == 0 then paths.take((paths.length / 2).max(1)) else Vector.empty
      TrieSpace.fromEncodedPaths((kept ++ mutated ++ added ++ rotated).distinct.take(56))

  private def inputFrames(p: ProbeProgram, inputCount: Int)(using rng: Random): Vector[InputFrame] =
    val choices = pathChoices(p.base)
    Vector.tabulate(inputCount) { i =>
      val spaces =
        p.base.args.map { a =>
          val trie = if i == 0 then a.loc.trie else perturbTrie(a.loc.trie, choices, i)
          a.name -> trie
        }.toMap
      val prefix = randomPathLike(choices, i)
      val payload = path(s"payload.${i % 17}.${atoms((i + rng.nextInt(atoms.length)) % atoms.length)}")
      InputFrame(
        PathContextMap(Map(prefixRef -> prefix, payloadRef -> payload)),
        TrieSpaceContextMap(spaces)
      )
    }

  private def entropy(freqs: Iterable[Int], total: Int): Double =
    if total <= 1 then 0.0
    else
      val h = freqs.foldLeft(0.0) { (acc, n) =>
        val p = n.toDouble / total.toDouble
        acc - p * (math.log(p) / math.log(2.0))
      }
      h / (math.log(total.toDouble) / math.log(2.0))

  private def score(unique: Int,
                    inputCount: Int,
                    ent: Double,
                    changes: Int,
                    nonEmpty: Int,
                    unionPaths: Int,
                    stddev: Double): Double =
    val uniqueNorm = (unique - 1).max(0).toDouble / (inputCount - 1).max(1).toDouble
    val changeNorm = changes.toDouble / (inputCount - 1).max(1).toDouble
    val nonEmptyNorm = nonEmpty.toDouble / inputCount.max(1).toDouble
    val unionNorm = (math.log1p(unionPaths.toDouble) / math.log1p(512.0)).min(1.0)
    val stdNorm = (math.log1p(stddev) / math.log1p(64.0)).min(1.0)
    100.0 * (0.34 * uniqueNorm + 0.22 * ent + 0.16 * changeNorm + 0.12 * nonEmptyNorm + 0.10 * unionNorm + 0.06 * stdNorm)

  def measureProgram(id: Int, inputCount: Int)(using rng: Random): ProgramStats =
    val base = ZipperProgramFuzzer.coverageSample(id)
    val program = instrument(base, id)
    val frames = inputFrames(program, inputCount)
    val start = System.nanoTime()
    val freqs = mutable.HashMap.empty[TrieSpace, Int]
    var unionOut = TrieSpace.empty
    var nonEmpty = 0
    var zero = 0
    var minPaths = Int.MaxValue
    var maxPaths = 0
    var sum = 0.0
    var sumSq = 0.0
    var changed = 0
    var prev: TrieSpace | Null = null
    frames.foreach { frame =>
      val out = evalTrie(program.expr)(using frame.pc, frame.sc, PartialFunction.empty)
      val n = out.pathCount
      freqs.update(out, freqs.getOrElse(out, 0) + 1)
      unionOut = unionOut.union(out)
      if out.isEmpty then zero += 1 else nonEmpty += 1
      minPaths = minPaths.min(n)
      maxPaths = maxPaths.max(n)
      sum += n
      sumSq += n.toDouble * n.toDouble
      if prev != null && out != prev then changed += 1
      prev = out
    }
    val elapsedMicros = ((System.nanoTime() - start) / 1000L).max(0L)
    val mean = sum / inputCount.max(1).toDouble
    val variance = (sumSq / inputCount.max(1).toDouble - mean * mean).max(0.0)
    val ent = entropy(freqs.values, inputCount)
    val interestingness = score(freqs.size, inputCount, ent, changed, nonEmpty, unionOut.pathCount, math.sqrt(variance))
    ProgramStats(id, program.name, program.wrapper, program.mentions.length, inputCount,
      freqs.size, ent, changed, nonEmpty, zero,
      if minPaths == Int.MaxValue then 0 else minPaths,
      maxPaths, mean, math.sqrt(variance), unionOut.pathCount, interestingness, elapsedMicros)

  def collect(count: Int, inputCount: Int, seed: Long, progressEvery: Int = 0): Summary =
    given Random = Random(seed)
    val start = System.nanoTime()
    val rows = Vector.newBuilder[ProgramStats]
    var i = 0
    while i < count do
      rows += measureProgram(i, inputCount)
      i += 1
      if progressEvery > 0 && i % progressEvery == 0 then
        val elapsed = (System.nanoTime() - start).toDouble / 1_000_000_000.0
        println(f"measured $i%,d / $count%,d programs in $elapsed%.1f s")
    val elapsedMs = ((System.nanoTime() - start) / 1_000_000L).max(0L)
    Summary(count, inputCount, seed, elapsedMs, rows.result())

  private def csvCell(s: String): String =
    if s.exists(ch => ch == ',' || ch == '"' || ch == '\n') then "\"" + s.replace("\"", "\"\"") + "\"" else s

  private def write(path: NioPath, text: String): Unit =
    Files.writeString(path, text, StandardCharsets.UTF_8)

  private def percentile(sorted: Vector[Double], p: Double): Double =
    if sorted.isEmpty then 0.0
    else sorted(((sorted.length - 1) * p).round.toInt.max(0).min(sorted.length - 1))

  private def bucketUnique(n: Int, inputs: Int): String =
    if n <= 1 then "constant"
    else if n <= 3 then "tiny"
    else if n <= 10 then "low"
    else if n < inputs then "medium"
    else "maximal"

  def writeOutputs(summary: Summary, outDir: NioPath): Unit =
    Files.createDirectories(outDir)
    val header = Vector("program_id", "name", "wrapper", "arg_count", "input_count", "unique_outputs",
      "output_entropy", "changed_transitions", "non_empty_outputs", "zero_outputs", "min_paths", "max_paths",
      "mean_paths", "path_count_stddev", "union_output_paths", "interestingness", "elapsed_micros")
    val csv = new StringBuilder
    csv.append(header.mkString(",")).append('\n')
    summary.stats.foreach { s =>
      val row = Vector(
        s.programId.toString, s.name, s.wrapper, s.argCount.toString, s.inputCount.toString, s.uniqueOutputs.toString,
        f"${s.outputEntropy}%.6f", s.changedTransitions.toString, s.nonEmptyOutputs.toString, s.zeroOutputs.toString,
        s.minPaths.toString, s.maxPaths.toString, f"${s.meanPaths}%.3f", f"${s.pathCountStddev}%.3f",
        s.unionOutputPaths.toString, f"${s.interestingness}%.3f", s.elapsedMicros.toString
      )
      csv.append(row.map(csvCell).mkString(",")).append('\n')
    }
    write(outDir.resolve("interestingness_programs.csv"), csv.result())

    val uniques = summary.stats.map(_.uniqueOutputs.toDouble).sorted
    val scores = summary.stats.map(_.interestingness).sorted
    val entropies = summary.stats.map(_.outputEntropy).sorted
    val buckets = summary.stats.groupMapReduce(s => bucketUnique(s.uniqueOutputs, summary.inputsPerProgram))(_ => 1)(_ + _)
    val wrappers = summary.stats.groupMapReduce(_.wrapper)(_ => 1)(_ + _).toVector.sortBy((_, n) => -n)
    val top = summary.stats.sortBy(s => (-s.interestingness, -s.uniqueOutputs, -s.unionOutputPaths)).take(20)

    val md = new StringBuilder
    md.append("# Zipper Fuzzer Output Interestingness\n\n")
    md.append(s"- Programs measured: ${summary.count}\n")
    md.append(s"- Inputs per program: ${summary.inputsPerProgram}\n")
    md.append(s"- Seed: ${summary.seed}\n")
    md.append(f"- Elapsed: ${summary.elapsedMs / 1000.0}%.3f s\n")
    md.append(f"- Mean time/program: ${summary.elapsedMs * 1000.0 / summary.count.max(1)}%.1f us\n")
    md.append("\n## Unique Output Counts\n\n")
    md.append(f"- mean: ${uniques.sum / uniques.length.max(1)}%.3f\n")
    md.append(f"- p50: ${percentile(uniques, 0.50)}%.0f\n")
    md.append(f"- p90: ${percentile(uniques, 0.90)}%.0f\n")
    md.append(f"- p99: ${percentile(uniques, 0.99)}%.0f\n")
    md.append(f"- max: ${if uniques.isEmpty then 0.0 else uniques.last}%.0f\n")
    md.append("\n## Interestingness Score\n\n")
    md.append(f"- mean: ${scores.sum / scores.length.max(1)}%.3f\n")
    md.append(f"- p50: ${percentile(scores, 0.50)}%.3f\n")
    md.append(f"- p90: ${percentile(scores, 0.90)}%.3f\n")
    md.append(f"- p99: ${percentile(scores, 0.99)}%.3f\n")
    md.append("\n## Entropy\n\n")
    md.append(f"- mean normalized entropy: ${entropies.sum / entropies.length.max(1)}%.3f\n")
    md.append(f"- p90 normalized entropy: ${percentile(entropies, 0.90)}%.3f\n")
    md.append("\n## Unique Count Buckets\n\n")
    md.append("| bucket | programs |\n|---|---:|\n")
    Vector("constant", "tiny", "low", "medium", "maximal").foreach { b =>
      md.append(s"| $b | ${buckets.getOrElse(b, 0)} |\n")
    }
    md.append("\n## Wrapper Mix\n\n")
    md.append("| wrapper | programs |\n|---|---:|\n")
    wrappers.foreach((w, n) => md.append(s"| `$w` | $n |\n"))
    md.append("\n## Top Programs By Interestingness\n\n")
    md.append("| id | wrapper | unique | entropy | changed | nonempty | union paths | score | name |\n")
    md.append("|---:|---|---:|---:|---:|---:|---:|---:|---|\n")
    top.foreach { s =>
      md.append(f"| ${s.programId} | `${s.wrapper}` | ${s.uniqueOutputs} | ${s.outputEntropy}%.3f | ${s.changedTransitions} | ${s.nonEmptyOutputs} | ${s.unionOutputPaths} | ${s.interestingness}%.3f | `${s.name}` |\n")
    }
    write(outDir.resolve("INTERESTINGNESS.md"), md.result())

  def run(count: Int, inputCount: Int, seed: Long, outDir: NioPath): Unit =
    val progressEvery = math.max(1, count / 20)
    val summary = collect(count, inputCount, seed, progressEvery)
    writeOutputs(summary, outDir)
    println(s"wrote ${outDir.resolve("INTERESTINGNESS.md")}")
    println(s"wrote ${outDir.resolve("interestingness_programs.csv")}")
    val uniqueMean = summary.stats.map(_.uniqueOutputs).sum.toDouble / summary.stats.length.max(1).toDouble
    val scoreMean = summary.stats.map(_.interestingness).sum / summary.stats.length.max(1).toDouble
    println(f"programs=${summary.count}%,d inputs=${summary.inputsPerProgram} unique_mean=$uniqueMean%.3f interestingness_mean=$scoreMean%.3f time=${summary.elapsedMs / 1000.0}%.3f s")

object ZipperFuzzerSensitiveCorpus:
  import ZipperProgramFuzzer.*

  private val prefixRef = PathRef("probe_prefix")
  private val payloadRef = PathRef("probe_payload")
  private val probeRefs = Vector(prefixRef, payloadRef)

  final case class Frame(pc: PathContextMap, sc: TrieSpaceContextMap)

  final case class AcceptedProgram(id: Int,
                                   candidateId: Int,
                                   name: String,
                                   base: FuzzCase,
                                   expr: Space,
                                   mentions: Vector[SpaceMention],
                                   refs: Vector[PathRef],
                                   sensitiveInputs: Vector[String],
                                   uniqueWitnessOutputs: Int,
                                   baseOutputPaths: Int,
                                   unionWitnessOutputPaths: Int,
                                   expressionChars: Int,
                                   attemptsSoFar: Int):
    def inputNames: Vector[String] =
      mentions.map(sm => s"space:${sm.s}") ++ refs.map(pr => s"path:${pr.s}")
    def fileStem: String = f"program_$id%04d_${sanitize(name)}"

  final case class Corpus(programs: Vector[AcceptedProgram],
                          seed: Long,
                          attempts: Int,
                          elapsedMs: Long):
    def acceptanceRate: Double =
      programs.length.toDouble / attempts.max(1).toDouble

  private def sanitize(s: String): String =
    s.map {
      case c if c.isLetterOrDigit => c
      case '-' | '_' => '_'
      case _ => '_'
    }.mkString.take(96)

  private def pv(s: String): PathValue =
    Syntax.parse(s)

  private def pc(s: String): Path =
    Path.Constant(pv(s))

  private def unionAll(xs: Iterable[Space]): Space =
    val it = xs.iterator
    if !it.hasNext then Space.Empty
    else
      var out = it.next()
      while it.hasNext do out = Space.Union(out, it.next())
      out

  private def pathChoices(base: FuzzCase): Vector[PathValue] =
    val fromArgs = base.args.flatMap(_.loc.paths).filter(_.items.nonEmpty)
    val fromResult = base.term.loc.paths.filter(_.items.nonEmpty)
    val prefixes = (fromArgs ++ fromResult).flatMap(_.prefixes)
    (prefixes ++ fromArgs ++ fromResult ++ Vector(pv("probe"), pv("seed"), pv("input"))).distinctBy(_.show).take(192)

  private def choosePath(base: FuzzCase, fallback: String)(using rng: Random): PathValue =
    val choices = pathChoices(base)
    if choices.nonEmpty then choices(rng.nextInt(choices.length)) else pv(fallback)

  private def inputProbe(a: Arg, idx: Int, candidateId: Int)(using rng: Random): Space =
    val label = pc(s"input.${idx}.${a.name.s}")
    val raw = Space.Wrap(a.expr, label)
    rng.nextInt(4) match
      case 0 => raw
      case 1 =>
        Space.Wrap(Space.Union(a.expr, Space.Singleton(pc(s"input_marker.$candidateId.$idx"))), label)
      case 2 =>
        Space.Union(raw, Space.Wrap(Space.Range(a.expr, 0, a.loc.trie.pathCount.max(1)), pc(s"input_range.${idx}.${a.name.s}")))
      case _ =>
        Space.Union(raw, Space.Wrap(\/(a.expr), pc(s"input_tails.${idx}.${a.name.s}")))

  private def instrument(base: FuzzCase, candidateId: Int)(using rng: Random): Space =
    val core =
      rng.nextInt(4) match
        case 0 => base.term.expr
        case 1 => Space.Wrap(base.term.expr, pc(s"core.$candidateId"))
        case 2 => Space.Union(base.term.expr, Space.Wrap(\/(base.term.expr), pc(s"core_tails.$candidateId")))
        case _ => Space.Union(base.term.expr, Space.Range(base.term.expr, 0, base.term.loc.trie.pathCount.min(8).max(1)))
    val inputBranches = base.args.zipWithIndex.map((a, i) => inputProbe(a, i, candidateId))
    val pathBranches = Vector(
      Space.Wrap(Space.Singleton(Path.Deref(prefixRef)), pc("path.probe_prefix")),
      Space.Wrap(Space.Singleton(Path.Deref(payloadRef)), pc("path.probe_payload")),
      Space.Wrap(base.term.expr, Path.Deref(prefixRef))
    )
    unionAll(rng.shuffle(core +: (inputBranches ++ pathBranches)))

  private def baseSpaces(base: FuzzCase): Map[SpaceMention, TrieSpace] =
    base.args.map(a => a.name -> a.loc.trie).toMap

  private def mutateTrie(base: TrieSpace, inputName: String, candidateId: Int, salt: Int): TrieSpace =
    val extra = TrieSpace.singleton(pv(s"sensitivity.$inputName.$candidateId.$salt"))
    base.union(extra)

  private def frame(spaces: Map[SpaceMention, TrieSpace], prefix: PathValue, payload: PathValue): Frame =
    Frame(
      PathContextMap(Map(prefixRef -> prefix, payloadRef -> payload)),
      TrieSpaceContextMap(spaces)
    )

  private def evalOut(expr: Space, f: Frame): TrieSpace =
    evalTrie(expr)(using f.pc, f.sc, PartialFunction.empty)

  private def verify(candidateId: Int, base: FuzzCase, expr: Space)(using rng: Random): Option[(Vector[String], Int, Int, Int)] =
    val spaces = baseSpaces(base)
    val basePrefix = choosePath(base, s"prefix.$candidateId")
    val basePayload = pv(s"payload.base.$candidateId")
    val baseFrame = frame(spaces, basePrefix, basePayload)
    val baseOut = evalOut(expr, baseFrame)
    val outputs = mutable.ArrayBuffer(baseOut)
    val sensitive = mutable.ArrayBuffer.empty[String]

    base.args.zipWithIndex.foreach { (arg, i) =>
      val changedSpaces = spaces.updated(arg.name, mutateTrie(arg.loc.trie, arg.name.s, candidateId, i))
      val out = evalOut(expr, frame(changedSpaces, basePrefix, basePayload))
      outputs += out
      if out != baseOut then sensitive += s"space:${arg.name.s}"
    }

    val prefixOut = evalOut(expr, frame(spaces, pv(s"prefix.changed.$candidateId"), basePayload))
    outputs += prefixOut
    if prefixOut != baseOut then sensitive += s"path:${prefixRef.s}"

    val payloadOut = evalOut(expr, frame(spaces, basePrefix, pv(s"payload.changed.$candidateId")))
    outputs += payloadOut
    if payloadOut != baseOut then sensitive += s"path:${payloadRef.s}"

    val unique = outputs.distinct.length
    val allInputs = base.args.map(a => s"space:${a.name.s}") ++ probeRefs.map(pr => s"path:${pr.s}")
    if unique >= 2 && allInputs.forall(sensitive.contains) then
      val unionPaths = outputs.foldLeft(TrieSpace.empty)(_.union(_)).pathCount
      Some((sensitive.toVector, unique, baseOut.pathCount, unionPaths))
    else None

  def generate(count: Int,
               seed: Long,
               maxAttempts: Int = 250000,
               progressEvery: Int = 0): Corpus =
    given Random = Random(seed)
    val accepted = Vector.newBuilder[AcceptedProgram]
    val start = System.nanoTime()
    var attempts = 0
    var nextId = 0
    while nextId < count && attempts < maxAttempts do
      val candidateId = attempts
      val base = ZipperProgramFuzzer.coverageSample(candidateId)
      val expr = instrument(base, candidateId)
      verify(candidateId, base, expr) match
        case Some((sensitive, unique, basePaths, unionPaths)) =>
          val name = s"sensitive-${base.name}#$candidateId"
          accepted += AcceptedProgram(nextId, candidateId, name, base, expr, base.mentions, probeRefs,
            sensitive, unique, basePaths, unionPaths, expr.show.length, attempts + 1)
          nextId += 1
          if progressEvery > 0 && nextId % progressEvery == 0 then
            val elapsed = (System.nanoTime() - start).toDouble / 1_000_000_000.0
            println(f"accepted $nextId%,d / $count%,d programs after ${attempts + 1}%,d attempts in $elapsed%.1f s")
        case None => ()
      attempts += 1
    if nextId < count then
      throw RuntimeException(s"only generated $nextId sensitive programs after $attempts attempts")
    val elapsedMs = ((System.nanoTime() - start) / 1_000_000L).max(0L)
    Corpus(accepted.result(), seed, attempts, elapsedMs)

  private def json(s: String): String =
    "\"" + s.flatMap {
      case '"' => "\\\""
      case '\\' => "\\\\"
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\t' => "\\t"
      case c if c.isControl => f"\\u${c.toInt}%04x"
      case c => c.toString
    } + "\""

  private def write(path: NioPath, text: String): Unit =
    Files.writeString(path, text, StandardCharsets.UTF_8)

  private def renderProgram(p: AcceptedProgram): String =
    val args = p.base.args.map(a => s"- `${a.name.s}` (${a.loc.trie.pathCount} paths): `${a.value.pretty}`").mkString("\n")
    s"""# ${p.fileStem}
       |
       |- Corpus id: ${p.id}
       |- Candidate id: ${p.candidateId}
       |- Space inputs: ${p.mentions.map(_.s).mkString(", ")}
       |- Path inputs: ${p.refs.map(_.s).mkString(", ")}
       |- Sensitive inputs witnessed: ${p.sensitiveInputs.mkString(", ")}
       |- Unique witness outputs: ${p.uniqueWitnessOutputs}
       |- Base output paths: ${p.baseOutputPaths}
       |- Union witness output paths: ${p.unionWitnessOutputPaths}
       |
       |## Arguments
       |
       |$args
       |
       |## Program
       |
       |```scala
       |${p.expr.show}
       |```
       |""".stripMargin

  def writeCorpus(corpus: Corpus, outDir: NioPath, sampleCount: Int = 3, sampleSeed: Long = 20260701L): Vector[AcceptedProgram] =
    Files.createDirectories(outDir)
    val programDir = outDir.resolve("programs")
    Files.createDirectories(programDir)

    corpus.programs.foreach { p =>
      write(programDir.resolve(p.fileStem + ".md"), renderProgram(p))
    }

    val jsonl = new StringBuilder
    corpus.programs.foreach { p =>
      jsonl.append("{")
      jsonl.append("\"id\":").append(p.id).append(',')
      jsonl.append("\"candidate_id\":").append(p.candidateId).append(',')
      jsonl.append("\"name\":").append(json(p.name)).append(',')
      jsonl.append("\"file\":").append(json(s"programs/${p.fileStem}.md")).append(',')
      jsonl.append("\"space_inputs\":").append(p.mentions.map(sm => json(sm.s)).mkString("[", ",", "]")).append(',')
      jsonl.append("\"path_inputs\":").append(p.refs.map(pr => json(pr.s)).mkString("[", ",", "]")).append(',')
      jsonl.append("\"sensitive_inputs\":").append(p.sensitiveInputs.map(json).mkString("[", ",", "]")).append(',')
      jsonl.append("\"unique_witness_outputs\":").append(p.uniqueWitnessOutputs).append(',')
      jsonl.append("\"base_output_paths\":").append(p.baseOutputPaths).append(',')
      jsonl.append("\"union_witness_output_paths\":").append(p.unionWitnessOutputPaths).append(',')
      jsonl.append("\"expression_chars\":").append(p.expressionChars)
      jsonl.append("}\n")
    }
    write(outDir.resolve("programs.jsonl"), jsonl.result())

    val sampleRng = Random(sampleSeed)
    val samples = sampleRng.shuffle(corpus.programs).take(sampleCount).toVector
    val sampleMd = new StringBuilder
    sampleMd.append("# Random Sensitive Corpus Samples\n\n")
    samples.foreach { p =>
      sampleMd.append(s"## ${p.fileStem}\n\n")
      sampleMd.append(s"- Inputs: ${p.inputNames.mkString(", ")}\n")
      sampleMd.append(s"- Unique witness outputs: ${p.uniqueWitnessOutputs}\n")
      sampleMd.append(s"- File: `programs/${p.fileStem}.md`\n\n")
      sampleMd.append("```scala\n")
      sampleMd.append(p.expr.show)
      sampleMd.append("\n```\n\n")
    }
    write(outDir.resolve("SAMPLES.md"), sampleMd.result())

    val byArgs = corpus.programs.groupMapReduce(_.mentions.length)(_ => 1)(_ + _).toVector.sortBy(_._1)
    val readme = new StringBuilder
    readme.append("# Sensitive Zipper Fuzzer Corpus\n\n")
    readme.append(s"- Programs: ${corpus.programs.length}\n")
    readme.append(s"- Seed: ${corpus.seed}\n")
    readme.append(s"- Attempts: ${corpus.attempts}\n")
    readme.append(f"- Acceptance rate: ${100.0 * corpus.acceptanceRate}%.2f%%\n")
    readme.append(f"- Generation time: ${corpus.elapsedMs / 1000.0}%.3f s\n")
    readme.append("- Acceptance criterion: changing each declared space input and each probe path input one at a time changes the output trie, and the witness run has at least two distinct output values.\n")
    readme.append("- Each program has a random core expression plus explicit input-probe disjuncts; every accepted program is still checked by evaluation over trie contexts.\n")
    readme.append("- Metadata: `programs.jsonl`\n")
    readme.append("- Random samples: `SAMPLES.md`\n")
    readme.append("- Full programs: `programs/*.md`\n\n")
    readme.append("## Space Input Count Mix\n\n")
    readme.append("| space inputs | programs |\n|---:|---:|\n")
    byArgs.foreach((n, c) => readme.append(s"| $n | $c |\n"))
    readme.append("\n## Random Samples\n\n")
    samples.foreach(p => readme.append(s"- `${p.fileStem}`\n"))
    write(outDir.resolve("README.md"), readme.result())
    samples

  def run(count: Int, seed: Long, outDir: NioPath): Vector[AcceptedProgram] =
    val progressEvery = math.max(1, count / 20)
    val corpus = generate(count, seed, progressEvery = progressEvery)
    val samples = writeCorpus(corpus, outDir)
    println(s"wrote ${outDir.resolve("README.md")}")
    println(s"wrote ${outDir.resolve("programs.jsonl")}")
    println(s"wrote ${outDir.resolve("SAMPLES.md")}")
    println(f"programs=${corpus.programs.length}%,d attempts=${corpus.attempts}%,d acceptance=${100.0 * corpus.acceptanceRate}%.2f%% time=${corpus.elapsedMs / 1000.0}%.3f s")
    samples.foreach(p => println(s"sample ${p.id}: ${p.fileStem}"))
    samples

object FreeExpressionTreeFuzzer:
  import RejectionSamplingFilters.*

  private val atoms = Vector(
    "ann", "bob", "cora", "dan", "eli", "fay", "gia", "hal", "ivy", "jo",
    "red", "blue", "green", "ops", "ml", "db",
    "hot", "cold", "dense", "sparse", "north", "south",
    "edge", "row", "tag", "score", "left", "right"
  )

  final case class Env(spaceInputs: Vector[SpaceMention],
                       pathInputs: Vector[PathRef],
                       boundSpaces: Vector[SpaceMention] = Vector.empty,
                       boundPaths: Vector[PathRef] = Vector.empty):
    def spaces: Vector[SpaceMention] = spaceInputs ++ boundSpaces
    def paths: Vector[PathRef] = pathInputs ++ boundPaths

  final case class Candidate(id: Int,
                             name: String,
                             env: Env,
                             expr: Space,
                             baseline: EvalFrame,
                             interestingFrames: Vector[EvalFrame],
                             perturbations: Vector[(String, EvalFrame)]):
    def requiredInputs: Vector[String] =
      env.spaceInputs.map(sm => s"space:${sm.s}") ++ env.pathInputs.map(pr => s"path:${pr.s}")

  final case class Accepted(id: Int,
                            candidateId: Int,
                            name: String,
                            env: Env,
                            expr: Space,
                            metrics: OutputMetrics,
                            witnesses: Vector[SensitivityWitness],
                            attemptsSoFar: Int):
    def fileStem: String = f"free_program_$id%04d_${sanitize(name)}"
    def inputNames: Vector[String] =
      env.spaceInputs.map(sm => s"space:${sm.s}") ++ env.pathInputs.map(pr => s"path:${pr.s}")

  final case class Corpus(programs: Vector[Accepted],
                          seed: Long,
                          attempts: Int,
                          rejectedInteresting: Int,
                          rejectedSensitivity: Int,
                          elapsedMs: Long):
    def acceptanceRate: Double =
      programs.length.toDouble / attempts.max(1).toDouble

  private def sanitize(s: String): String =
    s.map {
      case c if c.isLetterOrDigit => c
      case '-' | '_' => '_'
      case _ => '_'
    }.mkString.take(96)

  private def pv(s: String): PathValue =
    Syntax.parse(s)

  private def pc(s: String): Path =
    Path.Constant(pv(s))

  private def pick[T](xs: Vector[T])(using rng: Random): T =
    xs(rng.nextInt(xs.length))

  private def unionAll(xs: Iterable[Space]): Space =
    val it = xs.iterator
    if !it.hasNext then Space.Empty
    else
      var out = it.next()
      while it.hasNext do out = Space.Union(out, it.next())
      out

  private def randomPathValue(salt: Int, maxLen: Int = 4)(using rng: Random): PathValue =
    val len = 1 + rng.nextInt(maxLen.max(1))
    PathValue((0 until len).map { i =>
      PathItem(atoms((salt + i * 7 + rng.nextInt(atoms.length)) % atoms.length))
    }.toList)

  private def randomTrie(label: String, salt: Int)(using rng: Random): TrieSpace =
    val width = 4 + rng.nextInt(8)
    val rows = Vector.newBuilder[PathValue]
    var i = 0
    while i < width do
      val shape = rng.nextInt(5)
      val path =
        shape match
          case 0 => pv(s"$label.${atoms((salt + i) % atoms.length)}.${atoms((salt + i + 5) % atoms.length)}")
          case 1 => pv(s"edge.${atoms((salt + i * 2) % atoms.length)}.${atoms((salt + i * 2 + 1) % atoms.length)}")
          case 2 => pv(s"row.${i % 5}.${atoms((salt + i + 3) % atoms.length)}")
          case 3 => pv(s"tag.${atoms((salt + i + 9) % atoms.length)}")
          case _ => randomPathValue(salt + i, maxLen = 3)
      rows += path
      i += 1
    TrieSpace.fromPaths(rows.result())

  private def randomSpaceValue(salt: Int)(using rng: Random): SpaceValue =
    randomTrie(s"lit${salt % 11}", salt).toSpaceValue

  private def genPath(depth: Int, env: Env, salt: Int)(using rng: Random): Path =
    if depth <= 0 then
      if env.paths.nonEmpty && rng.nextBoolean() then Path.Deref(pick(env.paths))
      else Path.Constant(randomPathValue(salt))
    else
      rng.nextInt(5) match
        case 0 if env.paths.nonEmpty => Path.Deref(pick(env.paths))
        case 1 => Path.Constant(randomPathValue(salt))
        case 2 => Path.Concat(genPath(depth - 1, env, salt + 1), genPath(depth - 1, env, salt + 13))
        case 3 => Path.Concat(Path.Constant(randomPathValue(salt, maxLen = 1)), genPath(depth - 1, env, salt + 29))
        case _ if env.paths.nonEmpty => Path.Concat(Path.Deref(pick(env.paths)), Path.Constant(randomPathValue(salt, maxLen = 1)))
        case _ => Path.Constant(randomPathValue(salt))

  private def leaf(depth: Int, env: Env, salt: Int)(using rng: Random): Space =
    rng.nextInt(5) match
      case 0 if env.spaces.nonEmpty => Space.Mention(pick(env.spaces))
      case 1 => Space.Singleton(genPath(depth.max(0), env, salt))
      case 2 => Space.Literal(randomSpaceValue(salt))
      case 3 => Space.Empty
      case _ if env.spaces.nonEmpty => Space.Range(Space.Mention(pick(env.spaces)), 0, 1 + rng.nextInt(4))
      case _ => Space.Singleton(genPath(depth.max(0), env, salt))

  private def genSpace(depth: Int, env: Env, salt: Int)(using rng: Random): Space =
    if depth <= 0 then leaf(0, env, salt)
    else
      rng.nextInt(20) match
        case 0 => leaf(depth - 1, env, salt)
        case 1 => Space.Union(genSpace(depth - 1, env, salt + 1), genSpace(depth - 1, env, salt + 2))
        case 2 => Space.Intersection(genSpace(depth - 1, env, salt + 3), genSpace(depth - 1, env, salt + 4))
        case 3 => Space.Subtraction(genSpace(depth - 1, env, salt + 5), genSpace(depth - 1, env, salt + 6))
        case 4 => Space.Restriction(genSpace(depth - 1, env, salt + 7), genSpace(depth - 1, env, salt + 8))
        case 5 => Space.Raffination(genSpace(depth - 1, env, salt + 9), genSpace(depth - 1, env, salt + 10))
        case 6 => Space.Composition(genSpace(depth - 1, env, salt + 11), genSpace(depth - 1, env, salt + 12))
        case 7 => Space.Wrap(genSpace(depth - 1, env, salt + 13), genPath(1 + rng.nextInt(depth.min(3)), env, salt + 14))
        case 8 => Space.Unwrap(genSpace(depth - 1, env, salt + 15), genPath(1 + rng.nextInt(depth.min(3)), env, salt + 16))
        case 9 => Space.TailsUnion(genSpace(depth - 1, env, salt + 17))
        case 10 => Space.TailsIntersection(genSpace(depth - 1, env, salt + 18))
        case 11 =>
          val start = if rng.nextBoolean() then 0 else -1 - rng.nextInt(4)
          val end = if start < 0 then 0 else start + 1 + rng.nextInt(5)
          Space.Range(genSpace(depth - 1, env, salt + 19), start, end)
        case 12 => Space.PrefixClosure(genSpace(depth - 1, env, salt + 20))
        case 13 => Space.SuffixClosure(genSpace(depth - 1, env, salt + 22))
        case 14 =>
          val h = PathRef(s"free_h_${salt}_${rng.nextInt(100000)}").known(1)
          val r = SpaceMention(s"free_r_${salt}_${rng.nextInt(100000)}")
          val bodyEnv = env.copy(boundSpaces = env.boundSpaces :+ r, boundPaths = env.boundPaths :+ h)
          Space.Iteration(genSpace(depth - 1, env, salt + 24), h, r, genSpace(depth - 1, bodyEnv, salt + 25))
        case 15 =>
          val h = PathRef(s"fold_h_${salt}_${rng.nextInt(100000)}").known(1)
          val acc = PathRef(s"fold_acc_${salt}_${rng.nextInt(100000)}").known(1)
          val r = SpaceMention(s"fold_r_${salt}_${rng.nextInt(100000)}")
          val bodyEnv = env.copy(boundSpaces = env.boundSpaces :+ r, boundPaths = env.boundPaths ++ Vector(h, acc))
          Space.Fold(
            genSpace(depth - 1, env, salt + 26),
            genPath(1, env, salt + 27),
            acc,
            h,
            r,
            genSpace(depth - 1, bodyEnv, salt + 28),
            genPath(1, bodyEnv, salt + 29)
          )
        case 16 =>
          val v = SpaceMention(s"fix_v_${salt}_${rng.nextInt(100000)}")
          val initial = genSpace((depth - 2).max(0), env, salt + 30)
          val static = genSpace((depth - 2).max(0), env, salt + 31)
          val mention = Space.Mention(v)
          val step =
            rng.nextInt(3) match
              case 0 => Space.Union(mention, static)
              case 1 => Space.Union(Space.TailsUnion(mention), static)
              case _ => static
          Space.Fixpoint(initial, v, step)
        case 17 =>
          val a = genSpace(depth - 1, env, salt + 32)
          Space.Union(a, Space.Range(a, 0, 1 + rng.nextInt(4)))
        case 18 =>
          val a = genSpace(depth - 1, env, salt + 33)
          val b = genSpace(depth - 1, env, salt + 34)
          Space.Union(Space.Composition(a, b), Space.TailsUnion(a))
        case _ =>
          val src = genSpace(depth - 1, env, salt + 35)
          Space.Union(Space.Wrap(src, Path.Constant(randomPathValue(salt, maxLen = 1))), Space.Unwrap(src, Path.Constant(randomPathValue(salt + 1, maxLen = 1))))

  private def spaceInputBranch(sm: SpaceMention, idx: Int, env: Env, salt: Int)(using rng: Random): Space =
    val mention = Space.Mention(sm)
    rng.nextInt(6) match
      case 0 => Space.Wrap(mention, pc(s"touch.space.$idx.${sm.s}"))
      case 1 => Space.Union(mention, Space.Wrap(Space.TailsUnion(mention), pc(s"tails.space.$idx.${sm.s}")))
      case 2 => Space.Range(mention, 0, 1 + rng.nextInt(6))
      case 3 => Space.Composition(Space.Singleton(pc(s"cart.space.$idx")), mention)
      case 4 => Space.Raffination(mention, Space.Singleton(genPath(1, env, salt)))
      case _ => Space.Union(Space.Wrap(mention, genPath(1, env, salt)), Space.TailsIntersection(mention))

  private def pathInputBranch(pr: PathRef, idx: Int, env: Env, salt: Int)(using rng: Random): Space =
    val p = Path.Deref(pr)
    rng.nextInt(5) match
      case 0 => Space.Wrap(Space.Singleton(p), pc(s"touch.path.$idx.${pr.s}"))
      case 1 => Space.Singleton(Path.Concat(pc(s"path_seen.$idx"), p))
      case 2 if env.spaceInputs.nonEmpty => Space.Wrap(Space.Mention(pick(env.spaceInputs)), p)
      case 3 if env.spaceInputs.nonEmpty => Space.Union(Space.Singleton(p), Space.Unwrap(Space.Mention(pick(env.spaceInputs)), p))
      case _ => Space.Composition(Space.Singleton(p), Space.Literal(randomSpaceValue(salt)))

  private def candidateExpr(env: Env, id: Int)(using rng: Random): Space =
    val depth = 4 + rng.nextInt(4)
    val coreCount = 2 + rng.nextInt(4)
    val cores = Vector.tabulate(coreCount)(i => genSpace(depth, env, id * 97 + i * 17))
    val required =
      env.spaceInputs.zipWithIndex.map((sm, i) => spaceInputBranch(sm, i, env, id * 131 + i)) ++
        env.pathInputs.zipWithIndex.map((pr, i) => pathInputBranch(pr, i, env, id * 151 + i))
    unionAll(rng.shuffle(cores ++ required))

  private def randomEnv(id: Int)(using rng: Random): Env =
    val spaceCount = 1 + rng.nextInt(4)
    val pathCount = 1 + rng.nextInt(3)
    Env(
      Vector.tabulate(spaceCount)(i => SpaceMention(s"free_s${i}_${id % 997}")),
      Vector.tabulate(pathCount)(i => PathRef(s"free_p${i}_${id % 997}"))
    )

  private def frame(spaces: Map[SpaceMention, TrieSpace], paths: Map[PathRef, PathValue]): EvalFrame =
    EvalFrame(PathContextMap(paths), TrieSpaceContextMap(spaces))

  private def baseInputs(env: Env, id: Int)(using rng: Random): (Map[SpaceMention, TrieSpace], Map[PathRef, PathValue]) =
    val spaces = env.spaceInputs.zipWithIndex.map { (sm, i) =>
      sm -> randomTrie(sm.s, id * 31 + i)
    }.toMap
    val paths = env.pathInputs.zipWithIndex.map { (pr, i) =>
      pr -> randomPathValue(id * 43 + i, maxLen = 3)
    }.toMap
    spaces -> paths

  private def mutateTrie(base: TrieSpace, name: String, id: Int, salt: Int)(using rng: Random): TrieSpace =
    val extra = randomTrie(s"mut_$name", id * 59 + salt)
    val singleton = TrieSpace.singleton(pv(s"mutated.$name.$id.$salt"))
    if rng.nextBoolean() then base.union(extra).union(singleton)
    else base.diff(extra).union(singleton)

  private def mutatePath(name: String, id: Int, salt: Int)(using rng: Random): PathValue =
    pv(s"mutated_path.$name.$id.$salt.${atoms((id + salt) % atoms.length)}")

  private def makeFrames(env: Env, id: Int, inputCount: Int)(using rng: Random): (EvalFrame, Vector[EvalFrame], Vector[(String, EvalFrame)]) =
    val (baseSpaces, basePaths) = baseInputs(env, id)
    val baseline = frame(baseSpaces, basePaths)
    val perturbations =
      env.spaceInputs.zipWithIndex.map { (sm, i) =>
        s"space:${sm.s}" -> frame(baseSpaces.updated(sm, mutateTrie(baseSpaces(sm), sm.s, id, i)), basePaths)
      } ++ env.pathInputs.zipWithIndex.map { (pr, i) =>
        s"path:${pr.s}" -> frame(baseSpaces, basePaths.updated(pr, mutatePath(pr.s, id, i)))
      }
    val interesting = Vector.tabulate(inputCount) { i =>
      if i == 0 then baseline
      else
        val spaces = baseSpaces.map { (sm, tr) =>
          val changed =
            if rng.nextInt(100) < 70 then mutateTrie(tr, sm.s, id + i, i)
            else tr
          sm -> changed
        }
        val paths = basePaths.map { (pr, pv0) =>
          val changed =
            if rng.nextInt(100) < 70 then mutatePath(pr.s, id + i, i)
            else pv0
          pr -> changed
        }
        frame(spaces, paths)
    }
    (baseline, interesting, perturbations)

  def candidate(id: Int, inputCount: Int)(using rng: Random): Candidate =
    val env = randomEnv(id)
    val expr = candidateExpr(env, id)
    val (baseline, interesting, perturbations) = makeFrames(env, id, inputCount)
    Candidate(id, s"free-expression-$id", env, expr, baseline, interesting, perturbations)

  def generate(count: Int,
               seed: Long,
               inputCount: Int = 24,
               maxAttempts: Int = 100000,
               config: InterestingnessConfig = InterestingnessConfig(minUniqueOutputs = 4, minScore = 42.0, minNonEmptyOutputs = 4, maxOutputPaths = 4096),
               progressEvery: Int = 0): Corpus =
    given Random = Random(seed)
    val accepted = Vector.newBuilder[Accepted]
    val start = System.nanoTime()
    var attempts = 0
    var nextId = 0
    var rejectedInteresting = 0
    var rejectedSensitivity = 0
    while nextId < count && attempts < maxAttempts do
      val c = candidate(attempts, inputCount)
      RejectionSamplingFilters.interestingness(c.expr, c.interestingFrames, config) match
        case None =>
          rejectedInteresting += 1
        case Some((metrics, outputs)) =>
          RejectionSamplingFilters.sensitivity(c.expr, c.baseline, c.perturbations, c.requiredInputs, config.maxOutputPaths) match
            case Some(witnesses) =>
              accepted += Accepted(nextId, c.id, c.name, c.env, c.expr, metrics, witnesses, attempts + 1)
              nextId += 1
              if progressEvery > 0 && nextId % progressEvery == 0 then
                val elapsed = (System.nanoTime() - start).toDouble / 1_000_000_000.0
                println(f"accepted $nextId%,d / $count%,d free programs after ${attempts + 1}%,d attempts in $elapsed%.1f s")
            case None =>
              rejectedSensitivity += 1
      attempts += 1
    if nextId < count then
      throw RuntimeException(s"only generated $nextId free programs after $attempts attempts")
    val elapsedMs = ((System.nanoTime() - start) / 1_000_000L).max(0L)
    Corpus(accepted.result(), seed, attempts, rejectedInteresting, rejectedSensitivity, elapsedMs)

  private def json(s: String): String =
    "\"" + s.flatMap {
      case '"' => "\\\""
      case '\\' => "\\\\"
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\t' => "\\t"
      case c if c.isControl => f"\\u${c.toInt}%04x"
      case c => c.toString
    } + "\""

  private def write(path: NioPath, text: String): Unit =
    Files.writeString(path, text, StandardCharsets.UTF_8)

  private def renderProgram(p: Accepted): String =
    s"""# ${p.fileStem}
       |
       |- Corpus id: ${p.id}
       |- Candidate id: ${p.candidateId}
       |- Space inputs: ${p.env.spaceInputs.map(_.s).mkString(", ")}
       |- Path inputs: ${p.env.pathInputs.map(_.s).mkString(", ")}
       |- Sensitive inputs witnessed: ${p.witnesses.map(_.input).mkString(", ")}
       |- Unique outputs: ${p.metrics.uniqueOutputs}
       |- Interestingness: ${"%.3f".format(p.metrics.interestingness)}
       |- Union output paths: ${p.metrics.unionOutputPaths}
       |
       |## Program
       |
       |```scala
       |${p.expr.show}
       |```
       |""".stripMargin

  def writeCorpus(corpus: Corpus, outDir: NioPath, sampleCount: Int = 3, sampleSeed: Long = 20260702L): Vector[Accepted] =
    Files.createDirectories(outDir)
    val programDir = outDir.resolve("programs")
    Files.createDirectories(programDir)
    corpus.programs.foreach { p =>
      write(programDir.resolve(p.fileStem + ".md"), renderProgram(p))
    }
    val jsonl = new StringBuilder
    corpus.programs.foreach { p =>
      jsonl.append("{")
      jsonl.append("\"id\":").append(p.id).append(',')
      jsonl.append("\"candidate_id\":").append(p.candidateId).append(',')
      jsonl.append("\"name\":").append(json(p.name)).append(',')
      jsonl.append("\"file\":").append(json(s"programs/${p.fileStem}.md")).append(',')
      jsonl.append("\"space_inputs\":").append(p.env.spaceInputs.map(sm => json(sm.s)).mkString("[", ",", "]")).append(',')
      jsonl.append("\"path_inputs\":").append(p.env.pathInputs.map(pr => json(pr.s)).mkString("[", ",", "]")).append(',')
      jsonl.append("\"sensitive_inputs\":").append(p.witnesses.map(w => json(w.input)).mkString("[", ",", "]")).append(',')
      jsonl.append("\"unique_outputs\":").append(p.metrics.uniqueOutputs).append(',')
      jsonl.append("\"interestingness\":").append(f"${p.metrics.interestingness}%.6f").append(',')
      jsonl.append("\"union_output_paths\":").append(p.metrics.unionOutputPaths).append(',')
      jsonl.append("\"expression_chars\":").append(p.expr.show.length)
      jsonl.append("}\n")
    }
    write(outDir.resolve("programs.jsonl"), jsonl.result())

    val sampleRng = Random(sampleSeed)
    val samples = sampleRng.shuffle(corpus.programs).take(sampleCount).toVector
    val sampleMd = new StringBuilder
    sampleMd.append("# Random Free Expression Samples\n\n")
    samples.foreach { p =>
      sampleMd.append(s"## ${p.fileStem}\n\n")
      sampleMd.append(s"- Inputs: ${p.inputNames.mkString(", ")}\n")
      sampleMd.append(f"- Interestingness: ${p.metrics.interestingness}%.3f\n")
      sampleMd.append(s"- Unique outputs: ${p.metrics.uniqueOutputs}\n")
      sampleMd.append(s"- File: `programs/${p.fileStem}.md`\n\n")
      sampleMd.append("```scala\n")
      sampleMd.append(p.expr.show)
      sampleMd.append("\n```\n\n")
    }
    write(outDir.resolve("SAMPLES.md"), sampleMd.result())

    val readme = new StringBuilder
    readme.append("# Free Expression Tree Fuzzer Corpus\n\n")
    readme.append(s"- Programs: ${corpus.programs.length}\n")
    readme.append(s"- Seed: ${corpus.seed}\n")
    readme.append(s"- Attempts: ${corpus.attempts}\n")
    readme.append(s"- Rejected by interestingness: ${corpus.rejectedInteresting}\n")
    readme.append(s"- Rejected by sensitivity: ${corpus.rejectedSensitivity}\n")
    readme.append(f"- Acceptance rate: ${100.0 * corpus.acceptanceRate}%.2f%%\n")
    readme.append(f"- Generation time: ${corpus.elapsedMs / 1000.0}%.3f s\n")
    readme.append("- Generator: recursive free expression tree generation over pure MORKL space/path constructors, followed by rejection-sampling filters.\n")
    readme.append("- Filters: output interestingness over varied input frames, then one-input-at-a-time sensitivity witnesses for every free space/path input.\n")
    readme.append("- Metadata: `programs.jsonl`\n")
    readme.append("- Random samples: `SAMPLES.md`\n")
    readme.append("- Full programs: `programs/*.md`\n\n")
    readme.append("## Random Samples\n\n")
    samples.foreach(p => readme.append(s"- `${p.fileStem}`\n"))
    write(outDir.resolve("README.md"), readme.result())
    samples

  def run(count: Int, seed: Long, outDir: NioPath): Vector[Accepted] =
    val progressEvery = math.max(1, count / 20)
    val corpus = generate(count, seed, progressEvery = progressEvery)
    val samples = writeCorpus(corpus, outDir)
    println(s"wrote ${outDir.resolve("README.md")}")
    println(s"wrote ${outDir.resolve("programs.jsonl")}")
    println(s"wrote ${outDir.resolve("SAMPLES.md")}")
    println(f"programs=${corpus.programs.length}%,d attempts=${corpus.attempts}%,d rejectedInteresting=${corpus.rejectedInteresting}%,d rejectedSensitivity=${corpus.rejectedSensitivity}%,d acceptance=${100.0 * corpus.acceptanceRate}%.2f%% time=${corpus.elapsedMs / 1000.0}%.3f s")
    samples.foreach(p => println(s"sample ${p.id}: ${p.fileStem}"))
    samples

  def verificationFrames(program: Accepted, inputCount: Int, seed: Long): Vector[EvalFrame] =
    given Random = Random(seed)
    val (_, frames, _) = makeFrames(program.env, program.candidateId + 1_000_000, inputCount)
    frames

object FullBackendVerifier:
  import RejectionSamplingFilters.*

  final case class ProgramResult(id: Int,
                                 candidateId: Int,
                                 frames: Int,
                                 rawNodes: Int,
                                 optimizedNodes: Int,
                                 elapsedMs: Long)

  final case class Summary(programs: Int,
                           framesPerProgram: Int,
                           totalFrames: Long,
                           seed: Long,
                           corpusSeed: Long,
                           elapsedMs: Long,
                           rows: Vector[ProgramResult])

  private def csvCell(s: String): String =
    if s.exists(ch => ch == ',' || ch == '"' || ch == '\n') then "\"" + s.replace("\"", "\"\"") + "\"" else s

  private def write(path: NioPath, text: String): Unit =
    Files.writeString(path, text, StandardCharsets.UTF_8)

  private def referenceContext(frame: EvalFrame): SpaceContextMap =
    SpaceContextMap(frame.sc.m.map((sm, trie) => sm -> trie.toSpaceValue))

  private def execValue(g: RecursiveOpGraph,
                        refs: Vector[PathRef],
                        mentions: Vector[SpaceMention],
                        frame: EvalFrame): SpaceValue =
    val stack = mutable.Stack(new Array[PathValue | SpaceValue | Null](g.nodes.length))
    refs.zipWithIndex.foreach((pr, i) => stack.top(i) = frame.pc.resolve(pr))
    mentions.zipWithIndex.foreach((sm, i) => stack.top(refs.length + i) = frame.sc.resolve(sm).toSpaceValue)
    exec(g, stack)
    stack.top.last.asInstanceOf[SpaceValue]

  private def execTrieValue(g: RecursiveOpGraph,
                            refs: Vector[PathRef],
                            mentions: Vector[SpaceMention],
                            frame: EvalFrame): SpaceValue =
    val stack = mutable.Stack(new Array[PathValue | TrieSpace | Null](g.nodes.length))
    refs.zipWithIndex.foreach((pr, i) => stack.top(i) = frame.pc.resolve(pr))
    mentions.zipWithIndex.foreach((sm, i) => stack.top(refs.length + i) = frame.sc.resolve(sm))
    execTrie(g, stack)
    stack.top.last.asInstanceOf[TrieSpace].toSpaceValue

  private def execTValue(g: RecursiveOpGraph,
                         refs: Vector[PathRef],
                         mentions: Vector[SpaceMention],
                         frame: EvalFrame): SpaceValue =
    val stack = mutable.Stack(new Array[List[Int] | TrieSpace | Null](g.nodes.length))
    refs.zipWithIndex.foreach((pr, i) => stack.top(i) = TrieSpace.intern(frame.pc.resolve(pr)))
    mentions.zipWithIndex.foreach((sm, i) => stack.top(refs.length + i) = frame.sc.resolve(sm))
    execT(g, stack)
    stack.top.last.asInstanceOf[TrieSpace].toSpaceValue

  private def assertEqual(actual: SpaceValue, expected: SpaceValue, clue: String): Unit =
    if actual != expected then
      val missing = (expected.paths diff actual.paths).toVector.sortBy(_.show).take(30).map(_.show).mkString("; ")
      val extra = (actual.paths diff expected.paths).toVector.sortBy(_.show).take(30).map(_.show).mkString("; ")
      throw AssertionError(s"$clue expected=${expected.paths.size} actual=${actual.paths.size} missing=[$missing] extra=[$extra]")

  private def verifyProgram(program: FreeExpressionTreeFuzzer.Accepted,
                            frameCount: Int,
                            seed: Long): ProgramResult =
    val refs = program.env.pathInputs
    val mentions = program.env.spaceInputs
    val routine = Routine(RoutinePtr(s"verify_free_${program.id}"), refs, mentions, program.expr)
    val raw = transpile(routine)
    val optimized = optimize(transpile(routine))
    graphReferenceErrors(raw) match
      case bad if bad.nonEmpty => throw AssertionError(s"raw graph refs invalid for ${program.id}: ${bad.mkString("; ")}")
      case _ => ()
    graphReferenceErrors(optimized) match
      case bad if bad.nonEmpty => throw AssertionError(s"optimized graph refs invalid for ${program.id}: ${bad.mkString("; ")}")
      case _ => ()

    val frames = FreeExpressionTreeFuzzer.verificationFrames(program, frameCount, seed)
    val start = System.nanoTime()
    frames.zipWithIndex.foreach { (frame, frameId) =>
      val pc = frame.pc
      val scTrie = frame.sc
      val scRef = referenceContext(frame)
      val expected = eval(program.expr)(using pc, scRef, PartialFunction.empty)
      assertEqual(evalTrieValue(program.expr)(using pc, scTrie, PartialFunction.empty), expected,
        s"evalTrie mismatch program=${program.id} frame=$frameId")
      assertEqual(evalZValue(program.expr)(using pc, ZipperSpaceContext.fromTrie(scTrie), PartialFunction.empty), expected,
        s"evalZ mismatch program=${program.id} frame=$frameId")
      assertEqual(execValue(raw, refs, mentions, frame), expected,
        s"raw exec mismatch program=${program.id} frame=$frameId")
      assertEqual(execTrieValue(raw, refs, mentions, frame), expected,
        s"raw execTrie mismatch program=${program.id} frame=$frameId")
      assertEqual(execTValue(raw, refs, mentions, frame), expected,
        s"raw execT mismatch program=${program.id} frame=$frameId")
      assertEqual(execValue(optimized, refs, mentions, frame), expected,
        s"optimized exec mismatch program=${program.id} frame=$frameId")
      assertEqual(execTrieValue(optimized, refs, mentions, frame), expected,
        s"optimized execTrie mismatch program=${program.id} frame=$frameId")
      assertEqual(execTValue(optimized, refs, mentions, frame), expected,
        s"optimized execT mismatch program=${program.id} frame=$frameId")
    }
    val elapsedMs = ((System.nanoTime() - start) / 1_000_000L).max(0L)
    ProgramResult(program.id, program.candidateId, frameCount, Supercompiler.graphStats(raw).nodes, Supercompiler.graphStats(optimized).nodes, elapsedMs)

  def verify(programCount: Int,
             frameCount: Int,
             corpusSeed: Long,
             frameSeed: Long,
             progressEvery: Int = 0): Summary =
    val start = System.nanoTime()
    val corpus = FreeExpressionTreeFuzzer.generate(programCount, corpusSeed, progressEvery = 0)
    val rows = Vector.newBuilder[ProgramResult]
    corpus.programs.foreach { p =>
      rows += verifyProgram(p, frameCount, frameSeed + p.id.toLong * 1009L)
      if progressEvery > 0 && (p.id + 1) % progressEvery == 0 then
        val elapsed = (System.nanoTime() - start).toDouble / 1_000_000_000.0
        println(f"verified ${p.id + 1}%,d / $programCount%,d programs (${(p.id + 1).toLong * frameCount}%,d frames) in $elapsed%.1f s")
    }
    val elapsedMs = ((System.nanoTime() - start) / 1_000_000L).max(0L)
    Summary(programCount, frameCount, programCount.toLong * frameCount.toLong, frameSeed, corpusSeed, elapsedMs, rows.result())

  def writeSummary(summary: Summary, outDir: NioPath): Unit =
    Files.createDirectories(outDir)
    val csv = new StringBuilder
    csv.append("program_id,candidate_id,frames,raw_nodes,optimized_nodes,elapsed_ms\n")
    summary.rows.foreach { r =>
      csv.append(Vector(r.id.toString, r.candidateId.toString, r.frames.toString, r.rawNodes.toString, r.optimizedNodes.toString, r.elapsedMs.toString).map(csvCell).mkString(",")).append('\n')
    }
    write(outDir.resolve("per_program.csv"), csv.result())
    val md = new StringBuilder
    val totalEvalComparisons = summary.totalFrames * 8L
    md.append("# Full Backend Verification\n\n")
    md.append(s"- Programs: ${summary.programs}\n")
    md.append(s"- Frames per program: ${summary.framesPerProgram}\n")
    md.append(s"- Total input frames: ${summary.totalFrames}\n")
    md.append(s"- Corpus seed: ${summary.corpusSeed}\n")
    md.append(s"- Frame seed: ${summary.seed}\n")
    md.append(f"- Elapsed: ${summary.elapsedMs / 1000.0}%.3f s\n")
    md.append(s"- Checked backends: reference eval, evalTrie, evalZ, raw exec, raw execTrie, raw execT, optimized exec, optimized execTrie, optimized execT\n")
    md.append(s"- Equality comparisons against reference eval: $totalEvalComparisons\n")
    md.append("- Result: all checked outputs matched.\n")
    md.append("- Per-program timings: `per_program.csv`\n")
    write(outDir.resolve("README.md"), md.result())

  def run(programCount: Int,
          frameCount: Int,
          corpusSeed: Long,
          frameSeed: Long,
          outDir: NioPath): Summary =
    val progressEvery = math.max(1, programCount / 20)
    val summary = verify(programCount, frameCount, corpusSeed, frameSeed, progressEvery)
    writeSummary(summary, outDir)
    println(s"wrote ${outDir.resolve("README.md")}")
    println(s"wrote ${outDir.resolve("per_program.csv")}")
    println(f"verified programs=${summary.programs}%,d frames=${summary.totalFrames}%,d elapsed=${summary.elapsedMs / 1000.0}%.3f s")
    summary

class ZipperFuzzerTest extends FunSuite:
  import ZipperProgramFuzzer.*

  private def graphIndex(graphs: Map[String, RecursiveOpGraph]): PartialFunction[String, RecursiveOpGraph] =
    graphs.lift.unlift

  private def execTValue(g: RecursiveOpGraph, mentions: Vector[SpaceMention], ctx: TrieSpaceContextMap): SpaceValue =
    val stack = mutable.Stack(new Array[List[Int] | TrieSpace | Null](g.nodes.length))
    for (sm, i) <- mentions.zipWithIndex do stack.top(i) = ctx.resolve(sm)
    execT(g, stack)
    stack.top.last.asInstanceOf[TrieSpace].toSpaceValue

  private def execValue(g: RecursiveOpGraph, mentions: Vector[SpaceMention], ctx: SpaceContextMap): SpaceValue =
    val stack = mutable.Stack(new Array[PathValue | SpaceValue | Null](g.nodes.length))
    for (sm, i) <- mentions.zipWithIndex do stack.top(i) = ctx.resolve(sm)
    exec(g, stack, graphIndex(Map.empty))
    stack.top.last.asInstanceOf[SpaceValue]

  private def graphStages(raw: RecursiveOpGraph): Vector[(String, RecursiveOpGraph)] =
    val hoisted = hoist_loop_invariant_subgraphs(raw)
    val pushed = push_out(hoisted)
    val shared = optimize_sharing(pushed)
    Vector(
      "raw" -> raw,
      "hoist" -> hoisted,
      "hoist+push" -> pushed,
      "hoist+push+sharing" -> shared,
      "full optimize" -> optimize(raw)
    )

  private def assertSpaceEquals(actual: SpaceValue, expected: SpaceValue, clue: String): Unit =
    if actual != expected then
      val missing = (expected.paths diff actual.paths).toVector.sortBy(_.show).take(40).map(_.show).mkString("\n  ")
      val extra = (actual.paths diff expected.paths).toVector.sortBy(_.show).take(40).map(_.show).mkString("\n  ")
      fail(
        s"""$clue
           |expected paths: ${expected.paths.size}
           |actual paths:   ${actual.paths.size}
           |missing first 40:
           |  $missing
           |extra first 40:
           |  $extra""".stripMargin
      )

  test("zipper fuzzer expected spaces agree across eval, evalTrie, exec, and execT") {
    val cases = ZipperProgramFuzzer.samples(72, seed = 0x7a11cafeL)
    cases.zipWithIndex.foreach { (c, i) =>
      val expected = c.expected
      assertEquals(eval(c.term.expr)(using PathContext.emptyMap, c.context), expected,
        s"reference eval mismatch for sample $i\n${c.render}")
      assertEquals(evalTrieValue(c.term.expr)(using PathContext.emptyMap, c.trieContext), expected,
        s"evalTrie mismatch for sample $i\n${c.render}")
      assertEquals(evalZValue(c.term.expr)(using PathContext.emptyMap, ZipperSpaceContext.fromTrie(c.trieContext)), expected,
        s"evalZ mismatch for sample $i\n${c.render}")

      val graph = optimize(transpile(c.routine))
      val badRefs = graphReferenceErrors(graph)
      assert(badRefs.isEmpty, s"invalid graph refs for sample $i:\n${badRefs.mkString("\n")}\n${c.render}")
      assertSpaceEquals(execValue(graph, c.mentions, c.context), expected,
        s"exec mismatch for sample $i\n${c.render}")
      assertSpaceEquals(execTValue(graph, c.mentions, c.trieContext), expected,
        s"execT mismatch for sample $i\n${c.render}")
    }
  }

  test("operation graph materializes input and ancestor outputs") {
    val left = SpaceMention("left")
    val right = SpaceMention("right")
    val mentions = Vector(left, right)
    val ctx = SpaceContextMap(Map(left -> SpaceValue("a", "b"), right -> SpaceValue("seed")))
    val trieCtx = TrieSpaceContext.fromReference(ctx)

    val direct = Routine(RoutinePtr("alias_direct"), Vector.empty, mentions, S"left")
    val directGraph = transpile(direct)
    assert(directGraph.nodes.last.left.exists(_.operation == "Alias"))
    assertSpaceEquals(execValue(directGraph, mentions, ctx), SpaceValue("a", "b"), "direct input alias exec mismatch")
    assertSpaceEquals(execTValue(directGraph, mentions, trieCtx), SpaceValue("a", "b"), "direct input alias execT mismatch")

    val iterBody = Space.Iteration("tag" x S"left", PathRef("h").known(1), SpaceMention("rest"), S"right")
    val iter = Routine(RoutinePtr("alias_ancestor"), Vector.empty, mentions, iterBody)
    val iterGraph = transpile(iter)
    assert(iterGraph.show.contains("Alias"))
    assertSpaceEquals(execValue(iterGraph, mentions, ctx), SpaceValue("seed"), "ancestor alias exec mismatch")
    assertSpaceEquals(execTValue(iterGraph, mentions, trieCtx), SpaceValue("seed"), "ancestor alias execT mismatch")
  }

  test("coverage-biased zipper fuzzer agrees across optimized exec backends") {
    val cases = ZipperProgramFuzzer.coverageSamples(192, seed = 0x7a11cafeL)
    cases.zipWithIndex.foreach { (c, i) =>
      val expected = c.expected
      assertEquals(eval(c.term.expr)(using PathContext.emptyMap, c.context), expected,
        s"reference eval mismatch for coverage sample $i\n${c.render}")
      assertEquals(evalTrieValue(c.term.expr)(using PathContext.emptyMap, c.trieContext), expected,
        s"evalTrie mismatch for coverage sample $i\n${c.render}")
      assertEquals(evalZValue(c.term.expr)(using PathContext.emptyMap, ZipperSpaceContext.fromTrie(c.trieContext)), expected,
        s"evalZ mismatch for coverage sample $i\n${c.render}")

      graphStages(transpile(c.routine)).foreach { (stage, graph) =>
        val badRefs = graphReferenceErrors(graph)
        assert(badRefs.isEmpty, s"invalid graph refs for coverage sample $i at $stage:\n${badRefs.mkString("\n")}\n${c.render}")
        assertSpaceEquals(execValue(graph, c.mentions, c.context), expected,
          s"exec mismatch for coverage sample $i at $stage\n${c.render}")
        assertSpaceEquals(execTValue(graph, c.mentions, c.trieContext), expected,
          s"execT mismatch for coverage sample $i at $stage\n${c.render}")
      }
    }
  }

  test("zipper fuzzer showcase is stable and diverse") {
    val cases = ZipperProgramFuzzer.showcase(10, seed = 20260625L)
    assertEquals(cases.length, 10)
    assert(cases.map(_.name.stripPrefix("expr-").takeWhile(_ != '-')).distinct.length >= 4)
    assert(cases.exists(_.term.expr.show.contains("iter")))
    assert(cases.exists(_.term.expr.show.contains("Range")))
    assert(cases.forall(_.term.expr.show.length > 1200))
    assert(cases.forall(c => c.expected == eval(c.term.expr)(using PathContext.emptyMap, c.context)))
  }

  test("zipper fuzzer term matrix collector records child parent position counts") {
    val (collector, _) = ZipperFuzzerTermStats.collect(16, seed = 20260626L)
    assertEquals(collector.programs, 16L)
    assert(collector.totalNodes > 0L)
    assertEquals(collector.totalEdges, collector.totalNodes - collector.programs)
    assert(collector.edges.keys.exists(k =>
      k.childType == "Path.Constant" && k.parentType == "Space.Wrap" && k.position == "prefix"
    ))
    assert(collector.edges.keys.exists(k =>
      k.parentType == "Space.Iteration" && (k.position == "src" || k.position == "body")
    ))
  }

  test("zipper fuzzer interestingness measurement records output diversity") {
    val summary = ZipperFuzzerInterestingness.collect(8, inputCount = 12, seed = 20260629L)
    assertEquals(summary.stats.length, 8)
    assert(summary.stats.forall(s => s.inputCount == 12 && s.uniqueOutputs >= 1 && s.uniqueOutputs <= 12))
    assert(summary.stats.exists(_.unionOutputPaths > 0))
  }

  test("sensitive corpus generator verifies every declared input") {
    val corpus = ZipperFuzzerSensitiveCorpus.generate(12, seed = 20260701L, maxAttempts = 2000)
    assertEquals(corpus.programs.length, 12)
    assert(corpus.programs.forall(_.uniqueWitnessOutputs >= 2))
    assert(corpus.programs.forall(p => p.inputNames.forall(p.sensitiveInputs.contains)))
  }

  test("free expression tree generator uses rejection filters") {
    val corpus = FreeExpressionTreeFuzzer.generate(12, seed = 20260702L, maxAttempts = 3000)
    assertEquals(corpus.programs.length, 12)
    assert(corpus.attempts >= corpus.programs.length)
    assert(corpus.programs.forall(_.metrics.uniqueOutputs >= 4))
    assert(corpus.programs.forall(p => p.inputNames.forall(name => p.witnesses.exists(_.input == name))))
    val shown = corpus.programs.map(_.expr.show).mkString("\n")
    assert(shown.contains("iter") || shown.contains("fold") || shown.contains("fixpoint"))
  }

  test("full backend verifier checks free programs across evaluators and executors") {
    val summary = FullBackendVerifier.verify(3, frameCount = 5, corpusSeed = 20260702L, frameSeed = 20260703L)
    assertEquals(summary.programs, 3)
    assertEquals(summary.totalFrames, 15L)
    assertEquals(summary.rows.length, 3)
  }

@main def zipperFuzzerShowcase(): Unit =
  ZipperProgramFuzzer.showcase(10, seed = 20260625L).foreach(c => println(c.renderExpression))

@main def zipperFuzzerTermMatrix(count: Int = 1000000,
                                 seed: Long = 20260626L,
                                 outDir: String = "."): Unit =
  ZipperFuzzerTermStats.run(count, seed, Paths.get(outDir))

@main def zipperFuzzerInterestingnessRun(count: Int = 100000,
                                         inputCount: Int = 100,
                                         seed: Long = 20260629L,
                                         outDir: String = "fuzzer_interestingness_100k"): Unit =
  ZipperFuzzerInterestingness.run(count, inputCount, seed, Paths.get(outDir))

@main def zipperFuzzerSensitiveCorpusRun(count: Int = 1000,
                                         seed: Long = 20260701L,
                                         outDir: String = "fuzzer_sensitive_corpus_1000"): Unit =
  ZipperFuzzerSensitiveCorpus.run(count, seed, Paths.get(outDir))

@main def freeExpressionFuzzerCorpusRun(count: Int = 1000,
                                        seed: Long = 20260702L,
                                        outDir: String = "fuzzer_free_expression_corpus_1000"): Unit =
  FreeExpressionTreeFuzzer.run(count, seed, Paths.get(outDir))

@main def fullBackendVerifierRun(programCount: Int = 1000,
                                 frameCount: Int = 1000,
                                 corpusSeed: Long = 20260702L,
                                 frameSeed: Long = 20260703L,
                                 outDir: String = "fuzzer_full_backend_verify_1000x1000"): Unit =
  FullBackendVerifier.run(programCount, frameCount, corpusSeed, frameSeed, Paths.get(outDir))

object SlowProgramScTiming:
  import RejectionSamplingFilters.*

  final case class SourceRow(programId: Int,
                             candidateId: Int,
                             frames: Int,
                             rawNodes: Int,
                             optimizedNodes: Int,
                             elapsedMs: Long)

  final case class ProgramTiming(programId: Int,
                                 candidateId: Int,
                                 oldVerifierMs: Long,
                                 frames: Int,
                                 rawNodes: Int,
                                 optimizedNodes: Int,
                                 scBeforeAst: Int,
                                 scAfterAst: Int,
                                 scGraphNodes: Int,
                                 scCompileMs: Double,
                                 evalMs: Long,
                                 evalTrieMs: Long,
                                 evalZMs: Long,
                                 rawExecMs: Long,
                                 rawExecTrieMs: Long,
                                 rawExecTMs: Long,
                                 optExecMs: Long,
                                 optExecTrieMs: Long,
                                 optExecTMs: Long,
                                 scEvalMs: Long,
                                 scEvalTrieMs: Long,
                                 scEvalZMs: Long,
                                 scExecMs: Long,
                                 scExecTrieMs: Long,
                                 scExecTMs: Long)

  private def csvCell(s: String): String =
    if s.exists(ch => ch == ',' || ch == '"' || ch == '\n') then "\"" + s.replace("\"", "\"\"") + "\"" else s

  private def write(path: NioPath, text: String): Unit =
    Files.writeString(path, text, StandardCharsets.UTF_8)

  private def rows(csvPath: NioPath): Vector[SourceRow] =
    val lines = Files.readAllLines(csvPath, StandardCharsets.UTF_8).toArray(new Array[String](0)).toVector
    lines.drop(1).filter(_.trim.nonEmpty).map { line =>
      val cols = line.split(",", -1)
      SourceRow(cols(0).toInt, cols(1).toInt, cols(2).toInt, cols(3).toInt, cols(4).toInt, cols(5).toLong)
    }

  private def referenceContext(frame: EvalFrame): SpaceContextMap =
    SpaceContextMap(frame.sc.m.map((sm, trie) => sm -> trie.toSpaceValue))

  private def execValue(g: RecursiveOpGraph,
                        refs: Vector[PathRef],
                        mentions: Vector[SpaceMention],
                        frame: EvalFrame,
                        refCtx: SpaceContextMap): SpaceValue =
    val stack = mutable.Stack(new Array[PathValue | SpaceValue | Null](g.nodes.length))
    refs.zipWithIndex.foreach((pr, i) => stack.top(i) = frame.pc.resolve(pr))
    mentions.zipWithIndex.foreach((sm, i) => stack.top(refs.length + i) = refCtx.resolve(sm))
    exec(g, stack)
    stack.top.last.asInstanceOf[SpaceValue]

  private def execTrieValue(g: RecursiveOpGraph,
                            refs: Vector[PathRef],
                            mentions: Vector[SpaceMention],
                            frame: EvalFrame): SpaceValue =
    val stack = mutable.Stack(new Array[PathValue | TrieSpace | Null](g.nodes.length))
    refs.zipWithIndex.foreach((pr, i) => stack.top(i) = frame.pc.resolve(pr))
    mentions.zipWithIndex.foreach((sm, i) => stack.top(refs.length + i) = frame.sc.resolve(sm))
    execTrie(g, stack)
    stack.top.last.asInstanceOf[TrieSpace].toSpaceValue

  private def execTValue(g: RecursiveOpGraph,
                         refs: Vector[PathRef],
                         mentions: Vector[SpaceMention],
                         frame: EvalFrame): SpaceValue =
    val stack = mutable.Stack(new Array[List[Int] | TrieSpace | Null](g.nodes.length))
    refs.zipWithIndex.foreach((pr, i) => stack.top(i) = TrieSpace.intern(frame.pc.resolve(pr)))
    mentions.zipWithIndex.foreach((sm, i) => stack.top(refs.length + i) = frame.sc.resolve(sm))
    execT(g, stack)
    stack.top.last.asInstanceOf[TrieSpace].toSpaceValue

  private def assertEqual(actual: SpaceValue, expected: SpaceValue, clue: String): Unit =
    if actual != expected then
      val missing = (expected.paths diff actual.paths).toVector.sortBy(_.show).take(20).map(_.show).mkString("; ")
      val extra = (actual.paths diff expected.paths).toVector.sortBy(_.show).take(20).map(_.show).mkString("; ")
      throw AssertionError(s"$clue expected=${expected.paths.size} actual=${actual.paths.size} missing=[$missing] extra=[$extra]")

  private def timed[A](body: => A): (A, Long) =
    val start = System.nanoTime()
    val value = body
    value -> ((System.nanoTime() - start) / 1_000_000L).max(0L)

  private def timedExpected(frames: Vector[EvalFrame],
                            refContexts: Vector[SpaceContextMap],
                            expr: Space): (Vector[SpaceValue], Long) =
    timed {
      frames.indices.map { i =>
        eval(expr)(using frames(i).pc, refContexts(i), PartialFunction.empty)
      }.toVector
    }

  private def timedCheck(label: String,
                         expected: Vector[SpaceValue],
                         frames: Vector[EvalFrame])
                        (run: EvalFrame => SpaceValue): Long =
    val (_, ms) = timed {
      frames.indices.foreach { i =>
        assertEqual(run(frames(i)), expected(i), s"$label frame=$i")
      }
    }
    ms

  private def timedCheckWithRef(label: String,
                                expected: Vector[SpaceValue],
                                frames: Vector[EvalFrame],
                                refContexts: Vector[SpaceContextMap])
                               (run: (EvalFrame, SpaceContextMap) => SpaceValue): Long =
    val (_, ms) = timed {
      frames.indices.foreach { i =>
        assertEqual(run(frames(i), refContexts(i)), expected(i), s"$label frame=$i")
      }
    }
    ms

  private def timeProgram(program: FreeExpressionTreeFuzzer.Accepted,
                          row: SourceRow,
                          frameCount: Int,
                          frameSeed: Long,
                          compileBudgetMs: Long): ProgramTiming =
    val refs = program.env.pathInputs
    val mentions = program.env.spaceInputs
    val routine = Routine(RoutinePtr(s"slow_free_${program.id}"), refs, mentions, program.expr)
    val raw = transpile(routine)
    val optimized = optimize(transpile(routine))
    val rawErrors = graphReferenceErrors(raw)
    if rawErrors.nonEmpty then throw AssertionError(s"raw graph refs invalid for ${program.id}: ${rawErrors.mkString("; ")}")
    val optErrors = graphReferenceErrors(optimized)
    if optErrors.nonEmpty then throw AssertionError(s"optimized graph refs invalid for ${program.id}: ${optErrors.mkString("; ")}")

    val sc = Supercompiler.compile(routine, buildGraph = true, maxCompileMillis = compileBudgetMs)
    val scGraph = sc.graph.getOrElse(throw AssertionError(s"SC graph unavailable for ${program.id}: ${sc.report.graphError.getOrElse("unknown error")}"))
    val scErrors = graphReferenceErrors(scGraph)
    if scErrors.nonEmpty then throw AssertionError(s"SC graph refs invalid for ${program.id}: ${scErrors.mkString("; ")}")

    val frames = FreeExpressionTreeFuzzer.verificationFrames(program, frameCount, frameSeed + program.id.toLong * 1009L)
    val refContexts = frames.map(referenceContext)
    val (expected, evalMs) = timedExpected(frames, refContexts, program.expr)
    val evalTrieMs = timedCheck("evalTrie", expected, frames) { frame =>
      evalTrieValue(program.expr)(using frame.pc, frame.sc, PartialFunction.empty)
    }
    val evalZMs = timedCheck("evalZ", expected, frames) { frame =>
      evalZValue(program.expr)(using frame.pc, ZipperSpaceContext.fromTrie(frame.sc), PartialFunction.empty)
    }
    val rawExecMs = timedCheckWithRef("raw exec", expected, frames, refContexts) { (frame, refCtx) =>
      execValue(raw, refs, mentions, frame, refCtx)
    }
    val rawExecTrieMs = timedCheck("raw execTrie", expected, frames) { frame =>
      execTrieValue(raw, refs, mentions, frame)
    }
    val rawExecTMs = timedCheck("raw execT", expected, frames) { frame =>
      execTValue(raw, refs, mentions, frame)
    }
    val optExecMs = timedCheckWithRef("optimized exec", expected, frames, refContexts) { (frame, refCtx) =>
      execValue(optimized, refs, mentions, frame, refCtx)
    }
    val optExecTrieMs = timedCheck("optimized execTrie", expected, frames) { frame =>
      execTrieValue(optimized, refs, mentions, frame)
    }
    val optExecTMs = timedCheck("optimized execT", expected, frames) { frame =>
      execTValue(optimized, refs, mentions, frame)
    }
    val scEvalMs = timedCheckWithRef("SC eval", expected, frames, refContexts) { (frame, refCtx) =>
      eval(sc.routine.body)(using frame.pc, refCtx, PartialFunction.empty)
    }
    val scEvalTrieMs = timedCheck("SC evalTrie", expected, frames) { frame =>
      evalTrieValue(sc.routine.body)(using frame.pc, frame.sc, PartialFunction.empty)
    }
    val scEvalZMs = timedCheck("SC evalZ", expected, frames) { frame =>
      evalZValue(sc.routine.body)(using frame.pc, ZipperSpaceContext.fromTrie(frame.sc), PartialFunction.empty)
    }
    val scExecMs = timedCheckWithRef("SC exec", expected, frames, refContexts) { (frame, refCtx) =>
      execValue(scGraph, sc.routine.refs, sc.routine.mentions, frame, refCtx)
    }
    val scExecTrieMs = timedCheck("SC execTrie", expected, frames) { frame =>
      execTrieValue(scGraph, sc.routine.refs, sc.routine.mentions, frame)
    }
    val scExecTMs = timedCheck("SC execT", expected, frames) { frame =>
      execTValue(scGraph, sc.routine.refs, sc.routine.mentions, frame)
    }

    ProgramTiming(
      program.id,
      program.candidateId,
      row.elapsedMs,
      frameCount,
      Supercompiler.graphStats(raw).nodes,
      Supercompiler.graphStats(optimized).nodes,
      sc.report.before.totalNodes,
      sc.report.after.totalNodes,
      Supercompiler.graphStats(scGraph).nodes,
      sc.report.compileMs,
      evalMs,
      evalTrieMs,
      evalZMs,
      rawExecMs,
      rawExecTrieMs,
      rawExecTMs,
      optExecMs,
      optExecTrieMs,
      optExecTMs,
      scEvalMs,
      scEvalTrieMs,
      scEvalZMs,
      scExecMs,
      scExecTrieMs,
      scExecTMs
    )

  private def fmtMs(ms: Long): String = f"${ms / 1000.0}%.3f"
  private def fmtDoubleMs(ms: Double): String = f"${ms / 1000.0}%.3f"
  private def ratio(numer: Long, denom: Long): String =
    if denom <= 0 then "n/a" else f"${numer.toDouble / denom.toDouble}%.2f"

  def writeSummary(rows: Vector[ProgramTiming], outDir: NioPath, sourceCsv: NioPath, corpusSeed: Long, frameSeed: Long): Unit =
    Files.createDirectories(outDir)
    val csv = new StringBuilder
    csv.append("program_id,candidate_id,frames,old_verifier_ms,raw_nodes,optimized_nodes,sc_before_ast,sc_after_ast,sc_graph_nodes,sc_compile_ms,eval_ms,evalTrie_ms,evalZ_ms,raw_exec_ms,raw_execTrie_ms,raw_execT_ms,opt_exec_ms,opt_execTrie_ms,opt_execT_ms,sc_eval_ms,sc_evalTrie_ms,sc_evalZ_ms,sc_exec_ms,sc_execTrie_ms,sc_execT_ms\n")
    rows.foreach { r =>
      val values = Vector(
        r.programId.toString,
        r.candidateId.toString,
        r.frames.toString,
        r.oldVerifierMs.toString,
        r.rawNodes.toString,
        r.optimizedNodes.toString,
        r.scBeforeAst.toString,
        r.scAfterAst.toString,
        r.scGraphNodes.toString,
        f"${r.scCompileMs}%.3f",
        r.evalMs.toString,
        r.evalTrieMs.toString,
        r.evalZMs.toString,
        r.rawExecMs.toString,
        r.rawExecTrieMs.toString,
        r.rawExecTMs.toString,
        r.optExecMs.toString,
        r.optExecTrieMs.toString,
        r.optExecTMs.toString,
        r.scEvalMs.toString,
        r.scEvalTrieMs.toString,
        r.scEvalZMs.toString,
        r.scExecMs.toString,
        r.scExecTrieMs.toString,
        r.scExecTMs.toString
      )
      csv.append(values.map(csvCell).mkString(",")).append('\n')
    }
    write(outDir.resolve("timings.csv"), csv.result())

    val md = new StringBuilder
    md.append("# Top Slow Program SC Timing\n\n")
    md.append(s"- Source verifier CSV: `$sourceCsv`\n")
    md.append(s"- Corpus seed: $corpusSeed\n")
    md.append(s"- Frame seed: $frameSeed\n")
    md.append(s"- Programs timed: ${rows.length}\n")
    md.append("- Each runtime column evaluates/checks the same 1000 generated frames for that program.\n")
    md.append("- Legacy exec columns include stack setup and materialized `SpaceValue` results; trie exec columns include `TrieSpace` to `SpaceValue` materialization for equality.\n\n")
    md.append("## Top Programs From Verifier\n\n")
    md.append("| rank | program | candidate | previous verifier time (s) | raw graph nodes | optimized graph nodes |\n")
    md.append("|---:|---:|---:|---:|---:|---:|\n")
    rows.zipWithIndex.foreach { (r, i) =>
      md.append(s"| ${i + 1} | ${r.programId} | ${r.candidateId} | ${fmtMs(r.oldVerifierMs)} | ${r.rawNodes} | ${r.optimizedNodes} |\n")
    }
    md.append("\n## Runtime Timings\n\n")
    md.append("| program | eval | evalTrie | evalZ | opt exec | opt execTrie | opt execT | SC compile | SC eval | SC evalTrie | SC evalZ | SC exec | SC execTrie | SC execT |\n")
    md.append("|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|\n")
    rows.foreach { r =>
      md.append(s"| ${r.programId} | ${fmtMs(r.evalMs)} | ${fmtMs(r.evalTrieMs)} | ${fmtMs(r.evalZMs)} | ${fmtMs(r.optExecMs)} | ${fmtMs(r.optExecTrieMs)} | ${fmtMs(r.optExecTMs)} | ${fmtDoubleMs(r.scCompileMs)} | ${fmtMs(r.scEvalMs)} | ${fmtMs(r.scEvalTrieMs)} | ${fmtMs(r.scEvalZMs)} | ${fmtMs(r.scExecMs)} | ${fmtMs(r.scExecTrieMs)} | ${fmtMs(r.scExecTMs)} |\n")
    }
    md.append("\n## SC Shape And Speedups\n\n")
    md.append("| program | AST before -> after | graph nodes after SC | eval / SC eval | evalTrie / SC evalTrie | opt execT / SC execT | comp+SC execT vs eval |\n")
    md.append("|---:|---:|---:|---:|---:|---:|---:|\n")
    rows.foreach { r =>
      val compPlusScExecT = r.scExecTMs + math.round(r.scCompileMs)
      md.append(s"| ${r.programId} | ${r.scBeforeAst} -> ${r.scAfterAst} | ${r.scGraphNodes} | ${ratio(r.evalMs, r.scEvalMs)}x | ${ratio(r.evalTrieMs, r.scEvalTrieMs)}x | ${ratio(r.optExecTMs, r.scExecTMs)}x | ${ratio(r.evalMs, compPlusScExecT)}x |\n")
    }
    md.append("\nFull per-backend timings, including raw exec variants, are in `timings.csv`.\n")
    write(outDir.resolve("README.md"), md.result())

  def run(sourceCsv: NioPath,
          outDir: NioPath,
          topN: Int,
          frameCount: Int,
          corpusSeed: Long,
          frameSeed: Long,
          compileBudgetMs: Long): Vector[ProgramTiming] =
    val top = rows(sourceCsv).sortBy(r => -r.elapsedMs).take(topN)
    println("top slow programs from verifier:")
    top.zipWithIndex.foreach { (r, i) =>
      println(f"${i + 1}%d. program=${r.programId}%d candidate=${r.candidateId}%d previous=${r.elapsedMs / 1000.0}%.3f s rawNodes=${r.rawNodes}%d optNodes=${r.optimizedNodes}%d")
    }
    val corpus = FreeExpressionTreeFuzzer.generate(top.map(_.programId).max + 1, corpusSeed, progressEvery = 0)
    val byId = corpus.programs.map(p => p.id -> p).toMap
    val out = top.map { r =>
      println(s"timing program ${r.programId} over $frameCount frames")
      val timing = timeProgram(byId(r.programId), r, frameCount, frameSeed, compileBudgetMs)
      println(f"program ${timing.programId}%d done: eval=${timing.evalMs / 1000.0}%.3f s evalTrie=${timing.evalTrieMs / 1000.0}%.3f s optExecT=${timing.optExecTMs / 1000.0}%.3f s SC compile=${timing.scCompileMs / 1000.0}%.3f s SC execT=${timing.scExecTMs / 1000.0}%.3f s")
      timing
    }.toVector
    writeSummary(out, outDir, sourceCsv, corpusSeed, frameSeed)
    println(s"wrote ${outDir.resolve("README.md")}")
    println(s"wrote ${outDir.resolve("timings.csv")}")
    out

@main def slowProgramScTimingRun(sourceCsv: String = "fuzzer_full_backend_verify_1000x1000_seed20260705/per_program.csv",
                                 outDir: String = "fuzzer_top5_sc_timing_seed20260705",
                                 topN: Int = 5,
                                 frameCount: Int = 1000,
                                 corpusSeed: Long = 20260702L,
                                 frameSeed: Long = 20260705L,
                                 compileBudgetMs: Long = 30000L): Unit =
  SlowProgramScTiming.run(Paths.get(sourceCsv), Paths.get(outDir), topN, frameCount, corpusSeed, frameSeed, compileBudgetMs)

object SlowProgramDegeneracyAnalysis:
  final case class SourceRow(programId: Int,
                             candidateId: Int,
                             frames: Int,
                             rawNodes: Int,
                             optimizedNodes: Int,
                             elapsedMs: Long)

  final case class ProgramReport(programId: Int,
                                 candidateId: Int,
                                 beforeStats: SpaceStats,
                                 afterStats: SpaceStats,
                                 graphBefore: GraphStats,
                                 graphAfter: GraphStats,
                                 patternCounts: Vector[(String, Int)],
                                 opBefore: Vector[(String, Int)],
                                 opAfter: Vector[(String, Int)],
                                 duplicateSubterms: Vector[(String, Int, Int)],
                                 examples: Vector[(String, String)])

  private val ExampleLimit = 3

  private def rows(csvPath: NioPath): Vector[SourceRow] =
    val lines = Files.readAllLines(csvPath, StandardCharsets.UTF_8).toArray(new Array[String](0)).toVector
    lines.drop(1).filter(_.trim.nonEmpty).map { line =>
      val cols = line.split(",", -1)
      SourceRow(cols(0).toInt, cols(1).toInt, cols(2).toInt, cols(3).toInt, cols(4).toInt, cols(5).toLong)
    }

  private def write(path: NioPath, text: String): Unit =
    Files.writeString(path, text, StandardCharsets.UTF_8)

  private def short(s: Space): String =
    val text = s.show.replace('\n', ' ')
    if text.length <= 180 then text else text.take(177) + "..."

  private def shortP(p: Path): String =
    val text = p.show
    if text.length <= 140 then text else text.take(137) + "..."

  private def inc(m: mutable.Map[String, Int], key: String, by: Int = 1): Unit =
    m.update(key, m.getOrElse(key, 0) + by)

  private def addExample(examples: mutable.Map[String, Vector[String]], key: String, value: String): Unit =
    val current = examples.getOrElse(key, Vector.empty)
    if current.length < ExampleLimit && !current.contains(value) then examples.update(key, current :+ value)

  private def opName(s: Space): String = s match
    case Space.Empty => "Empty"
    case Space.Call(_, _, _) => "Call"
    case Space.Mention(_) => "Mention"
    case Space.Singleton(_) => "Singleton"
    case Space.Literal(_) => "Literal"
    case Space.Union(_, _) => "Union"
    case Space.Intersection(_, _) => "Intersection"
    case Space.Subtraction(_, _) => "Subtraction"
    case Space.Restriction(_, _) => "Restriction"
    case Space.Raffination(_, _) => "Raffination"
    case Space.Composition(_, _) => "Composition"
    case Space.Iteration(_, _, _, _) => "Iteration"
    case Space.Fold(_, _, _, _, _, _, _) => "Fold"
    case Space.Fixpoint(_, _, _) => "Fixpoint"
    case Space.Wrap(_, _) => "Wrap"
    case Space.Unwrap(_, _) => "Unwrap"
    case Space.TailsUnion(_) => "TailsUnion"
    case Space.TailsIntersection(_) => "TailsIntersection"
    case Space.PrefixClosure(_) => "PrefixClosure"
    case Space.SuffixClosure(_) => "SuffixClosure"
    case Space.TailsClosure(_) => "TailsClosure"
    case Space.GroundedPS(_, _) => "GroundedPS"
    case Space.GroundedSS(_, _) => "GroundedSS"
    case Space.Range(_, _, _) => "Range"

  private def usesMention(s: Space, target: SpaceMention): Boolean =
    def recp(p: Path, boundP: Set[String], boundS: Set[String]): Boolean = p match
      case Path.Deref(_) | Path.Constant(_) => false
      case Path.Concat(l, r) => recp(l, boundP, boundS) || recp(r, boundP, boundS)
      case Path.GroundedPP(p, _) => recp(p, boundP, boundS)
      case Path.GroundedSP(s, _) => recs(s, boundP, boundS)
    def recs(x: Space, boundP: Set[String], boundS: Set[String]): Boolean = x match
      case Space.Mention(sm) => sm == target && !boundS(sm.s)
      case Space.Empty | Space.Literal(_) => false
      case Space.Call(_, refs, mentions) => refs.exists(recp(_, boundP, boundS)) || mentions.exists(recs(_, boundP, boundS))
      case Space.Singleton(p) => recp(p, boundP, boundS)
      case Space.Union(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Intersection(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Subtraction(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Restriction(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Raffination(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Composition(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Iteration(src, sym, rest, body) => recs(src, boundP, boundS) || recs(body, boundP + sym.s, boundS + rest.s)
      case Space.Fold(src, initial, acc, sym, rest, body, update) =>
        recs(src, boundP, boundS) || recp(initial, boundP, boundS) ||
          recs(body, boundP + acc.s + sym.s, boundS + rest.s) || recp(update, boundP + acc.s + sym.s, boundS)
      case Space.Fixpoint(initial, variable, step) => recs(initial, boundP, boundS) || recs(step, boundP, boundS + variable.s)
      case Space.Wrap(src, p) => recs(src, boundP, boundS) || recp(p, boundP, boundS)
      case Space.Unwrap(src, p) => recs(src, boundP, boundS) || recp(p, boundP, boundS)
      case Space.TailsUnion(src) => recs(src, boundP, boundS)
      case Space.TailsIntersection(src) => recs(src, boundP, boundS)
      case Space.PrefixClosure(src) => recs(src, boundP, boundS)
      case Space.SuffixClosure(src) => recs(src, boundP, boundS)
      case Space.TailsClosure(src) => recs(src, boundP, boundS)
      case Space.GroundedPS(p, _) => recp(p, boundP, boundS)
      case Space.GroundedSS(src, _) => recs(src, boundP, boundS)
      case Space.Range(src, _, _) => recs(src, boundP, boundS)
    recs(s, Set.empty, Set.empty)

  private def usesRefInPath(p: Path, target: PathRef): Boolean =
    def recp(p: Path, boundP: Set[String], boundS: Set[String]): Boolean = p match
      case Path.Deref(pr) => pr == target && !boundP(pr.s)
      case Path.Constant(_) => false
      case Path.Concat(l, r) => recp(l, boundP, boundS) || recp(r, boundP, boundS)
      case Path.GroundedPP(p, _) => recp(p, boundP, boundS)
      case Path.GroundedSP(s, _) => recs(s, boundP, boundS)
    def recs(x: Space, boundP: Set[String], boundS: Set[String]): Boolean = x match
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => false
      case Space.Call(_, refs, mentions) => refs.exists(recp(_, boundP, boundS)) || mentions.exists(recs(_, boundP, boundS))
      case Space.Singleton(p) => recp(p, boundP, boundS)
      case Space.Union(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Intersection(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Subtraction(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Restriction(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Raffination(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Composition(a, b) => recs(a, boundP, boundS) || recs(b, boundP, boundS)
      case Space.Iteration(src, sym, rest, body) => recs(src, boundP, boundS) || recs(body, boundP + sym.s, boundS + rest.s)
      case Space.Fold(src, initial, acc, sym, rest, body, update) =>
        recs(src, boundP, boundS) || recp(initial, boundP, boundS) ||
          recs(body, boundP + acc.s + sym.s, boundS + rest.s) || recp(update, boundP + acc.s + sym.s, boundS)
      case Space.Fixpoint(initial, variable, step) => recs(initial, boundP, boundS) || recs(step, boundP, boundS + variable.s)
      case Space.Wrap(src, p) => recs(src, boundP, boundS) || recp(p, boundP, boundS)
      case Space.Unwrap(src, p) => recs(src, boundP, boundS) || recp(p, boundP, boundS)
      case Space.TailsUnion(src) => recs(src, boundP, boundS)
      case Space.TailsIntersection(src) => recs(src, boundP, boundS)
      case Space.PrefixClosure(src) => recs(src, boundP, boundS)
      case Space.SuffixClosure(src) => recs(src, boundP, boundS)
      case Space.TailsClosure(src) => recs(src, boundP, boundS)
      case Space.GroundedPS(p, _) => recp(p, boundP, boundS)
      case Space.GroundedSS(src, _) => recs(src, boundP, boundS)
      case Space.Range(src, _, _) => recs(src, boundP, boundS)
    recp(p, Set.empty, Set.empty)

  private def usesRef(s: Space, target: PathRef): Boolean =
    usesRefInPath(Path.GroundedSP(s, _ => PathValue(Nil)), target)

  private def unionOperands(s: Space): Vector[Space] = s match
    case Space.Union(a, b) => unionOperands(a) ++ unionOperands(b)
    case other => Vector(other)

  private def intersectionOperands(s: Space): Vector[Space] = s match
    case Space.Intersection(a, b) => intersectionOperands(a) ++ intersectionOperands(b)
    case other => Vector(other)

  private def isEmptySpace(s: Space): Boolean = s match
    case Space.Empty => true
    case Space.Literal(SpaceValue(paths)) => paths.isEmpty
    case _ => false

  private def containsFixpoint(s: Space): Boolean =
    collect(s)(spre = { case Space.Fixpoint(_, _, _) => () })._1.nonEmpty

  private def analyzePatterns(s: Space): (Vector[(String, Int)], Vector[(String, String)]) =
    val counts = mutable.Map.empty[String, Int]
    val examples = mutable.Map.empty[String, Vector[String]]

    def mark(key: String, node: Space, by: Int = 1): Unit =
      inc(counts, key, by)
      addExample(examples, key, short(node))

    def markP(key: String, p: Path): Unit =
      inc(counts, key)
      addExample(examples, key, shortP(p))

    def recp(p: Path): Unit = p match
      case Path.Deref(_) | Path.Constant(_) => ()
      case Path.Concat(l, r) =>
        if l == Path.Constant(PathValue(Nil)) || r == Path.Constant(PathValue(Nil)) then markP("path.concat_epsilon_survived", p)
        recp(l)
        recp(r)
      case Path.GroundedPP(p, _) => recp(p)
      case Path.GroundedSP(s, _) => recs(s)

    def recs(x: Space): Unit =
      inc(counts, s"op.${opName(x)}")
      x match
        case Space.Literal(SpaceValue(paths)) =>
          if paths.isEmpty then mark("literal.empty_spacevalue_not_canonical", x)
        case Space.Union(a, b) =>
          if a == b then mark("union.direct_duplicate", x)
          val ops = unionOperands(x)
          val grouped = ops.groupBy(_.show).view.mapValues(_.length).toMap
          val duplicateExtra = grouped.values.map(_ - 1).filter(_ > 0).sum
          if duplicateExtra > 0 then mark("union.associative_duplicate_operands", x, duplicateExtra)
          val opSet = ops.toSet
          ops.foreach {
            case Space.Range(src, _, _) if opSet(src) => mark("range.subset_absorption_union", x)
            case Space.Restriction(src, prefixes) if ops.exists {
              case Space.Raffination(`src`, `prefixes`) => true
              case _ => false
            } => mark("partition.restriction_raffination_union", x)
            case Space.Raffination(src, prefixes) if ops.exists {
              case Space.Restriction(`src`, `prefixes`) => true
              case _ => false
            } => mark("partition.restriction_raffination_union", x)
            case _ => ()
          }
          recs(a)
          recs(b)
        case Space.Intersection(a, b) =>
          if a == b then mark("intersection.direct_duplicate", x)
          val ops = intersectionOperands(x)
          val grouped = ops.groupBy(_.show).view.mapValues(_.length).toMap
          val duplicateExtra = grouped.values.map(_ - 1).filter(_ > 0).sum
          if duplicateExtra > 0 then mark("intersection.associative_duplicate_operands", x, duplicateExtra)
          val opSet = ops.toSet
          ops.foreach {
            case Space.Range(src, _, _) if opSet(src) => mark("range.subset_absorption_intersection", x)
            case _ => ()
          }
          recs(a)
          recs(b)
        case Space.Subtraction(a, b) =>
          (a, b) match
            case (Space.Range(src, _, _), y) if src == y => mark("range.subset_subtraction_empty", x)
            case (left, Space.Range(src, _, _)) if left == src => mark("range.subset_subtraction_remainder", x)
            case _ => ()
          recs(a)
          recs(b)
        case Space.Range(src, 0, 0) =>
          mark("range.identity_full_slice", x)
          recs(src)
        case Space.Range(src @ Space.Range(_, _, _), _, _) =>
          mark("range.nested_range", x)
          recs(src)
        case Space.Range(src, _, _) =>
          src match
            case Space.TailsUnion(_) => mark("range.over_tails_union", x)
            case Space.TailsIntersection(_) => mark("range.over_tails_intersection", x)
            case Space.Composition(_, _) => mark("range.over_composition", x)
            case _ => ()
          recs(src)
        case Space.TailsUnion(src @ Space.TailsUnion(_)) =>
          mark("tails.union_over_union", x)
          recs(src)
        case Space.TailsUnion(src @ Space.TailsIntersection(_)) =>
          mark("tails.union_over_intersection", x)
          recs(src)
        case Space.TailsUnion(src) =>
          recs(src)
        case Space.TailsIntersection(src @ Space.TailsUnion(_)) =>
          mark("tails.intersection_over_union", x)
          recs(src)
        case Space.TailsIntersection(src @ Space.TailsIntersection(_)) =>
          mark("tails.intersection_over_intersection", x)
          recs(src)
        case Space.TailsIntersection(src) =>
          recs(src)
        case Space.PrefixClosure(src @ Space.PrefixClosure(_)) =>
          mark("closure.prefix_idempotent", x)
          recs(src)
        case Space.PrefixClosure(src) =>
          recs(src)
        case Space.SuffixClosure(src @ Space.SuffixClosure(_)) =>
          mark("closure.suffix_idempotent", x)
          recs(src)
        case Space.SuffixClosure(src) =>
          recs(src)
        case Space.TailsClosure(src @ Space.TailsClosure(_)) =>
          mark("closure.tails_idempotent", x)
          recs(src)
        case Space.TailsClosure(src) =>
          recs(src)
        case Space.Iteration(src, symbol, rest, templates) =>
          if isEmptySpace(src) then mark("iteration.empty_source", x)
          if !usesRef(templates, symbol) && !usesMention(templates, rest) then mark("iteration.body_independent_of_binders", x)
          if templates == Space.Mention(rest) then mark("iteration.body_is_rest_identity", x)
          recs(src)
          recs(templates)
        case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
          if isEmptySpace(src) then mark("fold.empty_source", x)
          if !usesRef(templates, symbol) && !usesMention(templates, rest) && !usesRef(templates, acc) then mark("fold.body_independent_of_binders", x)
          if !usesRefInPath(update, acc) then mark("fold.update_independent_of_accumulator", x)
          if !usesRefInPath(update, symbol) then mark("fold.update_independent_of_head", x)
          recs(src)
          recp(initial)
          recs(templates)
          recp(update)
        case Space.Fixpoint(initial, variable, step) =>
          if !usesMention(step, variable) then mark("fixpoint.step_independent_of_state", x)
          val uops = unionOperands(step)
          if uops.exists(_ == Space.Mention(variable)) && uops.forall(op => op == Space.Mention(variable) || !usesMention(op, variable)) then
            mark("fixpoint.state_union_static", x)
          if uops.exists(_ == Space.TailsUnion(Space.Mention(variable))) && uops.forall(op => op == Space.TailsUnion(Space.Mention(variable)) || !usesMention(op, variable)) then
            mark("fixpoint.tails_state_union_static", x)
          if containsFixpoint(initial) || containsFixpoint(step) then mark("fixpoint.nested_fixpoint", x)
          recs(initial)
          recs(step)
        case Space.Empty | Space.Mention(_) => ()
        case Space.Call(_, refs, mentions) =>
          refs.foreach(recp)
          mentions.foreach(recs)
        case Space.Singleton(p) => recp(p)
        case Space.Restriction(a, b) =>
          recs(a)
          recs(b)
        case Space.Raffination(a, b) =>
          recs(a)
          recs(b)
        case Space.Composition(a, b) =>
          recs(a)
          recs(b)
        case Space.Wrap(src, p) =>
          recs(src)
          recp(p)
        case Space.Unwrap(src, p) =>
          recs(src)
          recp(p)
        case Space.GroundedPS(p, _) => recp(p)
        case Space.GroundedSS(src, _) => recs(src)

    recs(s)
    val countRows = counts.toVector.sortBy { case (k, v) => (-v, k) }
    val exampleRows = examples.toVector.flatMap { case (k, vs) => vs.map(k -> _) }.sortBy(_._1)
    countRows -> exampleRows

  private def opCounts(s: Space): Vector[(String, Int)] =
    val counts = mutable.Map.empty[String, Int]
    collect(s)(spre = { case sp => opName(sp) })._1.foreach((_, name) => inc(counts, name))
    counts.toVector.sortBy { case (k, v) => (-v, k) }

  private def duplicateSubterms(s: Space): Vector[(String, Int, Int)] =
    val counts = mutable.Map.empty[String, (Int, Int)]
    collect(s)(spre = { case sp => sp })._1.foreach { (sp, _) =>
      val key = sp.show
      val prev = counts.getOrElse(key, 0 -> key.length)
      counts.update(key, (prev._1 + 1) -> prev._2)
    }
    counts.toVector.collect {
      case (k, (count, size)) if count > 1 && size > 40 => (k, count, size)
    }.sortBy { case (_, count, size) => (-count, -size) }.take(12)

  private def reportProgram(program: FreeExpressionTreeFuzzer.Accepted, row: SourceRow): ProgramReport =
    val routine = Routine(RoutinePtr(s"degenerate_free_${program.id}"), program.env.pathInputs, program.env.spaceInputs, program.expr)
    val sc = Supercompiler.compile(routine, buildGraph = true, maxCompileMillis = 30000L)
    val graphBefore = Supercompiler.graphStats(transpile(routine))
    val graphAfter = sc.graph.map(Supercompiler.graphStats).getOrElse(GraphStats(0, 0, 0))
    val (patterns, examples) = analyzePatterns(sc.routine.body)
    ProgramReport(
      program.id,
      program.candidateId,
      Supercompiler.stats(program.expr),
      Supercompiler.stats(sc.routine.body),
      graphBefore,
      graphAfter,
      patterns,
      opCounts(program.expr),
      opCounts(sc.routine.body),
      duplicateSubterms(sc.routine.body),
      examples
    )

  private def renderCounts(rows: Vector[(String, Int)], limit: Int = 24): String =
    rows.take(limit).map { case (k, v) => s"`$k`=$v" }.mkString(", ")

  private def renderReport(reports: Vector[ProgramReport],
                           sourceCsv: NioPath,
                           corpusSeed: Long,
                           frameSeed: Long): String =
    val aggregate = mutable.Map.empty[String, Int]
    reports.foreach(_.patternCounts.foreach((k, v) => inc(aggregate, k, v)))
    val aggRows = aggregate.toVector.filterNot(_._1.startsWith("op.")).sortBy { case (k, v) => (-v, k) }
    val opRows = aggregate.toVector.filter(_._1.startsWith("op.")).sortBy { case (k, v) => (-v, k) }

    val md = new StringBuilder
    md.append("# Top Slow Program Degeneracy Analysis\n\n")
    md.append(s"- Source CSV: `$sourceCsv`\n")
    md.append(s"- Corpus seed: $corpusSeed\n")
    md.append(s"- Frame seed: $frameSeed\n")
    md.append(s"- Programs analyzed: ${reports.map(_.programId).mkString(", ")}\n")
    md.append("- Analysis target: SC residual expression after `Supercompiler.compile`; graph optimization is included only as shape context.\n\n")

    md.append("## Aggregate Residual Degeneracies\n\n")
    md.append("| pattern | count |\n")
    md.append("|---|---:|\n")
    aggRows.foreach((k, v) => md.append(s"| `$k` | $v |\n"))
    md.append("\n## Aggregate Residual Operation Counts\n\n")
    md.append("| op | count |\n")
    md.append("|---|---:|\n")
    opRows.foreach((k, v) => md.append(s"| `${k.stripPrefix("op.")}` | $v |\n"))

    md.append("\n## Per Program Summary\n\n")
    md.append("| program | AST before -> after | graph nodes before -> after | top residual degeneracies |\n")
    md.append("|---:|---:|---:|---|\n")
    reports.foreach { r =>
      val patterns = renderCounts(r.patternCounts.filterNot(_._1.startsWith("op.")), limit = 8)
      md.append(s"| ${r.programId} | ${r.beforeStats.totalNodes} -> ${r.afterStats.totalNodes} | ${r.graphBefore.nodes} -> ${r.graphAfter.nodes} | $patterns |\n")
    }

    md.append("\n## Repeated Residual Subterms\n\n")
    reports.foreach { r =>
      md.append(s"### Program ${r.programId}\n\n")
      if r.duplicateSubterms.isEmpty then md.append("No repeated residual subterms over the reporting threshold.\n\n")
      else
        md.append("| count | chars | subterm |\n")
        md.append("|---:|---:|---|\n")
        r.duplicateSubterms.take(6).foreach { (term, count, size) =>
          md.append(s"| $count | $size | `${term.replace('`', '\'').take(220)}` |\n")
        }
        md.append('\n')
    }

    md.append("## Example Residual Sites\n\n")
    reports.foreach { r =>
      md.append(s"### Program ${r.programId}\n\n")
      r.examples.groupBy(_._1).toVector.sortBy(_._1).foreach { (label, values) =>
        md.append(s"- `$label`:\n")
        values.take(ExampleLimit).foreach((_, value) => md.append(s"  - `$value`\n"))
      }
      md.append('\n')
    }

    md.append("## Diagnosis\n\n")
    md.append("1. Empty space literals are not canonicalized: `Literal(SpaceValue())` survives instead of becoming `Empty`. This hides obvious empty-source loop, empty residual, and algebraic annihilator rules from later passes.\n")
    md.append("2. `Supercompiler.compile` is not doing process-style driving on these expressions. They are direct free expression trees with no helper calls, so the process supercompiler has nothing to unfold/fold/generalize. The observed reductions come from source normalization plus graph optimization.\n")
    md.append("3. `Range` subset reasoning is now handled for the common unit-set cases: `Range(x, a, b)` participates in union/intersection/subtraction absorption and nested positive/suffix range composition. Remaining Range degeneracies are the harder ordered-border cases, especially negative-window composition and distribution through virtual frontier operators.\n")
    md.append("4. Several residual `Fixpoint` forms are degenerate: their step is independent of the state, `state \\/ static`, or `TailsUnion(state) \\/ static`. These can be collapsed to one-step union or a dedicated suffix-closure/native trie op instead of a general saturating loop.\n")
    md.append("5. `TailsUnion`/`TailsIntersection` combinations survive as opaque nodes. The trie algebra has native tails operations, but the source optimizer lacks laws for nested tails and tails through range/intersection/union patterns.\n")
    md.append("6. Binder-independent iteration/fold bodies survive where simplification would need a non-empty guard or a first-head witness. Adding a small `NonEmpty`/`ExistsHead` guard, or driving split-by-empty/source-shape, would make those rewrites sound.\n")
    md.append("7. Associative/commutative/idempotent normalization is shallow. Direct `x \\/ x` and `x /\\\\ x` are rare, but duplicate operands under nested unions/intersections and repeated large subterms remain unless the graph backend shares them.\n")
    md.result()

  def run(sourceCsv: NioPath,
          outDir: NioPath,
          topN: Int,
          corpusSeed: Long,
          frameSeed: Long): Vector[ProgramReport] =
    val top = rows(sourceCsv).sortBy(r => -r.elapsedMs).take(topN)
    val corpus = FreeExpressionTreeFuzzer.generate(top.map(_.programId).max + 1, corpusSeed, progressEvery = 0)
    val byId = corpus.programs.map(p => p.id -> p).toMap
    val reports = top.map(row => reportProgram(byId(row.programId), row)).toVector
    Files.createDirectories(outDir)
    write(outDir.resolve("README.md"), renderReport(reports, sourceCsv, corpusSeed, frameSeed))
    println(s"wrote ${outDir.resolve("README.md")}")
    reports.foreach { r =>
      val patterns = renderCounts(r.patternCounts.filterNot(_._1.startsWith("op.")), limit = 6)
      println(s"program ${r.programId}: ${r.beforeStats.totalNodes} -> ${r.afterStats.totalNodes}; $patterns")
    }
    reports

@main def slowProgramDegeneracyRun(sourceCsv: String = "fuzzer_full_backend_verify_1000x1000_seed20260705/per_program.csv",
                                   outDir: String = "fuzzer_top5_sc_degeneracies_seed20260705",
                                   topN: Int = 5,
                                   corpusSeed: Long = 20260702L,
                                   frameSeed: Long = 20260705L): Unit =
  SlowProgramDegeneracyAnalysis.run(Paths.get(sourceCsv), Paths.get(outDir), topN, corpusSeed, frameSeed)
