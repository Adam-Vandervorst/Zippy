package morkl

import morkl.Syntax.{*, given}
import scala.collection.Searching

object Fuzzer:
  import java.util.Random

  trait Dist[+T]:
    self =>
    def sample(using rng: Random): T
    def map[S](f: T => S): Dist[S] = Mapped(this, f)
    def filter(p: T => Boolean): Dist[T] = Filtered(this, p)
    def flatMap[S](f: T => Dist[S]): Dist[S] = Dep(this, f)
    def collect[S](pf: PartialFunction[T, S]): Dist[S] = Collected(this, pf)
    def samples(using rng: Random): LazyList[T] = LazyList.continually(sample)

  def Uniform(low: Int, high: Int): Dist[Int] =
    new Dist[Int]:
      override def sample(using rng: Random): Int = rng.nextInt(low, high)

  def Uniform(low: Long, high: Long): Dist[Long] =
    new Dist[Long]:
      override def sample(using rng: Random): Long = rng.nextLong(low, high)

  def Uniform(low: Float, high: Float): Dist[Float] =
    new Dist[Float]:
      override def sample(using rng: Random): Float = rng.nextFloat(low, high)

  def Uniform(low: Double, high: Double): Dist[Double] =
    new Dist[Double]:
      override def sample(using rng: Random): Double = rng.nextDouble(low, high)

  case class Filtered[T](d: Dist[T], p: T => Boolean) extends Dist[T]:
    override def sample(using rng: Random): T =
      while true do
        val s = d.sample
        if p(s) then return s
      throw IllegalStateException("unreachable filtered sampler exit")

  case class Mapped[T, S](d: Dist[T], f: T => S) extends Dist[S]:
    override def sample(using rng: Random): S = f(d.sample)

  case class Collected[T, S](d: Dist[T], pf: PartialFunction[T, S]) extends Dist[S]:
    override def sample(using rng: Random): S =
      while true do
        d.sample match
          case pf(s) => return s
          case _ => ()
      throw IllegalStateException("unreachable collected sampler exit")

  case class Pair[T0, T1, S](d0: Dist[T0], d1: Dist[T1], f: (T0, T1) => S) extends Dist[S]:
    override def sample(using rng: Random): S = f(d0.sample, d1.sample)

  case class Cond[X, Y, Z](dc: Dist[Boolean], dx: Dist[X], dy: Dist[Y], f: Either[X, Y] => Z) extends Dist[Z]:
    override def sample(using rng: Random): Z =
      f(Either.cond(dc.sample, dy.sample, dx.sample))

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

  case class Categorical[T](di: Dist[Int], ts: Vector[T]) extends Dist[T]:
    override def sample(using rng: Random): T = ts(di.sample)

  object Categorical:
    def uniform[T](ts: Vector[T]): Categorical[T] =
      Categorical(Uniform(0, ts.length), ts)

    def ratios[T](ep: IterableOnce[(T, Int)]): Categorical[T] =
      val elems = Vector.newBuilder[T]
      val cdf = Vector.newBuilder[Int]
      var sum = 0
      for (e, r) <- ep.iterator do
        elems += e
        cdf += sum
        sum += r
      require(sum > 0, "weighted categorical sampler needs positive total weight")
      val cdfv = cdf.result()
      Categorical(Mapped(Uniform(0, sum), x =>
        cdfv.search(x) match
          case Searching.Found(i) => i
          case Searching.InsertionPoint(i) => i - 1
      ), elems.result())

  case class Repeated[T](dlength: Dist[Int], ditem: Dist[T]) extends Dist[Vector[T]]:
    override def sample(using rng: Random): Vector[T] =
      Vector.fill(dlength.sample)(ditem.sample)

  case class Sentinel[T](dsent: Dist[Option[T]]) extends Dist[Vector[T]]:
    override def sample(using rng: Random): Vector[T] =
      val b = Vector.newBuilder[T]
      while true do
        dsent.sample match
          case None => return b.result()
          case Some(t) => b += t
      throw IllegalStateException("unreachable sentinel sampler exit")
end Fuzzer

trait Loc:
  def isPath(segment: PathValue): Boolean
  def branches(segment: PathValue): Set[PathItem]
  def descend(segment: PathValue, branch: Int): Loc = this

  def instantiate(segment: PathValue = PathValue(Nil)): SpaceValue =
    val rest = branches(segment).flatMap(b => instantiate(PathValue(segment.items appended b)).paths)
    if isPath(segment) then SpaceValue(rest.incl(segment)) else SpaceValue(rest)

object Loc:
  case class Const(path: PathValue) extends Loc:
    override def isPath(segment: PathValue): Boolean = segment == path
    override def branches(segment: PathValue): Set[PathItem] =
      if segment.items.length < path.items.length then Set(path.items(segment.items.length)) else Set.empty

  case class Repeat(alphabet: Set[PathItem], k: Int) extends Loc:
    override def isPath(segment: PathValue): Boolean = segment.items.length == k
    override def branches(segment: PathValue): Set[PathItem] =
      if segment.items.length < k then alphabet else Set.empty

  case class Full(alphabet: Set[PathItem]) extends Loc:
    override def isPath(segment: PathValue): Boolean = true
    override def branches(segment: PathValue): Set[PathItem] = alphabet

  case object Empty extends Loc:
    override def isPath(segment: PathValue): Boolean = false
    override def branches(segment: PathValue): Set[PathItem] = Set.empty

  case class Trie(space: SpaceValue) extends Loc:
    override def isPath(segment: PathValue): Boolean = space.paths.contains(segment)
    override def branches(segment: PathValue): Set[PathItem] =
      space.paths.collect {
        case e if e.items.length > segment.items.length && e.items.startsWith(segment.items) =>
          e.items(segment.items.length)
      }

  case class Union(locs: Set[Loc]) extends Loc:
    override def isPath(segment: PathValue): Boolean = locs.exists(_.isPath(segment))
    override def branches(segment: PathValue): Set[PathItem] = locs.flatMap(_.branches(segment))

  case class Intersection(locs: Set[Loc]) extends Loc:
    override def isPath(segment: PathValue): Boolean = locs.forall(_.isPath(segment))
    override def branches(segment: PathValue): Set[PathItem] =
      locs.map(_.branches(segment)).reduceOption(_ intersect _).getOrElse(Set.empty)

  case class Subtraction(loc: Loc, neg: Loc) extends Loc:
    override def isPath(segment: PathValue): Boolean = loc.isPath(segment) && !neg.isPath(segment)
    override def branches(segment: PathValue): Set[PathItem] =
      loc.branches(segment).removedAll(neg.branches(segment))

  case class Restriction(loc: Loc, accepted: Loc) extends Loc:
    private def hasAcceptedPrefix(segment: PathValue): Boolean =
      (0 to segment.items.length).exists(i => accepted.isPath(PathValue(segment.items.take(i))))
    override def isPath(segment: PathValue): Boolean =
      loc.isPath(segment) && hasAcceptedPrefix(segment)
    override def branches(segment: PathValue): Set[PathItem] =
      if hasAcceptedPrefix(segment) then loc.branches(segment) else Set.empty

  case class Raffination(loc: Loc, unaccepted: Loc) extends Loc:
    private def hasUnacceptedPrefix(segment: PathValue): Boolean =
      (0 to segment.items.length).exists(i => unaccepted.isPath(PathValue(segment.items.take(i))))
    override def isPath(segment: PathValue): Boolean =
      loc.isPath(segment) && !hasUnacceptedPrefix(segment)
    override def branches(segment: PathValue): Set[PathItem] =
      if hasUnacceptedPrefix(segment) then Set.empty else loc.branches(segment)

  case class Compose(left: Loc, right: Loc) extends Loc:
    override def isPath(segment: PathValue): Boolean =
      (0 to segment.items.length).exists { i =>
        val (l, r) = segment.items.splitAt(i)
        left.isPath(PathValue(l)) && right.isPath(PathValue(r))
      }
    override def branches(segment: PathValue): Set[PathItem] =
      left.branches(segment) ++
        (0 to segment.items.length)
          .filter(i => left.isPath(PathValue(segment.items.take(i))))
          .flatMap(i => right.branches(PathValue(segment.items.drop(i)))).toSet

  case class Dep(left: Loc, rightf: PathValue => Loc) extends Loc:
    override def isPath(segment: PathValue): Boolean =
      (0 to segment.items.length).exists { i =>
        val (l, r) = segment.items.splitAt(i)
        left.isPath(PathValue(l)) && rightf(PathValue(l)).isPath(PathValue(r))
      }
    override def branches(segment: PathValue): Set[PathItem] =
      left.branches(segment) ++
        (0 to segment.items.length)
          .filter(i => left.isPath(PathValue(segment.items.take(i))))
          .flatMap(i => rightf(PathValue(segment.items.take(i))).branches(PathValue(segment.items.drop(i)))).toSet

  def uop(src: Loc, pf: PathValue => PathValue): Loc =
    Dep(src, p => Const(pf(p)))

  def intToInt(f: Int => Int): Loc =
    uop(Full((0 to 9).map(k => PathItem(k.toString)).toSet), p =>
      PathValue(f(p.items.map(_.show).mkString.toInt).toString.map(c => PathItem(c.toString)).toList))

  def sqrt: Loc = intToInt(i => Math.sqrt(i.toDouble).toInt)
end Loc

object SpaceFuzzer:
  import Fuzzer.*
  import Space.*
  import java.util.Random

  val alphabet: Vector[PathItem] = Vector("a", "b", "c", "d").map(PathItem(_))
  val argM: SpaceMention = SpaceMention("x")
  val X: Space = Space.Mention(argM)
  val callArgM: SpaceMention = SpaceMention("call_x")
  val callRoutine: Routine = Routine(RoutinePtr("fuzzer_identity"), Vector.empty,
    Vector(callArgM), Space.Mention(callArgM))
  val routines: PartialFunction[RoutinePtr, Routine] = Syntax.mod(callRoutine)

  case class Example(program: Space, arg: SpaceValue, result: SpaceValue)

  private def randItem: Dist[PathItem] =
    Categorical.uniform(alphabet)

  private def randPath(maxLen: Int): Dist[PathValue] =
    Repeated(Uniform(1, maxLen + 1), randItem).map(v => PathValue(v.toList))

  private def randTrie(maxN: Int, maxLen: Int): Dist[Loc] =
    Repeated(Uniform(2, maxN + 1), randPath(maxLen)).map(v => Loc.Trie(SpaceValue(v.toSet)))

  private def randRepeat: Dist[Loc] =
    Uniform(1, 3).flatMap(k => Uniform(1, alphabet.length + 1).map(m => Loc.Repeat(alphabet.take(m).toSet, k)))

  private def argLoc: Dist[Loc] =
    Categorical.ratios(Seq[(Dist[Loc], Int)](
      randTrie(10, 4) -> 4,
      randRepeat -> 2,
      Pair(randTrie(8, 3), randTrie(8, 3), (a, b) => Loc.Union(Set(a, b))) -> 2,
      Pair(randTrie(10, 3), randTrie(5, 2), (a, b) => Loc.Subtraction(a, b)) -> 1,
      Pair(randRepeat, randTrie(6, 2), (a, b) => Loc.Compose(a, b)) -> 1
    )).flatMap(identity)

  def argDist: Dist[SpaceValue] =
    argLoc.map(_.instantiate()).filter(sv => sv.paths.nonEmpty && sv.paths.size <= 28)

  def genProg(arg: SpaceValue,
              maxDepth: Int,
              sargs: Vector[SpaceMention] = Vector(argM),
              pargs: Vector[PathRef] = Vector.empty,
              extended: Boolean = false): Dist[Space] = new Dist[Space]:
    private val paths = arg.paths.toVector
    private val firstItems = paths.flatMap(_.items.headOption).distinct
    private type Scope = Vector[(PathRef, SpaceMention)]

    override def sample(using rng: Random): Space = rec(maxDepth, Vector.empty)

    private def pick[T](v: Vector[T])(using rng: Random): T = v(rng.nextInt(v.length))
    private def constP(p: PathValue): Path = Path.Constant(p)
    private def freshTag(using rng: Random): PathValue =
      PathValue(List(PathItem("w" + rng.nextInt(4))))

    private def someArg(using rng: Random): SpaceValue =
      val chosen = paths.filter(_ => rng.nextBoolean())
      SpaceValue((if chosen.isEmpty then Vector(pick(paths)) else chosen).toSet)

    private def somePrefixLit(using rng: Random): Space =
      val use0 = firstItems.filter(_ => rng.nextBoolean())
      val use = if use0.isEmpty then Vector(pick(firstItems)) else use0
      Space.Literal(SpaceValue(use.map(it => PathValue(List(it))).toSet))

    private def leaf(scope: Scope)(using rng: Random): Space =
      val vars = if scope.isEmpty then Seq.empty else Seq("vsing" -> 4, "vment" -> 2, "vcat" -> 2)
      val pins = if pargs.isEmpty then Seq.empty else Seq("psing" -> 3, "pcat" -> 2)
      val extendedLeaves = if extended then Seq("empty" -> 1) else Seq.empty
      Categorical.ratios(Seq("x" -> 4, "lit" -> 1, "csing" -> 1) ++ extendedLeaves ++ vars ++ pins).sample match
        case "x" => Space.Mention(pick(sargs))
        case "lit" => Space.Literal(someArg)
        case "csing" => Space.Singleton(constP(pick(paths)))
        case "empty" => Space.Empty
        case "vsing" => Space.Singleton(Path.Deref(pick(scope)._1))
        case "vment" => Space.Mention(pick(scope)._2)
        case "vcat" => Space.Singleton(Path.Concat(Path.Deref(pick(scope)._1), constP(pick(paths))))
        case "psing" => Space.Singleton(Path.Deref(pick(pargs)))
        case _ => Space.Singleton(Path.Concat(Path.Deref(pick(pargs)), constP(pick(paths))))

    private def reorder(d: Int, scope: Scope)(using rng: Random): Space =
      val k = 1 + rng.nextInt(3)
      val hs = Vector.fill(k)(PathRef("h" + rng.nextInt(1000000)).known(1))
      val ts = Vector.fill(k)(SpaceMention("t" + rng.nextInt(1000000)))
      val tlen = 1 + rng.nextInt(k)
      val body = Space.Singleton((0 until tlen).map(_ => Path.Deref(hs(rng.nextInt(k))): Path).reduceLeft(Path.Concat(_, _)))
      var node: Space = body
      var i = k - 1
      while i >= 0 do
        node = Space.Iteration(if i == 0 then rec(d - 1, scope) else Space.Mention(ts(i - 1)), hs(i), ts(i), node)
        i -= 1
      node

    private def side(d: Int, scope: Scope, anchor: => Space)(using rng: Random): Space =
      if rng.nextInt(5) < 3 then rec(d - 1, scope) else anchor

    private def compRhs(d: Int, scope: Scope)(using rng: Random): Space =
      if rng.nextInt(5) < 3 then rec(math.min(d - 1, 2), scope) else Space.Singleton(constP(pick(paths)))

    private def rec(d: Int, scope: Scope)(using rng: Random): Space =
      if d <= 0 then leaf(scope)
      else
        val original = Seq(
          "leaf" -> 2,
          "union" -> 2,
          "inter" -> 2,
          "sub" -> 2,
          "wrap" -> 2,
          "unwrap" -> 2,
          "comp" -> 1,
          "restr" -> 2,
          "iter" -> 3,
          "tails" -> 1,
          "range" -> 1,
          "reorder" -> 1
        )
        val added = if extended then Seq(
          "raff" -> 1,
          "tailsInter" -> 1,
          "prefixClosure" -> 1,
          "suffixClosure" -> 1,
          "tailsClosure" -> 1,
          "fold" -> 1,
          "fix" -> 1,
          "groundPS" -> 1,
          "groundSS" -> 1,
          "call" -> 1,
        ) else Seq.empty
        Categorical.ratios(original ++ added).sample match
          case "leaf" => leaf(scope)
          case "union" => Space.Union(rec(d - 1, scope), rec(d - 1, scope))
          case "inter" => Space.Intersection(rec(d - 1, scope), side(d, scope, Space.Literal(someArg)))
          case "sub" => Space.Subtraction(rec(d - 1, scope), side(d, scope, Space.Singleton(constP(pick(paths)))))
          case "wrap" => Space.Wrap(rec(d - 1, scope), constP(freshTag))
          case "unwrap" => Space.Unwrap(rec(d - 1, scope), constP(PathValue(List(pick(firstItems)))))
          case "comp" => Space.Composition(rec(d - 1, scope), compRhs(d, scope))
          case "restr" => Space.Restriction(rec(d - 1, scope), side(d, scope, somePrefixLit))
          case "raff" => Space.Raffination(rec(d - 1, scope), side(d, scope, somePrefixLit))
          case "tails" => Space.TailsUnion(rec(d - 1, scope))
          case "tailsInter" => Space.TailsIntersection(rec(d - 1, scope))
          case "prefixClosure" => Space.PrefixClosure(rec(d - 1, scope))
          case "suffixClosure" => Space.SuffixClosure(rec(d - 1, scope))
          case "tailsClosure" => Space.TailsClosure(rec(d - 1, scope))
          case "fold" =>
            val head = PathRef("fold_h" + rng.nextInt(1000000)).known(1)
            val acc = PathRef("fold_acc" + rng.nextInt(1000000))
            val rest = SpaceMention("fold_t" + rng.nextInt(1000000))
            Space.Fold(
              rec(d - 1, scope), Path.ZERO, acc, head, rest,
              Space.Singleton(Path.Deref(acc)), Path.Deref(acc),
            )
          case "fix" =>
            val variable = SpaceMention("fix_v" + rng.nextInt(1000000))
            val universe = Space.Literal(someArg)
            val initial = Space.Intersection(rec(d - 1, scope), universe)
            val grown = Space.Wrap(Space.Mention(variable), constP(freshTag))
            Space.Fixpoint(initial, variable,
              Space.Intersection(Space.Union(Space.Mention(variable), grown), universe))
          case "groundPS" =>
            Space.GroundedPS(constP(pick(paths)), value =>
              SpaceValue(Set(value, PathValue(PathItem("g") :: value.items))))
          case "groundSS" =>
            Space.GroundedSS(rec(d - 1, scope), value =>
              SpaceValue(value.paths.map(path => PathValue(PathItem("g") :: path.items))))
          case "call" => Space.Call(callRoutine.name, Vector.empty, Vector(rec(d - 1, scope)))
          case "range" =>
            val lo = rng.nextInt(3)
            Space.Range(rec(d - 1, scope), lo, lo + 1 + rng.nextInt(3))
          case "reorder" => reorder(d, scope)
          case _ =>
            val hpr = PathRef("h" + rng.nextInt(1000000)).known(1)
            val tv = SpaceMention("t" + rng.nextInt(1000000))
            Space.Iteration(rec(d - 1, scope), hpr, tv, rec(d - 1, scope :+ (hpr -> tv)))

  private def evalEx(p: Space, arg: SpaceValue): Example =
    Example(p, arg, eval(p)(using PathContextMap(Map.empty), SpaceContextMap(Map(argM -> arg)), routines))

  def example(maxDepth: Int = 3, maxResult: Int = 400, extended: Boolean = false): Dist[Example] =
    Dep(argDist, arg => genProg(arg, maxDepth, extended = extended).map(p => evalEx(p, arg)).filter(e =>
      e.result.paths.nonEmpty &&
        e.result != e.arg &&
        e.result.paths.size <= maxResult &&
        Matching.freeMentions(e.program).contains(argM)
    ))
end SpaceFuzzer

object SpaceFuzzerCorpus:
  import java.nio.charset.StandardCharsets
  import java.nio.file.{Files, Path as NioPath}
  import java.util.Random

  final case class Record(id: Int, example: SpaceFuzzer.Example):
    def programNodes: Int = SpaceFuzzerCorpus.nodes(example.program)
    def opKinds: Vector[String] = SpaceFuzzerCorpus.opKinds(example.program).distinct.sorted

  private def json(s: String): String =
    s.flatMap {
      case '"' => "\\\""
      case '\\' => "\\\\"
      case '\n' => "\\n"
      case '\r' => "\\r"
      case '\t' => "\\t"
      case c if c.isControl => f"\\u${c.toInt}%04x"
      case c => c.toString
    }

  private def pathArray(sv: SpaceValue): String =
    sv.paths.toVector.sortBy(_.show).map(p => "\"" + json(p.show) + "\"").mkString("[", ",", "]")

  private def pathKinds(p: Path): Vector[String] = p match
    case Path.Deref(_) => Vector("Path.Deref")
    case Path.Constant(_) => Vector("Path.Constant")
    case Path.Concat(l, r) => "Path.Concat" +: (pathKinds(l) ++ pathKinds(r))
    case Path.GroundedPP(path, _) => "Path.GroundedPP" +: pathKinds(path)
    case Path.GroundedSP(space, _) => "Path.GroundedSP" +: opKinds(space)

  def opKinds(s: Space): Vector[String] = s match
    case Space.Empty => Vector("Space.Empty")
    case Space.Call(_, refs, mentions) => Vector("Space.Call") ++ refs.flatMap(pathKinds) ++ mentions.flatMap(opKinds)
    case Space.Mention(_) => Vector("Space.Mention")
    case Space.Singleton(path) => "Space.Singleton" +: pathKinds(path)
    case Space.Literal(_) => Vector("Space.Literal")
    case Space.Union(l, r) => "Space.Union" +: (opKinds(l) ++ opKinds(r))
    case Space.Intersection(l, r) => "Space.Intersection" +: (opKinds(l) ++ opKinds(r))
    case Space.Subtraction(l, r) => "Space.Subtraction" +: (opKinds(l) ++ opKinds(r))
    case Space.Restriction(l, r) => "Space.Restriction" +: (opKinds(l) ++ opKinds(r))
    case Space.Raffination(l, r) => "Space.Raffination" +: (opKinds(l) ++ opKinds(r))
    case Space.Composition(l, r) => "Space.Composition" +: (opKinds(l) ++ opKinds(r))
    case Space.Iteration(src, _, _, body) => "Space.Iteration" +: (opKinds(src) ++ opKinds(body))
    case Space.Fold(src, initial, _, _, _, body, update) =>
      Vector("Space.Fold") ++ opKinds(src) ++ pathKinds(initial) ++ opKinds(body) ++ pathKinds(update)
    case Space.Fixpoint(initial, _, step) => "Space.Fixpoint" +: (opKinds(initial) ++ opKinds(step))
    case Space.Wrap(src, prefix) => "Space.Wrap" +: (opKinds(src) ++ pathKinds(prefix))
    case Space.Unwrap(src, prefix) => "Space.Unwrap" +: (opKinds(src) ++ pathKinds(prefix))
    case Space.TailsUnion(src) => "Space.TailsUnion" +: opKinds(src)
    case Space.TailsIntersection(src) => "Space.TailsIntersection" +: opKinds(src)
    case Space.PrefixClosure(src) => "Space.PrefixClosure" +: opKinds(src)
    case Space.SuffixClosure(src) => "Space.SuffixClosure" +: opKinds(src)
    case Space.TailsClosure(src) => "Space.TailsClosure" +: opKinds(src)
    case Space.GroundedPS(path, _) => "Space.GroundedPS" +: pathKinds(path)
    case Space.GroundedSS(src, _) => "Space.GroundedSS" +: opKinds(src)
    case Space.Range(src, _, _) => "Space.Range" +: opKinds(src)

  def nodes(s: Space): Int = opKinds(s).count(_.startsWith("Space."))

  def generate(count: Int,
               seed: Long,
               maxDepth: Int = 5,
               maxResult: Int = 400,
               extended: Boolean = false): Vector[Record] =
    given Random = Random(seed)
    Vector.tabulate(count) { i =>
      Record(i, SpaceFuzzer.example(maxDepth, maxResult, extended).sample)
    }

  def write(records: Vector[Record], outDir: NioPath, seed: Long): Unit =
    Files.createDirectories(outDir)
    val jsonl = records.map { r =>
      val ops = r.opKinds.map(op => "\"" + json(op) + "\"").mkString("[", ",", "]")
      "{" +
        s""""id":${r.id},""" +
        s""""program_nodes":${r.programNodes},""" +
        s""""arg_paths":${r.example.arg.paths.size},""" +
        s""""result_paths":${r.example.result.paths.size},""" +
        s""""ops":$ops,""" +
        s""""arg":${pathArray(r.example.arg)},""" +
        s""""result":${pathArray(r.example.result)},""" +
        s""""program":"${json(r.example.program.show)}"""" +
        "}"
    }.mkString("\n") + "\n"
    Files.writeString(outDir.resolve("programs.jsonl"), jsonl, StandardCharsets.UTF_8)

    val samples = records.take(10).map { r =>
      s"""## Program ${r.id}
         |
         |- Program nodes: ${r.programNodes}
         |- Argument paths: ${r.example.arg.paths.size}
         |- Result paths: ${r.example.result.paths.size}
         |- Ops: ${r.opKinds.mkString(", ")}
         |
         |```scala
         |${r.example.program.show}
         |```
         |""".stripMargin
    }.mkString("\n")
    Files.writeString(outDir.resolve("SAMPLES.md"), "# Space Fuzzer Samples\n\n" + samples, StandardCharsets.UTF_8)

    val allOps = records.flatMap(_.opKinds).distinct.sorted
    val readme =
      s"""# Space Fuzzer Corpus
         |
         |- Seed: $seed
         |- Programs: ${records.length}
         |- Distinct operations: ${allOps.length}
         |- Operations: ${allOps.mkString(", ")}
         |
         |Artifacts:
         |
         |- `programs.jsonl`: replayable program, argument, result, and operation metadata.
         |- `SAMPLES.md`: first ten pretty-printed programs.
         |""".stripMargin
    Files.writeString(outDir.resolve("README.md"), readme, StandardCharsets.UTF_8)

  def run(count: Int,
          seed: Long,
          outDir: NioPath,
          maxDepth: Int = 5,
          maxResult: Int = 400): Vector[Record] =
    val records = generate(count, seed, maxDepth, maxResult)
    write(records, outDir, seed)
    records

@main def spaceFuzzerCorpusRun(count: Int = 1000,
                               seed: Long = 20260708L,
                               outDir: String = "space_fuzzer_dist_corpus_1000",
                               maxDepth: Int = 5,
                               maxResult: Int = 400): Unit =
  SpaceFuzzerCorpus.run(count, seed, java.nio.file.Paths.get(outDir), maxDepth, maxResult)
