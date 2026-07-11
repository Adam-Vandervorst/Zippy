import scala.collection.Searching
import morkl.Syntax.{*, given}

/** A small library of composable sampling combinators (`Dist[T]` = a distribution you can `sample`).
 *  These are the "zipper" primitives the program/space fuzzer is built from: `Pair`/`Cond`/`Dep`
 *  combine distributions, `Concentrated`/`Diluted` fold a running state over a stream of samples,
 *  `Categorical` picks weighted alternatives.  `Dep` is the key one — a sampled value can DETERMINE
 *  the next distribution, which is exactly how an argument space determines the program drawn over it. */
object Fuzzer:
  import java.util.Random

  trait Dist[T]:
    def sample(using rng: Random): T
    def map[S](f: T => S): Dist[S] = Mapped(this, f)
    def filter(p: T => Boolean): Dist[T] = Filtered(this, p)
    def flatMap[S](f: T => Dist[S]): Dist[S] = Dep(this, f)
    /** an infinite lazy stream of independent samples */
    def samples(using rng: Random): LazyList[T] = LazyList.continually(sample)

  // Range distributions over the four primitive numeric types (Java 17 RandomGenerator ranges).
  def Uniform(low: Int, high: Int): Dist[Int]       = new Dist[Int]    { def sample(using rng: Random) = rng.nextInt(low, high) }
  def Uniform(low: Long, high: Long): Dist[Long]    = new Dist[Long]   { def sample(using rng: Random) = rng.nextLong(low, high) }
  def Uniform(low: Float, high: Float): Dist[Float] = new Dist[Float]  { def sample(using rng: Random) = rng.nextFloat(low, high) }
  def Uniform(low: Double, high: Double): Dist[Double] = new Dist[Double] { def sample(using rng: Random) = rng.nextDouble(low, high) }

  /** rejection sampling: redraw until `p` holds */
  case class Filtered[T](d: Dist[T], p: T => Boolean) extends Dist[T]:
    override def sample(using rng: Random): T =
      while true do { val s = d.sample; if p(s) then return s }
      throw IllegalStateException()

  case class Mapped[T, S](d: Dist[T], f: T => S) extends Dist[S]:
    override def sample(using rng: Random): S = f(d.sample)

  /** rejection + map in one: redraw until the partial function is defined */
  case class Collected[T, S](d: Dist[T], pf: PartialFunction[T, S]) extends Dist[S]:
    override def sample(using rng: Random): S =
      while true do d.sample match { case pf(s) => return s; case _ => () }
      throw IllegalStateException()

  case class Pair[T0, T1, S](d0: Dist[T0], d1: Dist[T1], f: (T0, T1) => S) extends Dist[S]:
    override def sample(using rng: Random): S = f(d0.sample, d1.sample)

  case class Cond[X, Y, Z](dc: Dist[Boolean], dx: Dist[X], dy: Dist[Y], f: Either[X, Y] => Z) extends Dist[Z]:
    override def sample(using rng: Random): Z = f(Either.cond(dc.sample, dy.sample, dx.sample))

  /** dependent draw (monadic bind): sample `dx`, then the distribution it selects */
  case class Dep[X, Y](dx: Dist[X], fdy: X => Dist[Y]) extends Dist[Y]:
    override def sample(using rng: Random): Y = fdy(dx.sample).sample

  /** fold a running accumulator over a stream of `dx` samples until it yields a result (cf. the
   *  Monte-Carlo π estimator: accumulate hit/miss counts until enough samples, then emit the ratio) */
  case class Concentrated[X, Y, A](dx: Dist[X], initial: A, fa: (A, X) => Either[A, Y]) extends Dist[Y]:
    override def sample(using rng: Random): Y =
      var a = initial
      while true do fa(a, dx.sample) match { case Right(y) => return y; case Left(a2) => a = a2 }
      throw IllegalStateException()

  case class Degenerate[T](t: T) extends Dist[T]:
    override def sample(using rng: Random): T = t

  case class Categorical[T](di: Dist[Int], ts: Vector[T]) extends Dist[T]:
    override def sample(using rng: Random): T = ts(di.sample)
  object Categorical:
    def uniform[T](ts: Vector[T]): Categorical[T] = Categorical(Uniform(0, ts.length), ts)
    /** choose elements with probability proportional to their integer weights */
    def ratios[T](ep: IterableOnce[(T, Int)]): Categorical[T] =
      val elems = Vector.newBuilder[T]; val cdf = Vector.newBuilder[Int]; var sum = 0
      for (e, r) <- ep.iterator do { elems += e; cdf += sum; sum += r }
      val cdfv = cdf.result()
      Categorical(Mapped(Uniform(0, sum), x => cdfv.search(x) match {
        case Searching.Found(i) => i
        case Searching.InsertionPoint(i) => i - 1
      }), elems.result())

  /** a vector of `dlength` independent items */
  case class Repeated[T](dlength: Dist[Int], ditem: Dist[T]) extends Dist[Vector[T]]:
    override def sample(using rng: Random): Vector[T] = Vector.fill(dlength.sample)(ditem.sample)

  /** keep drawing items until the sentinel draws `None` */
  case class Sentinel[T](dsent: Dist[Option[T]]) extends Dist[Vector[T]]:
    override def sample(using rng: Random): Vector[T] =
      val b = Vector.newBuilder[T]
      while true do dsent.sample match { case None => return b.result(); case Some(t) => b += t }
      throw IllegalStateException()
end Fuzzer


/** A `Loc` is a LAZY, structural description of a set of paths (a [[SpaceValue]]) as a zipper: at any
 *  `segment` it answers "is this a member path?" (`is_path`) and "which items extend it?" (`branches`).
 *  `instantiate` walks the zipper to materialise the concrete space.  The combinators mirror the MORKL
 *  algebra (Union/Intersection/Subtraction/Restriction/Compose/Dep), so a structured argument space can
 *  be *described* and then realised — the fuzzer uses bounded `Loc`s to generate argument spaces. */
trait Loc:
  def is_path(segment: PathValue): Boolean
  def branches(segment: PathValue): Set[PathItem]
  def descend(segment: PathValue, branch: Int): Loc = this

  def instantiate(segment: PathValue = PathValue(Nil)): SpaceValue =
    val rec = branches(segment).flatMap(b => instantiate(PathValue(segment.items appended b)).paths)
    if is_path(segment) then SpaceValue(rec.incl(segment)) else SpaceValue(rec)

object Loc:
  case class Const(path: PathValue) extends Loc:
    def is_path(segment: PathValue): Boolean = segment == path
    def branches(segment: PathValue): Set[PathItem] =
      if segment.items.length < path.items.length then Set(path.items(segment.items.length)) else Set.empty

  case class Repeat(alphabet: Set[PathItem], k: Int) extends Loc:
    def is_path(segment: PathValue): Boolean = segment.items.length == k
    def branches(segment: PathValue): Set[PathItem] = if segment.items.length < k then alphabet else Set.empty

  case class Full(alphabet: Set[PathItem]) extends Loc:
    def is_path(segment: PathValue): Boolean = true
    def branches(segment: PathValue): Set[PathItem] = alphabet

  case object Empty extends Loc:
    def is_path(segment: PathValue): Boolean = false
    def branches(segment: PathValue): Set[PathItem] = Set.empty

  case class Trie(space: SpaceValue) extends Loc:
    def is_path(segment: PathValue): Boolean = space.paths.contains(segment)
    def branches(segment: PathValue): Set[PathItem] = space.paths.collect {
      case e if e.items.length > segment.items.length && e.items.startsWith(segment.items) => e.items(segment.items.length) }

  case class Union(locs: Set[Loc]) extends Loc:
    def is_path(segment: PathValue): Boolean = locs.exists(_.is_path(segment))
    def branches(segment: PathValue): Set[PathItem] = locs.flatMap(_.branches(segment))

  case class Intersection(locs: Set[Loc]) extends Loc:
    def is_path(segment: PathValue): Boolean = locs.forall(_.is_path(segment))
    def branches(segment: PathValue): Set[PathItem] = locs.map(_.branches(segment)).reduce(_ intersect _)

  case class Subtraction(loc: Loc, neg: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && !neg.is_path(segment)
    def branches(segment: PathValue): Set[PathItem] = loc.branches(segment) removedAll neg.branches(segment)

  case class Restriction(loc: Loc, accepted: Loc) extends Loc:
    private def hasAcceptedPrefix(segment: PathValue): Boolean =
      (0 to segment.items.length).exists(i => accepted.is_path(PathValue(segment.items.take(i))))
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && hasAcceptedPrefix(segment)
    def branches(segment: PathValue): Set[PathItem] = if hasAcceptedPrefix(segment) then loc.branches(segment) else Set.empty

  case class Raffination(loc: Loc, unaccepted: Loc) extends Loc:
    private def hasUnacceptedPrefix(segment: PathValue): Boolean =
      (0 to segment.items.length).exists(i => unaccepted.is_path(PathValue(segment.items.take(i))))
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && !hasUnacceptedPrefix(segment)
    def branches(segment: PathValue): Set[PathItem] = if !hasUnacceptedPrefix(segment) then loc.branches(segment) else Set.empty

  /** concatenation product: a path is a `left` path followed by a `right` path.  `branches` must both
   *  EXTEND the (in-progress) left part and, once any left prefix completes, START the right part —
   *  the draft omitted the former, so a Compose never grew its left side; fixed here. */
  case class Compose(left: Loc, right: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = (0 to segment.items.length).exists(i =>
      val (l, r) = segment.items.splitAt(i); left.is_path(PathValue(l)) && right.is_path(PathValue(r)))
    def branches(segment: PathValue): Set[PathItem] =
      left.branches(segment) ++
        (0 to segment.items.length).filter(i => left.is_path(PathValue(segment.items.take(i))))
          .flatMap(i => right.branches(PathValue(segment.items.drop(i)))).toSet

  /** dependent concatenation: the right factor is chosen by the left path actually taken */
  case class Dep(left: Loc, rightf: PathValue => Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = (0 to segment.items.length).exists(i =>
      val (l, r) = segment.items.splitAt(i); left.is_path(PathValue(l)) && rightf(PathValue(l)).is_path(PathValue(r)))
    def branches(segment: PathValue): Set[PathItem] =
      left.branches(segment) ++
        (0 to segment.items.length).filter(i => left.is_path(PathValue(segment.items.take(i))))
          .flatMap(i => rightf(PathValue(segment.items.take(i))).branches(PathValue(segment.items.drop(i)))).toSet

  def uop(src: Loc, pf: PathValue => PathValue) = Dep(src, p => Const(pf(p)))
  def int_to_int(f: Int => Int) = uop(Full((0 to 9).map(k => PathItem.Symbol(k.toString)).toSet),
    p => PathValue(f(p.items.map(_.show).mkString.toInt).toString.map(c => PathItem.Symbol(c.toString)).toList))
  def sqrt = int_to_int(i => Math.sqrt(i.toDouble).toInt)
end Loc


/** Generates realistic, diverse MORKL programs together with a DEPENDENT argument space and the
 *  result of running the program on it.  The dependency (the `Dep` below) is the point: an argument
 *  space is sampled first (as a bounded [[Loc]], then materialised), and the program is then drawn
 *  *over that space* — its literals, wrap/unwrap prefixes and restriction keys are taken from the
 *  argument's own paths, so unwraps land, intersections overlap, and restrictions keep something.
 *  The result space is `eval(program)` with the single free mention `x` bound to the argument. */
object SpaceFuzzer:
  import Fuzzer.*
  import Space.*
  import java.util.Random

  val alphabet: Vector[PathItem] = Vector("a", "b", "c", "d").map(PathItem.Symbol(_))
  val argM: SpaceMention = SpaceMention("x")
  val X: Space = Space.Mention(argM)

  case class Example(program: Space, arg: SpaceValue, result: SpaceValue)

  // ---- argument spaces, described with the Loc zipper primitives then materialised ----
  private def randItem: Dist[PathItem] = Categorical.uniform(alphabet)
  private def randPath(maxLen: Int): Dist[PathValue] = Repeated(Uniform(1, maxLen + 1), randItem).map(v => PathValue(v.toList))
  private def randTrie(maxN: Int, maxLen: Int): Dist[Loc] = Repeated(Uniform(2, maxN + 1), randPath(maxLen)).map(v => Loc.Trie(SpaceValue(v.toSet)))
  private def randRepeat: Dist[Loc] = Uniform(1, 3).flatMap(k => Uniform(1, alphabet.length + 1).map(m => Loc.Repeat(alphabet.take(m).toSet, k)))
  private def argLoc: Dist[Loc] = Categorical.ratios(Seq[(Dist[Loc], Int)](
    randTrie(10, 4) -> 4,
    randRepeat -> 2,
    Pair(randTrie(8, 3), randTrie(8, 3), (a, b) => Loc.Union(Set(a, b))) -> 2,
    Pair(randTrie(10, 3), randTrie(5, 2), (a, b) => Loc.Subtraction(a, b)) -> 1,
    Pair(randRepeat, randTrie(6, 2), (a, b) => Loc.Compose(a, b)) -> 1,
  )).flatMap(identity)
  def argDist: Dist[SpaceValue] = argLoc.map(_.instantiate()).filter(sv => sv.paths.nonEmpty && sv.paths.size <= 28)

  // ---- programs drawn OVER a given argument space (the dependency) ----
  /** `sargs`/`pargs` are the program's free SPACE and PATH arguments (any number); leaves reference a
   *  random one.  Defaults to the single space input `x` and no path input (the original behaviour). */
  def genProg(arg: SpaceValue, maxDepth: Int,
              sargs: Vector[SpaceMention] = Vector(argM), pargs: Vector[PathRef] = Vector.empty): Dist[Space] = new Dist[Space]:
    private val paths = arg.paths.toVector
    private val firstItems = paths.flatMap(_.items.headOption).distinct
    private type Scope = Vector[(PathRef, SpaceMention)]   // enclosing iteration binders (head var, tail-set var)
    def sample(using rng: Random): Space = rec(maxDepth, Vector.empty)

    private def pick[T](v: Vector[T])(using rng: Random): T = v(rng.nextInt(v.length))
    private def someArg(using rng: Random): SpaceValue =                       // a non-empty subset of the argument
      val chosen = paths.filter(_ => rng.nextBoolean()); SpaceValue((if chosen.isEmpty then Vector(pick(paths)) else chosen).toSet)
    private def constP(p: PathValue): Path = Path.Constant(p)
    private def freshTag(using rng: Random): PathValue = PathValue(List(PathItem.Symbol("w" + rng.nextInt(4))))
    private def somePrefixLit(using rng: Random): Space =                       // 1-item prefixes drawn from the argument's heads
      val its = firstItems.filter(_ => rng.nextBoolean()); val use = if its.isEmpty then Vector(pick(firstItems)) else its
      Space.Literal(SpaceValue(use.map(it => PathValue(List(it))).toSet))

    // a leaf MAY reference any enclosing iteration binder — `Singleton(Path.Deref(v))` is a VARIABLE
    // path (`sP"v"`), a core building block; `Mention(t)` is the bound tail-set; `v ++ const` mixes them.
    private def leaf(scope: Scope)(using rng: Random): Space =
      val vars = if scope.isEmpty then Seq.empty else Seq("vsing" -> 4, "vment" -> 2, "vcat" -> 2)
      val pins = if pargs.isEmpty then Seq.empty else Seq("psing" -> 3, "pcat" -> 2)             // free PATH inputs
      Categorical.ratios(Seq("x" -> 4, "lit" -> 1, "csing" -> 1) ++ vars ++ pins).sample match
        case "x"     => Space.Mention(pick(sargs))                                               // a free SPACE input
        case "lit"   => Space.Literal(someArg)
        case "csing" => Space.Singleton(constP(pick(paths)))
        case "vsing" => Space.Singleton(Path.Deref(pick(scope)._1))                              // bound VARIABLE path
        case "vment" => Space.Mention(pick(scope)._2)                                            // bound tail-set
        case "vcat"  => Space.Singleton(Path.Concat(Path.Deref(pick(scope)._1), constP(pick(paths))))  // var ++ const
        case "psing" => Space.Singleton(Path.Deref(pick(pargs)))                                 // a free path input
        case _       => Space.Singleton(Path.Concat(Path.Deref(pick(pargs)), constP(pick(paths))))   // path-arg ++ const

    /** transform-by-iteration (the iteration analogue of the removed Space.Transformation): descend `k`
     *  levels with nested `iter`, binding the first k path items h0..h{k-1}, then emit a Singleton that
     *  recombines them in a permuted / projected order. */
    private def reorder(d: Int, scope: Scope)(using rng: Random): Space =
      val k = 1 + rng.nextInt(3)
      val hs = Vector.fill(k)(PathRef("h" + rng.nextInt(1000000)).known(1))
      val ts = Vector.fill(k)(SpaceMention("t" + rng.nextInt(1000000)))
      val tlen = 1 + rng.nextInt(k)
      val body: Space = Space.Singleton((0 until tlen).map(_ => (Path.Deref(hs(rng.nextInt(k))): Path)).reduceLeft(Path.Concat(_, _)))
      var node = body; var i = k - 1
      while i >= 0 do
        node = Space.Iteration(if i == 0 then rec(d - 1, scope) else Space.Mention(ts(i - 1)), hs(i), ts(i), node); i -= 1
      node

    // a binary op's SECOND operand: usually a full sub-program (so every term type can occur here too),
    // sometimes a dependency-anchored leaf that keeps the result overlapping the argument.  Not
    // homogeneous, but no longer pinned to a single type.
    private def side(d: Int, scope: Scope, anchor: => Space)(using rng: Random): Space =
      if rng.nextInt(5) < 3 then rec(d - 1, scope) else anchor
    // composition's right operand: same idea, but DEPTH-BOUNDED — composition is multiplicative in
    // size, so an unbounded right side would blow up evaluation.
    private def compRhs(d: Int, scope: Scope)(using rng: Random): Space =
      if rng.nextInt(5) < 3 then rec(math.min(d - 1, 2), scope) else Space.Singleton(constP(pick(paths)))

    private def rec(d: Int, scope: Scope)(using rng: Random): Space =
      if d <= 0 then leaf(scope)
      else Categorical.ratios(Seq(
        "leaf" -> 2, "union" -> 2, "inter" -> 2, "sub" -> 2, "wrap" -> 2, "unwrap" -> 2, "comp" -> 1,
        "restr" -> 2, "iter" -> 3, "tails" -> 1, "range" -> 1, "reorder" -> 1)).sample match
        case "leaf"  => leaf(scope)
        case "union" => Space.Union(rec(d - 1, scope), rec(d - 1, scope))
        case "inter" => Space.Intersection(rec(d - 1, scope), side(d, scope, Space.Literal(someArg)))            // overlaps the argument
        case "sub"   => Space.Subtraction(rec(d - 1, scope), side(d, scope, Space.Singleton(constP(pick(paths)))))
        case "wrap"  => Space.Wrap(rec(d - 1, scope), constP(freshTag))                         // tag every path
        case "unwrap"=> Space.Unwrap(rec(d - 1, scope), constP(PathValue(List(pick(firstItems)))))  // strip a real head
        case "comp"  => Space.Composition(rec(d - 1, scope), compRhs(d, scope))
        case "restr" => Space.Restriction(rec(d - 1, scope), side(d, scope, somePrefixLit))
        case "tails" => Space.TailsUnion(rec(d - 1, scope))
        case "range" => val lo = rng.nextInt(3); Space.Range(rec(d - 1, scope), lo, lo + 1 + rng.nextInt(3))
        case "reorder" => reorder(d, scope)
        case _ =>                                                                              // iteration: binds a fresh var, visible in the body
          val hpr = PathRef("h" + rng.nextInt(1000000)).known(1); val tv = SpaceMention("t" + rng.nextInt(1000000))
          Space.Iteration(rec(d - 1, scope), hpr, tv, rec(d - 1, scope :+ (hpr -> tv)))

  private def evalEx(p: Space, arg: SpaceValue): Example =
    Example(p, arg, eval(p)(using PathContextMap(Map.empty), SpaceContextMap(Map(argM -> arg)), PartialFunction.empty))

  /** The headline distribution: argument FIRST, then a program drawn over it, then its result — a
   *  genuinely dependent triple (`Dep`), filtered to "interesting" programs (uses the argument and
   *  does something non-trivial to it). */
  def example(maxDepth: Int = 3, maxResult: Int = 400): Dist[Example] =
    Dep(argDist, arg => genProg(arg, maxDepth).map(p => evalEx(p, arg)).filter(e =>
      e.result.paths.nonEmpty && e.result != e.arg && e.result.paths.size <= maxResult && Matching.freeMentions(e.program).contains(argM)))
end SpaceFuzzer
