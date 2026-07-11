object Fuzzer:
  import java.util.Random

  trait Dist[T]:
    def sample(using rng: Random): T

  inline def Uniform(inline low: Float, inline high: Float): Dist[Float] = rng ?=> rng.nextFloat(low, high)
  inline def Uniform(inline low: Double, inline high: Double): Dist[Double] = rng ?=> rng.nextDouble(low, high)
  inline def Uniform(inline low: Int, inline high: Int): Dist[Int] = rng ?=> rng.nextInt(low, high)
  inline def Uniform(inline low: Long, inline high: Long): Dist[Long] = rng ?=> rng.nextLong(low, high)

  case class Filtered[T](d: Dist[T], p: T => Boolean) extends Dist[T]:
    override def sample(using rng: Random): T =
      while true do
        val s = d.sample
        if p(s) then return s
      throw IllegalStateException()

  case class Mapped[T, S](d: Dist[T], f: T => S) extends Dist[S]:
    override def sample(using rng: Random): S = f(d.sample)

  case class Collected[T, S](d: Dist[T], pf: PartialFunction[T, S]) extends Dist[S]:
    override def sample(using rng: Random): S =
      while true do
        d.sample match
          case pf(s) => return s
      throw IllegalStateException()

  case class Pair[T0, T1, S](d0: Dist[T0], d1: Dist[T1], f: (T0, T1) => S) extends Dist[S]:
    override def sample(using rng: Random): S = f(d0.sample, d1.sample)

  case class Cond[X, Y, Z](dc: Dist[Boolean], dx: Dist[X], dy: Dist[Y], f: Either[X, Y] => Z) extends Dist[Z]:
    override def sample(using rng: Random): Z = f(Either.cond(dc.sample, dy.sample, dx.sample))

  case class Dep[X, Y](dx: Dist[X], fdy: X => Dist[Y]) extends Dist[Y]:
    override def sample(using rng: Random): Y = fdy(dx.sample).sample

  case class Concentrated[X, Y, A](dx: Dist[X], initial: A, fa: (A, X) => Either[A, Y]) extends Dist[Y]:
    override def sample(using rng: Random): Y =
      var a = initial
      while true do
        fa(a, dx.sample) match
          case Right(y) => return y
          case Left(a_) => a = a_
      throw IllegalStateException()

  case class Diluted[X, Y, A](dx: Dist[X], initial: X => (A, Y), squeeze: A => Option[(A, Y)]) extends Dist[Y]:
    override def sample(using rng: Random): Y = throw NotImplementedError()

  case class Degenerate[T](t: T) extends Dist[T]:
    override def sample(using rng: Random): T = t

  case class Categorical[T](di: Dist[Int], ts: Vector[T]) extends Dist[T]:
    override def sample(using rng: Random): T = ts(di.sample)
  object Categorical:
    def uniform[T](ts: Vector[T]): Categorical[T] = Categorical((rng: Random) ?=> rng.nextInt(ts.length), ts)
    /// Creates a categorical distribution where elements are chosen with probability proportional to their weights.
    def ratios[T](ep: IterableOnce[(T, Int)]): Categorical[T] =
      val elements_builder = Vector.newBuilder[T]
      val cdf_builder = Vector.newBuilder[Int]
      var sum = 0
      for (e, r) <- ep.iterator do
        elements_builder += e
        cdf_builder += sum
        sum += r
      val us = Uniform(0, sum)
      val cdf = cdf_builder.result()
      Categorical(Mapped(us, x => cdf.search(x) match {
        case Searching.Found(i) => i
        case Searching.InsertionPoint(i) => i - 1
      }), elements_builder.result())

  case class Repeated[T](dlength: Dist[Int], ditem: Dist[T]) extends Dist[Vector[T]]:
    override def sample(using rng: Random): Vector[T] =
      Vector.fill(dlength.sample)(ditem.sample)

  case class Sentinel[T](dsent: Dist[Option[T]]) extends Dist[Vector[T]]:
    override def sample(using rng: Random): Vector[T] =
      val b = Vector.newBuilder[T]
      while true do dsent.sample match
        case None => return b.result()
        case Some(t) => b += t
      throw IllegalStateException()
end Fuzzer

trait Loc:
  def is_path(segment: PathValue): Boolean
  def branches(segment: PathValue): Set[PathItem]
  def descend(segment: PathValue, branch: Int): Loc = this

  def instantiate(segment: PathValue = PathValue(Nil)): SpaceValue =
    val rec = branches(segment).flatMap(b => instantiate(PathValue(segment.items appended b)).paths)  
    if is_path(segment) then SpaceValue(rec.incl(segment))
    else SpaceValue(rec)

object Loc:
  case class Const(path: PathValue) extends Loc:
    def is_path(segment: PathValue): Boolean = segment == path
    def branches(segment: PathValue): Set[PathItem] = if segment.items.length < path.items.length then Set(path.items(segment.items.length)) else Set.empty

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
    def branches(segment: PathValue): Set[PathItem] = space.paths.collect { case e if (e.items.length > segment.items.length) && e.items.startsWith(segment.items)  => e.items(segment.items.length) }

  case class Union(locs: Set[Loc]) extends Loc:
    def is_path(segment: PathValue): Boolean = locs.exists(_.is_path(segment))
    def branches(segment: PathValue): Set[PathItem] = locs.map(_.branches(segment)).reduce(_ union _)

  case class Intersection(locs: Set[Loc]) extends Loc:
    def is_path(segment: PathValue): Boolean = locs.forall(_.is_path(segment))
    def branches(segment: PathValue): Set[PathItem] = locs.map(_.branches(segment)).reduce(_ intersect _)

  case class Subtraction(loc: Loc, neg: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && !neg.is_path(segment)
    def branches(segment: PathValue): Set[PathItem] = loc.branches(segment) removedAll neg.branches(segment)

  case class Restriction(loc: Loc, accepted: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && (0 to segment.items.length).exists(i =>
      accepted.is_path(PathValue(segment.items.take(i))))
    def branches(segment: PathValue): Set[PathItem] = if (0 to segment.items.length).exists(i =>
      accepted.is_path(PathValue(segment.items.take(i)))) then loc.branches(segment) else Set.empty

  case class Raffination(loc: Loc, unaccepted: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && !(0 to segment.items.length).exists(i =>
      unaccepted.is_path(PathValue(segment.items.take(i))))
    def branches(segment: PathValue): Set[PathItem] = if !(0 to segment.items.length).exists(i =>
      unaccepted.is_path(PathValue(segment.items.take(i)))) then loc.branches(segment) else Set.empty

  case class Compose(left: Loc, right: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = (0 to segment.items.length).exists(i =>
      val (l, r) = segment.items.splitAt(i)
      left.is_path(PathValue(l)) && right.is_path(PathValue(r)))
    def branches(segment: PathValue): Set[PathItem] =
      (0 to segment.items.length).filter(i =>
        left.is_path(PathValue(segment.items.take(i)))
      ).flatMap(i => right.branches(PathValue(segment.items.drop(i)))).toSet

  case class Dep(left: Loc, rightf: PathValue => Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = (0 to segment.items.length).exists(i =>
      val (l, r) = segment.items.splitAt(i)
      left.is_path(PathValue(l)) && rightf(PathValue(l)).is_path(PathValue(r)))
    def branches(segment: PathValue): Set[PathItem] =
      (0 to segment.items.length).filter(i =>
        left.is_path(PathValue(segment.items.take(i)))
      ).flatMap(i => rightf(PathValue(segment.items.take(i))).branches(PathValue(segment.items.drop(i)))).toSet


  def uop(src: Loc, pf: PathValue => PathValue) = Dep(src, p => Const(pf(p)))

  def int_to_int(f: Int => Int) = uop(Full((0 to 9).map(k => PathItem.Symbol(k.toString)).toSet),
    p => PathValue(f(p.items.map(_.show).mkString.toInt).toString.map(c => PathItem.Symbol(c.toString)).toList))

  def sqrt = int_to_int(i => Math.sqrt(i.toDouble).toInt)
end Loc
