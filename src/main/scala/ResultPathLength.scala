package morkl

import scala.collection.concurrent.TrieMap
import scala.collection.mutable

/** Symbolic bounds on the length of every path in a result space.
  * `Infinity` is both an unknown upper bound and the lower-bound identity for
  * the empty set; consequently the canonical empty interval is `[∞, 0]`.
  */
enum PathLengthExpr:
  case Const(value: BigInt)
  case PathLengthOf(path: Path)
  case MinimumLengthOf(space: Space)
  case MaximumLengthOf(space: Space)
  case Add(terms: Vector[PathLengthExpr])
  case Maximum(terms: Vector[PathLengthExpr])
  case Minimum(terms: Vector[PathLengthExpr])
  case PositiveDifference(left: PathLengthExpr, right: PathLengthExpr)
  case Z3Bound(problem: Z3PathLengthProblem, direction: Z3BoundDirection, baseline: PathLengthExpr)
  case Infinity

  /** Resolve only lengths propagated through annotations and syntax. This
    * never evaluates a path, space, grounded function, or routine call. */
  def annotatedValue: Option[BigInt] = this match
    case PathLengthExpr.Const(value) => Some(value)
    case PathLengthExpr.PathLengthOf(_) | PathLengthExpr.MinimumLengthOf(_) |
         PathLengthExpr.MaximumLengthOf(_) | PathLengthExpr.Infinity => None
    case PathLengthExpr.Add(terms) =>
      terms.foldLeft(Option(BigInt(0))) { (acc, term) =>
        for left <- acc; right <- term.annotatedValue yield left + right
      }
    case PathLengthExpr.Maximum(terms) =>
      if terms.exists(_.annotatedValue.isEmpty) then None else terms.flatMap(_.annotatedValue).maxOption
    case PathLengthExpr.Minimum(terms) =>
      val values = terms.map(_.annotatedValue)
      if values.contains(Some(BigInt(0))) then Some(BigInt(0))
      else if values.forall(_.nonEmpty) then values.flatten.minOption
      else None
    case PathLengthExpr.PositiveDifference(left, right) =>
      (left.annotatedValue, right.annotatedValue) match
        case (Some(l), Some(r)) => Some((l - r).max(BigInt(0)))
        case (Some(l), None) if l == 0 => Some(BigInt(0))
        case _ => None
    case PathLengthExpr.Z3Bound(problem, direction, baseline) =>
      val fallback = baseline.annotatedValue
      problem.solveAnnotated(direction) match
        case None => fallback
        case Some(None) =>
          direction match
            case Z3BoundDirection.Lower => None
            case Z3BoundDirection.Upper => fallback
        case Some(Some(refined)) =>
          direction match
            case Z3BoundDirection.Lower => fallback.map(_.max(refined))
            case Z3BoundDirection.Upper => Some(fallback.fold(refined)(_.min(refined)))

  /** Resolve a sound one-sided path-length bound from annotations only. */
  def annotatedBound(direction: Z3BoundDirection): Option[BigInt] =
    def lower(value: PathLengthExpr): BigInt = value match
      case PathLengthExpr.Const(n) => n
      case PathLengthExpr.PathLengthOf(_) | PathLengthExpr.MinimumLengthOf(_) |
           PathLengthExpr.MaximumLengthOf(_) | PathLengthExpr.Infinity => BigInt(0)
      case PathLengthExpr.Add(terms) => terms.map(lower).sum
      case PathLengthExpr.Maximum(terms) => terms.map(lower).maxOption.getOrElse(BigInt(0))
      case PathLengthExpr.Minimum(terms) => terms.map(lower).minOption.getOrElse(BigInt(0))
      case PathLengthExpr.PositiveDifference(left, right) =>
        upper(right).fold(BigInt(0))(r => (lower(left) - r).max(BigInt(0)))
      case value @ PathLengthExpr.Z3Bound(_, storedDirection, _) =>
        value.annotatedValue.orElse(z3Bound(value, storedDirection)).getOrElse(BigInt(0))
    def upper(value: PathLengthExpr): Option[BigInt] = value match
      case PathLengthExpr.Const(n) => Some(n)
      case PathLengthExpr.PathLengthOf(_) | PathLengthExpr.MinimumLengthOf(_) |
           PathLengthExpr.MaximumLengthOf(_) | PathLengthExpr.Infinity => None
      case PathLengthExpr.Add(terms) =>
        terms.foldLeft(Option(BigInt(0)))((sum, term) => for a <- sum; b <- upper(term) yield a + b)
      case PathLengthExpr.Maximum(terms) =>
        val values = terms.map(upper)
        if values.forall(_.nonEmpty) then values.flatten.maxOption else None
      case PathLengthExpr.Minimum(terms) => terms.flatMap(upper).minOption
      case PathLengthExpr.PositiveDifference(left, _) => upper(left)
      case value @ PathLengthExpr.Z3Bound(_, storedDirection, _) =>
        value.annotatedValue.orElse(z3Bound(value, storedDirection))
    def z3Bound(value: PathLengthExpr, storedDirection: Z3BoundDirection): Option[BigInt] = value match
      case PathLengthExpr.Z3Bound(problem, _, baseline) =>
        val base = storedDirection match
          case Z3BoundDirection.Lower => Some(lower(baseline))
          case Z3BoundDirection.Upper => upper(baseline)
        problem.solveAnnotated(storedDirection) match
          case None => base
          case Some(None) => if storedDirection == Z3BoundDirection.Upper then base else None
          case Some(Some(refined)) => storedDirection match
            case Z3BoundDirection.Lower => Some(base.getOrElse(BigInt(0)).max(refined))
            case Z3BoundDirection.Upper => Some(base.fold(refined)(_.min(refined)))
      case _ => None
    direction match
      case Z3BoundDirection.Lower => Some(lower(this))
      case Z3BoundDirection.Upper => upper(this)

  def show: String = this match
    case PathLengthExpr.Const(value) => value.toString
    case PathLengthExpr.PathLengthOf(path) => s"len(${path.show})"
    case PathLengthExpr.MinimumLengthOf(space) => s"minLen(${space.show})"
    case PathLengthExpr.MaximumLengthOf(space) => s"maxLen(${space.show})"
    case PathLengthExpr.Add(terms) => terms.map(_.show).mkString("(", " + ", ")")
    case PathLengthExpr.Maximum(terms) => terms.map(_.show).mkString("max(", ", ", ")")
    case PathLengthExpr.Minimum(terms) => terms.map(_.show).mkString("min(", ", ", ")")
    case PathLengthExpr.PositiveDifference(left, right) => s"relu(${left.show} - ${right.show})"
    case PathLengthExpr.Z3Bound(problem, direction, baseline) =>
      s"z3${direction.toString.toLowerCase}(${problem.show}; fallback=${baseline.show})"
    case PathLengthExpr.Infinity => "∞"

  def evaluate(using
    pc: PathContext = PathContext.emptyMap,
    sc: SpaceContext = SpaceContextMap(Map.empty),
    rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  ): Option[BigInt] = this match
    case PathLengthExpr.Const(value) => Some(value)
    case PathLengthExpr.PathLengthOf(path) => Some(BigInt(eval(Space.Singleton(path)).paths.head.items.length))
    case PathLengthExpr.MinimumLengthOf(space) =>
      eval(space).paths.iterator.map(path => BigInt(path.items.length)).minOption
    case PathLengthExpr.MaximumLengthOf(space) =>
      Some(eval(space).paths.iterator.map(path => BigInt(path.items.length)).maxOption.getOrElse(BigInt(0)))
    case PathLengthExpr.Add(terms) =>
      terms.foldLeft(Option(BigInt(0))) { (acc, term) =>
        for left <- acc; right <- term.evaluate yield left + right
      }
    case PathLengthExpr.Maximum(terms) =>
      if terms.exists(_.evaluate.isEmpty) then None
      else terms.flatMap(_.evaluate).maxOption
    case PathLengthExpr.Minimum(terms) =>
      val finite = terms.flatMap(_.evaluate)
      if finite.nonEmpty then finite.minOption else None
    case PathLengthExpr.PositiveDifference(left, right) =>
      (left.evaluate, right.evaluate) match
        case (Some(l), Some(r)) => Some((l - r).max(BigInt(0)))
        case (None, Some(_)) => None
        case (Some(_), None) => Some(BigInt(0))
        case (None, None) => None
    case PathLengthExpr.Z3Bound(problem, direction, baseline) =>
      val fallback = baseline.evaluate
      problem.solve(direction) match
        case None => fallback
        case Some(None) =>
          direction match
            case Z3BoundDirection.Lower => None
            case Z3BoundDirection.Upper => fallback
        case Some(Some(refined)) =>
          direction match
            case Z3BoundDirection.Lower =>
              fallback match
                case Some(value) => Some(value.max(refined))
                case None => None
            case Z3BoundDirection.Upper =>
              fallback match
                case Some(value) => Some(value.min(refined))
                case None => Some(refined)
    case PathLengthExpr.Infinity => None

object PathLengthExpr:
  val Zero: PathLengthExpr = PathLengthExpr.Const(0)
  val One: PathLengthExpr = PathLengthExpr.Const(1)

  def const(value: BigInt): PathLengthExpr =
    require(value >= 0, s"path length must be non-negative, got $value")
    PathLengthExpr.Const(value)

  def add(values: PathLengthExpr*): PathLengthExpr =
    val terms = values.iterator.flatMap {
      case PathLengthExpr.Const(value) if value == 0 => Vector.empty
      case PathLengthExpr.Add(nested) => nested
      case other => Vector(other)
    }.toVector
    if terms.contains(PathLengthExpr.Infinity) then PathLengthExpr.Infinity
    else terms match
      case Vector() => Zero
      case Vector(value) => value
      case result if result.forall(_.isInstanceOf[PathLengthExpr.Const]) =>
        const(result.collect { case PathLengthExpr.Const(value) => value }.sum)
      case result => PathLengthExpr.Add(result)

  def maximum(values: PathLengthExpr*): PathLengthExpr =
    val terms = values.iterator.flatMap {
      case PathLengthExpr.Maximum(nested) => nested
      case other => Vector(other)
    }.toVector.distinct
    if terms.contains(PathLengthExpr.Infinity) then PathLengthExpr.Infinity
    else terms match
      case Vector() => Zero
      case Vector(value) => value
      case result if result.forall(_.isInstanceOf[PathLengthExpr.Const]) =>
        const(result.collect { case PathLengthExpr.Const(value) => value }.max)
      case result => PathLengthExpr.Maximum(result)

  def minimum(values: PathLengthExpr*): PathLengthExpr =
    val terms = values.iterator.flatMap {
      case PathLengthExpr.Infinity => Vector.empty
      case PathLengthExpr.Minimum(nested) => nested
      case other => Vector(other)
    }.toVector.distinct
    terms match
      case Vector() => PathLengthExpr.Infinity
      case Vector(value) => value
      case result if result.forall(_.isInstanceOf[PathLengthExpr.Const]) =>
        const(result.collect { case PathLengthExpr.Const(value) => value }.min)
      case result => PathLengthExpr.Minimum(result)

  def positiveDifference(left: PathLengthExpr, right: PathLengthExpr): PathLengthExpr = (left, right) match
    case (PathLengthExpr.Const(l), PathLengthExpr.Const(r)) => const((l - r).max(BigInt(0)))
    case (PathLengthExpr.Const(zero), _) if zero == 0 => Zero
    case (_, PathLengthExpr.Const(zero)) if zero == 0 => left
    case (PathLengthExpr.Infinity, PathLengthExpr.Infinity) => PathLengthExpr.Infinity
    case (PathLengthExpr.Infinity, _) => PathLengthExpr.Infinity
    case (_, PathLengthExpr.Infinity) => Zero
    case _ => PathLengthExpr.PositiveDifference(left, right)

case class PathLengthEstimate(lower: PathLengthExpr, upper: PathLengthExpr):
  def exact: Boolean = lower == upper
  def show: String = s"minPathLen≥${lower.show}, maxPathLen≤${upper.show}"

object PathLengthEstimate:
  def exact(value: PathLengthExpr): PathLengthEstimate = PathLengthEstimate(value, value)
  val empty: PathLengthEstimate = PathLengthEstimate(PathLengthExpr.Infinity, PathLengthExpr.Zero)
  val unknown: PathLengthEstimate = PathLengthEstimate(PathLengthExpr.Zero, PathLengthExpr.Infinity)

/** Full compositional path-length analysis. Boolean set algebra is refined by
  * [[Z3ResultPathLength]], while all nested non-Boolean constructs recursively
  * feed their own refined bounds into their parent.
  */
object ResultPathLength:
  def estimate(
    space: Space,
    assumptions: Map[SpaceMention, PathLengthEstimate] = Map.empty,
    pathAssumptions: Map[PathRef, PathLengthEstimate] = Map.empty,
    sizeAssumptions: Map[SpaceMention, ResultSizeEstimate] = Map.empty
  ): PathLengthEstimate =
    analyze(space, assumptions, pathAssumptions, sizeAssumptions, Set.empty, Set.empty, refineBoolean = true)

  def estimateBaseline(
    space: Space,
    assumptions: Map[SpaceMention, PathLengthEstimate] = Map.empty,
    pathAssumptions: Map[PathRef, PathLengthEstimate] = Map.empty,
    sizeAssumptions: Map[SpaceMention, ResultSizeEstimate] = Map.empty
  ): PathLengthEstimate =
    analyze(space, assumptions, pathAssumptions, sizeAssumptions, Set.empty, Set.empty, refineBoolean = false)

  private def dependsOnBound(space: Space, spaces: Set[SpaceMention], paths: Set[PathRef]): Boolean =
    val (spaceUses, pathUses) = collect(space)(
      { case Space.Mention(mention) if spaces(mention) => () },
      { case Path.Deref(ref) if paths(ref) => () }
    )
    spaceUses.nonEmpty || pathUses.nonEmpty

  private def path(
    value: Path,
    assumptions: Map[SpaceMention, PathLengthEstimate],
    pathAssumptions: Map[PathRef, PathLengthEstimate],
    sizeAssumptions: Map[SpaceMention, ResultSizeEstimate],
    boundSpaces: Set[SpaceMention],
    boundPaths: Set[PathRef],
    refineBoolean: Boolean
  ): PathLengthEstimate = value match
    case Path.Deref(ref) =>
      pathAssumptions.getOrElse(ref,
        if ref.lengthHint >= 0 then PathLengthEstimate.exact(PathLengthExpr.const(ref.lengthHint))
        else PathLengthEstimate.exact(PathLengthExpr.PathLengthOf(value)))
    case Path.Constant(PathValue(items)) => PathLengthEstimate.exact(PathLengthExpr.const(items.length))
    case Path.Concat(left, right) =>
      val l = path(left, assumptions, pathAssumptions, sizeAssumptions, boundSpaces, boundPaths, refineBoolean)
      val r = path(right, assumptions, pathAssumptions, sizeAssumptions, boundSpaces, boundPaths, refineBoolean)
      PathLengthEstimate(PathLengthExpr.add(l.lower, r.lower), PathLengthExpr.add(l.upper, r.upper))
    case Path.GroundedPP(_, _) | Path.GroundedSP(_, _) =>
      val wrapped = Space.Singleton(value)
      if dependsOnBound(wrapped, boundSpaces, boundPaths) then PathLengthEstimate.unknown
      else PathLengthEstimate.exact(PathLengthExpr.PathLengthOf(value))

  private def opaque(space: Space, boundSpaces: Set[SpaceMention], boundPaths: Set[PathRef]): PathLengthEstimate =
    if dependsOnBound(space, boundSpaces, boundPaths) then PathLengthEstimate.unknown
    else PathLengthEstimate(PathLengthExpr.MinimumLengthOf(space), PathLengthExpr.MaximumLengthOf(space))

  private def analyze(
    space: Space,
    assumptions: Map[SpaceMention, PathLengthEstimate],
    pathAssumptions: Map[PathRef, PathLengthEstimate],
    sizeAssumptions: Map[SpaceMention, ResultSizeEstimate],
    boundSpaces: Set[SpaceMention],
    boundPaths: Set[PathRef],
    refineBoolean: Boolean
  ): PathLengthEstimate =
    def rec(next: Space): PathLengthEstimate =
      analyze(next, assumptions, pathAssumptions, sizeAssumptions, boundSpaces, boundPaths, refineBoolean)
    def booleanResult(fallback: PathLengthEstimate): PathLengthEstimate =
      if refineBoolean then Z3ResultPathLength.refine(space, fallback, rec, sizeAssumptions)
      else fallback

    space match
      case Space.Empty => PathLengthEstimate.empty
      case Space.Mention(variable) =>
        assumptions.getOrElse(variable,
          PathLengthEstimate(PathLengthExpr.MinimumLengthOf(space), PathLengthExpr.MaximumLengthOf(space)))
      case Space.Call(_, _, _) => opaque(space, boundSpaces, boundPaths)
      case Space.Singleton(value) =>
        path(value, assumptions, pathAssumptions, sizeAssumptions, boundSpaces, boundPaths, refineBoolean)
      case Space.Literal(SpaceValue(paths)) =>
        if paths.isEmpty then PathLengthEstimate.empty
        else
          val lengths = paths.iterator.map(_.items.length).toVector
          PathLengthEstimate(PathLengthExpr.const(lengths.min), PathLengthExpr.const(lengths.max))
      case Space.Union(left, right) =>
        val l = rec(left)
        val r = rec(right)
        booleanResult(PathLengthEstimate(
          PathLengthExpr.minimum(l.lower, r.lower),
          PathLengthExpr.maximum(l.upper, r.upper)
        ))
      case Space.Intersection(left, right) =>
        val l = rec(left)
        val r = rec(right)
        booleanResult(PathLengthEstimate(
          PathLengthExpr.maximum(l.lower, r.lower),
          PathLengthExpr.minimum(l.upper, r.upper)
        ))
      case Space.Subtraction(left, _) =>
        val l = rec(left)
        booleanResult(l)
      case Space.Restriction(left, prefixes) =>
        val l = rec(left)
        val p = rec(prefixes)
        PathLengthEstimate(PathLengthExpr.maximum(l.lower, p.lower), l.upper)
      case Space.Raffination(left, _) => rec(left)
      case Space.Composition(left, right) =>
        val l = rec(left)
        val r = rec(right)
        PathLengthEstimate(PathLengthExpr.add(l.lower, r.lower), PathLengthExpr.add(l.upper, r.upper))
      case Space.Iteration(src, symbol, rest, body) =>
        val sourceLength = rec(src)
        val sourceSize = ResultSpaceSize.estimate(src, sizeAssumptions)
        val tailLength = PathLengthEstimate(
          PathLengthExpr.positiveDifference(sourceLength.lower, PathLengthExpr.One),
          PathLengthExpr.positiveDifference(sourceLength.upper, PathLengthExpr.One)
        )
        val tailSize =
          if rest.sizeHint >= 0 then ResultSizeEstimate.exact(SizeExpr.const(rest.sizeHint))
          else ResultSizeEstimate(sourceSize.upper, SizeExpr.One)
        analyze(
          body,
          assumptions.updated(rest, tailLength),
          pathAssumptions.updated(symbol, PathLengthEstimate.exact(PathLengthExpr.One)),
          sizeAssumptions.updated(rest, tailSize),
          boundSpaces + rest,
          boundPaths + symbol,
          refineBoolean
        )
      case Space.Fold(src, initial, acc, symbol, rest, body, update) =>
        val sourceLength = rec(src)
        val sourceSize = ResultSpaceSize.estimate(src, sizeAssumptions)
        val initialLength = path(initial, assumptions, pathAssumptions, sizeAssumptions, boundSpaces, boundPaths, refineBoolean)
        val updateProbe = path(
          update,
          assumptions,
          pathAssumptions.updated(acc, initialLength).updated(symbol, PathLengthEstimate.exact(PathLengthExpr.One)),
          sizeAssumptions,
          boundSpaces + rest,
          boundPaths ++ Set(acc, symbol),
          refineBoolean
        )
        val accumulatorLength =
          if initialLength == updateProbe then initialLength
          else if acc.lengthHint >= 0 then PathLengthEstimate.exact(PathLengthExpr.const(acc.lengthHint))
          else PathLengthEstimate.unknown
        val tailLength = PathLengthEstimate(
          PathLengthExpr.positiveDifference(sourceLength.lower, PathLengthExpr.One),
          PathLengthExpr.positiveDifference(sourceLength.upper, PathLengthExpr.One)
        )
        val tailSize =
          if rest.sizeHint >= 0 then ResultSizeEstimate.exact(SizeExpr.const(rest.sizeHint))
          else ResultSizeEstimate(sourceSize.upper, SizeExpr.One)
        analyze(
          body,
          assumptions.updated(rest, tailLength),
          pathAssumptions.updated(acc, accumulatorLength).updated(symbol, PathLengthEstimate.exact(PathLengthExpr.One)),
          sizeAssumptions.updated(rest, tailSize),
          boundSpaces + rest,
          boundPaths ++ Set(acc, symbol),
          refineBoolean
        )
      case Space.Fixpoint(initial, variable, step) =>
        val base = rec(initial)
        step match
          case Space.Mention(mention) if mention == variable => base
          case _ if !Matching.freeMentions(step).contains(variable) =>
            val next = rec(step)
            PathLengthEstimate(
              PathLengthExpr.minimum(base.lower, next.lower),
              PathLengthExpr.maximum(base.upper, next.upper)
            )
          case _ => PathLengthEstimate(PathLengthExpr.Zero, PathLengthExpr.Infinity)
      case Space.Wrap(src, prefix) =>
        val source = rec(src)
        val prefixLength = path(prefix, assumptions, pathAssumptions, sizeAssumptions, boundSpaces, boundPaths, refineBoolean)
        PathLengthEstimate(
          PathLengthExpr.add(prefixLength.lower, source.lower),
          PathLengthExpr.add(prefixLength.upper, source.upper)
        )
      case Space.Unwrap(src, prefix) =>
        val source = rec(src)
        val prefixLength = path(prefix, assumptions, pathAssumptions, sizeAssumptions, boundSpaces, boundPaths, refineBoolean)
        PathLengthEstimate(
          PathLengthExpr.positiveDifference(source.lower, prefixLength.upper),
          PathLengthExpr.positiveDifference(source.upper, prefixLength.lower)
        )
      case Space.TailsUnion(src) =>
        val source = rec(src)
        PathLengthEstimate(
          PathLengthExpr.positiveDifference(source.lower, PathLengthExpr.One),
          PathLengthExpr.positiveDifference(source.upper, PathLengthExpr.One)
        )
      case Space.TailsIntersection(src) =>
        val source = rec(src)
        PathLengthEstimate(
          PathLengthExpr.positiveDifference(source.lower, PathLengthExpr.One),
          PathLengthExpr.positiveDifference(source.upper, PathLengthExpr.One)
        )
      case Space.PrefixClosure(src) =>
        val source = rec(src)
        PathLengthEstimate(PathLengthExpr.One, source.upper)
      case Space.SuffixClosure(src) =>
        val source = rec(src)
        PathLengthEstimate(PathLengthExpr.One, source.upper)
      case Space.TailsClosure(src) =>
        val source = rec(src)
        PathLengthEstimate(PathLengthExpr.Zero, source.upper)
      case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => opaque(space, boundSpaces, boundPaths)
      case Space.Range(src, _, _) => rec(src)

case class Z3PathLengthProblem(
  formula: Z3SetFormula,
  lengths: Vector[PathLengthEstimate],
  cardinalities: Vector[ResultSizeEstimate],
  relations: Vector[Z3AtomRelation]
):
  def show: String = s"${formula.render}; atoms=${lengths.size}"

  /** `None` means solver unavailable; `Some(None)` means infinity. */
  def solve(direction: Z3BoundDirection)(using
    pc: PathContext,
    sc: SpaceContext,
    rc: PartialFunction[RoutinePtr, Routine]
  ): Option[Option[BigInt]] =
    def safelyLength(expression: PathLengthExpr): Option[BigInt] =
      try expression.evaluate
      catch case _: NoSuchElementException => None
    def safelySize(expression: SizeExpr): Option[BigInt] =
      try expression.evaluate
      catch case _: NoSuchElementException => None
    val lengthBounds = lengths.map(length => safelyLength(length.lower) -> safelyLength(length.upper))
    val sizeBounds = cardinalities.map(size => safelySize(size.lower) -> safelySize(size.upper))
    Z3PathLengthSolver.solve(formula, lengthBounds, sizeBounds, relations, direction)

  /** Solver entry using only abstract annotations; opaque atoms are unknown. */
  def solveAnnotated(direction: Z3BoundDirection): Option[Option[BigInt]] =
    val lengthBounds = lengths.map(length =>
      length.lower.annotatedBound(Z3BoundDirection.Lower) -> length.upper.annotatedBound(Z3BoundDirection.Upper))
    val sizeBounds = cardinalities.map(size =>
      size.lower.annotatedBound(Z3BoundDirection.Lower) -> size.upper.annotatedBound(Z3BoundDirection.Upper))
    Z3PathLengthSolver.solve(formula, lengthBounds, sizeBounds, relations, direction)

private[morkl] object Z3PathLengthSolver:
  private val cache = TrieMap.empty[String, Set[Int]]

  private def sum(values: Iterable[String]): String =
    values.toVector match
      case Vector() => "0"
      case Vector(value) => value
      case terms => terms.mkString("(+ ", " ", ")")

  private def status(output: String, marker: String): Option[String] =
    output.split(marker, 2).lift(1).flatMap(_.linesIterator.map(_.trim)
      .find(line => line == "sat" || line == "unsat" || line == "unknown"))

  private[morkl] def parsePossibleMasks(output: String, relevant: IndexedSeq[Int]): Option[Set[Int]] =
    if Z3Executable.reportSolverUnknown(output, "path-length atom feasibility") then None
    else
      val statuses = relevant.map(mask => mask -> status(output, s"MASK_$mask"))
      Option.when(statuses.forall(_._2.nonEmpty))(
        statuses.collect { case (mask, Some("sat")) => mask }.toSet
      )

  private def possibleMasks(
    formula: Z3SetFormula,
    bounds: Vector[(Option[BigInt], Option[BigInt])],
    relations: Vector[Z3AtomRelation]
  ): Option[Set[Int]] =
    val atomCount = bounds.size
    if atomCount == 0 then return Some(Set.empty)
    if atomCount >= 20 then return None
    val masks = 1 until (1 << atomCount)
    val relevant = masks.filter(formula.contains)
    val declarations = masks.map(mask => s"(declare-const r$mask Int)\n(assert (>= r$mask 0))").mkString("\n")
    val constraints = bounds.indices.flatMap { atom =>
      val cardinality = sum(masks.iterator.filter(mask => (mask & (1 << atom)) != 0).map(mask => s"r$mask").toVector)
      val (lower, upper) = bounds(atom)
      lower.map(value => s"(assert (>= $cardinality $value))").toVector ++
        upper.map(value => s"(assert (<= $cardinality $value))").toVector
    }.mkString("\n")
    val relationConstraints = relations.flatMap {
      case Z3AtomRelation.Subset(left, right) =>
        masks.iterator.filter(mask => (mask & (1 << left)) != 0 && (mask & (1 << right)) == 0)
          .map(mask => s"(assert (= r$mask 0))").toVector
      case Z3AtomRelation.Disjoint(left, right) =>
        masks.iterator.filter(mask => (mask & (1 << left)) != 0 && (mask & (1 << right)) != 0)
          .map(mask => s"(assert (= r$mask 0))").toVector
    }.distinct.mkString("\n")
    val checks = relevant.map { mask =>
      s"""(echo "MASK_$mask")
         |(push)
         |(assert (> r$mask 0))
         |(check-sat)
         |(pop)
         |""".stripMargin
    }.mkString
    val script =
      s"""${Z3Executable.timeoutOption}(set-logic QF_LIA)
         |$declarations
         |$constraints
         |$relationConstraints
         |$checks
         |""".stripMargin
    Z3Executable.run(script).flatMap(parsePossibleMasks(_, relevant))

  def solve(
    formula: Z3SetFormula,
    lengthBounds: Vector[(Option[BigInt], Option[BigInt])],
    sizeBounds: Vector[(Option[BigInt], Option[BigInt])],
    relations: Vector[Z3AtomRelation],
    direction: Z3BoundDirection
  ): Option[Option[BigInt]] =
    if lengthBounds.size != sizeBounds.size then None
    else
      val key = formula.render +
        sizeBounds.map { case (lower, upper) => s":s${lower.getOrElse("_")}:${upper.getOrElse("_")}" }.mkString +
        relations.map(relation => s":${relation.render}").mkString
      val possible = cache.get(key).orElse {
        val computed = possibleMasks(formula, sizeBounds, relations)
        computed.foreach(result => cache.putIfAbsent(key, result))
        computed
      }
      possible.map { possible =>
        val candidates = possible.flatMap { mask =>
          val members = lengthBounds.indices.filter(index => (mask & (1 << index)) != 0)
          val lowers = members.map(lengthBounds(_)._1)
          val uppers = members.map(lengthBounds(_)._2)
          val lower = if lowers.forall(_.nonEmpty) then Some(lowers.flatten.max) else None
          val upper = if uppers.forall(_.nonEmpty) then Some(uppers.flatten.min) else None
          Option.when(lower.forall(l => upper.forall(l <= _)))(lower -> upper)
        }
        if candidates.isEmpty then
          direction match
            case Z3BoundDirection.Lower => None
            case Z3BoundDirection.Upper => Some(BigInt(0))
        else direction match
          case Z3BoundDirection.Lower =>
            val values = candidates.flatMap(_._1)
            if values.size == candidates.size then Some(values.min) else Some(BigInt(0))
          case Z3BoundDirection.Upper =>
            val values = candidates.flatMap(_._2)
            if values.size == candidates.size then Some(values.max) else None
      }

object Z3ResultPathLength:
  private val maxAtoms = Option(System.getProperty("morkl.z3.maxPathLengthAtoms"))
    .flatMap(_.toIntOption).getOrElse(8).max(1).min(16)

  private case class Encoding(formula: Z3SetFormula, atoms: Vector[Space], relations: Vector[Z3AtomRelation])

  private def staticPaths(space: Space): Option[Set[PathValue]] = space match
    case Space.Empty => Some(Set.empty)
    case Space.Singleton(Path.Constant(value)) => Some(Set(value))
    case Space.Literal(value) => Some(value.paths)
    case Space.Union(left, right) => for l <- staticPaths(left); r <- staticPaths(right) yield l union r
    case Space.Intersection(left, right) => for l <- staticPaths(left); r <- staticPaths(right) yield l intersect r
    case Space.Subtraction(left, right) => for l <- staticPaths(left); r <- staticPaths(right) yield l diff r
    case _ => None

  private def subset(left: Space, right: Space, fuel: Int = 64): Boolean =
    if fuel <= 0 then false
    else if left == Space.Empty || left == right then true
    else (staticPaths(left), staticPaths(right)) match
      case (Some(l), Some(r)) => l.subsetOf(r)
      case _ => left match
        case Space.Union(a, b) => subset(a, right, fuel - 1) && subset(b, right, fuel - 1)
        case Space.Intersection(a, b) => subset(a, right, fuel - 1) || subset(b, right, fuel - 1)
        case Space.Subtraction(a, _) => subset(a, right, fuel - 1)
        case Space.Restriction(a, _) => subset(a, right, fuel - 1)
        case Space.Raffination(a, _) => subset(a, right, fuel - 1)
        case Space.Range(a, _, _) => subset(a, right, fuel - 1)
        case _ => right match
          case Space.Union(a, b) => subset(left, a, fuel - 1) || subset(left, b, fuel - 1)
          case Space.Intersection(a, b) => subset(left, a, fuel - 1) && subset(left, b, fuel - 1)
          case _ => false

  private def disjoint(left: Space, right: Space, fuel: Int = 64): Boolean =
    if fuel <= 0 then false
    else (staticPaths(left), staticPaths(right)) match
      case (Some(l), Some(r)) => l.intersect(r).isEmpty
      case _ => (left, right) match
        case (Space.Empty, _) | (_, Space.Empty) => true
        case (Space.Union(a, b), other) => disjoint(a, other, fuel - 1) && disjoint(b, other, fuel - 1)
        case (other, Space.Union(a, b)) => disjoint(other, a, fuel - 1) && disjoint(other, b, fuel - 1)
        case (Space.Intersection(a, b), other) => disjoint(a, other, fuel - 1) || disjoint(b, other, fuel - 1)
        case (other, Space.Intersection(a, b)) => disjoint(other, a, fuel - 1) || disjoint(other, b, fuel - 1)
        case (Space.Subtraction(_, removed), other) if subset(other, removed, fuel - 1) => true
        case (other, Space.Subtraction(_, removed)) if subset(other, removed, fuel - 1) => true
        case _ => false

  private def encode(space: Space): Option[Encoding] =
    val atomIds = mutable.LinkedHashMap.empty[Space, Int]
    var overflow = false
    def atom(value: Space): Z3SetFormula =
      atomIds.get(value) match
        case Some(index) => Z3SetFormula.Atom(index)
        case None if atomIds.size < maxAtoms =>
          val index = atomIds.size
          atomIds(value) = index
          Z3SetFormula.Atom(index)
        case None =>
          overflow = true
          Z3SetFormula.False
    def rec(value: Space): Z3SetFormula =
      if overflow then Z3SetFormula.False
      else value match
        case Space.Empty => Z3SetFormula.False
        case Space.Union(left, right) =>
          val l = rec(left)
          Z3SetFormula.Or(l, rec(right))
        case Space.Intersection(left, right) =>
          val l = rec(left)
          Z3SetFormula.And(l, rec(right))
        case Space.Subtraction(left, right) =>
          val l = rec(left)
          Z3SetFormula.And(l, Z3SetFormula.Not(rec(right)))
        case other => atom(other)
    val formula = rec(space)
    Option.unless(overflow) {
      val atoms = atomIds.keys.toVector
      val relations = (for
        left <- atoms.indices
        right <- (left + 1) until atoms.size
        relation <-
          if disjoint(atoms(left), atoms(right)) then Vector(Z3AtomRelation.Disjoint(left, right))
          else Vector(
            Option.when(subset(atoms(left), atoms(right)))(Z3AtomRelation.Subset(left, right)),
            Option.when(subset(atoms(right), atoms(left)))(Z3AtomRelation.Subset(right, left))
          ).flatten
      yield relation).toVector
      Encoding(formula, atoms, relations)
    }

  def refine(
    space: Space,
    fallback: PathLengthEstimate,
    atomLength: Space => PathLengthEstimate,
    sizeAssumptions: Map[SpaceMention, ResultSizeEstimate]
  ): PathLengthEstimate =
    encode(space) match
      case None => fallback
      case Some(encoding) if encoding.atoms.isEmpty => PathLengthEstimate.empty
      case Some(encoding) =>
        val lengths = encoding.atoms.map(atomLength)
        val cardinalities = encoding.atoms.map(ResultSpaceSize.estimate(_, sizeAssumptions))
        val problem = Z3PathLengthProblem(encoding.formula, lengths, cardinalities, encoding.relations)
        PathLengthEstimate(
          PathLengthExpr.Z3Bound(problem, Z3BoundDirection.Lower, fallback.lower),
          PathLengthExpr.Z3Bound(problem, Z3BoundDirection.Upper, fallback.upper)
        )
