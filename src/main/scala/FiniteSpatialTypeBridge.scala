package morkl

/** Canonical finite bridge between the three-element semantic set-interval
  * domain and the production [[SpatialType]] representation.
  *
  * The bridge is deliberately small and fail-closed. It is shared by the
  * executable lattice regression and the generated bounded SMT theorem, so the
  * proof generator observes the live production representation rather than a
  * test-only copy. This is not a general decoder for arbitrary spatial types.
  */
object FiniteSpatialTypeBridge:
  val Width: Int = 3
  val FullMask: Int = (1 << Width) - 1

  /** Bottom is distinct from the non-bottom empty interval. */
  case class Interval(isBottom: Boolean, mustMask: Int, mayMask: Int):
    require((mustMask & ~FullMask) == 0,
      s"must mask is outside the three-bit universe: $mustMask")
    require((mayMask & ~FullMask) == 0,
      s"may mask is outside the three-bit universe: $mayMask")
    require((mustMask & ~mayMask) == 0,
      s"must mask $mustMask is not a subset of may mask $mayMask")
    require(!isBottom || (mustMask == 0 && mayMask == 0),
      "bottom must use the canonical zero masks")

  /** Deterministic bottom-plus-interval enumeration: 1 + 3^3 = 28 values. */
  val domain: Vector[Interval] =
    val intervals = (0 to FullMask).iterator.flatMap { mayMask =>
      (0 to FullMask).iterator.collect {
        case mustMask if (mustMask & ~mayMask) == 0 =>
          Interval(isBottom = false, mustMask, mayMask)
      }
    }.toVector
    val result = Interval(isBottom = true, 0, 0) +: intervals
    require(result.size == 28, s"expected 28 finite spatial values, got ${result.size}")
    require(result.distinct.size == result.size,
      "finite spatial domain contains duplicate values")
    result

  /** Embed one set interval into production: each possible member is an exact
    * singleton-path stratum, with `[1,1]` for a required member and `[0,1]`
    * for a may-only member.
    */
  def embed(value: Interval): SpatialType =
    if value.isBottom then SpatialType.bottom
    else SpatialType.fromStrata((0 until Width).iterator.collect {
      case item if (value.mayMask & (1 << item)) != 0 =>
        SpatialStratum(
          PathLengthEstimate.exact(PathLengthExpr.One),
          ResultSizeEstimate(
            SizeExpr.One,
            if (value.mustMask & (1 << item)) != 0 then SizeExpr.One else SizeExpr.Zero,
          ),
          Some(SpatialPattern.constant(PathValue(List(PathItem(item.toString))))),
        )
    }.toVector)

  /** Decode only the canonical three-path quotient. Unexpected patterns,
    * symbolic/non-unit bounds, duplicate members, scalar/length disagreement,
    * cost, and shape overrides are errors rather than approximations.
    */
  def decode(value: SpatialType): Either[String, Interval] =
    if value.isBottom then
      if value == SpatialType.bottom then Right(Interval(isBottom = true, 0, 0))
      else Left(s"noncanonical bottom value: ${value.show}")
    else if value.shapeOverride.nonEmpty then
      Left(s"unexpected shape override: ${value.show}")
    else if value.cost != SpatialCostEstimate.zero then
      Left(s"unexpected nonzero cost: ${value.show}")
    else
      var mustMask = 0
      var mayMask = 0
      var index = 0
      while index < value.strata.size do
        val stratum = value.strata(index)
        if stratum.length != PathLengthEstimate.exact(PathLengthExpr.One) then
          return Left(s"stratum $index does not have exact singleton length: ${stratum.show}")
        val pattern = stratum.pattern match
          case Some(result) => result
          case None => return Left(s"stratum $index has no exact pattern: ${stratum.show}")
        val path = pattern.constantValue match
          case Some(result) => result
          case None => return Left(s"stratum $index has a nonconstant pattern: ${stratum.show}")
        if path.items.size != 1 then
          return Left(s"stratum $index is not a singleton path: ${stratum.show}")
        val item = path.items.head.show.toIntOption match
          case Some(result) => result
          case None => return Left(s"stratum $index has a nonnumeric path item: ${stratum.show}")
        if item < 0 || item >= Width then
          return Left(s"stratum $index has an item outside 0..2: ${stratum.show}")
        val bit = 1 << item
        if (mayMask & bit) != 0 then
          return Left(s"stratum $index duplicates finite item $item: ${value.show}")
        val lower = stratum.cardinality.lower.annotatedValue match
          case Some(result) => result
          case None => return Left(s"stratum $index has a symbolic lower cardinality: ${stratum.show}")
        val upper = stratum.cardinality.upper.annotatedValue match
          case Some(result) => result
          case None => return Left(s"stratum $index has a symbolic upper cardinality: ${stratum.show}")
        if lower != 0 && lower != 1 then
          return Left(s"stratum $index lower cardinality is outside 0..1: ${stratum.show}")
        if upper != 1 then
          return Left(s"stratum $index upper cardinality is not one: ${stratum.show}")
        mayMask |= bit
        if lower == 1 then mustMask |= bit
        index += 1

      val requiredCount = BigInt(Integer.bitCount(mustMask))
      val possibleCount = BigInt(Integer.bitCount(mayMask))
      val scalarLower = value.size.lower.annotatedValue
      val scalarUpper = value.size.upper.annotatedValue
      if scalarLower.isEmpty || scalarUpper.isEmpty then
        Left(s"scalar cardinality is symbolic: ${value.show}")
      else if scalarLower.get < requiredCount || scalarLower.get > scalarUpper.get ||
          scalarUpper.get > possibleCount
      then Left(s"scalar cardinality contradicts decoded masks: ${value.show}")
      else
        val expectedLength =
          if mayMask == 0 then PathLengthEstimate.empty
          else PathLengthEstimate.exact(PathLengthExpr.One)
        if value.pathLength != expectedLength then
          Left(s"global path length does not match decoded masks: ${value.show}")
        else Right(Interval(isBottom = false, mustMask, mayMask))
