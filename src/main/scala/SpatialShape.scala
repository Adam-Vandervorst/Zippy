package morkl

/** Three-valued presence used by the bounded trie projection. */
enum SpatialPresence:
  case No, May, Must

  def union(that: SpatialPresence): SpatialPresence = (this, that) match
    case (SpatialPresence.No, value) => value
    case (value, SpatialPresence.No) => value
    case (SpatialPresence.Must, _) | (_, SpatialPresence.Must) => SpatialPresence.Must
    case _ => SpatialPresence.May

/** A bounded head-indexed projection of a path set.
  *
  * `heads` records constant heads and their tail spaces. `otherHeads` bounds
  * distinct untracked heads; `otherTail` describes their tails. The carrier is
  * intentionally depth/width bounded, so overflow is summarized rather than
  * dropped. It is a reduced-product channel, not a second source of truth.
  */
case class SpatialHeadShape(
  epsilon: SpatialPresence,
  heads: Map[PathItem, SpatialHeadShape],
  otherHeads: ResultSizeEstimate,
  otherTail: Option[SpatialHeadShape],
):
  def isUnknown: Boolean = heads.isEmpty && otherHeads == ResultSizeEstimate.unknown && otherTail.nonEmpty

  def headCount: ResultSizeEstimate =
    val trackedUpper = SizeExpr.const(heads.size)
    val trackedLower = SizeExpr.const(heads.count((_, child) => child.inhabited == SpatialPresence.Must))
    ResultSizeEstimate(
      SizeExpr.add(trackedUpper, otherHeads.upper),
      SizeExpr.add(trackedLower, otherHeads.lower),
    )

  def inhabited: SpatialPresence =
    if epsilon == SpatialPresence.Must || heads.values.exists(_.inhabited == SpatialPresence.Must) ||
        otherHeads.lower.annotatedBound(Z3BoundDirection.Lower).exists(_ > 0)
    then SpatialPresence.Must
    else if epsilon == SpatialPresence.May || heads.nonEmpty ||
        otherHeads.upper.annotatedBound(Z3BoundDirection.Upper).forall(_ > 0)
    then SpatialPresence.May
    else SpatialPresence.No

  /** Distinct labels at one depth, reached through the bounded trie. */
  def distinctItemsAt(depth: Int): ResultSizeEstimate =
    require(depth >= 0)
    if depth == 0 then headCount
    else
      val known = heads.values.toVector.map(_.distinctItemsAt(depth - 1))
      val unknownUpper = otherTail.fold(SizeExpr.Zero)(_.distinctItemsAt(depth - 1).upper)
      val upper = SizeExpr.add((known.map(_.upper) :+ unknownUpper)*)
      val lower = SizeExpr.maximum((known.map(_.lower) :+ otherTail.fold(SizeExpr.Zero)(_.distinctItemsAt(depth - 1).lower))* )
      ResultSizeEstimate(upper, lower)

  /** Number of distinct prefixes of a given positive length. */
  def prefixCount(length: Int): ResultSizeEstimate =
    require(length >= 0)
    if length == 0 then ResultSizeEstimate(SizeExpr.One,
      if inhabited == SpatialPresence.Must then SizeExpr.One else SizeExpr.Zero)
    else if length == 1 then headCount
    else
      val known = heads.values.toVector.map(_.prefixCount(length - 1))
      val other = otherTail.map(_.prefixCount(length - 1)).getOrElse(ResultSizeEstimate.empty)
      ResultSizeEstimate(
        SizeExpr.add((known.map(_.upper) :+ SizeExpr.multiply(otherHeads.upper, other.upper))*),
        SizeExpr.maximum((known.map(_.lower) :+ SizeExpr.multiply(otherHeads.lower, other.lower))*),
      )

  def show: String =
    val tracked = heads.toVector.sortBy(_._1.show).map((head, tail) => s"${head.show}→${tail.show}").mkString("{", ",", "}")
    s"shape(eps=${epsilon.toString.toLowerCase}, heads=$tracked, other=${otherHeads.show})"

object SpatialHeadShape:
  private val MaxDepth = 6
  private val MaxHeads = 16

  val empty: SpatialHeadShape = SpatialHeadShape(SpatialPresence.No, Map.empty, ResultSizeEstimate.empty, None)
  val unknown: SpatialHeadShape = SpatialHeadShape(SpatialPresence.May, Map.empty, ResultSizeEstimate.unknown, Some(empty))

  private def positive(value: SizeExpr): Boolean =
    value.annotatedBound(Z3BoundDirection.Lower).exists(_ > 0)

  private def possible(value: SizeExpr): Boolean =
    value.annotatedBound(Z3BoundDirection.Upper).forall(_ > 0)

  private def suffix(stratum: SpatialStratum): SpatialStratum =
    val length = PathLengthEstimate(
      PathLengthExpr.positiveDifference(stratum.length.lower, PathLengthExpr.One),
      PathLengthExpr.positiveDifference(stratum.length.upper, PathLengthExpr.One),
    )
    SpatialStratum(length, stratum.cardinality, stratum.pattern.map(_.tail))

  private def derive(strata: Vector[SpatialStratum], depth: Int): SpatialHeadShape =
    if strata.isEmpty then empty
    else if depth >= MaxDepth then
      val total = ResultSizeEstimate(
        SizeExpr.add(strata.map(_.cardinality.upper)*),
        SizeExpr.maximum(strata.map(_.cardinality.lower)*),
      )
      SpatialHeadShape(SpatialPresence.May, Map.empty,
        ResultSizeEstimate(total.upper, SizeExpr.positive(total.lower)), Some(unknown))
    else
      val epsilonStrata = strata.filter(_.length.lower.annotatedBound(Z3BoundDirection.Lower).contains(BigInt(0)))
      val epsilon =
        if epsilonStrata.exists(stratum => positive(stratum.cardinality.lower) && stratum.length.upper.annotatedBound(Z3BoundDirection.Upper).contains(BigInt(0)))
        then SpatialPresence.Must
        else if epsilonStrata.exists(stratum => possible(stratum.cardinality.upper)) then SpatialPresence.May
        else SpatialPresence.No
      val headed = strata.filter(_.length.upper.annotatedBound(Z3BoundDirection.Upper).forall(_ > 0))
      val (constant, untracked) = headed.partition(_.pattern.flatMap(_.items.headOption).exists {
        case SpatialItem.Constant(_) => true
        case _ => false
      })
      val grouped = constant.groupBy(_.pattern.get.items.head.asInstanceOf[SpatialItem.Constant].value)
      val kept = grouped.toVector.sortBy(_._1.show).take(MaxHeads).map { (head, values) =>
        head -> derive(values.map(suffix), depth + 1)
      }.toMap
      val overflow = grouped.toVector.sortBy(_._1.show).drop(MaxHeads).flatMap(_._2)
      val other = untracked ++ overflow
      val otherCard = if other.isEmpty then ResultSizeEstimate.empty else
        ResultSizeEstimate(
          SizeExpr.add(other.map(_.cardinality.upper)*),
          SizeExpr.maximum(other.map(s => SizeExpr.positive(s.cardinality.lower))*),
        )
      SpatialHeadShape(epsilon, kept, otherCard,
        Option.when(other.nonEmpty)(derive(other.map(suffix), depth + 1)))

  def fromStrata(strata: Vector[SpatialStratum]): SpatialHeadShape = derive(strata, 0)

  /** Preserve bounded head information for large literals even after their
    * per-path strata have been collapsed by `patternLimit`. This is linear in
    * the represented literal and retains exact tracked-head sets. */
  def fromValue(value: SpaceValue): SpatialHeadShape =
    def derivePaths(paths: Vector[List[PathItem]], depth: Int): SpatialHeadShape =
      if paths.isEmpty then empty
      else if depth >= MaxDepth then
        val headed = paths.count(_.nonEmpty)
        SpatialHeadShape(
          if paths.exists(_.isEmpty) then SpatialPresence.Must else SpatialPresence.No,
          Map.empty,
          ResultSizeEstimate.exact(SizeExpr.const(headed)),
          Option.when(headed > 0)(unknown),
        )
      else
        val grouped = paths.collect { case head :: tail => head -> tail }.groupMap(_._1)(_._2)
        val ordered = grouped.toVector.sortBy(_._1.show)
        val kept = ordered.take(MaxHeads).map { (head, tails) =>
          head -> derivePaths(tails, depth + 1)
        }.toMap
        val overflow = ordered.drop(MaxHeads)
        val overflowTails = overflow.flatMap(_._2)
        SpatialHeadShape(
          if paths.exists(_.isEmpty) then SpatialPresence.Must else SpatialPresence.No,
          kept,
          ResultSizeEstimate.exact(SizeExpr.const(overflow.size)),
          Option.when(overflow.nonEmpty)(derivePaths(overflowTails, depth + 1)),
        )
    derivePaths(value.paths.iterator.map(_.items).toVector, 0)
