package morkl

case class SpatialDegreeEstimate(
  minimum: ResultSizeEstimate,
  maximum: ResultSizeEstimate,
  edges: ResultSizeEstimate,
  keys: ResultSizeEstimate,
):
  def averageShow: String = s"${edges.lower.show}..${edges.upper.show} / ${keys.lower.show}..${keys.upper.show}"
  def show: String = s"degree(min=${minimum.show}, max=${maximum.show}, avg=$averageShow)"

case class SpatialDepthDegree(depth: Int, distinctItems: ResultSizeEstimate, fibers: SpatialDegreeEstimate)

/** Resolved, optimization-facing view of a spatial type. */
case class SpatialFacts(value: SpatialType):
  def isDead: Boolean = value.isBottom || value.isEmpty
  def definitelyNonEmpty: Boolean = definitelyAtLeast(1)
  def definitelyAtLeast(count: Int): Boolean =
    require(count >= 0)
    value.size.lower.annotatedBound(Z3BoundDirection.Lower).exists(_ >= count)
  def definiteSize: Option[BigInt] =
    for
      lower <- value.size.lower.annotatedValue
      upper <- value.size.upper.annotatedValue
      if lower == upper
    yield lower
  def maxDepth: Option[Int] = value.pathLength.upper.annotatedBound(Z3BoundDirection.Upper)
    .filter(_.isValidInt).map(_.toInt)
  def definitePathAt(index: Int): Option[PathValue] =
    if index < 0 then None else value.exactValue.flatMap(_.paths.toVector.sortBy(_.show).lift(index))
  def commonConstantPrefix: Option[PathValue] =
    val patterns = value.strata.flatMap(_.pattern)
    Option.when(patterns.nonEmpty && patterns.size == value.strata.size) {
      val commonLength = patterns.map(_.items.length).min
      val prefix = (0 until commonLength).takeWhile { index =>
        patterns.map(_.items(index)).distinct match
          case Vector(SpatialItem.Constant(_)) => true
          case _ => false
      }.flatMap(index => patterns.head.items(index) match
        case SpatialItem.Constant(item) => Some(item)
        case _ => None).toList
      PathValue(prefix)
    }.filter(_.items.nonEmpty)
  def depthProfile: Vector[SpatialDepthDegree] =
    maxDepth.toVector.flatMap { maximum =>
      (0 until maximum).map { depth =>
        val relevant = value.strata.filter(s => s.length.upper.annotatedBound(Z3BoundDirection.Upper).forall(_ > depth))
        val choices = relevant.map { stratum =>
          stratum.pattern.flatMap(_.items.lift(depth)).fold(stratum.cardinality.upper)(SpatialFacts.itemChoices)
        }
        val strataUpper = SizeExpr.minimum(value.size.upper, SizeExpr.add(choices*))
        val shapeItems = value.shape.distinctItemsAt(depth)
        val upper = SizeExpr.minimum(strataUpper, shapeItems.upper)
        val strataLower = if relevant.exists(_.cardinality.lower.annotatedBound(Z3BoundDirection.Lower).exists(_ > 0))
          then SizeExpr.One else SizeExpr.Zero
        val lower = SizeExpr.maximum(strataLower, shapeItems.lower)
        SpatialDepthDegree(depth, ResultSizeEstimate(upper, lower), value.fiberDegree(depth + 1))
      }
    }

object SpatialFacts:
  private[morkl] def itemChoices(item: SpatialItem): SizeExpr = item match
    case SpatialItem.Constant(_) => SizeExpr.One
    case SpatialItem.Affine(_, _, minimum, maximum) => SizeExpr.const(BigInt(maximum) - BigInt(minimum) + 1)
    case SpatialItem.Unknown(_) => SizeExpr.Infinity

enum SpatialSpecialization:
  case TrieUnroll(maxDepth: Int, profile: Vector[SpatialDepthDegree])
  case ZipperPrefocus(prefix: PathValue)
  case GraphConstantFold(value: SpaceValue)

object SpatialBackendSelection:
  def candidates(value: SpatialType): Vector[SpatialSpecialization] =
    val facts = value.facts
    Vector(
      facts.maxDepth.map(depth => SpatialSpecialization.TrieUnroll(depth, facts.depthProfile)),
      facts.commonConstantPrefix.map(SpatialSpecialization.ZipperPrefocus.apply),
      value.exactValue.map(SpatialSpecialization.GraphConstantFold.apply),
    ).flatten
