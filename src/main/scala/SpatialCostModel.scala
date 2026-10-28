package morkl

enum SpatialBackend:
  case Reference, Trie, Zipper, Graph

case class SpatialCostComponents(
  nodeVisits: SizeExpr = SizeExpr.Zero,
  patriciaVisits: SizeExpr = SizeExpr.Zero,
  pathComparisons: SizeExpr = SizeExpr.Zero,
  allocations: SizeExpr = SizeExpr.Zero,
  rounds: SizeExpr = SizeExpr.Zero,
):
  def +(that: SpatialCostComponents): SpatialCostComponents = SpatialCostComponents(
    SizeExpr.add(nodeVisits, that.nodeVisits),
    SizeExpr.add(patriciaVisits, that.patriciaVisits),
    SizeExpr.add(pathComparisons, that.pathComparisons),
    SizeExpr.add(allocations, that.allocations),
    SizeExpr.add(rounds, that.rounds),
  )

  def scale(factor: SizeExpr): SpatialCostComponents = SpatialCostComponents(
    SizeExpr.multiply(nodeVisits, factor),
    SizeExpr.multiply(patriciaVisits, factor),
    SizeExpr.multiply(pathComparisons, factor),
    SizeExpr.multiply(allocations, factor),
    SizeExpr.multiply(rounds, factor),
  )

object SpatialCostComponents:
  val zero: SpatialCostComponents = SpatialCostComponents()

case class SpatialCostInterval(
  workLower: SizeExpr,
  workUpper: SizeExpr,
  allocationLower: SizeExpr,
  allocationUpper: SizeExpr,
  roundsLower: SizeExpr = SizeExpr.Zero,
  roundsUpper: SizeExpr = SizeExpr.Zero,
  componentsUpper: SpatialCostComponents = SpatialCostComponents.zero,
):
  def show: String =
    s"work=[${workLower.show},${workUpper.show}], alloc=[${allocationLower.show},${allocationUpper.show}], " +
      s"rounds=[${roundsLower.show},${roundsUpper.show}], components=$componentsUpper"

case class SpatialCostEstimate(
  workUpper: SizeExpr,
  allocationUpper: SizeExpr,
  workLower: SizeExpr = SizeExpr.Zero,
  allocationLower: SizeExpr = SizeExpr.Zero,
  backend: Map[SpatialBackend, SpatialCostInterval] = Map.empty,
  roundsUpper: SizeExpr = SizeExpr.Zero,
  roundsLower: SizeExpr = SizeExpr.Zero,
):
  def generic: SpatialCostInterval =
    SpatialCostInterval(workLower, workUpper, allocationLower, allocationUpper, roundsLower, roundsUpper)
  def forBackend(value: SpatialBackend): SpatialCostInterval = backend.getOrElse(value, generic)
  def show: String =
    val base = generic.show
    if backend.isEmpty then base
    else
      val details = SpatialBackend.values.map(value =>
        s"${value.toString.toLowerCase}={${forBackend(value).show}}").mkString(", ")
      s"$base; $details"

object SpatialCostEstimate:
  val zero: SpatialCostEstimate = SpatialCostEstimate(SizeExpr.Zero, SizeExpr.Zero)
  val unknown: SpatialCostEstimate = SpatialCostEstimate(SizeExpr.Infinity, SizeExpr.Infinity,
    roundsUpper = SizeExpr.Infinity)

  /** Exact finite sums in a shallow chunked tree: no notation-driven
    * `TermLimit => Infinity`, and no repeated copying of one flat vector. */
  private def treeAdd(values: Seq[SizeExpr]): SizeExpr =
    val direct = values.filterNot(_ == SizeExpr.Zero).flatMap {
      case SizeExpr.Add(terms) => terms
      case value => Vector(value)
    }
    if direct.contains(SizeExpr.Infinity) then SizeExpr.Infinity
    else if direct.exists(_.nodeCount(65) > 64) then
      // A named atom denotes this finite sum without distributing/copying its
      // representation. Unlike the removed cliff, this is not semantic ∞.
      SizeExpr.symbol(s"finiteCostSum(${direct.size})")
    else
      val (constants, symbolic) = direct.partition(_.isInstanceOf[SizeExpr.Const])
      val constant = constants.collect { case SizeExpr.Const(value) => value }.sum
      val terms = (Option.when(constant > 0)(SizeExpr.const(constant)).toVector ++ symbolic).toVector
      def chunk(items: Vector[SizeExpr]): SizeExpr = items match
        case Vector() => SizeExpr.Zero
        case Vector(value) => value
        case values if values.size <= 32 => SizeExpr.Add(values)
        case values => SizeExpr.Add(values.grouped(32).map(group => chunk(group.toVector)).toVector)
      chunk(terms)

  private def lowerAdd(values: Seq[SizeExpr]): SizeExpr = treeAdd(values)

  def sequential(values: SpatialCostEstimate*): SpatialCostEstimate = SpatialCostEstimate(
    treeAdd(values.map(_.workUpper)), treeAdd(values.map(_.allocationUpper)),
    lowerAdd(values.map(_.workLower)), lowerAdd(values.map(_.allocationLower)),
    SpatialBackend.values.map { backend =>
      val intervals = values.map(_.forBackend(backend))
      backend -> SpatialCostInterval(
        lowerAdd(intervals.map(_.workLower)), treeAdd(intervals.map(_.workUpper)),
        lowerAdd(intervals.map(_.allocationLower)), treeAdd(intervals.map(_.allocationUpper)),
        lowerAdd(intervals.map(_.roundsLower)), treeAdd(intervals.map(_.roundsUpper)),
        intervals.map(_.componentsUpper).foldLeft(SpatialCostComponents.zero)(_ + _),
      )
    }.toMap,
    treeAdd(values.map(_.roundsUpper)), lowerAdd(values.map(_.roundsLower)),
  )

  def scale(value: SpatialCostEstimate, lower: SizeExpr, upper: SizeExpr): SpatialCostEstimate =
    def scaleInterval(interval: SpatialCostInterval): SpatialCostInterval = SpatialCostInterval(
      SizeExpr.multiply(lower, interval.workLower), SizeExpr.multiply(upper, interval.workUpper),
      SizeExpr.multiply(lower, interval.allocationLower), SizeExpr.multiply(upper, interval.allocationUpper),
      SizeExpr.multiply(lower, interval.roundsLower), SizeExpr.multiply(upper, interval.roundsUpper),
      interval.componentsUpper.scale(upper),
    )
    val generic = scaleInterval(value.generic)
    SpatialCostEstimate(generic.workUpper, generic.allocationUpper, generic.workLower, generic.allocationLower,
      SpatialBackend.values.map(backend => backend -> scaleInterval(value.forBackend(backend))).toMap,
      generic.roundsUpper, generic.roundsLower)

  def withRounds(value: SpatialCostEstimate, lower: SizeExpr, upper: SizeExpr): SpatialCostEstimate =
    value.copy(roundsLower = lower, roundsUpper = upper,
      backend = value.backend.view.mapValues(interval => interval.copy(
        roundsLower = lower,
        roundsUpper = upper,
        componentsUpper = interval.componentsUpper.copy(rounds = upper),
      )).toMap)

  def add(left: SizeExpr, right: SizeExpr): SizeExpr = treeAdd(Seq(left, right))

  def bounded(workLower: SizeExpr, workUpper: SizeExpr,
    allocationLower: SizeExpr, allocationUpper: SizeExpr): SpatialCostEstimate =
    val interval = SpatialCostInterval(workLower, workUpper, allocationLower, allocationUpper)
    SpatialCostEstimate(workUpper, allocationUpper, workLower, allocationLower,
      SpatialBackend.values.map(_ -> interval).toMap)

/** Operation classes whose costs are derived from executor behaviour. */
enum SpatialCostOperation:
  case Generic, Union, Intersection, Subtraction, Restriction, Raffination, Composition,
    Wrap, Unwrap, Range, GroupCollect, Fixpoint

case class SpatialCostMeasure(
  size: ResultSizeEstimate,
  length: PathLengthEstimate,
  heads: ResultSizeEstimate,
  shape: SpatialHeadShape = SpatialHeadShape.unknown,
):
  /** Root plus the unshared nodes of every represented path. Sharing can only
    * lower this count, so it is a sound trie-node upper bound. */
  def nodesUpper: SizeExpr = SizeExpr.add(SizeExpr.One, SizeExpr.multiply(size.upper, lengthUpper))
  def nodesLower: SizeExpr = SizeExpr.maximum(SizeExpr.One, SizeExpr.multiply(size.lower, lengthLower))
  def internalNodesUpper: SizeExpr = SizeExpr.add(SizeExpr.One, SizeExpr.multiply(
    size.upper,
    SizeExpr.positiveDifference(lengthUpper, SizeExpr.One),
  ))
  def lengthUpper: SizeExpr = length.upper.annotatedBound(Z3BoundDirection.Upper)
    .fold[SizeExpr](SizeExpr.symbol(s"len(${length.show})"))(SizeExpr.const)
  def lengthLower: SizeExpr = SizeExpr.const(length.lower.annotatedBound(Z3BoundDirection.Lower).getOrElse(BigInt(0)))

  /** Child-map entries encountered along every source frontier reached by a
    * prefix of the given maximum length. The bounded shape is used only while
    * it still represents that depth; otherwise the full trie-node bound is the
    * sound fallback. */
  def prefixFrontierUpper(prefixLength: SizeExpr): SizeExpr =
    prefixLength.annotatedBound(Z3BoundDirection.Upper) match
      case Some(value) if value.isValidInt && value >= 0 && value <= 6 =>
        SizeExpr.add((0 until value.toInt).map(depth => shape.distinctItemsAt(depth).upper)*)
      case _ => nodesUpper

  /** True only when the bounded shape accounts for every possible head and
    * the tracked head sets cannot overlap. */
  def definitelyHeadDisjoint(that: SpatialCostMeasure): Boolean =
    val completeHere = shape.otherHeads.upper.annotatedBound(Z3BoundDirection.Upper).contains(BigInt(0))
    val completeThere = that.shape.otherHeads.upper.annotatedBound(Z3BoundDirection.Upper).contains(BigInt(0))
    completeHere && completeThere && shape.heads.keySet.intersect(that.shape.heads.keySet).isEmpty

object SpatialCostMeasure:
  def apply(value: SpatialType): SpatialCostMeasure = SpatialCostMeasure(value.size, value.pathLength,
    value.shape.headCount, value.shape)

/** One independently testable model per concrete executor. */
trait SpatialCostModel:
  def backend: SpatialBackend
  def operation(
    kind: SpatialCostOperation,
    inputs: Vector[SpatialCostMeasure],
    result: SpatialCostMeasure,
    fallback: SpatialCostInterval,
  ): SpatialCostInterval

object SpatialCostModels:
  private def add(values: SizeExpr*): SizeExpr = SizeExpr.add(values*)
  private def mul(values: SizeExpr*): SizeExpr = SizeExpr.multiply(values*)
  private def binary(inputs: Vector[SpatialCostMeasure]): Option[(SpatialCostMeasure, SpatialCostMeasure)] =
    inputs match
      case Vector(left, right, _*) => Some(left -> right)
      case _ => None

  private def log2ceil(value: SizeExpr): SizeExpr = value.annotatedValue match
    case Some(number) if number <= 1 => SizeExpr.One
    case Some(number) => SizeExpr.const(BigInt((number - 1).bitLength))
    case None => SizeExpr.symbol(s"log2ceil(${value.show})")

  object Reference extends SpatialCostModel:
    val backend = SpatialBackend.Reference
    def operation(kind: SpatialCostOperation, inputs: Vector[SpatialCostMeasure], result: SpatialCostMeasure,
      fallback: SpatialCostInterval): SpatialCostInterval =
      binary(inputs) match
        case Some((left, right)) =>
          val work = kind match
            case SpatialCostOperation.Composition =>
              mul(left.size.upper, right.size.upper, add(left.lengthUpper, right.lengthUpper))
            case SpatialCostOperation.Restriction => mul(left.size.upper, right.size.upper, right.lengthUpper)
            case SpatialCostOperation.Raffination => mul(left.size.upper, right.size.upper, right.lengthUpper)
            case SpatialCostOperation.Union =>
              // SpaceValue is an immutable HAMT set. A disjoint union hashes
              // each path and updates several 5-bit trie levels; path equality
              // also traverses its items. Seven is the maximum material HAMT
              // depth for the 32-bit hashes used by this representation.
              mul(SizeExpr.const(7), add(left.size.upper, right.size.upper),
                SizeExpr.maximum(left.lengthUpper, right.lengthUpper))
            case SpatialCostOperation.Intersection | SpatialCostOperation.Subtraction =>
              add(left.size.upper, right.size.upper)
            case _ => fallback.workUpper
          val allocation = kind match
            case SpatialCostOperation.Intersection => SizeExpr.minimum(left.size.upper, right.size.upper)
            case SpatialCostOperation.Subtraction => left.size.upper
            case SpatialCostOperation.Composition | SpatialCostOperation.Restriction => result.size.upper
            case SpatialCostOperation.Union => add(left.size.upper, right.size.upper)
            case _ => fallback.allocationUpper
          val components = kind match
            case SpatialCostOperation.Composition => SpatialCostComponents(
              nodeVisits = mul(left.size.upper, right.size.upper),
              allocations = result.size.upper,
            )
            case SpatialCostOperation.Restriction => SpatialCostComponents(
              pathComparisons = mul(left.size.upper, right.size.upper),
              allocations = result.size.upper,
            )
            case SpatialCostOperation.Raffination => SpatialCostComponents(
              pathComparisons = mul(left.size.upper, right.size.upper),
              allocations = left.size.upper,
            )
            case SpatialCostOperation.Union | SpatialCostOperation.Intersection | SpatialCostOperation.Subtraction =>
              SpatialCostComponents(pathComparisons = work, allocations = allocation)
            case _ => fallback.componentsUpper
          fallback.copy(workUpper = work, allocationUpper = allocation, componentsUpper = components)
        case None => kind match
          case SpatialCostOperation.Range if inputs.nonEmpty =>
            val source = inputs.head
            val log = log2ceil(source.size.upper)
            fallback.copy(
              workUpper = mul(source.size.upper, log, source.lengthUpper),
              componentsUpper = SpatialCostComponents(pathComparisons = mul(source.size.upper, log)),
            )
          case _ => fallback

  object Trie extends SpatialCostModel:
    val backend = SpatialBackend.Trie
    def operation(kind: SpatialCostOperation, inputs: Vector[SpatialCostMeasure], result: SpatialCostMeasure,
      fallback: SpatialCostInterval): SpatialCostInterval =
      binary(inputs) match
        case Some((left, right)) =>
          val disjoint = left.definitelyHeadDisjoint(right)
          val binaryPatricia = mul(SizeExpr.const(2), add(left.nodesUpper, right.nodesUpper))
          val restrictionPatricia = add(
            mul(SizeExpr.const(2), right.nodesUpper),
            left.prefixFrontierUpper(right.lengthUpper),
          )
          val work = kind match
            // concat traverses the left trie and grafts the complete right trie
            // at terminals. The right operand and Cartesian result are shared.
            case SpatialCostOperation.Composition => left.nodesUpper
            // restrictBy walks the prefix trie and grafts accepted source
            // subtries wholesale. Its complexity is independent of |left|.
            case SpatialCostOperation.Restriction => right.nodesUpper
            case SpatialCostOperation.Raffination => mul(SizeExpr.const(2), right.nodesUpper)
            case SpatialCostOperation.Union | SpatialCostOperation.Intersection | SpatialCostOperation.Subtraction
                if left.definitelyHeadDisjoint(right) => SizeExpr.One
            case SpatialCostOperation.Union | SpatialCostOperation.Intersection | SpatialCostOperation.Subtraction =>
              add(left.nodesUpper, right.nodesUpper)
            case _ => fallback.workUpper
          val components = kind match
            case SpatialCostOperation.Composition => SpatialCostComponents(
              nodeVisits = left.nodesUpper,
              patriciaVisits = mul(SizeExpr.const(2), left.nodesUpper),
              allocations = left.internalNodesUpper,
            )
            case SpatialCostOperation.Restriction => SpatialCostComponents(
              nodeVisits = mul(SizeExpr.const(2), right.nodesUpper),
              patriciaVisits = restrictionPatricia,
              pathComparisons = right.nodesUpper,
              allocations = right.internalNodesUpper,
            )
            case SpatialCostOperation.Raffination => SpatialCostComponents(
              nodeVisits = mul(SizeExpr.const(4), right.nodesUpper),
              patriciaVisits = mul(SizeExpr.const(2), restrictionPatricia),
              pathComparisons = right.nodesUpper,
              allocations = mul(SizeExpr.const(2), right.internalNodesUpper),
            )
            case SpatialCostOperation.Union if disjoint => SpatialCostComponents(
              nodeVisits = SizeExpr.One,
              patriciaVisits = SizeExpr.One,
              allocations = SizeExpr.One,
            )
            case SpatialCostOperation.Intersection | SpatialCostOperation.Subtraction if disjoint =>
              SpatialCostComponents(nodeVisits = SizeExpr.One, patriciaVisits = SizeExpr.One)
            case SpatialCostOperation.Union | SpatialCostOperation.Intersection | SpatialCostOperation.Subtraction =>
              SpatialCostComponents(
                nodeVisits = add(left.nodesUpper, right.nodesUpper),
                patriciaVisits = binaryPatricia,
                allocations = result.nodesUpper,
              )
            case _ => fallback.componentsUpper
          fallback.copy(workUpper = work, allocationUpper = result.nodesUpper, componentsUpper = components)
        case None => kind match
          case SpatialCostOperation.Range if inputs.nonEmpty =>
            fallback.copy(
              workUpper = add(inputs.head.size.upper, inputs.head.lengthUpper),
              allocationUpper = result.nodesUpper,
              componentsUpper = SpatialCostComponents(
                nodeVisits = add(inputs.head.lengthUpper, result.nodesUpper),
                patriciaVisits = mul(SizeExpr.const(2), result.nodesUpper),
                allocations = result.nodesUpper,
              ),
            )
          case SpatialCostOperation.Unwrap =>
            fallback.copy(
              allocationUpper = SizeExpr.Zero,
              componentsUpper = SpatialCostComponents(
                nodeVisits = fallback.workUpper,
                pathComparisons = SizeExpr.positiveDifference(fallback.workUpper, SizeExpr.One),
              ),
            )
          case _ => fallback.copy(allocationUpper = result.nodesUpper)

  object Zipper extends SpatialCostModel:
    val backend = SpatialBackend.Zipper
    def operation(kind: SpatialCostOperation, inputs: Vector[SpatialCostMeasure], result: SpatialCostMeasure,
      fallback: SpatialCostInterval): SpatialCostInterval =
      val trie = Trie.operation(kind, inputs, result, fallback)
      kind match
        case SpatialCostOperation.Unwrap => trie
        case _ => trie.copy(
          workUpper = add(trie.workUpper, result.lengthUpper),
          componentsUpper = trie.componentsUpper.copy(
            nodeVisits = add(trie.componentsUpper.nodeVisits, result.lengthUpper),
          ),
        )

  object Graph extends SpatialCostModel:
    val backend = SpatialBackend.Graph
    def operation(kind: SpatialCostOperation, inputs: Vector[SpatialCostMeasure], result: SpatialCostMeasure,
      fallback: SpatialCostInterval): SpatialCostInterval =
      // execT adds one graph-node dispatch and then calls the same native trie
      // operation. Counting only graph nodes loses the operator asymptotics.
      val native = Trie.operation(kind, inputs, result, fallback)
      native.copy(
        workUpper = add(SizeExpr.One, native.workUpper),
        componentsUpper = native.componentsUpper.copy(
          nodeVisits = add(SizeExpr.One, native.componentsUpper.nodeVisits),
        ),
      )

  val all: Vector[SpatialCostModel] = Vector(Reference, Trie, Zipper, Graph)

/** Closed forms used by recursive and fixed-point cost transfers. */
object SpatialRecurrence:
  def solve(additive: SizeExpr, branching: SizeExpr, rounds: SizeExpr): SizeExpr =
    SizeExpr.multiply(additive, SizeExpr.geometricSeries(branching, rounds))
