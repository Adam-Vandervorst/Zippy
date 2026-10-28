package morkl

import scala.collection.mutable
import scala.util.DynamicVariable

object SpatialTypeAnalysis:
  private val analysisTrace = DynamicVariable(Option.empty[mutable.ArrayBuffer[SpatialNodeAnalysis]])
  private final class AnalysisFuel(var remaining: Int)
  private val analysisFuel = DynamicVariable(Option.empty[AnalysisFuel])

  private def withinBudget[A](config: SpatialAnalysisConfig)(body: => A): A =
    analysisFuel.value match
      case Some(_) => body
      case None => analysisFuel.withValue(Some(AnalysisFuel(config.analysisNodeBudget)))(body)

  def output(
    space: Space,
    assumptions: SpatialAssumptions = SpatialAssumptions(),
    routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  ): SpatialType =
    withinBudget(assumptions.config) {
      constrain(space, analyze(space, assumptions, routines, Set.empty), assumptions)
    }

  /** Spatial result with every Z3 fallback/timeout encountered by its scalar
    * and path-length reduced products. */
  def outputReported(
    space: Space,
    assumptions: SpatialAssumptions = SpatialAssumptions(),
    routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
  ): Z3AnalysisReport[SpatialType] =
    Z3Diagnostics.capture(output(space, assumptions, routines))

  /** Analyze once while retaining every intermediate result together with the
    * lexical bindings under which it was computed. Repeated observations are
    * intentional for loop/fixpoint nodes. */
  def outputDecorated(
    space: Space,
    assumptions: SpatialAssumptions = SpatialAssumptions(),
    routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
  ): DecoratedSpatialAnalysis =
    val nodes = mutable.ArrayBuffer.empty[SpatialNodeAnalysis]
    val root = analysisTrace.withValue(Some(nodes)) {
      output(space, assumptions, routines)
    }
    def children(value: Space): Vector[Space] = value match
      case Space.Call(_, _, mentions) => mentions
      case Space.Union(left, right) => Vector(left, right)
      case Space.Intersection(left, right) => Vector(left, right)
      case Space.Subtraction(left, right) => Vector(left, right)
      case Space.Restriction(left, right) => Vector(left, right)
      case Space.Raffination(left, right) => Vector(left, right)
      case Space.Composition(left, right) => Vector(left, right)
      case Space.Iteration(source, _, _, body) => Vector(source, body)
      case Space.Fold(source, _, _, _, _, body, _) => Vector(source, body)
      case Space.Fixpoint(initial, _, step) => Vector(initial, step)
      case Space.Wrap(source, _) => Vector(source)
      case Space.Unwrap(source, _) => Vector(source)
      case Space.TailsUnion(source) => Vector(source)
      case Space.TailsIntersection(source) => Vector(source)
      case Space.PrefixClosure(source) => Vector(source)
      case Space.SuffixClosure(source) => Vector(source)
      case Space.TailsClosure(source) => Vector(source)
      case Space.GroundedSS(source, _) => Vector(source)
      case Space.Range(source, _, _) => Vector(source)
      case _ => Vector.empty
    def occurrences(value: Space, position: Vector[Int]): Vector[(Space, Vector[Int])] =
      (value -> position) +: children(value).zipWithIndex.flatMap { (child, index) =>
        occurrences(child, position :+ index)
      }
    val raw = nodes.toVector
    val positional = occurrences(space, Vector.empty).map { (expression, position) =>
      val identity = raw.filter(node => node.expression.asInstanceOf[AnyRef] eq expression.asInstanceOf[AnyRef])
      val matches = if identity.nonEmpty then identity else raw.filter(_.expression == expression)
      val observations = matches.map(node => SpatialNodeObservation(node.result, node.spaces, node.paths))
      val summary = if position.isEmpty then root else observations.map(_.result).reduceOption(SpatialType.joinAlternatives)
        .getOrElse(SpatialType.top)
      val bindings = observations.headOption
      SpatialNodeAnalysis(expression, summary,
        bindings.fold(assumptions.spaces)(_.spaces), bindings.fold(assumptions.paths)(_.paths),
        position, observations)
    }
    DecoratedSpatialAnalysis(root, positional)

  def outputRoutine(
    routine: Routine,
    pathInputs: Map[PathRef, SpatialPathType],
    spaceInputs: Map[SpaceMention, SpatialType],
    routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
    prefixCoverage: Set[SpatialPrefixCoverage] = Set.empty
  ): SpatialType =
    outputRoutineAbstract(routine, pathInputs, spaceInputs, routines, prefixCoverage)

  /** Interpret a routine from abstract argument annotations. This explicit
    * name remains as a compatibility alias for callers that want to emphasize
    * the always-abstract contract; `outputRoutine` now has the same contract.
    */
  def outputRoutineAbstract(
    routine: Routine,
    pathInputs: Map[PathRef, SpatialPathType],
    spaceInputs: Map[SpaceMention, SpatialType],
    routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
    prefixCoverage: Set[SpatialPrefixCoverage] = Set.empty,
    boundLaws: Vector[SpatialBoundLaw] = Vector.empty
  ): SpatialType =
    outputRoutineAbstract(
      routine,
      SpatialRoutineAnnotations(pathInputs, spaceInputs, prefixCoverage, boundLaws),
      routines,
    )

  /** Strict abstract entry point. Its dataflow is deliberately one-way:
    * annotated arguments and routine syntax -> spatial type. Concrete
    * evaluation is reserved for external validation and cannot feed this
    * method.
    */
  def outputRoutineAbstract(
    routine: Routine,
    annotations: SpatialRoutineAnnotations,
    routines: PartialFunction[RoutinePtr, Routine],
  ): SpatialType =
    val assumptions = annotations.assumptions
    withinBudget(assumptions.config) {
      SpatialBoundLaw.reduce(
        SpatialType.reduce(analyze(routine.body, assumptions, routines, Set(routine.name))),
        annotations.spaces,
        annotations.resultLaws,
      )
    }

  private def constrain(space: Space, raw: SpatialType, assumptions: SpatialAssumptions): SpatialType =
    val scalarSize = ResultSpaceSize.estimate(space, assumptions.sizeAssumptions)
    val scalarLength = ResultPathLength.estimate(
      space,
      assumptions.lengthAssumptions,
      assumptions.pathLengthAssumptions,
      assumptions.sizeAssumptions
    )
    SpatialType.reduce(raw.copy(
      size = if raw.size.exact then raw.size else ResultSizeEstimate(
        SizeExpr.minimum(raw.size.upper, scalarSize.upper),
        SizeExpr.maximum(raw.size.lower, scalarSize.lower)
      ),
      pathLength = if raw.pathLength.exact then raw.pathLength else PathLengthEstimate(
        PathLengthExpr.maximum(raw.pathLength.lower, scalarLength.lower),
        PathLengthExpr.minimum(raw.pathLength.upper, scalarLength.upper)
      )
    ))

  private def exactLength(length: PathLengthEstimate): Option[Int] = (length.lower, length.upper) match
    case (PathLengthExpr.Const(lower), PathLengthExpr.Const(upper)) if lower == upper && lower.isValidInt => Some(lower.toInt)
    case _ => None

  private def definitelyHeaded(length: PathLengthEstimate): Boolean =
    length.lower.annotatedBound(Z3BoundDirection.Lower).exists(_ > 0)

  private def mayBeHeaded(length: PathLengthEstimate): Boolean =
    length.upper.annotatedBound(Z3BoundDirection.Upper).forall(_ > 0)

  private def mayHaveLengthAtLeast(length: PathLengthEstimate, required: Int): Boolean =
    length.upper.annotatedBound(Z3BoundDirection.Upper).forall(_ >= required)

  private def path(
    value: Path,
    assumptions: SpatialAssumptions,
    routines: PartialFunction[RoutinePtr, Routine],
    active: Set[RoutinePtr]
  ): SpatialPathType = value match
    case Path.Deref(ref) => assumptions.paths.getOrElse(ref,
      if ref.lengthHint >= 0 then SpatialPathType.length(ref.lengthHint, ref.s)
      else SpatialPathType(PathLengthEstimate.exact(PathLengthExpr.PathLengthOf(value)), Vector.empty))
    case Path.Constant(constant) => SpatialPathType.constant(constant)
    case Path.Concat(left, right) =>
      val l = path(left, assumptions, routines, active)
      val r = path(right, assumptions, routines, active)
      val product = for a <- l.patterns; b <- r.patterns yield a.concat(b)
      val patterns = if product.size <= assumptions.config.patternLimit then product else Vector.empty
      SpatialPathType(
        PathLengthEstimate(PathLengthExpr.add(l.length.lower, r.length.lower), PathLengthExpr.add(l.length.upper, r.length.upper)),
        patterns
      )
    case Path.GroundedPP(_, _) | Path.GroundedSP(_, _) =>
      SpatialPathType(ResultPathLength.estimate(Space.Singleton(value), assumptions.lengthAssumptions,
        assumptions.pathLengthAssumptions, assumptions.sizeAssumptions), Vector.empty)

  private def singleton(value: SpatialPathType): SpatialType =
    val result = value.patterns match
      case Vector(pattern) => SpatialType.fromStrata(Vector(SpatialStratum(value.length,
        ResultSizeEstimate.exact(SizeExpr.One), Some(pattern))))
      case patterns if patterns.nonEmpty =>
        val optional = ResultSizeEstimate(SizeExpr.One, SizeExpr.Zero)
        SpatialType.fromStrata(patterns.map(pattern => SpatialStratum(value.length, optional, Some(pattern))),
          sizeOverride = Some(ResultSizeEstimate.exact(SizeExpr.One)), lengthOverride = Some(value.length))
      case _ => SpatialType.fromStrata(Vector(SpatialStratum(value.length, ResultSizeEstimate.exact(SizeExpr.One))))
    withTrieConstructionCost(
      result,
      SpatialCostEstimate.bounded(SizeExpr.One, SizeExpr.One, SizeExpr.One, SizeExpr.One),
      graphDispatch = true,
    )

  /** Literal and singleton zipper/trie evaluation constructs an immutable
    * trie before any outer lazy consumer can constrain it. The number of
    * allocated nodes is bounded by one root plus the unshared length of every
    * path; singleton insertion can attain that bound exactly. Keep the
    * reference interval unchanged, but expose construction counters for every
    * trie-backed executor. */
  private def withTrieConstructionCost(
    result: SpatialType,
    base: SpatialCostEstimate,
    graphDispatch: Boolean,
  ): SpatialType =
    val nodes = SpatialCostMeasure(result).nodesUpper
    def native(current: SpatialCostInterval, dispatch: Boolean): SpatialCostInterval =
      val visits = if dispatch then SizeExpr.One else SizeExpr.Zero
      current.copy(
        workLower = SizeExpr.Zero,
        workUpper = SizeExpr.maximum(current.workUpper, SizeExpr.add(nodes, visits)),
        allocationLower = SizeExpr.Zero,
        allocationUpper = SizeExpr.maximum(current.allocationUpper, nodes),
        componentsUpper = current.componentsUpper.copy(
          nodeVisits = SizeExpr.maximum(current.componentsUpper.nodeVisits, visits),
          // Singleton insertion performs a Patricia update and bulk literal
          // construction may change implementation; the node bound covers
          // either representation without relying on today’s zero/one count.
          patriciaVisits = SizeExpr.maximum(current.componentsUpper.patriciaVisits, nodes),
          allocations = SizeExpr.maximum(current.componentsUpper.allocations, nodes),
        ),
      )
    val backend = base.backend
      .updated(SpatialBackend.Trie, native(base.forBackend(SpatialBackend.Trie), dispatch = false))
      .updated(SpatialBackend.Zipper, native(base.forBackend(SpatialBackend.Zipper), dispatch = false))
      .updated(SpatialBackend.Graph, native(base.forBackend(SpatialBackend.Graph), graphDispatch))
    result.copy(cost = base.copy(backend = backend))

  private def unionCount(left: ResultSizeEstimate, right: ResultSizeEstimate): ResultSizeEstimate =
    ResultSizeEstimate(SizeExpr.add(left.upper, right.upper), SizeExpr.maximum(left.lower, right.lower))

  private def charge(
    result: SpatialType,
    inputs: SpatialType*,
  )(
    work: SizeExpr,
    allocation: SizeExpr = SizeExpr.Zero,
    workLower: SizeExpr = SizeExpr.Zero,
    allocationLower: SizeExpr = SizeExpr.Zero,
    operationKind: SpatialCostOperation = SpatialCostOperation.Generic,
    roundsLower: SizeExpr = SizeExpr.Zero,
    roundsUpper: SizeExpr = SizeExpr.Zero,
  ): SpatialType =
    val inputCost = SpatialCostEstimate.sequential(inputs.map(_.cost)*)
    val generic = SpatialCostInterval(
      workLower,
      work,
      allocationLower,
      allocation,
      roundsLower,
      roundsUpper,
      SpatialCostComponents(nodeVisits = work, allocations = allocation, rounds = roundsUpper),
    )
    val measures = inputs.toVector.map(SpatialCostMeasure.apply)
    val resultMeasure = SpatialCostMeasure(result)
    val intervals = SpatialCostModels.all.map { model =>
      model.backend -> model.operation(operationKind, measures, resultMeasure, generic)
    }.toMap
    val reference = intervals(SpatialBackend.Reference)
    val operation = SpatialCostEstimate(reference.workUpper, reference.allocationUpper,
      reference.workLower, reference.allocationLower, intervals,
      reference.roundsUpper, reference.roundsLower)
    result.copy(cost = SpatialCostEstimate.sequential(inputCost, operation))

  private def capStrata(values: Vector[SpatialStratum], limit: Int = 64): Vector[SpatialStratum] =
    if values.size <= limit then values
    else
      val (exact, ranged) = values.partition(_.exactLength.nonEmpty)
      val exactCollapsed = exact.groupBy(_.exactLength.get).toVector.sortBy(_._1).map { (length, group) =>
        val groupType = SpatialType.fromStrata(group)
        SpatialStratum(PathLengthEstimate.exact(PathLengthExpr.const(length)), groupType.size)
      }
      val rangedCollapsed =
        if ranged.isEmpty then Vector.empty
        else
          val groupType = SpatialType.fromStrata(ranged)
          Vector(SpatialStratum(groupType.pathLength, groupType.size))
      exactCollapsed ++ rangedCollapsed

  /** Intersect a spatial result with a proved aggregate upper bound without
    * retaining an exponentially unfolded structural projection. Each stratum
    * is a subset of the whole result, so the aggregate cap is also a sound
    * cap for every stratum. We retain the ordinary reduced-product minimum
    * while it is compact; once only the structural side exceeds the budget,
    * replacing it by the proved cap is a safe (slightly less precise)
    * normalization that prevents later iterations from re-embedding the
    * oversized expression. */
  private def capAggregateUpper(value: SpatialType, provedUpper: SizeExpr): SpatialType =
    val structuralUpper = value.size.upper
    val compactStructural = structuralUpper.nodeCount(257) <= 256
    val compactProof = provedUpper.nodeCount(257) <= 256
    val discardOversizedStructural = !compactStructural && compactProof
    val upper =
      if discardOversizedStructural then provedUpper
      else SizeExpr.minimum(structuralUpper, provedUpper)
    val strata =
      if discardOversizedStructural then value.strata.map { stratum =>
        stratum.copy(cardinality = ResultSizeEstimate(provedUpper, stratum.cardinality.lower))
      }
      else value.strata
    SpatialType.reduce(value.copy(strata = strata, size = ResultSizeEstimate(upper, value.size.lower)))

  private def union(left: SpatialType, right: SpatialType): SpatialType =
    val result =
      if left.isBottom || right.isBottom then SpatialType.bottom
      else if left.copy(cost = SpatialCostEstimate.zero) == right.copy(cost = SpatialCostEstimate.zero) then left
      else if left.isEmpty then right
      else if right.isEmpty then left
      else
        val grouped = (left.strata ++ right.strata).groupBy(value => value.length -> value.pattern)
        val strata = grouped.valuesIterator.map { values =>
          val combined = values.reduce { (a, b) => a.copy(cardinality = unionCount(a.cardinality, b.cardinality)) }
          val singletonPattern = combined.pattern.flatMap(_.constantValue).nonEmpty
          if singletonPattern then combined.copy(cardinality = ResultSizeEstimate(
            SizeExpr.One,
            SizeExpr.minimum(combined.cardinality.lower, SizeExpr.One),
          ))
          else combined
        }.toVector
        SpatialType.fromStrata(capStrata(strata),
          sizeOverride = Some(unionCount(left.size, right.size)))
    charge(result, left, right)(
      SizeExpr.add(left.size.upper, right.size.upper), result.size.upper,
      SizeExpr.add(left.size.lower, right.size.lower), result.size.lower,
      operationKind = SpatialCostOperation.Union)

  private case class ZipperDemandPlan(factor: BigInt, virtual: Boolean)

  /** Count the virtual membership probes needed for one forced trie node.
    * `None` deliberately rejects expressions whose construction, `hasChild`,
    * or emptiness test can inspect resident data outside the consumer frontier.
    * In particular, stored intersections take the native eager merge and the
    * other set operators may scan a whole descendant subtree merely to answer
    * `hasChild`. The proved fragment is deliberately just flat or nested union
    * over resident mentions/empty leaves: even a fixed Wrap around such a union
    * can repeatedly re-observe the resident union while descending a long
    * demanded prefix. This is not a generic syntactic virtuality test. */
  private def zipperDemandPlan(expression: Space): Option[ZipperDemandPlan] =
    def leaf(value: Space): Option[ZipperDemandPlan] = value match
      case Space.Empty | Space.Mention(_) => Some(ZipperDemandPlan(1, virtual = false))
      case _ => None
    def union(left: Space, right: Space): Option[ZipperDemandPlan] =
      for
        l <- zipperDemandPlan(left)
        r <- zipperDemandPlan(right)
      yield ZipperDemandPlan(l.factor + r.factor + 1, virtual = true)
    expression match
      case value @ (Space.Empty | Space.Mention(_)) => leaf(value)
      // Singleton eagerly allocates its complete path trie before an outer
      // consumer is known. Its construction cost cannot be frontier-capped.
      case Space.Singleton(_) => None
      case Space.Union(left, right) => union(left, right)
      // Intersection can eagerly merge stored tries. Subtraction, restriction,
      // raffination and prefix closure answer `hasChild` via recursive emptiness
      // tests. Composition accumulates split candidates, and Wrap can repeat
      // resident-union observations along a demanded prefix. None has a proved
      // constant-per-frontier-node bound here.
      case _ => None

  /** Cap only the Zipper backend of a resident virtual expression. Lower
    * bounds are clamped with the same cap, preserving interval ordering. */
  private def capZipperForDemand(value: SpatialType, demand: SpatialType, factor: BigInt): SpatialType =
    val cost = value.cost
    val original = cost.forBackend(SpatialBackend.Zipper)
    val demandNodes = SpatialCostMeasure(demand).nodesUpper
    val cap = SizeExpr.multiply(SizeExpr.const(factor), demandNodes)
    val bounded = original.copy(
      // A consumer frontier proves only an upper bound on forced work. It
      // cannot justify retaining a local eager lower bound.
      workLower = SizeExpr.Zero,
      workUpper = SizeExpr.minimum(original.workUpper, cap),
      allocationLower = SizeExpr.Zero,
      allocationUpper = SizeExpr.minimum(original.allocationUpper, cap),
      componentsUpper = original.componentsUpper.copy(
        nodeVisits = SizeExpr.minimum(original.componentsUpper.nodeVisits, cap),
        patriciaVisits = SizeExpr.minimum(original.componentsUpper.patriciaVisits, cap),
        pathComparisons = SizeExpr.minimum(original.componentsUpper.pathComparisons, cap),
        allocations = SizeExpr.minimum(original.componentsUpper.allocations, cap),
      ),
    )
    value.copy(cost = cost.copy(backend = cost.backend.updated(SpatialBackend.Zipper, bounded)))

  private def capZipperIntersectionForDemand(value: SpatialType, demand: SpatialType, factor: BigInt): SpatialType =
    val cost = value.cost
    val original = cost.forBackend(SpatialBackend.Zipper)
    val demandNodes = SpatialCostMeasure(demand).nodesUpper
    val cap = SizeExpr.multiply(SizeExpr.const(factor + 1), demandNodes)
    val bounded = original.copy(
      workLower = SizeExpr.Zero,
      workUpper = SizeExpr.minimum(original.workUpper, cap),
      allocationLower = SizeExpr.Zero,
      allocationUpper = SizeExpr.minimum(original.allocationUpper, cap),
      componentsUpper = original.componentsUpper.copy(
        nodeVisits = SizeExpr.minimum(original.componentsUpper.nodeVisits, cap),
        patriciaVisits = SizeExpr.minimum(original.componentsUpper.patriciaVisits, cap),
        pathComparisons = SizeExpr.minimum(original.componentsUpper.pathComparisons, cap),
        allocations = SizeExpr.minimum(original.componentsUpper.allocations, cap),
      ),
    )
    value.copy(cost = cost.copy(backend = cost.backend.updated(SpatialBackend.Zipper, bounded)))

  private def intersection(left: SpatialType, right: SpatialType): SpatialType =
    if left.isBottom || right.isBottom then return SpatialType.bottom
    if left.isEmpty || right.isEmpty then return SpatialType.empty
    val strata = for
      l <- left.strata
      r <- right.strata
      if !lengthsDisjoint(l.length, r.length)
      if !((l.pattern, r.pattern) match
        case (Some(a), Some(b)) => a.definitelyDifferent(b)
        case _ => false)
    yield
      val samePattern = l.pattern.nonEmpty && l.pattern == r.pattern
      val exactSingleton = samePattern && l.cardinality.lower == SizeExpr.One && l.cardinality.upper == SizeExpr.One &&
        r.cardinality.lower == SizeExpr.One && r.cardinality.upper == SizeExpr.One
      SpatialStratum(
        PathLengthEstimate(PathLengthExpr.maximum(l.length.lower, r.length.lower),
          PathLengthExpr.minimum(l.length.upper, r.length.upper)),
        ResultSizeEstimate(SizeExpr.minimum(l.cardinality.upper, r.cardinality.upper),
          if exactSingleton then SizeExpr.One else SizeExpr.Zero),
        if samePattern then l.pattern else None
      )
    val raw = SpatialType.fromStrata(capStrata(strata))
    charge(SpatialType.reduce(raw.copy(size = ResultSizeEstimate(
      SizeExpr.minimum(raw.size.upper, left.size.upper, right.size.upper), raw.size.lower))), left, right)(
      SizeExpr.minimum(left.size.upper, right.size.upper), workLower = SizeExpr.minimum(left.size.lower, right.size.lower),
      operationKind = SpatialCostOperation.Intersection)

  private def subtraction(left: SpatialType, right: SpatialType): SpatialType =
    if left.isBottom || right.isBottom then return SpatialType.bottom
    if left.isEmpty || right.isEmpty then return left
    val strata = left.strata.flatMap { l =>
      val relevant = right.strata.filter { r =>
        !lengthsDisjoint(l.length, r.length) && !((l.pattern, r.pattern) match
          case (Some(a), Some(b)) => a.definitelyDifferent(b)
          case _ => false)
      }
      if relevant.isEmpty then Vector(l)
      else
        val exactMatches = relevant.filter(r => l.pattern.nonEmpty && l.pattern == r.pattern)
        val removedUpper = SizeExpr.add(relevant.map(_.cardinality.upper)*)
        val removedLower = SpatialType.fromStrata(exactMatches).size.lower
        val cardinality = ResultSizeEstimate(
          SizeExpr.positiveDifference(l.cardinality.upper, removedLower),
          SizeExpr.positiveDifference(l.cardinality.lower, removedUpper)
        )
        Option.when(cardinality.upper != SizeExpr.Zero)(l.copy(cardinality = cardinality)).toVector
    }
    val raw = SpatialType.fromStrata(capStrata(strata))
    charge(SpatialType.reduce(raw.copy(size = ResultSizeEstimate(
      SizeExpr.minimum(raw.size.upper, left.size.upper), raw.size.lower))), left, right)(left.size.upper,
      workLower = left.size.lower, operationKind = SpatialCostOperation.Subtraction)

  private def composition(left: SpatialType, right: SpatialType): SpatialType =
    if left.isBottom || right.isBottom then return SpatialType.bottom
    if left.isEmpty || right.isEmpty then return SpatialType.empty
    val strata = for l <- left.strata; r <- right.strata yield
      val pattern = for a <- l.pattern; b <- r.pattern yield a.concat(b)
      SpatialStratum(
        PathLengthEstimate(PathLengthExpr.add(l.length.lower, r.length.lower), PathLengthExpr.add(l.length.upper, r.length.upper)),
        ResultSizeEstimate(
          SizeExpr.multiply(l.cardinality.upper, r.cardinality.upper),
          SizeExpr.maximum(
            SizeExpr.multiply(l.cardinality.lower, SizeExpr.positive(r.cardinality.lower)),
            SizeExpr.multiply(r.cardinality.lower, SizeExpr.positive(l.cardinality.lower))
          )
        ),
        pattern
      )
    val raw = SpatialType.fromStrata(capStrata(strata))
    charge(SpatialType.reduce(raw.copy(size = ResultSizeEstimate(
      SizeExpr.minimum(raw.size.upper, SizeExpr.multiply(left.size.upper, right.size.upper)), raw.size.lower))), left, right)(
      SizeExpr.multiply(left.size.upper, right.size.upper), raw.size.upper,
      operationKind = SpatialCostOperation.Composition)

  private def lengthsDisjoint(left: PathLengthEstimate, right: PathLengthEstimate): Boolean =
    val leftLower = left.lower.annotatedBound(Z3BoundDirection.Lower)
    val leftUpper = left.upper.annotatedBound(Z3BoundDirection.Upper)
    val rightLower = right.lower.annotatedBound(Z3BoundDirection.Lower)
    val rightUpper = right.upper.annotatedBound(Z3BoundDirection.Upper)
    (for l <- leftUpper; r <- rightLower yield l < r).contains(true) ||
      (for r <- rightUpper; l <- leftLower yield r < l).contains(true)

  private def singletonRefs(space: Space): Set[PathRef] = space match
    case Space.Singleton(Path.Deref(ref)) => Set(ref)
    case Space.Union(left, right) => singletonRefs(left) ++ singletonRefs(right)
    case _ => Set.empty

  private def directMention(space: Space): Option[SpaceMention] = space match
    case Space.Mention(mention) => Some(mention)
    case _ => None

  private def restriction(
    leftExpression: Space,
    prefixExpression: Space,
    left: SpatialType,
    prefixes: SpatialType,
    assumptions: SpatialAssumptions
  ): SpatialType =
    val prefixRefs = singletonRefs(prefixExpression)
    val sourceMention = directMention(leftExpression)
    val coverage = for
      ref <- prefixRefs
      mention <- sourceMention.toSet
      fact <- assumptions.prefixCoverage
      if fact.prefix == ref && fact.space == mention
    yield fact
    if prefixes.shape.epsilon == SpatialPresence.Must then
      return charge(left.copy(cost = SpatialCostEstimate.zero), left, prefixes)(
        SizeExpr.add(left.size.upper, prefixes.size.upper),
        left.size.upper,
        operationKind = SpatialCostOperation.Restriction,
      )
    val compatibleStrata = left.strata.flatMap { l =>
      val compatible = prefixes.strata.filter { p =>
        val lengthPossible = (l.length.upper, p.length.lower) match
          case (PathLengthExpr.Const(leftUpper), PathLengthExpr.Const(prefixLower)) => leftUpper >= prefixLower
          case _ => true
        lengthPossible && !((l.pattern, p.pattern) match
          case (Some(value), Some(prefix)) => value.definitelyDifferentPrefix(prefix)
          case _ => false)
      }
      if compatible.isEmpty then Vector.empty
      else Vector(l -> compatible)
    }
    val strata = compatibleStrata.map { (l, compatible) =>
        val retainedGuard = SizeExpr.maximum(compatible.map { p =>
          (l.pattern, p.pattern) match
            case (Some(value), Some(prefix)) if value.definitelyHasPrefix(prefix) =>
              SizeExpr.positive(p.cardinality.lower)
            case _ => SizeExpr.Zero
        }*)
        val soleStratumCoverage = l.exactLength.flatMap { length =>
          Option.when(compatibleStrata.count(_._1.exactLength.contains(length)) == 1) {
            SizeExpr.maximum(coverage.iterator.filter(_.covers(length)).map(_.minimumMatches).toVector*)
          }
        }.getOrElse(SizeExpr.Zero)
        val lower = SizeExpr.maximum(
          if retainedGuard != SizeExpr.Zero then SizeExpr.multiply(l.cardinality.lower, retainedGuard)
          else SizeExpr.Zero,
          soleStratumCoverage,
        )
        l.copy(cardinality = ResultSizeEstimate(l.cardinality.upper, lower))
    }
    val raw = SpatialType.fromStrata(strata)
    // A coverage fact is one aggregate witness for the selected relation, not
    // a separate witness for every compatible spatial stratum. Assigning it
    // to each stratum can multiply one selected path across disjoint patterns.
    // Multiple selected prefixes at one length may overlap, so their safe
    // combination is maximum. Distinct exact path lengths are disjoint and may
    // be added. When a covered length has exactly one stratum, the witness is
    // also attached there to retain the useful per-length projection; with two
    // or more patterns it remains aggregate-only. Pattern-specific retained
    // guards above remain attached because those are independent proofs.
    val coverageLower = SizeExpr.add(compatibleStrata.flatMap(_._1.exactLength).distinct.map { length =>
      SizeExpr.maximum(coverage.iterator.filter(_.covers(length)).map(_.minimumMatches).toVector*)
    }*)
    charge(SpatialType.reduce(raw.copy(size = ResultSizeEstimate(
      SizeExpr.minimum(raw.size.upper, left.size.upper),
      SizeExpr.maximum(raw.size.lower, coverageLower),
    ))), left, prefixes)(
      SizeExpr.multiply(left.size.upper, prefixes.size.upper),
      operationKind = SpatialCostOperation.Restriction)

  private def affineFiber(value: SpaceValue, prefix: SpatialPattern): Option[SpatialPattern] =
    if prefix.items.size != 1 || value.paths.isEmpty || !value.paths.forall(_.items.size == 2) then None
    else
      val rows = value.paths.toVector.flatMap { path =>
        for
          input <- path.items.head.show.toIntOption
          output <- path.items(1).show.toIntOption
        yield input -> output
      }
      if rows.size != value.paths.size then None
      else
        val mapping = rows.toMap
        val deltas = rows.map((input, output) => output - input).distinct
        val keys = mapping.keys.toVector.sorted
        if mapping.size != rows.size || deltas.size != 1 || keys.isEmpty || keys != (keys.head to keys.last).toVector then None
        else prefix.items.head match
          case SpatialItem.Constant(item) =>
            item.show.toIntOption.flatMap(mapping.get).map(output =>
              SpatialPattern(Vector(SpatialItem.Constant(PathItem(output.toString)))))
          case SpatialItem.Affine(variable, offset, minimum, maximum)
              if minimum + offset >= keys.head && maximum + offset <= keys.last =>
            Some(SpatialPattern(Vector(SpatialItem.Affine(variable, offset + deltas.head, minimum, maximum))))
          case _ => None

  private def unwrap(sourceExpression: Space, source: SpatialType, prefix: SpatialPathType): SpatialType =
    sourceExpression match
      case Space.Literal(value) if prefix.patterns.size == 1 =>
        affineFiber(value, prefix.patterns.head) match
          case Some(pattern) => SpatialType.fromStrata(Vector(SpatialStratum(
            PathLengthEstimate.exact(PathLengthExpr.const(pattern.length)),
            ResultSizeEstimate.exact(SizeExpr.One), Some(pattern))))
          case None => unwrapGeneral(source, prefix)
      case _ => unwrapGeneral(source, prefix)

  private def unwrapGeneral(source: SpatialType, prefix: SpatialPathType): SpatialType =
    // All optimized backends descend the prefix and then retain the selected
    // subtrie by reference. The root visit makes the empty prefix cost one.
    val prefixNodes = SizeExpr.add(SizeExpr.One,
      prefix.length.upper.annotatedBound(Z3BoundDirection.Upper)
        .fold[SizeExpr](SizeExpr.symbol(s"pathLen(${prefix.length.show})"))(SizeExpr.const))
    val strata = for
      value <- source.strata
      prefixPattern <- if prefix.patterns.nonEmpty then prefix.patterns else Vector.empty
      if !value.pattern.exists(_.definitelyDifferentPrefix(prefixPattern))
      prefixLength <- exactLength(prefix.length).toVector
      if mayHaveLengthAtLeast(value.length, prefixLength)
    yield
      val retained = value.pattern.exists(_.definitelyHasPrefix(prefixPattern))
      SpatialStratum(
        PathLengthEstimate(
          PathLengthExpr.positiveDifference(value.length.lower, prefix.length.upper),
          PathLengthExpr.positiveDifference(value.length.upper, prefix.length.lower)
        ),
        ResultSizeEstimate(value.cardinality.upper, if retained then value.cardinality.lower else SizeExpr.Zero),
        value.pattern.map(_.drop(prefixLength))
      )
    if strata.nonEmpty then
      val raw = SpatialType.fromStrata(strata)
      charge(SpatialType.reduce(raw.copy(size = ResultSizeEstimate(
        SizeExpr.minimum(raw.size.upper, source.size.upper), raw.size.lower))), source)(prefixNodes,
        operationKind = SpatialCostOperation.Unwrap)
    else
      val length = PathLengthEstimate(
        PathLengthExpr.positiveDifference(source.pathLength.lower, prefix.length.upper),
        PathLengthExpr.positiveDifference(source.pathLength.upper, prefix.length.lower)
      )
      charge(SpatialType.fromStrata(Vector(SpatialStratum(
        length, ResultSizeEstimate(source.size.upper, SizeExpr.Zero)))), source)(prefixNodes,
        operationKind = SpatialCostOperation.Unwrap)

  private def tails(source: SpatialType, intersection: Boolean): SpatialType =
    val strata = source.strata.flatMap { value =>
      Option.when(mayBeHeaded(value.length))(SpatialStratum(
        PathLengthEstimate(
          PathLengthExpr.positiveDifference(value.length.lower, PathLengthExpr.One),
          PathLengthExpr.positiveDifference(value.length.upper, PathLengthExpr.One)
        ),
        ResultSizeEstimate(value.cardinality.upper,
          if intersection || !definitelyHeaded(value.length) then SizeExpr.Zero
          else SizeExpr.positive(value.cardinality.lower)),
        value.pattern.map(_.tail)
      ))
    }
    val raw = SpatialType.fromStrata(strata)
    charge(SpatialType.reduce(raw.copy(size = ResultSizeEstimate(
      SizeExpr.minimum(raw.size.upper, source.size.upper), raw.size.lower))), source)(source.size.upper, raw.size.upper)

  private def closure(source: SpatialType, prefixes: Boolean, suffixes: Boolean, includeEpsilon: Boolean): SpatialType =
    val strata = source.strata.flatMap { value =>
      value.pattern match
        case Some(pattern) =>
          val start = if includeEpsilon then 0 else 1
          (start to pattern.length).map { length =>
            val result = if prefixes then pattern.take(length) else if suffixes then SpatialPattern(pattern.items.takeRight(length))
              else SpatialPattern(pattern.items.drop(pattern.length - length))
            SpatialStratum(PathLengthEstimate.exact(PathLengthExpr.const(length)),
              ResultSizeEstimate(value.cardinality.upper, SizeExpr.positive(value.cardinality.lower)), Some(result))
          }
        case None => Vector(SpatialStratum(
          PathLengthEstimate(if includeEpsilon then PathLengthExpr.Zero else PathLengthExpr.One, value.length.upper),
          ResultSizeEstimate(SizeExpr.Infinity, SizeExpr.Zero)
        ))
    }
    val result = SpatialType.fromStrata(capStrata(strata))
    charge(result, source)(SizeExpr.multiply(source.size.upper, source.pathLength.upper match
      case PathLengthExpr.Const(value) => SizeExpr.const(value)
      case _ => SizeExpr.Infinity), result.size.upper)

  private def matchIfEmpty(space: Space): Option[(Space, Space)] = space match
    case Space.Iteration(
          Space.Subtraction(
            Space.Singleton(Path.Constant(sentinel)),
            Space.Iteration(innerSource, innerHead, _, Space.Singleton(Path.Deref(emittedHead)))
          ), _, _, fallback
        ) if sentinel.items.length == 1 && innerHead == emittedHead =>
      innerSource match
        case Space.Composition(Space.Singleton(Path.Constant(prefix)), condition) if prefix == sentinel => Some(condition -> fallback)
        case Space.Wrap(condition, Path.Constant(prefix)) if prefix == sentinel => Some(condition -> fallback)
        case _ => None
    case _ => None

  /** Number of distinct first-item groups represented by a stratum.  Iteration
    * visits groups, not paths: a relation whose first item is the constant
    * `edge` has one group regardless of its edge cardinality.  Affine items
    * retain a finite domain cap; only unconstrained items fall back to the
    * path-count upper bound.
    */
  private def iterationGroups(stratum: SpatialStratum, definitelyNonEmptyPath: Boolean): ResultSizeEstimate =
    val count = stratum.cardinality
    val upper = stratum.pattern.flatMap(_.items.headOption) match
      case Some(SpatialItem.Constant(_)) => SizeExpr.positive(count.upper)
      case Some(SpatialItem.Affine(_, _, minimum, maximum)) =>
        SizeExpr.minimum(count.upper, SizeExpr.const(BigInt(maximum) - BigInt(minimum) + 1))
      case _ => count.upper
    ResultSizeEstimate(upper,
      if definitelyNonEmptyPath then SizeExpr.positive(count.lower) else SizeExpr.Zero)

  /** Cardinality of one tail fiber selected by Iteration.  A constant head
    * selects the whole represented stratum; otherwise a visited group is known
    * non-empty but may contain any number of the source paths.
    */
  private def iterationTail(stratum: SpatialStratum, definitelyNonEmptyPath: Boolean): ResultSizeEstimate =
    val lower = if definitelyNonEmptyPath then SizeExpr.positive(stratum.cardinality.lower) else SizeExpr.Zero
    stratum.pattern.flatMap(_.items.headOption) match
      case Some(SpatialItem.Constant(_)) => ResultSizeEstimate(stratum.cardinality.upper, lower)
      case _ => ResultSizeEstimate(stratum.cardinality.upper, lower)

  /** Analyze the leaf of a canonical nested iterator chain for one source
    * path.  Such a chain is a map over paths, not a Cartesian product of the
    * maximum sizes of every intermediate tail fiber.  Returning `None` keeps
    * the general grouped-iteration transfer for templates that stop before
    * consuming the complete path or iterate some unrelated space.
    */
  private def pointwiseIterationLeaf(
    body: Space,
    currentRest: SpaceMention,
    remainingPattern: Option[SpatialPattern],
    remainingLength: Int,
    assumptions: SpatialAssumptions,
    routines: PartialFunction[RoutinePtr, Routine],
    active: Set[RoutinePtr]
  ): Option[SpatialType] =
    if remainingLength == 0 then Some(analyze(body, assumptions, routines, active))
    else body match
      case Space.Iteration(Space.Mention(source), symbol, nextRest, nextBody) if source == currentRest =>
        val headPattern = remainingPattern.flatMap(_.items.headOption).map(item => SpatialPattern(Vector(item)))
        val tailPattern = remainingPattern.map(_.tail)
        val headType = SpatialPathType(PathLengthEstimate.exact(PathLengthExpr.One), headPattern.toVector)
        val tailType = SpatialType.fromStrata(Vector(SpatialStratum(
          PathLengthEstimate.exact(PathLengthExpr.const(remainingLength - 1)),
          ResultSizeEstimate.exact(SizeExpr.One),
          tailPattern,
        )))
        val nested = assumptions.copy(
          spaces = assumptions.spaces.updated(nextRest, tailType),
          paths = assumptions.paths.updated(symbol, headType),
        )
        pointwiseIterationLeaf(nextBody, nextRest, tailPattern, remainingLength - 1, nested, routines, active)
      case _ => None

  private def pointwiseIterationUpper(
    source: SpatialType,
    symbol: PathRef,
    rest: SpaceMention,
    body: Space,
    assumptions: SpatialAssumptions,
    routines: PartialFunction[RoutinePtr, Routine],
    active: Set[RoutinePtr]
  ): Option[SizeExpr] =
    val bounds = source.strata.map { stratum =>
      stratum.exactLength.filter(_ > 0).flatMap { length =>
        val headPattern = stratum.pattern.flatMap(_.items.headOption).map(item => SpatialPattern(Vector(item)))
        val tailPattern = stratum.pattern.map(_.tail)
        val headType = SpatialPathType(PathLengthEstimate.exact(PathLengthExpr.One), headPattern.toVector)
        val tailType = SpatialType.fromStrata(Vector(SpatialStratum(
          PathLengthEstimate.exact(PathLengthExpr.const(length - 1)),
          ResultSizeEstimate.exact(SizeExpr.One),
          tailPattern,
        )))
        val nested = assumptions.copy(
          spaces = assumptions.spaces.updated(rest, tailType),
          paths = assumptions.paths.updated(symbol, headType),
        )
        pointwiseIterationLeaf(body, rest, tailPattern, length - 1, nested, routines, active)
          .map(leaf => SizeExpr.multiply(stratum.cardinality.upper, leaf.size.upper))
      }
    }
    Option.when(bounds.forall(_.nonEmpty))(SizeExpr.add(bounds.flatten*))

  /** Bound a dependent relation lookup without enumerating either operand.
    * Iterator heads select relation fibers; the selected fibers are capped by
    * the relation's inferred maximum degree. A prefix-coverage annotation also
    * proves a non-empty (or quantitatively covered) result fiber. */
  private def dependentFiberBound(
    source: SpatialType,
    symbol: PathRef,
    body: Space,
    assumptions: SpatialAssumptions,
  ): Option[ResultSizeEstimate] = body match
    case Space.Unwrap(Space.Mention(relation), Path.Deref(prefix)) if prefix == symbol =>
      assumptions.spaces.get(relation).map { relationType =>
        val groups = source.strata.map(stratum =>
          iterationGroups(stratum, definitelyHeaded(stratum.length)))
        val selectedKeys = ResultSizeEstimate(
          SizeExpr.add(groups.map(_.upper)*),
          SizeExpr.maximum(groups.map(_.lower)*),
        )
        val degree = relationType.fiberDegree(prefixLength = 1)
        val upper = SizeExpr.minimum(
          relationType.size.upper,
          SizeExpr.multiply(selectedKeys.upper, degree.maximum.upper),
        )
        val witnesses = assumptions.prefixCoverage.iterator
          .filter(fact => fact.prefix == symbol && fact.space == relation)
          .map(fact => SizeExpr.maximum(fact.minimumMatches, degree.minimum.lower))
          .toVector
        val lower =
          if witnesses.isEmpty then SizeExpr.Zero
          else SizeExpr.multiply(SizeExpr.positive(selectedKeys.lower), SizeExpr.maximum(witnesses*))
        ResultSizeEstimate(upper, lower)
      }
    case _ => None

  private def conditional(condition: SpatialType, ifZero: SpatialType, ifNonZero: SpatialType): SpatialType =
    val exactCondition = Option.when(condition.size.exact)(condition.size.upper)
    exactCondition match
      case None => SpatialType.reduce(union(ifZero, ifNonZero).copy(size = ResultSizeEstimate(
        SizeExpr.maximum(ifZero.size.upper, ifNonZero.size.upper),
        SizeExpr.minimum(ifZero.size.lower, ifNonZero.size.lower)
      )))
      case Some(test) =>
        val groupedZero = ifZero.strata.groupBy(value => value.length -> value.pattern)
        val groupedNonZero = ifNonZero.strata.groupBy(value => value.length -> value.pattern)
        val keys = groupedZero.keySet ++ groupedNonZero.keySet
        val strata = keys.toVector.map { key =>
          def cardinality(group: Option[Vector[SpatialStratum]]): ResultSizeEstimate =
            group.fold(ResultSizeEstimate.empty)(values => SpatialType.fromStrata(values).size)
          val zero = cardinality(groupedZero.get(key))
          val nonzero = cardinality(groupedNonZero.get(key))
          val prototype = groupedZero.get(key).flatMap(_.headOption).orElse(groupedNonZero.get(key).flatMap(_.headOption)).get
          prototype.copy(cardinality = ResultSizeEstimate(
            SizeExpr.ifZero(test, zero.upper, nonzero.upper),
            SizeExpr.ifZero(test, zero.lower, nonzero.lower)
          ))
        }
        SpatialType.fromStrata(strata, sizeOverride = Some(ResultSizeEstimate(
          SizeExpr.ifZero(test, ifZero.size.upper, ifNonZero.size.upper),
          SizeExpr.ifZero(test, ifZero.size.lower, ifNonZero.size.lower)
        )))

  private def fixpoint(
    initial: Space,
    variable: SpaceMention,
    step: Space,
    assumptions: SpatialAssumptions,
    routines: PartialFunction[RoutinePtr, Routine],
    active: Set[RoutinePtr],
  ): SpatialType =
    def nodes(value: Space, remaining: Int): Int =
      if remaining <= 0 then 1
      else value match
        case Space.Empty | Space.Mention(_) | Space.Singleton(_) | Space.Literal(_) |
             Space.GroundedPS(_, _) => 1
        case Space.Call(_, _, mentions) => 1 + mentions.foldLeft(0) { (sum, child) =>
          sum + nodes(child, remaining - sum - 1)
        }
        case binary @ (Space.Union(_, _) | Space.Intersection(_, _) |
             Space.Subtraction(_, _) | Space.Restriction(_, _) |
             Space.Raffination(_, _) | Space.Composition(_, _)) =>
          val (left, right) = binary match
            case Space.Union(l, r) => l -> r
            case Space.Intersection(l, r) => l -> r
            case Space.Subtraction(l, r) => l -> r
            case Space.Restriction(l, r) => l -> r
            case Space.Raffination(l, r) => l -> r
            case Space.Composition(l, r) => l -> r
          val leftSize = nodes(left, remaining - 1)
          1 + leftSize + nodes(right, remaining - leftSize - 1)
        case Space.Iteration(source, _, _, body) =>
          val sourceSize = nodes(source, remaining - 1)
          1 + sourceSize + nodes(body, remaining - sourceSize - 1)
        case Space.Fold(source, _, _, _, _, body, _) =>
          val sourceSize = nodes(source, remaining - 1)
          1 + sourceSize + nodes(body, remaining - sourceSize - 1)
        case Space.Fixpoint(seed, _, body) =>
          val seedSize = nodes(seed, remaining - 1)
          1 + seedSize + nodes(body, remaining - seedSize - 1)
        case unary @ (Space.Wrap(_, _) | Space.Unwrap(_, _) | Space.TailsUnion(_) |
             Space.TailsIntersection(_) | Space.PrefixClosure(_) |
             Space.SuffixClosure(_) | Space.TailsClosure(_) |
             Space.GroundedSS(_, _) | Space.Range(_, _, _)) =>
          val source = unary match
            case Space.Wrap(s, _) => s
            case Space.Unwrap(s, _) => s
            case Space.TailsUnion(s) => s
            case Space.TailsIntersection(s) => s
            case Space.PrefixClosure(s) => s
            case Space.SuffixClosure(s) => s
            case Space.TailsClosure(s) => s
            case Space.GroundedSS(s, _) => s
            case Space.Range(s, _, _) => s
          1 + nodes(source, remaining - 1)
    val budget = assumptions.config.fixpointAstBudget
    if nodes(initial, budget) + nodes(step, budget) > budget then
      return SpatialType.top.copy(cost = SpatialCostEstimate.unknown)
    var current = analyze(initial, assumptions, routines, active)
    val seedCost = current.cost
    var lastStepCost = SpatialCostEstimate.zero
    def costed(value: SpatialType): SpatialType =
      val roundUpper = value.size.upper match
        case SizeExpr.Infinity => SizeExpr.symbol(s"rounds(${variable.s})")
        case finite => SizeExpr.add(finite, SizeExpr.One)
      val repeated = SpatialCostEstimate.withRounds(
        SpatialCostEstimate.scale(lastStepCost, SizeExpr.One, roundUpper),
        SizeExpr.One, roundUpper)
      value.copy(cost = SpatialCostEstimate.sequential(seedCost, repeated))
    var iteration = 0
    while iteration < assumptions.config.fixpointIterations do
      val nested = assumptions.copy(spaces = assumptions.spaces.updated(variable, current))
      val next = analyze(step, nested, routines, active)
      lastStepCost = next.cost
      val candidate = union(current, next)
      if SpatialType.lessOrEqual(candidate, current) then return costed(current)
      iteration += 1
      if iteration >= assumptions.config.fixpointWidenAfter then
        val widened = SpatialType.widenCardinalities(candidate)
        val widenedAssumptions = assumptions.copy(spaces = assumptions.spaces.updated(variable, widened))
        val widenedStep = analyze(step, widenedAssumptions, routines, active)
        lastStepCost = widenedStep.cost
        val post = union(widened, widenedStep)
        if SpatialType.lessOrEqual(post, widened) then return costed(widened)
        current = post
      else current = candidate
    // A finite cap is a resource guard, never a semantic assumption. If the
    // post-fixpoint check did not succeed, forget every component.
    SpatialType.top.copy(cost = SpatialCostEstimate.unknown)

  private def analyze(
    space: Space,
    assumptions: SpatialAssumptions,
    routines: PartialFunction[RoutinePtr, Routine],
    active: Set[RoutinePtr]
  ): SpatialType =
    analysisFuel.value match
      case Some(fuel) if fuel.remaining <= 0 =>
        return SpatialType.top.copy(cost = SpatialCostEstimate.unknown)
      case Some(fuel) => fuel.remaining -= 1
      case None => ()
    def rec(next: Space): SpatialType = analyze(next, assumptions, routines, active)
    val result = space match
      case Space.Empty => SpatialType.empty
      case Space.Mention(mention) => assumptions.spaces.get(mention).map(_.copy(cost = SpatialCostEstimate.zero)).getOrElse(
        SpatialType.fromStrata(Vector(SpatialStratum(
          ResultPathLength.estimate(space, assumptions.lengthAssumptions, assumptions.pathLengthAssumptions,
            assumptions.sizeAssumptions),
          ResultSpaceSize.estimate(space, assumptions.sizeAssumptions)
        ))))
      case Space.Call(name, refs, mentions) if routines.isDefinedAt(name) && !active(name) =>
        val routine = routines(name)
        val pathValues = refs.map(path(_, assumptions, routines, active))
        val spaceValues = mentions.map(rec)
        val nested = assumptions.copy(
          spaces = assumptions.spaces ++ routine.mentions.zip(spaceValues),
          paths = assumptions.paths ++ routine.refs.zip(pathValues)
        )
        val body =
          if Supercompiler.wellFoundedPartitionRecursion(routine, routines) then
            Supercompiler.lowerFixpointCalls(routine.body, routines)
          else routine.body
        SpatialRecursion.close(name, routine, spaceValues,
          analyze(body, nested, routines, active + name))
      case Space.Call(name, _, mentions)
          if routines.isDefinedAt(name) && active(name) &&
            Supercompiler.wellFoundedPartitionRecursion(routines(name), routines) =>
        val routine = routines(name)
        val nodeIndex = routine.body match
          case Space.Iteration(Space.Range(Space.Mention(nodes), 0, 1), _, _, _) =>
            routine.mentions.indexOf(nodes)
          case _ => -1
        if nodeIndex < 0 || nodeIndex >= mentions.length then SpatialType.top
        else
          val nodes = rec(mentions(nodeIndex))
          val pairLength = PathLengthEstimate(
            PathLengthExpr.add(nodes.pathLength.lower, nodes.pathLength.lower),
            PathLengthExpr.add(nodes.pathLength.upper, nodes.pathLength.upper),
          )
          SpatialType.fromStrata(Vector(SpatialStratum(
            pairLength,
            ResultSizeEstimate(nodes.size.upper, SizeExpr.Zero),
          )), sizeOverride = Some(ResultSizeEstimate(nodes.size.upper, SizeExpr.Zero)))
            .copy(cost = SpatialRecursion.marker(name))
      case Space.Call(name, _, _) =>
        SpatialType.fromStrata(Vector(SpatialStratum(
          ResultPathLength.estimate(space, assumptions.lengthAssumptions, assumptions.pathLengthAssumptions,
            assumptions.sizeAssumptions),
          ResultSpaceSize.estimate(space, assumptions.sizeAssumptions)
        ))).copy(cost = Option.when(active(name))(SpatialRecursion.marker(name)).getOrElse(SpatialCostEstimate.zero))
      case Space.Singleton(value) => singleton(path(value, assumptions, routines, active))
      case Space.Literal(value) =>
        val literal = SpatialType.exact(value, assumptions.config.patternLimit)
        withTrieConstructionCost(
          literal,
          SpatialCostEstimate.bounded(
            SizeExpr.const(value.paths.size), SizeExpr.const(value.paths.size),
            SizeExpr.const(value.paths.size), SizeExpr.const(value.paths.size)),
          graphDispatch = false,
        )
      case Space.Union(left, right) =>
        right match
          case candidate if matchIfEmpty(candidate).exists(_._1 == left) =>
            val fallback = matchIfEmpty(candidate).get._2
            conditional(rec(left), analyze(fallback, assumptions, routines, active), rec(left))
          case _ if matchIfEmpty(left).exists(_._1 == right) =>
            val fallback = matchIfEmpty(left).get._2
            conditional(rec(right), analyze(fallback, assumptions, routines, active), rec(right))
          case _ if left == right => rec(left)
          case _ => union(rec(left), rec(right))
      case Space.Intersection(left, right) =>
        if left == right then rec(left)
        else
          val leftType = rec(left)
          val rightType = rec(right)
          val leftDemand = zipperDemandPlan(left).filter(_.virtual)
          val rightDemand = zipperDemandPlan(right).filter(_.virtual)
          // If both sides are virtual there is no independent frontier to
          // bound either one; retain the compositional upper bound.
          val demandedLeft = (leftDemand, rightDemand) match
            case (Some(plan), None) => capZipperForDemand(leftType, rightType, plan.factor)
            case _ => leftType
          val demandedRight = (leftDemand, rightDemand) match
            case (None, Some(plan)) => capZipperForDemand(rightType, leftType, plan.factor)
            case _ => rightType
          val combined = intersection(demandedLeft, demandedRight)
          (leftDemand, rightDemand) match
            case (Some(plan), None) => capZipperIntersectionForDemand(combined, rightType, plan.factor)
            case (None, Some(plan)) => capZipperIntersectionForDemand(combined, leftType, plan.factor)
            case _ => combined
      case Space.Subtraction(left, right) =>
        if left == right then SpatialType.empty
        else subtraction(rec(left), rec(right))
      case Space.Restriction(left, prefixes) => restriction(left, prefixes, rec(left), rec(prefixes), assumptions)
      case Space.Raffination(left, prefixes) =>
        val l = rec(left)
        val p = rec(prefixes)
        val selected = restriction(left, prefixes, l.copy(cost = SpatialCostEstimate.zero),
          p.copy(cost = SpatialCostEstimate.zero), assumptions)
        val semantic = subtraction(l.copy(cost = SpatialCostEstimate.zero),
          selected.copy(cost = SpatialCostEstimate.zero)).copy(cost = SpatialCostEstimate.zero)
        charge(semantic, l, p)(
          SizeExpr.multiply(l.size.upper, p.size.upper),
          semantic.size.upper,
          operationKind = SpatialCostOperation.Raffination,
        )
      case Space.Composition(left, right) => composition(rec(left), rec(right))
      case iteration @ Space.Iteration(src, symbol, rest, body) =>
        matchIfEmpty(iteration) match
          case Some((condition, fallback)) => conditional(rec(condition), analyze(fallback, assumptions, routines, active), SpatialType.empty)
          case None =>
            val source = rec(src)
            val branchCosts = mutable.ArrayBuffer.empty[(ResultSizeEstimate, SpatialCostEstimate)]
            val branches = source.strata.flatMap { stratum =>
              if !mayBeHeaded(stratum.length) then Vector.empty
              else
                val definitelyNonEmptyPath = definitelyHeaded(stratum.length)
                val headPattern = stratum.pattern.flatMap(_.items.headOption).map(item => SpatialPattern(Vector(item)))
                val headType = SpatialPathType(PathLengthEstimate.exact(PathLengthExpr.One), headPattern.toVector)
                val tailLength = PathLengthEstimate(
                  PathLengthExpr.positiveDifference(stratum.length.lower, PathLengthExpr.One),
                  PathLengthExpr.positiveDifference(stratum.length.upper, PathLengthExpr.One)
                )
                val tailCardinality = iterationTail(stratum, definitelyNonEmptyPath)
                val tailType = SpatialType.fromStrata(Vector(SpatialStratum(tailLength, tailCardinality, stratum.pattern.map(_.tail))))
                val nested = assumptions.copy(
                  spaces = assumptions.spaces.updated(rest, tailType),
                  paths = assumptions.paths.updated(symbol, headType)
                )
                val branch = analyze(body, nested, routines, active)
                val groups = iterationGroups(stratum, definitelyNonEmptyPath)
                branchCosts += groups -> branch.cost
                branch.strata.map(value => value.copy(cardinality = ResultSizeEstimate(
                  SizeExpr.multiply(groups.upper, value.cardinality.upper),
                  SizeExpr.multiply(groups.lower, value.cardinality.lower)
                )))
            }
            val general = SpatialType.fromStrata(capStrata(branches, assumptions.config.patternLimit))
            val pointwise = pointwiseIterationUpper(source, symbol, rest, body, assumptions, routines, active) match
              case Some(upper) => capAggregateUpper(general, upper)
              case None => general
            val typed = dependentFiberBound(source, symbol, body, assumptions) match
              case Some(bound) =>
                val capped = capAggregateUpper(pointwise, bound.upper)
                SpatialType.reduce(capped.copy(size = capped.size.copy(
                  lower = SizeExpr.maximum(capped.size.lower, bound.lower),
                )))
              case None => pointwise
            val groups = source.shape.headCount
            val scaledBranches = SpatialCostEstimate.sequential(branchCosts.toSeq.map { (count, cost) =>
              SpatialCostEstimate.scale(cost, count.lower, count.upper)
            }*)
            charge(typed, source)(
              SizeExpr.add(source.size.upper, scaledBranches.workUpper, typed.size.upper),
              SizeExpr.add(scaledBranches.allocationUpper, typed.size.upper),
              operationKind = SpatialCostOperation.GroupCollect,
              roundsLower = groups.lower,
              roundsUpper = groups.upper,
            )
      case Space.Fold(src, initial, acc, symbol, rest, body, _) =>
        val source = rec(src)
        val initialType = path(initial, assumptions, routines, active)
        val nested = assumptions.copy(
          spaces = assumptions.spaces.updated(rest, source),
          paths = assumptions.paths.updated(acc, initialType).updated(symbol, SpatialPathType.length(1, symbol.s))
        )
        val branch = analyze(body, nested, routines, active)
        val optionalBranch = branch.copy(
          strata = branch.strata.map(stratum => stratum.copy(cardinality =
            ResultSizeEstimate(stratum.cardinality.upper, SizeExpr.Zero))),
          size = ResultSizeEstimate(SizeExpr.multiply(source.size.upper, branch.size.upper), SizeExpr.Zero),
        )
        charge(SpatialType.reduce(optionalBranch), source, branch)(
          SizeExpr.multiply(source.size.upper, branch.cost.workUpper))
      case Space.Fixpoint(initial, variable, step) =>
        fixpoint(initial, variable, step, assumptions, routines, active)
      case Space.Wrap(src, prefix) => composition(singleton(path(prefix, assumptions, routines, active)), rec(src))
      case Space.Unwrap(src, prefix) => unwrap(src, rec(src), path(prefix, assumptions, routines, active))
      case Space.TailsUnion(src) => tails(rec(src), intersection = false)
      case Space.TailsIntersection(src) => tails(rec(src), intersection = true)
      case Space.PrefixClosure(src) => closure(rec(src), prefixes = true, suffixes = false, includeEpsilon = false)
      case Space.SuffixClosure(src) => closure(rec(src), prefixes = false, suffixes = true, includeEpsilon = false)
      case Space.TailsClosure(src) => closure(rec(src), prefixes = false, suffixes = true, includeEpsilon = true)
      case Space.Range(src, start, end) =>
        val source = rec(src)
        val capacity = RangeBounds.cardinalityUpperBound(start, end).map(SizeExpr.const)
        val total =
          if source.size.exact then ResultSizeEstimate.exact(SizeExpr.range(source.size.upper, start, end))
          else ResultSizeEstimate(
            capacity.fold(source.size.upper)(SizeExpr.minimum(source.size.upper, _)),
            SizeExpr.Zero,
          )
        charge(SpatialType.fromStrata(
          source.strata.map { value =>
            val upper = capacity.fold(value.cardinality.upper)(SizeExpr.minimum(value.cardinality.upper, _))
            value.copy(cardinality = ResultSizeEstimate(upper, SizeExpr.Zero))
          },
          sizeOverride = Some(total)
        ), source)(source.size.upper, total.upper, operationKind = SpatialCostOperation.Range)
      case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) =>
        SpatialType.fromStrata(Vector(SpatialStratum(
          ResultPathLength.estimate(space, assumptions.lengthAssumptions, assumptions.pathLengthAssumptions,
            assumptions.sizeAssumptions),
          ResultSpaceSize.estimate(space, assumptions.sizeAssumptions)
        ))).copy(cost = SpatialCostEstimate.unknown)
    analysisTrace.value.foreach(_ += SpatialNodeAnalysis(
      space, result, assumptions.spaces, assumptions.paths))
    result
