package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}

class SpatialTypeTest extends FunSuite:
  private val noPaths = PathContextMap(Map.empty)
  private val noRoutines = PartialFunction.empty[RoutinePtr, Routine]

  private def path(length: Int, prefix: String): PathValue =
    PathValue(List.tabulate(length)(index => PathItem(s"${prefix}_$index")))

  test("spatial membership distinguishes signature envelopes from full gamma") {
    val k = PathItem("k")
    val declared = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.const(2)),
      ResultSizeEstimate(SizeExpr.const(3), SizeExpr.One),
      Some(SpatialPattern(Vector(SpatialItem.Constant(k), SpatialItem.Unknown("v"))))
    )))
    val one = SpaceValue(PathValue(List(k, PathItem("a"))))
    val two = SpaceValue(PathValue(List(k, PathItem("a"))), PathValue(List(k, PathItem("b"))))

    assert(SpatialMembership.satisfies(one, declared))
    assert(SpatialMembership.gammaMember(two, declared))
    assert(SpatialType.lessOrEqual(SpatialType.exact(one), declared))
    assert(!SpatialMembership.satisfies(SpaceValue(PathValue(List(PathItem("z"), PathItem("a")))), declared))
    assert(!SpatialMembership.satisfies(SpaceValue(PathValue(List(k, PathItem("a"), PathItem("b")))), declared))

    val twoRequiredClasses = SpatialType.fromStrata(Vector(
      SpatialStratum(PathLengthEstimate.exact(PathLengthExpr.const(1)), ResultSizeEstimate.exact(SizeExpr.One),
        Some(SpatialPattern(Vector(SpatialItem.Constant(PathItem("a")))))),
      SpatialStratum(PathLengthEstimate.exact(PathLengthExpr.const(1)), ResultSizeEstimate.exact(SizeExpr.One),
        Some(SpatialPattern(Vector(SpatialItem.Constant(PathItem("b"))))))
    ), sizeOverride = Some(ResultSizeEstimate(SizeExpr.const(2), SizeExpr.One)))
    val onlyA = SpaceValue(PathValue(List(PathItem("a"))))
    assert(SpatialMembership.satisfies(onlyA, twoRequiredClasses))
    assert(!SpatialMembership.gammaMember(onlyA, twoRequiredClasses))
  }

  test("generated membership corpus is sound and complete for a declared pattern") {
    val k = PathItem("k")
    val declared = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.const(2)),
      ResultSizeEstimate(SizeExpr.const(3), SizeExpr.One),
      Some(SpatialPattern(Vector(SpatialItem.Constant(k), SpatialItem.Unknown("value"))))
    )))
    val universe = Vector("a", "b", "c").map(item => PathValue(List(k, PathItem(item)))) ++ Vector(
      PathValue(List(PathItem("z"), PathItem("a"))),
      PathValue(List(k)),
    )
    var accepted = 0
    var rejected = 0
    (0 until (1 << universe.size)).foreach { mask =>
      val value = SpaceValue(universe.indices.collect { case index if (mask & (1 << index)) != 0 => universe(index) }.toSet)
      val expected = value.paths.size >= 1 && value.paths.size <= 3 &&
        value.paths.forall(path => path.items.size == 2 && path.items.head == k)
      assertEquals(SpatialMembership.gammaMember(value, declared), expected, value.pretty)
      assertEquals(SpatialMembership.satisfies(value, declared), expected, value.pretty)
      if expected then accepted += 1 else rejected += 1
    }
    assertEquals(accepted, 7)
    assertEquals(rejected, 25)
  }

  test("bounded head shape distinguishes one fat fiber from four heads") {
    val fat = SpatialType.exact(SpaceValue(
      PathValue(List(PathItem("a"), PathItem("0"))),
      PathValue(List(PathItem("a"), PathItem("1"))),
      PathValue(List(PathItem("a"), PathItem("2"))),
      PathValue(List(PathItem("a"), PathItem("3"))),
    ))
    val wide = SpatialType.exact(SpaceValue(
      PathValue(List(PathItem("a"), PathItem("0"))),
      PathValue(List(PathItem("b"), PathItem("0"))),
      PathValue(List(PathItem("c"), PathItem("0"))),
      PathValue(List(PathItem("d"), PathItem("0"))),
    ))
    assertEquals(fat.shape.headCount, ResultSizeEstimate.exact(SizeExpr.One))
    assertEquals(wide.shape.headCount, ResultSizeEstimate.exact(SizeExpr.const(4)))
    assertEquals(fat.fiberDegree(1).keys, ResultSizeEstimate.exact(SizeExpr.One))
    assertEquals(wide.fiberDegree(1).keys, ResultSizeEstimate.exact(SizeExpr.const(4)))
  }

  test("spatial specialization is guarded and fires only from an annotation") {
    val input = SpaceMention("input")
    val literal = SpaceValue(PathValue(List(PathItem("kept"))))
    val routine = Routine(RoutinePtr("guarded"), Vector.empty, Vector(input),
      Space.Intersection(Space.Mention(input), Space.Literal(literal)))
    val annotated = SpatialCompilation.specialize(routine,
      SpatialRoutineAnnotations(spaces = Map(input -> SpatialType.empty)))
    val unannotated = SpatialCompilation.specialize(routine, SpatialRoutineAnnotations())

    assertEquals(annotated.residual.body, Space.Empty)
    assert(annotated.facts.nonEmpty)
    assert(annotated.applicableTo(Map(input -> SpaceValue())))
    assert(!annotated.applicableTo(Map(input -> literal)))
    assertNotEquals(unannotated.residual.body, Space.Empty)

    val accepted = SpatialCompilation.selectApplicable(
      routine,
      SpatialRoutineAnnotations(spaces = Map(input -> SpatialType.empty)),
      Map(input -> SpaceValue()),
      Map.empty,
    )
    val rejected = SpatialCompilation.selectApplicable(
      routine,
      SpatialRoutineAnnotations(spaces = Map(input -> SpatialType.empty)),
      Map(input -> literal),
      Map.empty,
    )
    assert(accepted.usedSpatialSpecialization)
    assertEquals(accepted.routine.body, Space.Empty)
    assert(!rejected.usedSpatialSpecialization)
    assertEquals(rejected.routine, routine)

    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map(input -> SpaceValue()))
    assertEquals(eval(annotated.residual.body), eval(routine.body))
  }

  test("production compilation selects an applicable guarded spatial residual") {
    val input = SpaceMention("compiled_input")
    val a = PathValue(List(PathItem("a")))
    val argument = SpaceValue(a, PathValue(List(PathItem("b"))))
    val routine = Routine(
      RoutinePtr("compiled_spatial_residual"),
      Vector.empty,
      Vector(input),
      Space.Intersection(
        Space.Mention(input),
        Space.Singleton(Path.Constant(a)),
      ),
    )
    val compiled = Supercompiler.specialize(
      routine,
      spaceArgs = Map(input -> Space.Literal(argument)),
      buildGraph = false,
    )

    assert(compiled.report.spatialRewriteFacts.exists(_.isInstanceOf[SpatialRewriteFact.ConstantFolded]))
    assert(compiled.report.changed)
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map(input -> argument))
    assertEquals(eval(compiled.routine.body), eval(routine.body))
  }

  test("iteration cost records groups and reference/trie models differ") {
    val source = Space.Literal(SpaceValue(
      PathValue(List(PathItem("a"), PathItem("0"))),
      PathValue(List(PathItem("b"), PathItem("0"))),
      PathValue(List(PathItem("c"), PathItem("0"))),
      PathValue(List(PathItem("d"), PathItem("0"))),
    ))
    val head = PathRef("head")
    val tails = SpaceMention("tails")
    val result = SpatialTypeAnalysis.output(Space.Iteration(source, head, tails, Space.Singleton(Path.Deref(head))))
    assertEquals(result.cost.roundsLower.annotatedValue, Some(BigInt(4)))
    assertEquals(result.cost.roundsUpper.annotatedValue, Some(BigInt(4)))
    assert(result.cost.workUpper.annotatedBound(Z3BoundDirection.Lower).exists(_ > 0))

    val left = SpatialType.lengths(2 -> ResultSizeEstimate.exact(SizeExpr.const(256)))
    val right = SpatialType.lengths(2 -> ResultSizeEstimate.exact(SizeExpr.const(256)))
    val fallback = SpatialCostInterval(SizeExpr.Zero, SizeExpr.const(65536), SizeExpr.Zero, SizeExpr.const(65536))
    val measures = Vector(SpatialCostMeasure(left), SpatialCostMeasure(right))
    val resultMeasure = SpatialCostMeasure(left)
    val referenceRestriction = SpatialCostModels.Reference.operation(
      SpatialCostOperation.Restriction, measures, resultMeasure, fallback)
    val trieRestriction = SpatialCostModels.Trie.operation(
      SpatialCostOperation.Restriction, measures, resultMeasure, fallback)
    assertNotEquals(referenceRestriction.workUpper, trieRestriction.workUpper)
  }

  test("law registry contains proved obligations and checked negative witnesses") {
    assert(SpatialLawRegistry.certificates.exists(_.verdict == SpatialLawVerdict.Proved))
    assert(SpatialLawRegistry.certificates.exists(_.verdict == SpatialLawVerdict.Refuted))

    val a = Space.Literal(SpaceValue(PathValue(List(PathItem("a")))))
    val empty = Space.Empty
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    val falseDistribution = Space.Subtraction(a, Space.Union(a, empty))
    val claimedRight = Space.Union(Space.Subtraction(a, a), Space.Subtraction(a, empty))
    assertNotEquals(eval(falseDistribution), eval(claimedRight))

    val ab = Space.Literal(SpaceValue(PathValue(List(PathItem("a"), PathItem("b")))))
    assertNotEquals(eval(Space.Restriction(ab, a)), eval(Space.Restriction(a, ab)))
  }

  test("spatial restriction retains compatible length strata and prefix witnesses") {
    val xs = SpaceMention("xs")
    val ys = SpaceMention("ys")
    val k = PathRef("k")
    val xsType = SpatialType.lengths(
      2 -> ResultSizeEstimate.exact(SizeExpr.const(5)),
      4 -> ResultSizeEstimate.exact(SizeExpr.const(7)),
      6 -> ResultSizeEstimate.exact(SizeExpr.const(9))
    )
    val assumptions = SpatialAssumptions(
      spaces = Map(xs -> xsType, ys -> SpatialType.empty),
      paths = Map(k -> SpatialPathType.length(3, "k")),
      prefixCoverage = Set(SpatialPrefixCoverage(k, xs, Set(4, 6)))
    )
    val expression = Space.TailsUnion(Space.Restriction(
      Space.Mention(xs),
      Space.Union(Space.Mention(ys), Space.Singleton(Path.Deref(k)))
    ))

    val result = SpatialTypeAnalysis.output(expression, assumptions).collapseByLength
    assertEquals(result.map(_.exactLength), Vector(Some(3), Some(5)))
    assertEquals(result.map(_.cardinality.lower), Vector(SizeExpr.One, SizeExpr.One))
    assertEquals(result.map(_.cardinality.upper), Vector(SizeExpr.const(7), SizeExpr.const(9)))

    val spatial = SpatialTypeAnalysis.output(expression, assumptions)
    assertEquals(spatial.size.lower, SizeExpr.const(2))
    assertEquals(spatial.size.upper, SizeExpr.const(16))
    val lengthPc = PathContextMap(Map(k -> PathValue(List("a", "b", "c").map(PathItem(_)))))
    assertEquals(spatial.pathLength.lower.evaluate(using lengthPc, SpaceContextMap(Map.empty), noRoutines), Some(BigInt(3)))
    assertEquals(spatial.pathLength.upper.evaluate(using lengthPc, SpaceContextMap(Map.empty), noRoutines), Some(BigInt(5)))

    val kValue = PathValue(List("a", "b", "c").map(PathItem(_)))
    val values = SpaceValue(
      (Vector.tabulate(5)(index => path(2, s"two_$index")) ++
       Vector(PathValue(kValue.items :+ PathItem("four"))) ++
       Vector.tabulate(6)(index => path(4, s"four_$index")) ++
       Vector(PathValue(kValue.items ++ List(PathItem("six_0"), PathItem("six_1"), PathItem("six_2")))) ++
       Vector.tabulate(8)(index => path(6, s"six_$index"))).toSet
    )
    given PathContext = PathContextMap(Map(k -> kValue))
    given SpaceContext = SpaceContextMap(Map(xs -> values, ys -> SpaceValue()))
    val actual = eval(expression)
    assertEquals(actual.paths.map(_.items.length), Set(3, 5))
    assert(spatial.size.lower.evaluate.exists(_ <= actual.paths.size))
    assert(spatial.size.upper.evaluate.exists(_ >= actual.paths.size))
  }

  test("quantitative prefix coverage preserves a symbolic restriction lower bound") {
    val source = SpaceMention("quantified_coverage_source")
    val prefix = PathRef("quantified_coverage_prefix")
    val sourceType = SpatialType.lengths(
      2 -> ResultSizeEstimate.exact(SizeExpr.const(10)))
    val result = SpatialTypeAnalysis.output(
      Space.Restriction(Space.Mention(source), Space.Singleton(Path.Deref(prefix))),
      SpatialAssumptions(
        spaces = Map(source -> sourceType),
        paths = Map(prefix -> SpatialPathType.length(1, "coverage")),
        prefixCoverage = Set(SpatialPrefixCoverage(
          prefix, source, lengths = Set(2), minimumMatches = SizeExpr.const(3))),
      ),
    )
    assertEquals(result.size, ResultSizeEstimate(SizeExpr.const(10), SizeExpr.const(3)))
  }

  test("one coverage witness is not duplicated across disjoint source strata") {
    val source = SpaceMention("aggregate_coverage_source")
    val prefix = PathRef("aggregate_coverage_prefix")
    val sourceValue = SpaceValue("a.x", "b.y")
    val expression = Space.Restriction(
      Space.Mention(source), Space.Singleton(Path.Deref(prefix)))
    val result = SpatialTypeAnalysis.output(
      expression,
      SpatialAssumptions(
        spaces = Map(source -> SpatialType.exact(sourceValue)),
        paths = Map(prefix -> SpatialPathType.length(1, "aggregate coverage")),
        prefixCoverage = Set(SpatialPrefixCoverage(prefix, source, minimumMatches = SizeExpr.One)),
      ),
    )

    assertEquals(result.size, ResultSizeEstimate(SizeExpr.const(2), SizeExpr.One))
    assertEquals(result.strata.map(_.cardinality.lower).toSet, Set(SizeExpr.Zero))
    given PathContext = PathContextMap(Map(prefix -> Syntax.parse("a")))
    given SpaceContext = SpaceContextMap(Map(source -> sourceValue))
    given PartialFunction[RoutinePtr, Routine] = noRoutines
    assertEquals(eval(expression), SpaceValue("a.x"))
  }

  test("encoded if-empty control has a piecewise exact spatial type") {
    val source = SpaceMention("control_source")
    val fallback = SpaceMention("control_fallback")
    val sourceCount = SizeExpr.symbol("S")
    val fallbackCount = SizeExpr.symbol("G")
    val assumptions = SpatialAssumptions(spaces = Map(
      source -> SpatialType.lengths(2 -> ResultSizeEstimate.exact(sourceCount)),
      fallback -> SpatialType.lengths(4 -> ResultSizeEstimate.exact(fallbackCount))
    ))
    val expression = Space.Union(Space.Mention(source), Space.Mention(source).on_empty(Space.Mention(fallback)))
    val result = SpatialTypeAnalysis.output(expression, assumptions)

    assertEquals(result.size.lower, SizeExpr.ifZero(sourceCount, fallbackCount, sourceCount))
    assertEquals(result.size.upper, SizeExpr.ifZero(sourceCount, fallbackCount, sourceCount))
    assertEquals(result.strataAt(2).head.cardinality.upper, SizeExpr.ifZero(sourceCount, SizeExpr.Zero, sourceCount))
    assertEquals(result.strataAt(4).head.cardinality.upper, SizeExpr.ifZero(sourceCount, fallbackCount, SizeExpr.Zero))

    Vector(
      SpaceValue() -> SpaceValue(path(4, "g0"), path(4, "g1")),
      SpaceValue(path(2, "s0"), path(2, "s1"), path(2, "s2")) -> SpaceValue(path(4, "ignored"))
    ).foreach { (sourceValue, fallbackValue) =>
      given PathContext = noPaths
      given SpaceContext = SpaceContextMap(Map(source -> sourceValue, fallback -> fallbackValue))
      given PartialFunction[RoutinePtr, Routine] = noRoutines
      val concreteAssumptions = SpatialAssumptions(spaces = Map(source -> SpatialType.exact(sourceValue), fallback -> SpatialType.exact(fallbackValue)))
      val concreteType = SpatialTypeAnalysis.output(expression, concreteAssumptions)
      val actual = eval(expression)
      assertEquals(concreteType.size.lower.evaluate, Some(BigInt(actual.paths.size)))
      assertEquals(concreteType.size.upper.evaluate, Some(BigInt(actual.paths.size)))
    }
  }

  test("iteration counts constant-headed fibers as groups rather than paths") {
    val source = SpaceMention("constant_head_source")
    val head = PathRef("constant_head")
    val rest = SpaceMention("constant_tail")
    val count = SizeExpr.symbol("N")
    val sourceType = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.const(2)),
      ResultSizeEstimate.exact(count),
      Some(SpatialPattern(Vector(
        SpatialItem.Constant(PathItem("edge")),
        SpatialItem.Unknown("target"),
      ))),
    )))
    val expression = Space.Iteration(
      Space.Mention(source), head, rest, Space.Singleton(Path.Deref(head)))
    val result = SpatialTypeAnalysis.output(expression, SpatialAssumptions(spaces = Map(source -> sourceType)))

    assertEquals(result.size, ResultSizeEstimate.exact(SizeExpr.positive(count)))
    assertEquals(result.pathLength, PathLengthEstimate.exact(PathLengthExpr.One))
  }

  test("nested full-path iterator chains are bounded as pointwise maps") {
    val source = SpaceMention("pointwise_source")
    val x = PathRef("x")
    val xs = SpaceMention("xs")
    val y = PathRef("y")
    val ys = SpaceMention("ys")
    val count = SizeExpr.symbol("N")
    val sourceType = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.const(2)),
      ResultSizeEstimate.exact(count),
      Some(SpatialPattern(Vector(SpatialItem.Unknown("x"), SpatialItem.Unknown("y")))),
    )))
    val leaf = Space.Union(
      Space.Singleton(Path.Constant(Syntax.parse("cux")) x Path.Deref(x)),
      Space.Singleton(Path.Constant(Syntax.parse("cux")) x Path.Deref(y)),
    )
    val expression = Space.Iteration(
      Space.Mention(source), x, xs,
      Space.Iteration(Space.Mention(xs), y, ys, leaf),
    )
    val result = SpatialTypeAnalysis.output(expression, SpatialAssumptions(spaces = Map(source -> sourceType)))

    val pointwiseCap = SizeExpr.multiply(count, SizeExpr.const(2))
    result.size.upper match
      case SizeExpr.Minimum(terms) => assert(terms.contains(pointwiseCap))
      case value => assertEquals(value, pointwiseCap)
    assertEquals(result.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(2)))
  }

  test("pure Game-of-Life neighbor arithmetic has eight length-two outputs") {
    val coordinate = LifeExample.neigh.refs.head
    val result = SpatialTypeAnalysis.outputRoutine(
      LifeExample.neigh,
      pathInputs = Map(coordinate -> SpatialPathType.numericPair("coord", -64, 64)),
      spaceInputs = Map.empty
    )
    val lengths = result.collapseByLength
    assertEquals(result.size, ResultSizeEstimate.exact(SizeExpr.const(8)))
    assertEquals(result.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(2)))
    assertEquals(lengths.map(_.exactLength), Vector(Some(2)))
    assertEquals(lengths.head.cardinality, ResultSizeEstimate.exact(SizeExpr.const(8)))
    assertEquals(result.strata.flatMap(_.pattern).map(_.show).toSet.size, 8)
  }

  test("finite Range windows clamp spatial strata and Game-of-Life rank witnesses") {
    val source = SpaceMention("spatial_range_source")
    val count = SizeExpr.symbol("spatialRangeN")
    val sourceType = SpatialType.fromStrata(Vector(
      SpatialStratum(
        PathLengthEstimate.exact(PathLengthExpr.One),
        ResultSizeEstimate(count, SizeExpr.Zero),
        Some(SpatialPattern(Vector(SpatialItem.Unknown("short")))),
      ),
      SpatialStratum(
        PathLengthEstimate.exact(PathLengthExpr.const(2)),
        ResultSizeEstimate(count, SizeExpr.Zero),
        Some(SpatialPattern(Vector(SpatialItem.Unknown("left"), SpatialItem.Unknown("right")))),
      ),
    ), sizeOverride = Some(ResultSizeEstimate(count, SizeExpr.Zero)))
    val assumptions = SpatialAssumptions(spaces = Map(source -> sourceType))
    val ranged = SpatialTypeAnalysis.output(Space.Range(Space.Mention(source), 2, 3), assumptions)
    val unitCap = SizeExpr.minimum(count, SizeExpr.One)

    assertEquals(ranged.size.lower, SizeExpr.Zero)
    assert(SizeExpr.provablyNoGreater(ranged.size.upper, unitCap), ranged.size.show)
    assert(SizeExpr.provablyNoGreater(ranged.size.upper, SizeExpr.One), ranged.size.show)
    assert(ranged.strata.nonEmpty)
    assert(ranged.strata.forall(stratum =>
      SizeExpr.provablyNoGreater(stratum.cardinality.upper, SizeExpr.One)), ranged.size.show)

    val exactlyThree = SpatialTypeAnalysis.output(
      LifeExample.exactly(Space.Mention(source), 3),
      assumptions,
    )
    assert(SizeExpr.provablyNoGreater(exactlyThree.size.upper, SizeExpr.One), exactlyThree.size.show)
    assert(exactlyThree.size.upper.nodeCount(129) <= 128, exactlyThree.size.show)
  }

  test("spatial types propagate through five Game-of-Life steps without result feedback") {
    val field = SpaceValue("Cell.0.1", "Cell.1.2", "Cell.2.0", "Cell.2.1", "Cell.2.2")
    val fieldMention = SpaceMention("initial_glider")
    val fiveSteps = (1 to 5).foldLeft[Space](Space.Mention(fieldMention)) { (current, _) =>
      LifeExample.nextStep.name(current)
    }
    given PathContext = noPaths
    given SpaceContext = SpaceContextMap(Map(fieldMention -> field))
    given PartialFunction[RoutinePtr, Routine] = mod(LifeExample.neigh, LifeExample.nextStep)

    val outputType = SpatialTypeAnalysis.output(
      fiveSteps,
      SpatialAssumptions(spaces = Map(fieldMention -> SpatialType.exact(field))),
      summon[PartialFunction[RoutinePtr, Routine]],
    )
    // Evaluation is deliberately downstream: it validates but cannot feed the
    // annotation or any intermediate abstract step.
    val actual = eval(fiveSteps)
    assertEquals(outputType.exactValue, None)
    assert(outputType.size.lower.annotatedBound(Z3BoundDirection.Lower).exists(_ <= actual.paths.size))
    assert(outputType.size.upper.annotatedBound(Z3BoundDirection.Upper).forall(_ >= actual.paths.size))
    assertEquals(outputType.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(3)))
    assertEquals(actual.paths.size, 5)
  }

  test("exact spatial types expose graph fiber degree statistics") {
    val graph = SpatialType.exact(SpaceValue("edge.a.b", "edge.a.c", "edge.b.c"))
    val degree = graph.fiberDegree(prefixLength = 2)
    assertEquals(degree.minimum, ResultSizeEstimate.exact(SizeExpr.One))
    assertEquals(degree.maximum, ResultSizeEstimate.exact(SizeExpr.const(2)))
    assertEquals(degree.edges, ResultSizeEstimate.exact(SizeExpr.const(3)))
    assertEquals(degree.keys, ResultSizeEstimate.exact(SizeExpr.const(2)))
    assertEquals(degree.averageShow, "3..3 / 2..2")
  }

  test("symbolic graph patterns infer key and fiber-degree arithmetic") {
    val relation = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.const(2)),
      ResultSizeEstimate.exact(SizeExpr.const(8)),
      Some(SpatialPattern(Vector(
        SpatialItem.Affine("key", 0, 0, 3),
        SpatialItem.Affine("value", 0, 0, 3),
      ))),
    )))
    val degree = relation.fiberDegree(prefixLength = 1)
    assertEquals(degree.keys, ResultSizeEstimate(SizeExpr.const(4), SizeExpr.const(2)))
    assertEquals(degree.minimum, ResultSizeEstimate(SizeExpr.const(4), SizeExpr.One))
    assertEquals(degree.maximum, ResultSizeEstimate(SizeExpr.const(4), SizeExpr.const(2)))
    assertEquals(degree.edges, ResultSizeEstimate.exact(SizeExpr.const(8)))
  }

  test("fiber-degree lowers ignore strata that may be shorter than the key") {
    val maybeHeaded = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate(PathLengthExpr.Zero, PathLengthExpr.const(2)),
      ResultSizeEstimate.exact(SizeExpr.One),
    )))
    val degree = maybeHeaded.fiberDegree(prefixLength = 1)
    assertEquals(degree.edges, ResultSizeEstimate(SizeExpr.One, SizeExpr.Zero))
    assertEquals(degree.keys, ResultSizeEstimate(SizeExpr.One, SizeExpr.Zero))
    assertEquals(degree.minimum, ResultSizeEstimate(SizeExpr.One, SizeExpr.Zero))
    assertEquals(degree.maximum, ResultSizeEstimate(SizeExpr.One, SizeExpr.Zero))
  }

  test("dependent symbolic lookup uses degree caps without assuming disjoint suffix fibers") {
    val source = SpaceMention("dependent_keys")
    val relation = SpaceMention("dependent_relation")
    val head = PathRef("dependent_key")
    val rest = SpaceMention("dependent_key_rest")
    val sourceType = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.One),
      ResultSizeEstimate.exact(SizeExpr.One),
      Some(SpatialPattern(Vector(SpatialItem.Constant(PathItem("0"))))),
    )))
    val relationType = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.const(2)),
      ResultSizeEstimate.exact(SizeExpr.const(8)),
      Some(SpatialPattern(Vector(
        SpatialItem.Affine("lookup.key", 0, 0, 3),
        SpatialItem.Affine("lookup.value", 0, 0, 3),
      ))),
    )))
    val lookup = Space.Iteration(
      Space.Mention(source), head, rest,
      Space.Unwrap(Space.Mention(relation), Path.Deref(head)),
    )
    val result = SpatialTypeAnalysis.output(lookup, SpatialAssumptions(
      spaces = Map(source -> sourceType, relation -> relationType),
      prefixCoverage = Set(SpatialPrefixCoverage(head, relation)),
    ))
    assertEquals(result.size, ResultSizeEstimate(SizeExpr.const(4), SizeExpr.One))

    val sharedSource = SpatialType.exact(SpaceValue("0", "1"))
    val sharedRelation = SpatialType.exact(SpaceValue("0.x", "1.x"))
    val shared = SpatialTypeAnalysis.output(lookup, SpatialAssumptions(
      spaces = Map(source -> sharedSource, relation -> sharedRelation),
      prefixCoverage = Set(SpatialPrefixCoverage(head, relation)),
    ))
    // Both selected fibers contain the same suffix `x`; key count must not be
    // multiplied into the lower bound.
    assertEquals(shared.size.lower, SizeExpr.One)
    given PathContext = noPaths
    given SpaceContext = SpaceContextMap(Map(
      source -> SpaceValue("0", "1"), relation -> SpaceValue("0.x", "1.x")))
    given PartialFunction[RoutinePtr, Routine] = noRoutines
    assertEquals(eval(lookup), SpaceValue("x"))
  }

  test("spatial projections refine scalar size and path-length projections") {
    val x = SpaceMention("projection_x")
    val value = SpaceValue(path(2, "a"), path(4, "b"), path(4, "c"), path(6, "d"))
    val expressions = Vector[Space](
      Space.Mention(x),
      Space.Union(Space.Mention(x), Space.Singleton(Path.ZERO)),
      Space.Intersection(Space.Mention(x), Space.Literal(value)),
      Space.Subtraction(Space.Mention(x), Space.Singleton(Path.Constant(path(2, "a")))),
      Space.Composition(Space.TailsUnion(Space.Mention(x)), Space.Singleton(Path.Constant(path(2, "tail")))),
      Space.PrefixClosure(Space.Mention(x)),
      Space.Range(Space.Mention(x), 1, 3)
    )
    given PathContext = noPaths
    given SpaceContext = SpaceContextMap(Map(x -> value))
    given PartialFunction[RoutinePtr, Routine] = noRoutines
    val assumptions = SpatialAssumptions(spaces = Map(x -> SpatialType.exact(value)))

    expressions.foreach { expression =>
      def finite(value: Option[BigInt], label: String): BigInt =
        value.getOrElse(fail(s"$label was unbounded for ${expression.show}"))
      val spatial = SpatialTypeAnalysis.output(expression, assumptions)
      val size = ResultSpaceSize.estimate(expression, assumptions.sizeAssumptions)
      val length = ResultPathLength.estimate(expression, assumptions.lengthAssumptions,
        assumptions.pathLengthAssumptions, assumptions.sizeAssumptions)
      val actual = eval(expression)
      val spatialLower = finite(spatial.size.lower.evaluate, "spatial size lower")
      val spatialUpper = finite(spatial.size.upper.evaluate, "spatial size upper")
      assert(spatialLower <= actual.paths.size && spatialUpper >= actual.paths.size, expression.show)
      size.lower.evaluate.foreach(bound => assert(spatialLower >= bound, expression.show))
      size.upper.evaluate.foreach(bound => assert(spatialUpper <= bound, expression.show))
      if actual.paths.nonEmpty then
        val actualMin = BigInt(actual.paths.map(_.items.length).min)
        val actualMax = BigInt(actual.paths.map(_.items.length).max)
        val spatialMin = finite(spatial.pathLength.lower.evaluate, "spatial length lower")
        val spatialMax = finite(spatial.pathLength.upper.evaluate, "spatial length upper")
        assert(spatialMin <= actualMin && spatialMax >= actualMax, expression.show)
        length.lower.evaluate.foreach(bound => assert(spatialMin >= bound, expression.show))
        length.upper.evaluate.foreach(bound => assert(spatialMax <= bound, expression.show))
    }
  }

  test("fixpoint reaches a checked post-fixpoint before exposing shapes") {
    val variable = SpaceMention("fixpoint_probe")
    val universe = SpaceValue("a", "x.a", "x.x.a")
    val fix = Space.Fixpoint(
      Space.Literal(SpaceValue("a")),
      variable,
      Space.Intersection(
        Space.Union(
          Space.Mention(variable),
          Space.Wrap(Space.Mention(variable), Path.Constant(Syntax.parse("x"))),
        ),
        Space.Literal(universe),
      ),
    )
    val expression = Space.Unwrap(fix, Path.ZERO)
    given PathContext = noPaths
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = noRoutines

    val actual = eval(expression)
    val result = SpatialTypeAnalysis.output(expression)
    assertEquals(actual, universe)
    assertEquals(actual.paths.map(_.items.length), Set(1, 2, 3))
    assert(result.pathLength.upper.annotatedBound(Z3BoundDirection.Upper).forall(_ >= 3), result.show)
    val represented = result.strata.flatMap(_.exactLength).toSet
    assert(Set(1, 2, 3).subsetOf(represented), result.show)
  }

  test("tails does not assume an interval-length path is headed") {
    val source = SpaceMention("maybe_epsilon")
    val sourceType = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate(PathLengthExpr.Zero, PathLengthExpr.One),
      ResultSizeEstimate.exact(SizeExpr.One),
    )))
    val result = SpatialTypeAnalysis.output(
      Space.TailsUnion(Space.Mention(source)),
      SpatialAssumptions(spaces = Map(source -> sourceType)),
    )
    assertEquals(result.size.lower.annotatedBound(Z3BoundDirection.Lower), Some(BigInt(0)))

    given PathContext = noPaths
    given SpaceContext = SpaceContextMap(Map(source -> SpaceValue(PathValue(Nil))))
    given PartialFunction[RoutinePtr, Routine] = noRoutines
    assertEquals(eval(Space.TailsUnion(Space.Mention(source))), SpaceValue())
  }

  test("semantic result laws intersect structural facts and expose contradictions") {
    val seed = SpaceMention("law_seed")
    val routine = Routine(
      RoutinePtr("contradictory_result_law"),
      Vector.empty,
      Vector(seed),
      Space.Literal(SpaceValue("only")),
    )
    val seedType = SpatialType.exact(SpaceValue("seed"))
    val connected = SpatialTypeAnalysis.outputRoutineAbstract(
      routine,
      SpatialRoutineAnnotations(
        spaces = Map(seed -> seedType),
        resultLaws = Vector(SpatialBoundLaw.ConnectedFiniteComponent(seed, SizeExpr.const(181440))),
      ),
      PartialFunction.empty,
    )
    val constrained = SpatialTypeAnalysis.outputRoutineAbstract(
      routine,
      SpatialRoutineAnnotations(
        spaces = Map(seed -> seedType),
        resultLaws = Vector(SpatialBoundLaw.FiniteConstraintSolutions(
          FiniteIntConstraintProblem(
            domains = Vector(Vector(1, 2), Vector(1, 2)),
            constraints = Vector(FiniteIntConstraint.NotEqual(0, 1)),
          ))),
      ),
      PartialFunction.empty,
    )
    assert(connected.isBottom, connected.show)
    assert(constrained.isBottom, constrained.show)
  }

  test("repeated union mentions remain coherent across total and strata") {
    val source = SpaceMention("same_source")
    val count = SizeExpr.symbol("N")
    val sourceType = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.const(2)),
      ResultSizeEstimate.exact(count),
      Some(SpatialPattern(Vector(SpatialItem.Constant(PathItem("k")), SpatialItem.Unknown("v")))),
    )))
    val expression = Space.Union(
      Space.Mention(source),
      Space.Union(Space.Mention(source), Space.Mention(source)),
    )
    val result = SpatialTypeAnalysis.output(expression, SpatialAssumptions(spaces = Map(source -> sourceType)))
    assertEquals(result.size, ResultSizeEstimate.exact(count))
    assertEquals(result.strataAt(2).map(_.cardinality), Vector(ResultSizeEstimate.exact(count)))
  }

  test("union preserves optionality of a known singleton pattern") {
    val ranged = Space.Range(Space.Literal(SpaceValue("b", "c")), 0, 1)
    val expression = Space.Union(
      Space.Singleton(Path.Constant(PathValue(List(PathItem("a"))))),
      ranged,
    )
    val result = SpatialTypeAnalysis.output(expression)
    assert(!result.isBottom)
    assertEquals(result.size, ResultSizeEstimate(SizeExpr.const(2), SizeExpr.One))
    assert(result.strata.exists(stratum =>
      stratum.pattern.flatMap(_.constantValue).contains(PathValue(List(PathItem("b")))) &&
        stratum.cardinality.lower == SizeExpr.Zero))
  }

  test("decorated analysis retains lexical iterator bindings") {
    val source = SpaceMention("decorated_source")
    val head = PathRef("decorated_head").known(1)
    val rest = SpaceMention("decorated_rest")
    val body = Space.Union(Space.Singleton(Path.Deref(head)), Space.Mention(rest))
    val expression = Space.Iteration(Space.Mention(source), head, rest, body)
    val decorated = SpatialTypeAnalysis.outputDecorated(
      expression,
      SpatialAssumptions(spaces = Map(source -> SpatialType.exact(SpaceValue("a.b")))),
    )
    val bodyObservation = decorated.at(body).headOption.getOrElse(fail("body was not decorated"))
    assert(bodyObservation.paths.contains(head))
    assert(bodyObservation.spaces.contains(rest))
    assertEquals(decorated.root, SpatialTypeAnalysis.output(
      expression,
      SpatialAssumptions(spaces = Map(source -> SpatialType.exact(SpaceValue("a.b")))),
    ))
  }

  test("cost intervals remain finite through a five-node expression") {
    val expression = Space.Wrap(
      Space.TailsUnion(Space.Union(
        Space.Literal(SpaceValue("a", "b")),
        Space.Literal(SpaceValue("c", "d")),
      )),
      Path.Constant(PathValue(List(PathItem("prefix")))),
    )
    val cost = SpatialTypeAnalysis.output(expression).cost
    assertNotEquals(cost.workUpper, SizeExpr.Infinity, clues(cost.show))
    assertNotEquals(cost.allocationUpper, SizeExpr.Infinity)
    SpatialBackend.values.foreach { backend =>
      val interval = cost.forBackend(backend)
      assertNotEquals(interval.workUpper, SizeExpr.Infinity)
      assert(SizeExpr.provablyNoGreater(interval.workLower, interval.workUpper))
      assert(SizeExpr.provablyNoGreater(interval.allocationLower, interval.allocationUpper))
    }
  }

  test("spatial facts expose optimization decisions and symbolic depth degrees") {
    val symbolic = SpatialType.fromStrata(Vector(SpatialStratum(
      PathLengthEstimate.exact(PathLengthExpr.const(2)),
      ResultSizeEstimate(SizeExpr.symbol("N"), SizeExpr.One),
      Some(SpatialPattern(Vector(
        SpatialItem.Constant(PathItem("edge")),
        SpatialItem.Affine("v", 0, 0, 7),
      ))),
    )))
    val facts = symbolic.facts
    assert(facts.definitelyNonEmpty)
    assertEquals(facts.maxDepth, Some(2))
    assertEquals(facts.depthProfile.map(_.depth), Vector(0, 1))
    assertEquals(facts.depthProfile.head.distinctItems.upper.annotatedBound(Z3BoundDirection.Upper), Some(BigInt(1)))
    assertEquals(facts.commonConstantPrefix, Some(PathValue(List(PathItem("edge")))))
    assert(SpatialBackendSelection.candidates(symbolic).exists(_.isInstanceOf[SpatialSpecialization.TrieUnroll]))
    assert(SpatialBackendSelection.candidates(symbolic).exists(_.isInstanceOf[SpatialSpecialization.ZipperPrefocus]))
  }

  test("decorated nodes have positional identity and joined observations") {
    val leaf = Space.Literal(SpaceValue("same"))
    val expression = Space.Union(leaf, leaf)
    val decorated = SpatialTypeAnalysis.outputDecorated(expression)
    assertEquals(decorated.atPosition(0).map(_.expression), Some(leaf))
    assertEquals(decorated.atPosition(1).map(_.expression), Some(leaf))
    assertNotEquals(decorated.atPosition(0).map(_.position), decorated.atPosition(1).map(_.position))
    assert(decorated.atPosition(0).exists(_.observations.nonEmpty))
  }

  test("extended fuzzer call routine is analyzed across its annotation boundary") {
    val call = Space.Call(SpaceFuzzer.callRoutine.name, Vector.empty,
      Vector(Space.Literal(SpaceValue("a", "b"))))
    val result = SpatialTypeAnalysis.output(call, routines = SpaceFuzzer.routines)
    assertEquals(result.exactValue, Some(SpaceValue("a", "b")))
    assert(SpaceFuzzerCorpus.opKinds(call).contains("Space.Call"))
  }

  test("dominant monomials distinguish linear from quadratic cost") {
    val edges = SizeExpr.symbol("E")
    val linear = SizeExpr.growth(SizeExpr.add(edges, SizeExpr.const(3)), Set("E")).get
    val quadratic = SizeExpr.growth(SizeExpr.multiply(edges, edges), Set("E")).get
    assert(linear.noGreaterThan(quadratic))
    assert(!quadratic.noGreaterThan(linear))
  }

  test("asymptotic projection and recurrence solver retain closed forms") {
    val n = SizeExpr.symbol("N")
    val linear = SpatialRecurrence.solve(SizeExpr.const(3), SizeExpr.One, n)
    val branching = SpatialRecurrence.solve(SizeExpr.const(3), SizeExpr.const(2), n)
    assertEquals(SizeExpr.asymptotic(linear, Set("N")), Some(AsymptoticOrder(0, 1, 0)))
    assertEquals(SizeExpr.asymptotic(branching, Set("N")), Some(AsymptoticOrder(1, 0, 0)))
    assert(SizeExpr.asymptotic(linear, Set("N")).get < SizeExpr.asymptotic(branching, Set("N")).get)
    assertEquals(SpatialRecurrence.solve(SizeExpr.const(3), SizeExpr.const(2), SizeExpr.const(4)).annotatedValue,
      Some(BigInt(45)))
    assert(branching.show.contains("geomSeries"), branching.show)
    val unknownBranching = SpatialRecurrence.solve(SizeExpr.const(3), SizeExpr.symbol("B"), n)
    assertEquals(SizeExpr.asymptotic(unknownBranching, Set("N")), None)
  }

  test("recursive routine costs close when every self call consumes tails") {
    val name = RoutinePtr("spatial_tail_recursion")
    val input = SpaceMention("recursive_input")
    val self = Space.Call(name, Vector.empty, Vector(Space.TailsUnion(Space.Mention(input))))
    val routine = Routine(name, Vector.empty, Vector(input),
      Space.Union(Space.Singleton(Path.ZERO), self))
    val inputType = SpatialType.lengths(4 -> ResultSizeEstimate.exact(SizeExpr.One))
    assertEquals(SpatialRecursion.depthBound(routine, Vector(inputType)), Some(SizeExpr.const(4)))
    val routines: PartialFunction[RoutinePtr, Routine] = { case `name` => routine }
    val result = SpatialTypeAnalysis.output(
      Space.Call(name, Vector.empty, Vector(Space.Mention(input))),
      SpatialAssumptions(spaces = Map(input -> inputType)), routines)
    assert(!result.cost.show.contains("recWork("), result.cost.show)
    assert(!result.cost.show.contains("recPatriciaVisits("), result.cost.show)
    assert(result.cost.workUpper != SizeExpr.Infinity)
    assert(result.cost.forBackend(SpatialBackend.Trie).componentsUpper.patriciaVisits != SizeExpr.Infinity)
  }
