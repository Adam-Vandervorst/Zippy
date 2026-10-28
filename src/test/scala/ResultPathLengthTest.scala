package morkl

import munit.FunSuite

class ResultPathLengthTest extends FunSuite:
  private def path(length: Int, tag: String): PathValue =
    PathValue(List.tabulate(length)(index => PathItem(s"${tag}_$index")))

  private def bounds(
    space: Space
  )(using pc: PathContext, sc: SpaceContext, rc: PartialFunction[RoutinePtr, Routine]): (Option[BigInt], Option[BigInt]) =
    val estimate = ResultPathLength.estimate(space)
    estimate.lower.evaluate -> estimate.upper.evaluate

  test("Z3 removes impossible length intersections before composition") {
    val length10 = Space.Singleton(Path.Constant(path(10, "ten")))
    val lengths20To30 = Space.Literal(SpaceValue((20 to 30).map(length => path(length, s"range_$length")).toSet))
    val length15 = Space.Singleton(Path.Constant(path(15, "fifteen")))
    val epsilon = Space.Singleton(Path.ZERO)
    val length2 = Space.Singleton(Path.Constant(path(2, "two")))
    val threePlusThree = Space.Singleton(Path.Concat(
      Path.Constant(path(3, "three_left")),
      Path.Constant(path(3, "three_right"))
    ))
    val expression = Space.Composition(
      Space.Union(Space.Intersection(Space.Union(length10, lengths20To30), length15), epsilon),
      Space.Union(length2, threePlusThree),
    )

    given PathContext = PathContext.emptyMap
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty

    val baseline = ResultPathLength.estimateBaseline(expression)
    val refined = ResultPathLength.estimate(expression)
    assertEquals(baseline.lower.evaluate, Some(BigInt(2)))
    assertEquals(baseline.upper.evaluate, Some(BigInt(21)))
    assertEquals(refined.lower.evaluate, Some(BigInt(2)))
    assertEquals(refined.upper.evaluate, Some(BigInt(6)))
    assertEquals(eval(expression).paths.map(_.items.length), Set(2, 6))
  }

  test("path-length bounds penetrate every path and space construct") {
    val x = SpaceMention("length_x")
    val y = SpaceMention("length_y")
    val free = PathRef("free_length")
    val xValue = SpaceValue(Set(PathValue(Nil), path(1, "x1"), path(3, "x3"), path(5, "x5")))
    val yValue = SpaceValue(Set(path(1, "x1"), path(2, "y2"), path(4, "y4")))
    val formal = SpaceMention("length_formal")
    val identityRoutine = Routine(RoutinePtr("length_identity"), Vector.empty, Vector(formal), Space.Mention(formal))
    val head = PathRef("length_head").known(1)
    val rest = SpaceMention("length_rest")
    val acc = PathRef("length_acc")
    val fixed = SpaceMention("length_fixed")
    val one = Path.Constant(path(1, "one"))
    val two = Path.Constant(path(2, "two"))

    given PathContext = PathContextMap(Map(free -> path(3, "free")))
    given SpaceContext = SpaceContextMap(Map(x -> xValue, y -> yValue))
    given PartialFunction[RoutinePtr, Routine] = { case identityRoutine.name => identityRoutine }

    val expressions = Vector(
      Space.Empty,
      Space.Mention(x),
      Space.Call(identityRoutine.name, Vector.empty, Vector(Space.Mention(x))),
      Space.Singleton(Path.Deref(free)),
      Space.Singleton(Path.Concat(one, two)),
      Space.Singleton(Path.GroundedPP(two, value => PathValue(value.items ++ value.items))),
      Space.Singleton(Path.GroundedSP(Space.Mention(x), value => path(value.paths.size, "grounded_sp"))),
      Space.Literal(xValue),
      Space.Union(Space.Mention(x), Space.Mention(y)),
      Space.Intersection(Space.Mention(x), Space.Mention(y)),
      Space.Subtraction(Space.Mention(x), Space.Mention(y)),
      Space.Restriction(Space.Mention(x), Space.Mention(y)),
      Space.Raffination(Space.Mention(x), Space.Mention(y)),
      Space.Composition(Space.Mention(x), Space.Mention(y)),
      Space.Iteration(Space.Mention(x), head, rest,
        Space.Union(Space.Singleton(Path.Deref(head)), Space.Mention(rest))),
      Space.Fold(Space.Mention(x), Path.ZERO, acc, head, rest,
        Space.Singleton(Path.Concat(Path.Deref(acc), Path.Deref(head))), Path.Deref(acc)),
      Space.Fixpoint(Space.Mention(x), fixed, Space.Mention(fixed)),
      Space.Fixpoint(Space.Mention(x), fixed, Space.Mention(y)),
      Space.Wrap(Space.Mention(x), two),
      Space.Unwrap(Space.Wrap(Space.Mention(x), two), two),
      Space.TailsUnion(Space.Mention(x)),
      Space.TailsIntersection(Space.Mention(x)),
      Space.PrefixClosure(Space.Mention(x)),
      Space.SuffixClosure(Space.Mention(x)),
      Space.TailsClosure(Space.Mention(x)),
      Space.GroundedPS(two, value => SpaceValue(Set(value, PathValue(value.items ++ value.items)))),
      Space.GroundedSS(Space.Mention(x), value => SpaceValue(value.paths.map(p => PathValue(PathItem("g") :: p.items)))),
      Space.Range(Space.Mention(x), 1, 3)
    )

    expressions.foreach { expression =>
      val result = eval(expression)
      val baseline = ResultPathLength.estimateBaseline(expression)
      val refined = ResultPathLength.estimate(expression)
      val baselineLower = baseline.lower.evaluate
      val baselineUpper = baseline.upper.evaluate
      val refinedLower = refined.lower.evaluate
      val refinedUpper = refined.upper.evaluate

      if result.paths.nonEmpty then
        val actualLower = BigInt(result.paths.iterator.map(_.items.length).min)
        val actualUpper = BigInt(result.paths.iterator.map(_.items.length).max)
        assert(refinedLower.exists(_ <= actualLower),
          s"lower bound failed for ${expression.show}: ${refined.show}, actual=$actualLower..$actualUpper")
        assert(refinedUpper.forall(_ >= actualUpper),
          s"upper bound failed for ${expression.show}: ${refined.show}, actual=$actualLower..$actualUpper")
        assert((baselineLower, refinedLower) match
          case (Some(base), Some(value)) => value >= base
          case (None, None) => true
          case _ => false,
          s"refined lower weakened baseline for ${expression.show}: baseline=${baseline.show}, refined=${refined.show}")
        assert((baselineUpper, refinedUpper) match
          case (Some(base), Some(value)) => value <= base
          case (None, _) => true
          case _ => false,
          s"refined upper weakened baseline for ${expression.show}: baseline=${baseline.show}, refined=${refined.show}")
    }
  }
