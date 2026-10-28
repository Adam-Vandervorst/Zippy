package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import java.io.{ByteArrayOutputStream, PrintStream}

class ResultSpaceSizeTest extends FunSuite:
  test("analyzer Z3 wrapper distinguishes missing executable from timeout") {
    val missing = intercept[MissingZ3Executable] {
      Z3Executable.runCommand(Vector("/definitely/missing/morkl-z3"), "", waitMillis = 10L)
    }
    assert(missing.getMessage.contains("Install Z3"), missing.getMessage)

    val diagnostics = ByteArrayOutputStream()
    val started = System.nanoTime()
    val timed = Console.withErr(PrintStream(diagnostics)) {
      Z3Diagnostics.capture {
        // The child deliberately never reads stdin. A multi-megabyte script
        // fills the pipe, proving that the watchdog covers the write as well
        // as process.waitFor.
        Z3Executable.runCommand(Vector("/bin/sh", "-c", "sleep 1"), "x" * (4 * 1024 * 1024), waitMillis = 20L)
      }
    }
    val elapsedMillis = (System.nanoTime() - started) / 1000000L
    assertEquals(timed.value, None)
    assert(timed.diagnostics.exists(_.isInstanceOf[Z3Diagnostic.ProcessTimeout]), timed.diagnostics)
    assert(elapsedMillis < 900L, s"timeout did not cover blocking stdin write: ${elapsedMillis}ms")
    assert(diagnostics.toString.contains("Z3 timed out"), diagnostics.toString)

    val solverDiagnostics = ByteArrayOutputStream()
    val solverTimeout = Console.withErr(PrintStream(solverDiagnostics)) {
      Z3Diagnostics.capture {
        Z3Executable.reportSolverUnknown("unknown\n(:reason-unknown \"timeout\")", "test obligation")
      }
    }
    assert(solverTimeout.value)
    assert(solverTimeout.diagnostics.exists(_.isInstanceOf[Z3Diagnostic.SolverTimeout]), solverTimeout.diagnostics)
    assert(
      solverDiagnostics.toString.contains("Z3 timed out after 1000ms in test obligation"),
      solverDiagnostics.toString,
    )

    val pathLengthTimeout = Z3Diagnostics.capture {
      Z3PathLengthSolver.parsePossibleMasks(
        "MASK_1\nunknown\n(:reason-unknown \"timeout\")",
        Vector(1),
      )
    }
    assertEquals(pathLengthTimeout.value, None)
    assert(pathLengthTimeout.diagnostics.exists {
      case Z3Diagnostic.SolverTimeout(obligation, _) => obligation.contains("path-length")
      case _ => false
    }, pathLengthTimeout.diagnostics)

    val completed = Z3Diagnostics.capture {
      Z3Executable.runCommand(Vector("/bin/sh", "-c", "printf solved"), "", waitMillis = 100L)
    }
    assertEquals(completed.value, Some("solved"))
    assertEquals(completed.diagnostics, Vector.empty)
  }

  test("natural expression normalization removes proved dominated bounds") {
    val p = SizeExpr.symbol("P")
    val a = SizeExpr.symbol("A")
    val b = SizeExpr.symbol("B")
    val c = SizeExpr.symbol("C")
    val broad = SizeExpr.multiply(p, SizeExpr.minimum(a, b))
    val tight = SizeExpr.multiply(p, SizeExpr.minimum(a, b, c))
    assertEquals(SizeExpr.minimum(broad, tight), tight)
    assertEquals(SizeExpr.maximum(a, SizeExpr.positive(a)), a)
    assertEquals(
      SizeExpr.multiply(SizeExpr.positive(a), SizeExpr.positive(a)),
      SizeExpr.positive(a),
    )
    assertEquals(
      SizeExpr.add(
        SizeExpr.ifZero(a, b, SizeExpr.Zero),
        SizeExpr.ifZero(a, SizeExpr.Zero, c),
      ),
      SizeExpr.ifZero(a, b, c),
    )
    val maybeZeroDenominator = SizeExpr.minimum(a, SizeExpr.One)
    val quotient = SizeExpr.ceilingDivide(SizeExpr.One, maybeZeroDenominator)
    assertEquals(quotient.annotatedBound(Z3BoundDirection.Lower), Some(BigInt(0)))
    assertEquals(quotient.annotatedBound(Z3BoundDirection.Upper), Some(BigInt(1)))
  }

  test("finite Range windows cap symbolic cardinality without evaluating their source") {
    val finiteCases = Vector(
      (0, 3, BigInt(3)),
      (2, 3, BigInt(1)),
      (-3, 0, BigInt(3)),
      (-4, -1, BigInt(3)),
      (-4, 3, BigInt(2)),
      (Int.MinValue, 0, BigInt(Int.MaxValue) + 1),
    )
    finiteCases.foreach { (start, end, expected) =>
      assertEquals(RangeBounds.cardinalityUpperBound(start, end), Some(expected))
    }
    assertEquals(RangeBounds.cardinalityUpperBound(0, 0), None)
    assertEquals(RangeBounds.cardinalityUpperBound(1, 0), None)
    assertEquals(RangeBounds.cardinalityUpperBound(0, -1), None)
    assertEquals(RangeBounds.cardinalityUpperBound(1, -1), None)

    for
      start <- -4 to 4
      end <- -4 to 4
      capacity <- RangeBounds.cardinalityUpperBound(start, end)
      sourceSize <- 0 to 32
    do
      val (lower, upper) = RangeBounds.normalize(sourceSize, start, end)
      assert(BigInt(upper - lower) <= capacity,
        s"Range($start,$end) selected ${upper - lower} of $sourceSize paths above cap $capacity")

    val source = SpaceMention("finite_range_source")
    val count = SizeExpr.symbol("finiteRangeN")
    val estimate = ResultSpaceSize.estimateBaseline(
      Space.Range(Space.Mention(source), 2, 3),
      Map(source -> ResultSizeEstimate(count, SizeExpr.Zero)),
    )
    assertEquals(estimate, ResultSizeEstimate(SizeExpr.minimum(count, SizeExpr.One), SizeExpr.Zero))

    // An exact symbolic source keeps the threshold-sensitive expression:
    // Range(S,2,3) is still empty at |S|=1, despite having upper cap one.
    val exact = ResultSpaceSize.estimateBaseline(
      Space.Range(Space.Mention(source), 2, 3),
      Map(source -> ResultSizeEstimate.exact(count)),
    )
    assertEquals(exact, ResultSizeEstimate.exact(SizeExpr.range(count, 2, 3)))
    assertEquals(exact.upper.annotatedBound(Z3BoundDirection.Upper), Some(BigInt(1)))
    assert(SizeExpr.provablyNoGreater(exact.upper, SizeExpr.One))
  }

  private val emptyPathContext = PathContextMap(Map.empty)
  private val emptyRoutines = PartialFunction.empty[RoutinePtr, Routine]

  private def evaluated(expression: SizeExpr, context: SpaceContext): BigInt =
    expression.evaluate(using emptyPathContext, context, emptyRoutines).getOrElse(
      fail(s"expected a finite expression, got ${expression.show}")
    )

  test("reference hints cover binders, uses, freshening, and exact space mentions") {
    assertEquals(PathRef("same").known(1), PathRef("same"))
    assertEquals(SpaceMention("same").known(2), SpaceMention("same"))

    val head = PathRef("hint_head")
    val rest = SpaceMention("hint_rest")
    val source = Space.Literal(SpaceValue(Set(
      Syntax.parse("a.x"), Syntax.parse("a.y"),
      Syntax.parse("b.z"), Syntax.parse("b.w")
    )))
    val raw = Space.Iteration(
      source,
      head,
      rest,
      Space.Union(Space.Singleton(Path.Deref(head)), Space.Mention(rest))
    )

    val tagged = ReferenceHints.tag(raw)
    val (taggedHead, taggedRest, taggedBody) = tagged match
      case Space.Iteration(_, symbol, tails, body) => (symbol, tails, body)
      case other => fail(s"expected iteration, got ${other.show}")
    assertEquals(taggedHead.lengthHint, 1)
    assertEquals(taggedRest.sizeHint, 2)
    val (mentions, refs) = collect(taggedBody)(
      { case Space.Mention(sm) => sm },
      { case Path.Deref(pr) => pr }
    )
    assert(mentions.map(_._2).filter(_.s == rest.s).forall(_.sizeHint == 2))
    assert(refs.map(_._2).filter(_.s == head.s).forall(_.lengthHint == 1))

    val fold = ReferenceHints.tag(Space.Fold(
      source,
      Path.Constant(Syntax.parse("seed.value")),
      PathRef("hint_acc"),
      PathRef("hint_fold_head"),
      SpaceMention("hint_fold_rest"),
      Space.Singleton(Path.Deref(PathRef("hint_acc"))),
      Path.Constant(Syntax.parse("next.value"))
    ))
    fold match
      case Space.Fold(_, _, acc, symbol, tails, Space.Singleton(Path.Deref(bodyAcc)), _) =>
        assertEquals(acc.lengthHint, 2)
        assertEquals(bodyAcc.lengthHint, 2)
        assertEquals(symbol.lengthHint, 1)
        assertEquals(tails.sizeHint, 2)
      case other => fail(s"expected tagged fold, got ${other.show}")

    val identityAcc = PathRef("identity_acc")
    ReferenceHints.tag(Space.Fold(
      source,
      Path.Constant(Syntax.parse("seed.value")),
      identityAcc,
      PathRef("identity_fold_head"),
      SpaceMention("identity_fold_rest"),
      Space.Singleton(Path.Deref(identityAcc)),
      Path.Deref(identityAcc)
    )) match
      case Space.Fold(_, _, acc, _, _, Space.Singleton(Path.Deref(bodyAcc)), Path.Deref(updateAcc)) =>
        assertEquals(acc.lengthHint, 2)
        assertEquals(bodyAcc.lengthHint, 2)
        assertEquals(updateAcc.lengthHint, 2)
      case other => fail(s"expected identity fold, got ${other.show}")

    val uneven = ReferenceHints.tag(Space.Iteration(
      Space.Literal(SpaceValue(Set(
        Syntax.parse("a.x"), Syntax.parse("a.y"), Syntax.parse("b.z")
      ))),
      PathRef("uneven_head"),
      SpaceMention("uneven_rest"),
      Space.Mention(SpaceMention("uneven_rest"))
    ))
    uneven match
      case Space.Iteration(_, symbol, tails, Space.Mention(bodyTails)) =>
        assertEquals(symbol.lengthHint, 1)
        assertEquals(tails.sizeHint, -1)
        assertEquals(bodyTails.sizeHint, -1)
      case other => fail(s"expected uneven iteration, got ${other.show}")

    Matching.canon(tagged) match
      case Space.Iteration(_, symbol, tails, _) =>
        assertEquals(symbol.lengthHint, 1)
        assertEquals(tails.sizeHint, 2)
      case other => fail(s"expected canonical iteration, got ${other.show}")

    val formalPath = PathRef("formal_path").known(4)
    val formalSpace = SpaceMention("formal_space").known(3)
    val formalGraph = transpile(Routine(
      RoutinePtr("formal_hint_roundtrip"),
      Vector(formalPath),
      Vector(formalSpace),
      Space.Union(Space.Singleton(Path.Deref(formalPath)), Space.Mention(formalSpace))
    ))
    Vector(
      formalGraph,
      optimize_sharing(formalGraph),
      push_out(formalGraph),
      hoist_loop_invariant_subgraphs(formalGraph)
    ).foreach { roundtripGraph =>
      val formalStack = scala.collection.mutable.Stack(new Array[Path | Space | Null](roundtripGraph.nodes.length))
      untranspile(roundtripGraph, formalStack)
      formalStack.top.last.asInstanceOf[Space] match
        case Space.Union(Space.Singleton(Path.Deref(path)), Space.Mention(space)) =>
          assertEquals(path.lengthHint, 4)
          assertEquals(space.sizeHint, 3)
        case other => fail(s"expected formal-reference round trip, got ${other.show}")
    }

    val graph = transpile(Routine(RoutinePtr("hint_roundtrip"), Vector.empty, Vector.empty, raw))
    val stack = scala.collection.mutable.Stack(new Array[Path | Space | Null](graph.nodes.length))
    untranspile(graph, stack)
    stack.top.last.asInstanceOf[Space] match
      case Space.Iteration(_, symbol, tails, body) =>
        assertEquals(symbol.lengthHint, 1)
        assertEquals(tails.sizeHint, 2)
        val (roundtripMentions, roundtripRefs) = collect(body)(
          { case Space.Mention(sm) => sm },
          { case Path.Deref(pr) => pr }
        )
        assert(roundtripMentions.map(_._2).forall(_.sizeHint == 2))
        assert(roundtripRefs.map(_._2).forall(_.lengthHint == 1))
      case other => fail(s"expected round-tripped iteration, got ${other.show}")

    val known = SpaceMention("known_size").known(3)
    val knownEstimate = ResultSpaceSize.estimateOperationLaws(Space.Mention(known))
    assertEquals(knownEstimate.upper.evaluate, Some(BigInt(3)))
    assertEquals(knownEstimate.lower.evaluate, Some(BigInt(3)))
  }

  test("symbolic cardinality rules preserve useful path-set bounds") {
    val left = S"left"
    val right = S"right"
    val l = SizeExpr.sizeOf(left)
    val r = SizeExpr.sizeOf(right)

    assertEquals(
      ResultSpaceSize.estimateBaseline(left \/ right),
      ResultSizeEstimate(SizeExpr.add(l, r), SizeExpr.maximum(l, r))
    )
    assertEquals(
      ResultSpaceSize.estimateBaseline(left /\ right),
      ResultSizeEstimate(SizeExpr.minimum(l, r), SizeExpr.Zero)
    )
    assertEquals(
      ResultSpaceSize.estimateBaseline(left \ right),
      ResultSizeEstimate(l, SizeExpr.positiveDifference(l, r))
    )
    assertEquals(
      ResultSpaceSize.estimateBaseline(left <| right),
      ResultSizeEstimate(l, SizeExpr.Zero)
    )
    assertEquals(ResultSpaceSize.estimateBaseline(left \/ left), ResultSizeEstimate.exact(l))
    assertEquals(ResultSpaceSize.estimateBaseline(left /\ left), ResultSizeEstimate.exact(l))
    assertEquals(ResultSpaceSize.estimateBaseline(left \ left), ResultSizeEstimate.empty)

    val product = ResultSpaceSize.estimateBaseline(left x right)
    assertEquals(product.upper, SizeExpr.multiply(l, r))
    assertEquals(
      product.lower,
      SizeExpr.maximum(
        SizeExpr.multiply(l, SizeExpr.positive(r)),
        SizeExpr.multiply(r, SizeExpr.positive(l))
      )
    )

    // Concatenation by one fixed path is injective and therefore exact.
    assertEquals(ResultSpaceSize.estimateBaseline("prefix" x left), ResultSizeEstimate.exact(l))
    val suffix = Space.Singleton(Path.Constant(Syntax.parse("suffix")))
    assertEquals(ResultSpaceSize.estimateBaseline(left x suffix), ResultSizeEstimate.exact(l))

    val prefix = Path.Constant(Syntax.parse("a"))
    val unwrapped = Space.Unwrap(left, prefix)
    assertEquals(
      ResultSpaceSize.estimateBaseline(unwrapped),
      ResultSizeEstimate.exact(SizeExpr.sizeOf(unwrapped))
    )
    assertEquals(
      ResultSpaceSize.estimateBaseline(Space.TailsUnion(left)),
      ResultSizeEstimate(l, SizeExpr.Zero)
    )
    assertEquals(
      ResultSpaceSize.estimateBaseline(Space.Range(left, 0, 2)),
      ResultSizeEstimate.exact(SizeExpr.range(l, 0, 2))
    )
    assertEquals(Supercompiler.resultSize(left \/ right), ResultSpaceSize.estimate(left \/ right))
    assertEquals(
      Supercompiler.optimizedResultSize(left \/ Space.Empty),
      ResultSpaceSize.estimate(left)
    )

    val opaqueCall = Space.Call(RoutinePtr("unknown"), Vector.empty, Vector(left))
    assertEquals(
      ResultSpaceSize.estimate(opaqueCall),
      ResultSizeEstimate.exact(SizeExpr.sizeOf(opaqueCall))
    )
  }

  test("empty-control iteration has the expected exact symbolic size") {
    val source = S"s"
    val fallback = S"g"
    val sentinel = Path.Constant(Syntax.parse("E"))
    val innerHead = PathRef("h").known(1)
    val innerTail = SpaceMention("inner_tail")
    val outerHead = PathRef("ignored_head").known(1)
    val outerTail = SpaceMention("ignored_tail")

    val nonEmptyProbe = Space.Iteration(
      Space.Composition(Space.Singleton(sentinel), source),
      innerHead,
      innerTail,
      Space.Singleton(Path.Deref(innerHead))
    )
    val ifEmpty = Space.Iteration(
      Space.Subtraction(Space.Singleton(sentinel), nonEmptyProbe),
      outerHead,
      outerTail,
      fallback
    )
    val control = source \/ ifEmpty

    val sourceSize = SizeExpr.sizeOf(source)
    val fallbackSize = SizeExpr.sizeOf(fallback)
    val expected = SizeExpr.add(
      sourceSize,
      SizeExpr.multiply(SizeExpr.isZero(sourceSize), fallbackSize)
    )
    assertEquals(ResultSpaceSize.estimate(control), ResultSizeEstimate.exact(expected))

    val whenEmpty = ResultSpaceSize.estimate(
      control,
      Map(source.variable -> ResultSizeEstimate.empty)
    )
    assertEquals(whenEmpty, ResultSizeEstimate.exact(fallbackSize))

    val residual = S"s_tail"
    val definitelyNonEmpty = Space.Singleton(Path.Constant(Syntax.parse("x"))) \/ residual
    val nonEmptyControl = subs(control)(spost = { case Space.Mention(sm) if sm == source.variable => definitelyNonEmpty })
    assertEquals(ResultSpaceSize.estimate(nonEmptyControl), ResultSpaceSize.estimate(definitelyNonEmpty))
  }

  test("Z3 refinement preserves correlations and is pointwise tighter than baseline") {
    val x = S"x"
    val y = S"y"
    val unionAbsorption = x \/ (x /\ y)
    val intersectionAbsorption = x /\ (x \/ y)
    val repeatedIntersection = x /\ (x /\ y)
    val differenceCorrelation = (x \/ y) \ x
    val expressions = Vector(unionAbsorption, intersectionAbsorption, repeatedIntersection, differenceCorrelation)
    val universe = Vector(PathValue(Nil), Syntax.parse("a"), Syntax.parse("b"), Syntax.parse("a.b"))

    for
      leftMask <- 0 until (1 << universe.size)
      rightMask <- 0 until (1 << universe.size)
    do
      val left = SpaceValue(universe.indices.collect {
        case index if (leftMask & (1 << index)) != 0 => universe(index)
      }.toSet)
      val right = SpaceValue(universe.indices.collect {
        case index if (rightMask & (1 << index)) != 0 => universe(index)
      }.toSet)
      val context = SpaceContextMap(Map(x.variable -> left, y.variable -> right))

      expressions.foreach { expression =>
        val baseline = ResultSpaceSize.estimateBaseline(expression)
        val refined = ResultSpaceSize.estimate(expression)
        val baselineLower = evaluated(baseline.lower, context)
        val refinedLower = evaluated(refined.lower, context)
        val baselineUpper = baseline.upper.evaluate(using emptyPathContext, context, emptyRoutines)
        val refinedUpper = refined.upper.evaluate(using emptyPathContext, context, emptyRoutines)
        val actual = BigInt(eval(expression)(using emptyPathContext, context, emptyRoutines).paths.size)

        assert(refinedLower >= baselineLower,
          s"weaker refined lower for ${expression.show}: baseline=$baselineLower refined=$refinedLower")
        assert(refinedLower <= actual,
          s"unsound refined lower for ${expression.show}: refined=$refinedLower actual=$actual")
        (baselineUpper, refinedUpper) match
          case (Some(base), Some(value)) => assert(value <= base,
            s"weaker refined upper for ${expression.show}: baseline=$base refined=$value")
          case (Some(_), None) => fail(s"refinement lost a finite baseline upper for ${expression.show}")
          case _ => ()
        refinedUpper.foreach(value => assert(actual <= value,
          s"unsound refined upper for ${expression.show}: actual=$actual refined=$value"))
      }

      val unionSize = ResultSpaceSize.estimate(unionAbsorption)
      assertEquals(evaluated(unionSize.lower, context), BigInt(left.paths.size))
      assertEquals(unionSize.upper.evaluate(using emptyPathContext, context, emptyRoutines), Some(BigInt(left.paths.size)))

      val intersectionSize = ResultSpaceSize.estimate(intersectionAbsorption)
      assertEquals(evaluated(intersectionSize.lower, context), BigInt(left.paths.size))
      assertEquals(intersectionSize.upper.evaluate(using emptyPathContext, context, emptyRoutines), Some(BigInt(left.paths.size)))

      val repeatedSize = ResultSpaceSize.estimate(repeatedIntersection)
      val innerSize = ResultSpaceSize.estimate(x /\ y)
      assertEquals(evaluated(repeatedSize.lower, context), evaluated(innerSize.lower, context))
      assertEquals(
        repeatedSize.upper.evaluate(using emptyPathContext, context, emptyRoutines),
        innerSize.upper.evaluate(using emptyPathContext, context, emptyRoutines)
      )

      val differenceSize = ResultSpaceSize.estimate(differenceCorrelation)
      assert(differenceSize.upper.evaluate(using emptyPathContext, context, emptyRoutines).forall(_ <= right.paths.size))
  }

  test("mixed operation laws refine former opaque graph boundaries") {
    val source = S"source"
    val body = S"body"
    val head = PathRef("law_head").known(1)
    val rest = SpaceMention("law_rest")
    val independentIteration = Space.Iteration(source, head, rest, body)
    val sourceValue = SpaceValue(Set(PathValue(Nil), Syntax.parse("a.x"), Syntax.parse("b.y"), Syntax.parse("c.z")))
    val bodyValue = SpaceValue(Set(Syntax.parse("p"), Syntax.parse("q"), Syntax.parse("r")))
    val context = SpaceContextMap(Map(source.variable -> sourceValue, body.variable -> bodyValue))

    val iterationBaseline = ResultSpaceSize.estimateBaseline(independentIteration)
    val iterationRefined = ResultSpaceSize.estimate(independentIteration)
    assertEquals(evaluated(iterationBaseline.upper, context), BigInt(12))
    assertEquals(evaluated(iterationRefined.upper, context), BigInt(3))
    assertEquals(evaluated(iterationRefined.lower, context), BigInt(3))

    val prefix = ResultSpaceSize.estimate(Space.PrefixClosure(source))
    val suffix = ResultSpaceSize.estimate(Space.SuffixClosure(source))
    val tails = ResultSpaceSize.estimate(Space.TailsClosure(source))
    assertEquals(evaluated(prefix.lower, context), BigInt(3))
    assertEquals(evaluated(suffix.lower, context), BigInt(3))
    assertEquals(evaluated(tails.lower, context), BigInt(4))

    val boundUnwrap = Space.Iteration(
      source,
      head,
      rest,
      Space.Unwrap(Space.Mention(rest), Path.Constant(Syntax.parse("x")))
    )
    val unwrapBaseline = ResultSpaceSize.estimateBaseline(boundUnwrap)
    val unwrapRefined = ResultSpaceSize.estimate(boundUnwrap)
    assert(unwrapBaseline.upper.evaluate(using emptyPathContext, context, emptyRoutines).isEmpty)
    assert(unwrapRefined.upper.evaluate(using emptyPathContext, context, emptyRoutines).nonEmpty)

    val epsilonOnly = SpaceContextMap(Map(
      source.variable -> SpaceValue(Set(PathValue(Nil))),
      body.variable -> bodyValue
    ))
    assertEquals(evaluated(iterationRefined.lower, epsilonOnly), BigInt(0))
    assertEquals(evaluated(iterationRefined.upper, epsilonOnly), BigInt(3))
  }

  test("literal fibers and nested iteration maps remain visible to the mixed graph") {
    val relation = Space.Literal(SpaceValue(Set(
      Syntax.parse("a.x"),
      Syntax.parse("a.y"),
      Syntax.parse("b.z")
    )))
    val dynamicPrefix = PathRef("fiber_prefix").known(1)
    val prefixRest = SpaceMention("fiber_rest")
    val lookup = Space.Iteration(
      Space.Literal(SpaceValue(Set(Syntax.parse("a"), Syntax.parse("b")))),
      dynamicPrefix,
      prefixRest,
      Space.Unwrap(relation, Path.Deref(dynamicPrefix))
    )
    val lookupBaseline = ResultSpaceSize.estimateBaseline(lookup)
    val lookupRefined = ResultSpaceSize.estimate(lookup)
    assertEquals(lookupBaseline.upper.evaluate, None)
    assertEquals(lookupRefined, ResultSizeEstimate.exact(SizeExpr.const(3)))
    assertEquals(eval(lookup).paths.size, 3)

    val source = S"map_source"
    val outerHead = PathRef("map_outer").known(1)
    val outerRest = SpaceMention("map_outer_rest")
    val innerHead = PathRef("map_inner").known(1)
    val innerRest = SpaceMention("map_inner_rest")
    val emitted = Space.Singleton(Path.Concat(Path.Deref(outerHead), Path.Deref(innerHead)))
    val nestedMap = Space.Iteration(
      source,
      outerHead,
      outerRest,
      Space.Iteration(Space.Mention(outerRest), innerHead, innerRest, emitted)
    )
    val sourceValue = SpaceValue(Set(
      Syntax.parse("a.x"),
      Syntax.parse("a.y"),
      Syntax.parse("b.z"),
      Syntax.parse("c.w")
    ))
    val context = SpaceContextMap(Map(source.variable -> sourceValue))
    assertEquals(evaluated(ResultSpaceSize.estimateBaseline(nestedMap).upper, context), BigInt(16))
    assertEquals(evaluated(ResultSpaceSize.estimate(nestedMap).upper, context), BigInt(4))
    assertEquals(eval(nestedMap)(using emptyPathContext, context, emptyRoutines).paths.size, 4)
  }

  test("pointwise tail and nested-group caps contain exhaustive concrete outputs") {
    val source = S"pointwise_tail_source"
    val outerHead = PathRef("pointwise_tail_outer_head").known(1)
    val outerRest = SpaceMention("pointwise_tail_outer_rest")
    val innerHead = PathRef("pointwise_tail_inner_head").known(1)
    val innerRest = SpaceMention("pointwise_tail_inner_rest")
    val tailBodies = Vector[Space](
      Space.TailsUnion(Space.Mention(outerRest)),
      Space.TailsIntersection(Space.Mention(outerRest)),
    )
    val tailMaps = tailBodies.map(body =>
      Space.Iteration(source, outerHead, outerRest, body))
    val nestedMap = Space.Iteration(
      source,
      outerHead,
      outerRest,
      Space.Iteration(
        Space.Mention(outerRest),
        innerHead,
        innerRest,
        Space.Union(
          Space.Singleton(Path.Deref(innerHead)),
          Space.Mention(innerRest),
        ),
      ),
    )
    // TailsUnion removes exactly one head; it is TailsClosure, deliberately
    // absent from the pointwise rule, that can emit many suffixes per path.
    val universe = Vector(
      PathValue(Nil),
      Syntax.parse("a"),
      Syntax.parse("a.x"),
      Syntax.parse("a.x.p"),
      Syntax.parse("a.y.q"),
      Syntax.parse("b.x.r"),
      Syntax.parse("b.z.s.t"),
    )
    for mask <- 0 until (1 << universe.size) do
      val sourceValue = SpaceValue(universe.indices.collect {
        case index if (mask & (1 << index)) != 0 => universe(index)
      }.toSet)
      val context = SpaceContextMap(Map(source.variable -> sourceValue))
      tailMaps.foreach { expression =>
        val upper = evaluated(ResultSpaceSize.estimate(expression).upper, context)
        val actual = BigInt(eval(expression)(using emptyPathContext, context, emptyRoutines).paths.size)
        assert(actual <= upper, s"tail cap excluded mask $mask: actual=$actual upper=$upper")
        assert(upper <= sourceValue.paths.size,
          s"one-step tail cap was not linear for mask $mask: upper=$upper source=${sourceValue.paths.size}")
      }
      val nestedUpper = evaluated(ResultSpaceSize.estimate(nestedMap).upper, context)
      val nestedActual = BigInt(eval(nestedMap)(using emptyPathContext, context, emptyRoutines).paths.size)
      assert(nestedActual <= nestedUpper,
        s"nested-group cap excluded mask $mask: actual=$nestedActual upper=$nestedUpper")
      assert(nestedUpper <= BigInt(sourceValue.paths.size * 2),
        s"nested-group cap was not pointwise for mask $mask: upper=$nestedUpper source=${sourceValue.paths.size}")
    end for
  }

  test("restriction and reconstruct iteration preserve nonzero lower bounds") {
    val sourceValue = SpaceValue(PathValue(Nil), Syntax.parse("a.x"), Syntax.parse("b.y"))
    val source = Space.Literal(sourceValue)
    val prefixes = Space.Literal(SpaceValue(Syntax.parse("a"), Syntax.parse("b")))
    val selected = ResultSpaceSize.estimate(Space.Restriction(source, prefixes))
    assertEquals(selected, ResultSizeEstimate.exact(SizeExpr.const(2)))
    assertEquals(ResultSpaceSize.estimate(Space.Restriction(source, source)), ResultSizeEstimate.exact(SizeExpr.const(3)))
    assertEquals(
      ResultSpaceSize.estimate(Space.Restriction(source, Space.Singleton(Path.Constant(PathValue(Nil))))),
      ResultSizeEstimate.exact(SizeExpr.const(3)),
    )

    val head = PathRef("reconstruct_head").known(1)
    val rest = SpaceMention("reconstruct_rest")
    val reconstruct = Space.Iteration(source, head, rest,
      Space.Wrap(Space.Mention(rest), Path.Deref(head)))
    assertEquals(ResultSpaceSize.estimate(reconstruct), ResultSizeEstimate.exact(SizeExpr.const(2)))
    assertEquals(eval(reconstruct).paths.size, 2)
  }

  test("symbolic prefix coverage and correlated product maps stay nonzero and linear") {
    val source = S"symbolic_covered_source"
    val prefixes = Space.Singleton(Path.Constant(Syntax.parse("tag")))
    val wrapped = Space.Wrap(source, Path.Constant(Syntax.parse("tag")))
    assertEquals(ResultSpaceSize.estimate(Space.Restriction(wrapped, prefixes)),
      ResultSpaceSize.estimate(source))

    val head = PathRef("linear_map_head").known(1)
    val rest = SpaceMention("linear_map_rest")
    val reconstruct = Space.Wrap(Space.Mention(rest), Path.Deref(head))
    val body = Space.Union(
      reconstruct,
      Space.Composition(Space.Singleton(Path.Constant(Syntax.parse("copy"))), reconstruct),
    )
    val mapped = Space.Iteration(source, head, rest, body)
    val sourceValue = SpaceValue(
      PathValue(Nil), Syntax.parse("a.x"), Syntax.parse("b.y"), Syntax.parse("c.z"))
    val context = SpaceContextMap(Map(source.variable -> sourceValue))
    val baseline = ResultSpaceSize.estimateBaseline(mapped)
    val refined = ResultSpaceSize.estimate(mapped)
    assertEquals(evaluated(baseline.upper, context), BigInt(32))
    assertEquals(evaluated(refined.upper, context), BigInt(8))
    assertEquals(evaluated(refined.lower, context), BigInt(3))
    assertEquals(eval(mapped)(using emptyPathContext, context, emptyRoutines).paths.size, 6)
  }

  test("binder-dependent grounded wrappers do not inherit an injective reconstruction lower bound") {
    val head = PathRef("grounded_collision_head").known(1)
    val rest = SpaceMention("grounded_collision_rest")
    val source = Space.Literal(SpaceValue(Syntax.parse("a.b"), Syntax.parse("b")))
    val reconstructed = Space.Wrap(Space.Mention(rest), Path.Deref(head))
    val collapsingPrefix = Path.GroundedPP(
      Path.Deref(head),
      value => if value == Syntax.parse("a") then PathValue(Nil) else Syntax.parse("a"),
    )
    val expression = Space.Iteration(
      source,
      head,
      rest,
      Space.Wrap(reconstructed, collapsingPrefix),
    )

    assertEquals(eval(expression).paths, Set(Syntax.parse("a.b")))
    val estimate = ResultSpaceSize.estimate(expression)
    assert(SizeExpr.provablyNoGreater(estimate.lower, SizeExpr.One), estimate.show)
    assert(SizeExpr.provablyNoGreater(SizeExpr.One, estimate.upper), estimate.show)
    val spatial = SpatialTypeAnalysis.output(expression).size
    assert(SizeExpr.provablyNoGreater(spatial.lower, SizeExpr.One), spatial.show)
    assert(SizeExpr.provablyNoGreater(SizeExpr.One, spatial.upper), spatial.show)
  }

  test("operation subset constraints cross opaque Z3 atoms") {
    val source = S"relation_source"
    val prefixes = S"relation_prefixes"
    val other = S"relation_other"
    val selected = Space.Restriction(source, prefixes)
    val absorbed = source \/ selected
    val residual = (selected \/ other) \ source
    val sourceValue = SpaceValue(Set(Syntax.parse("a.x"), Syntax.parse("b.y"), Syntax.parse("c.z")))
    val prefixValue = SpaceValue(Set(Syntax.parse("a"), Syntax.parse("c")))
    val otherValue = SpaceValue(Set(Syntax.parse("b.y"), Syntax.parse("q")))
    val context = SpaceContextMap(Map(
      source.variable -> sourceValue,
      prefixes.variable -> prefixValue,
      other.variable -> otherValue
    ))

    assertEquals(evaluated(ResultSpaceSize.estimateBaseline(absorbed).upper, context), BigInt(6))
    val refined = ResultSpaceSize.estimate(absorbed)
    assertEquals(evaluated(refined.lower, context), BigInt(3))
    assertEquals(refined.upper.evaluate(using emptyPathContext, context, emptyRoutines), Some(BigInt(3)))

    assertEquals(evaluated(ResultSpaceSize.estimateBaseline(residual).upper, context), BigInt(5))
    val residualRefined = ResultSpaceSize.estimate(residual)
    assert(residualRefined.upper.show.contains("relations="), residualRefined.show)
    assertEquals(residualRefined.upper.evaluate(using emptyPathContext, context, emptyRoutines), Some(BigInt(2)))
  }

  test("symbolic bounds contain exhaustive concrete denotations") {
    val x = S"x"
    val y = S"y"
    val h = PathRef("head").known(1)
    val acc = PathRef("acc")
    val tail = SpaceMention("tail")
    val fixed = Path.Constant(Syntax.parse("a"))
    val fixedPoint = SpaceMention("fixed")
    val expressions = Vector(
      Space.Empty,
      Space.Singleton(fixed),
      Space.Literal(SpaceValue(Set(Syntax.parse("a"), Syntax.parse("b")))),
      x \/ y,
      x /\ y,
      x \ y,
      x <| y,
      Space.Raffination(x, y),
      x x y,
      Space.Wrap(x, fixed),
      Space.Unwrap(x, fixed),
      Space.TailsUnion(x),
      Space.TailsIntersection(x),
      Space.PrefixClosure(x),
      Space.SuffixClosure(x),
      Space.TailsClosure(x),
      Space.Range(x, 0, 2),
      Space.Iteration(x, h, tail, Space.Singleton(Path.Deref(h))),
      Space.Iteration(x, h, tail, y),
      Space.Fold(x, Path.ZERO, acc, h, tail, Space.Singleton(Path.Deref(h)), Path.Deref(acc)),
      Space.Fixpoint(x, fixedPoint, Space.Empty),
      Space.GroundedPS(fixed, _ => SpaceValue(Set(Syntax.parse("a"), Syntax.parse("b")))),
      Space.GroundedSS(x, identity)
    )
    val universe = Vector(PathValue(Nil), Syntax.parse("a"), Syntax.parse("b"), Syntax.parse("a.b"))

    for
      leftMask <- 0 until (1 << universe.size)
      rightMask <- 0 until (1 << universe.size)
    do
      val left = SpaceValue(universe.indices.collect {
        case index if (leftMask & (1 << index)) != 0 => universe(index)
      }.toSet)
      val right = SpaceValue(universe.indices.collect {
        case index if (rightMask & (1 << index)) != 0 => universe(index)
      }.toSet)
      val context = SpaceContextMap(Map(x.variable -> left, y.variable -> right))

      expressions.foreach { expression =>
        val estimate = ResultSpaceSize.estimate(expression)
        val actual = BigInt(eval(expression)(using emptyPathContext, context, emptyRoutines).paths.size)
        val lower = evaluated(estimate.lower, context)
        assert(lower <= actual,
          s"lower bound failed for ${expression.show}: ${estimate.show}, lower=$lower, actual=$actual, x=${left.pretty}, y=${right.pretty}")
        estimate.upper.evaluate(using emptyPathContext, context, emptyRoutines).foreach { upper =>
          assert(actual <= upper,
            s"upper bound failed for ${expression.show}: ${estimate.show}, actual=$actual, x=${left.pretty}, y=${right.pretty}")
        }
      }
  }
