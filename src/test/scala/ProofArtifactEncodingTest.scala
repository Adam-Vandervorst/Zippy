package morkl

import munit.FunSuite
import morkl.ProofArtifacts as PA

class ProofArtifactEncodingTest extends FunSuite:
  test("compact bitvector encoding covers bit zero and the highest bit") {
    val ctx = PA.Ctx(Vector("a", "b"), maxLen = 1)
    val highest = ctx.width - 1
    val smt = PA.endpointEncodingLaw(ctx).smt2(ctx)

    assert(smt.contains(s"((_ extract 0 0)"), smt)
    assert(smt.contains(s"((_ extract $highest $highest)"), smt)
    assert(smt.contains(s"(bvshl (_ bv1 ${ctx.width}) (_ bv0 ${ctx.width}))"), smt)
    assert(smt.contains(s"(bvshl (_ bv1 ${ctx.width}) (_ bv$highest ${ctx.width}))"), smt)
    assert(smt.endsWith("(check-sat)\n(get-model)"), smt)
  }

  test("finite SpatialType bridge emits a code-connected theorem and detected mutation") {
    assertEquals(FiniteSpatialTypeBridge.domain.size, 28)
    FiniteSpatialTypeBridge.domain.foreach { value =>
      assertEquals(
        FiniteSpatialTypeBridge.decode(FiniteSpatialTypeBridge.embed(value)),
        Right(value),
      )
    }

    val problems = PA.finiteSpatialCodeBridgeProblems.map(problem => problem.name -> problem).toMap
    val bridge = problems("spatial_type_finite_code_bridge")
    val mutation = problems("bad_spatial_type_finite_code_bridge_flipped_output_generated_negative_control")
    assertEquals(bridge.expected, "unsat")
    assertEquals(mutation.expected, "sat")
    assert(bridge.smt2.contains("canonical-domain-size: 28"), bridge.smt2)
    assert(bridge.smt2.contains("ordered-pair-count: 784"), bridge.smt2)
    assert(bridge.smt2.contains("production-observation-count: 2380"), bridge.smt2)
    assert(bridge.smt2.contains("(define-fun semantic-normalize"), bridge.smt2)
    assert(bridge.smt2.contains("(declare-fun code-reduce"), bridge.smt2)
    assert(bridge.smt2.contains("(declare-fun code-leq"), bridge.smt2)
    assert(bridge.smt2.contains("(declare-fun code-join"), bridge.smt2)
    assert(bridge.smt2.contains("(declare-fun code-meet"), bridge.smt2)
    assert(!bridge.smt2.contains("negative-control mutation"), bridge.smt2)
    assert(mutation.smt2.contains("deliberately flipped production output"), mutation.smt2)
    assertNotEquals(bridge.smt2, mutation.smt2)
  }

  test("range encoding reduces sentinels and grows linearly with universe width") {
    val shortCtx = PA.Ctx(Vector("a", "b", "c"), maxLen = 3)
    val longCtx = PA.Ctx(Vector("a", "b", "c"), maxLen = 4)
    val x = PA.Var("X")

    val full = PA.Law("range-full", PA.Range(x, 0, 0), x).smt2(longCtx)
    val empty = PA.Law("range-empty", PA.Range(x, 2, 2), PA.Empty).smt2(longCtx)
    val shortSlice = PA.Law("range-first", PA.Range(x, 0, 1), PA.Empty).smt2(shortCtx)
    val longSlice = PA.Law("range-first", PA.Range(x, 0, 1), PA.Empty).smt2(longCtx)
    val rankIncrement = raw"\(ite \(= \(\(_ extract \d+ \d+\) (?:X|__pa_direct_range_src)\) #b1\) \(_ bv1 \d+\) \(_ bv0 \d+\)\)".r

    assert(full.contains("(assert (not (= X X)))"), full)
    assert(empty.contains(s"(assert (not (= ${longCtx.zero} ${longCtx.zero})))"), empty)
    assertEquals(rankIncrement.findAllIn(longSlice).length, longCtx.width)
    val directSlice = PA.Range(x, 0, 1).smt(longCtx)
    assert(!directSlice.contains("__pa_direct_range_rank_0"), directSlice)
    assertEquals(rankIncrement.findAllIn(directSlice).length, longCtx.width)
    assert(
      longSlice.length < shortSlice.length * 4,
      s"range SMT should grow linearly: short=${shortSlice.length}, long=${longSlice.length}",
    )
    assert(longSlice.length < 200000, s"unexpectedly large range SMT: ${longSlice.length} bytes")
  }

  test("nested range SMT composes every static-safe suffix and prefix family") {
    val ctx = PA.Ctx(Vector("a", "b"), maxLen = 2)
    val source = PA.Var("X")
    val positives = (1 to ctx.width + 2).toVector
    val negatives = (-1 to -(ctx.width + 2) by -1).toVector

    val positiveSuffixes =
      for
        innerStart <- positives
        outerStart <- positives
      yield (
        s"positive suffix $innerStart then $outerStart",
        PA.Range(PA.Range(source, innerStart, 0), outerStart, 0),
        PA.Range(source, innerStart + outerStart - 1, 0),
      )
    val positivePrefixes =
      for
        innerStart <- positives
        outerEnd <- positives
      yield (
        s"positive suffix $innerStart then prefix $outerEnd",
        PA.Range(PA.Range(source, innerStart, 0), 0, outerEnd),
        PA.Range(source, innerStart, innerStart + outerEnd),
      )
    val negativeSuffixes =
      for
        innerStart <- negatives
        outerStart <- negatives
      yield (
        s"negative suffix $innerStart then $outerStart",
        PA.Range(PA.Range(source, innerStart, 0), outerStart, 0),
        PA.Range(source, math.max(innerStart, outerStart), 0),
      )
    val coveredNegativeSuffixes =
      for
        innerStart <- negatives
        outerEnd <- positives
        if outerEnd.toLong >= -innerStart.toLong
      yield (
        s"negative suffix $innerStart then covering prefix $outerEnd",
        PA.Range(PA.Range(source, innerStart, 0), 0, outerEnd),
        PA.Range(source, innerStart, 0),
      )
    val cases = positiveSuffixes ++ positivePrefixes ++ negativeSuffixes ++ coveredNegativeSuffixes

    // This oracle deliberately evaluates the original tree: evaluate does not
    // call the SMT-only normalization being tested here.
    (0 until (1 << ctx.width)).foreach { mask =>
      val selected = ctx.paths.zipWithIndex.collect {
        case (path, i) if (mask & (1 << i)) != 0 => path
      }.toSet
      val variables = Map("X" -> selected)
      cases.foreach { (label, original, composed) =>
        assertEquals(
          PA.evaluate(original, ctx, variables),
          PA.evaluate(composed, ctx, variables),
          s"$label diverged for mask=$mask",
        )
      }
    }

    val structuralCases = Vector(
      positiveSuffixes.last,
      positivePrefixes.last,
      negativeSuffixes.last,
      coveredNegativeSuffixes.last,
    )
    val rankIncrement = raw"\(bvadd ".r
    structuralCases.foreach { (label, original, composed) =>
      val direct = original.smt(ctx)
      assertEquals(direct, composed.smt(ctx), s"direct emitter did not compose $label")
      assertEquals(rankIncrement.findAllIn(direct).length, ctx.width, s"direct emitter retained a nested Range for $label")

      val shared = PA.Law(s"nested-range-$label", original, composed).smt2(ctx)
      assertEquals(rankIncrement.findAllIn(shared).length, ctx.width, s"shared emitter retained a nested Range for $label")
    }

    val decreasing = Vector(
      PA.Range(source, 3, 2),
      PA.Range(source, -2, -3),
    )
    decreasing.foreach { original =>
      (0 until (1 << ctx.width)).foreach { mask =>
        val selected = ctx.paths.zipWithIndex.collect {
          case (path, i) if (mask & (1 << i)) != 0 => path
        }.toSet
        assertEquals(PA.evaluate(original, ctx, Map("X" -> selected)), Set.empty)
      }
      assertEquals(original.smt(ctx), ctx.zero, s"direct emitter retained decreasing $original")
      val shared = PA.Law(s"decreasing-$original", original, PA.Empty).smt2(ctx)
      assert(!shared.contains("__pa_range_rank_"), s"shared emitter retained decreasing $original")
    }
  }

  test("tails-union laws cover every configured alphabet branch") {
    val ctx = PA.Ctx(Vector("a", "b", "c"), maxLen = 3)
    val laws = PA.laws(ctx.alphabet).map(law => law.name -> law).toMap
    val source = Set(Vector("c", "a", "a"), Vector("b", "b"))
    val variables = Map("X" -> source)

    Vector("tails_union_children", "child_tails_union_a", "child_tails_union_b").foreach { name =>
      val law = laws(name)
      assertEquals(
        PA.evaluate(law.lhs, ctx, variables),
        PA.evaluate(law.rhs, ctx, variables),
        s"$name omitted a configured frontier branch",
      )
    }
  }

  test("Vampire closure proofs are decomposed into plain-strategy named lemmas") {
    val problems = PA.vampireProblems.map(problem => problem.name -> problem).toMap
    val plainNames = Set(
      "spatial_optimizer_preserves_analysis_soundness_fo",
      "set_suffix_closure_nonempty_recurrence_fo",
      "set_child_suffix_closure_derivative",
      "antimirov_suffix_frontier_state_child_fo",
      "antimirov_suffix_frontier_nested_fo",
      "spatial_tails_union_monotone_fo",
      "spatial_prefix_closure_monotone_fo",
      "spatial_suffix_closure_monotone_fo",
      "spatial_tails_closure_monotone_fo",
      "spatial_closure_transfer_sound_fo",
    )

    plainNames.foreach { name =>
      assertEquals(problems(name).note, "vampire-strategy=plain", name)
    }
    assertEquals(PA.VampireProblem("default", "", "").note, "")

    val recurrence = problems("set_suffix_closure_nonempty_recurrence_fo")
    assert(recurrence.prelude.contains("path_suffix_step_decompose"), recurrence.prelude)
    assert(recurrence.conjecture.contains("p_mem(cons(I,P),ssuffix_closure(A))"), recurrence.conjecture)

    Vector(
      "set_child_suffix_closure_derivative",
      "antimirov_suffix_frontier_state_child_fo",
      "antimirov_suffix_frontier_nested_fo",
    ).foreach { name =>
      val prelude = problems(name).prelude
      assert(prelude.contains("lemma_set_suffix_closure_nonempty_recurrence"), prelude)
      assert(!prelude.contains("set_range"), s"$name retained the broad trie/set prelude")
    }

    val transferPrelude = problems("spatial_closure_transfer_sound_fo").prelude
    Vector("tails_union", "prefix_closure", "suffix_closure", "tails_closure").foreach { operation =>
      assert(transferPrelude.contains(s"lemma_spatial_${operation}_monotone"), transferPrelude)
    }
    assert(!transferPrelude.contains("spatial_set_tails_union"), transferPrelude)
    assert(!transferPrelude.contains("spatial_set_suffix_closure"), transferPrelude)
  }

  test("declared fixpoint round bounds agree with exact finite iteration") {
    val ctx = PA.Ctx(Vector("a", "b"), maxLen = 2)
    val laws = PA.laws(ctx.alphabet)
    val classifiedNames = Set(
      "fixpoint_tail_closure",
      "fixpoint_head_closure",
      "fixpoint_reconstruct_identity",
      "fixpoint_prefixed_reconstruct_empty_prefix_identity",
      "fixpoint_range_tail_full_sentinel_closure",
      "fixpoint_range_tail_empty_slice_identity",
      "fixpoint_range_reconstruct_full_sentinel_identity",
      "fixpoint_range_reconstruct_first_identity",
      "fixpoint_range_reconstruct_drop_last_identity",
      "fixpoint_prefixed_range_reconstruct_empty_prefix_first_identity",
      "fixpoint_prefixed_range_reconstruct_empty_prefix_drop_last_identity",
      "bad_fixpoint_range_tail_first_as_tail_closure_generated_negative_control",
      "bad_fixpoint_prefixed_reconstruct_nonempty_prefix_identity_generated_negative_control",
      "bad_fixpoint_prefixed_range_reconstruct_nonempty_prefix_identity_generated_negative_control",
    )
    val expressions = laws.filter(law => classifiedNames(law.name)).map(_.lhs)
    assertEquals(expressions.length, classifiedNames.size)
    expressions.foreach {
      case fix: PA.FixpointExpr =>
        assertNotEquals(fix.roundBound, PA.FixpointRoundBound.FiniteUniverse)
      case other => fail(s"expected classified fixpoint, got $other")
    }

    val universe = ctx.paths
    (0 until (1 << ctx.width)).foreach { mask =>
      val source = universe.zipWithIndex.collect { case (path, i) if (mask & (1 << i)) != 0 => path }.toSet
      val variables = Map("X" -> source)
      expressions.foreach { expr =>
        assertEquals(
          PA.evaluate(expr, ctx, variables, respectFixpointRoundBounds = true),
          PA.evaluate(expr, ctx, variables),
          s"declared fixpoint bound diverged for mask=$mask expr=$expr",
        )
      }
    }
  }
