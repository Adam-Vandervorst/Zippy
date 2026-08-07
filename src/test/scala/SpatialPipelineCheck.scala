package morkl

import munit.FunSuite

/** THE PIPELINE, unit by unit and end to end (review.md finding 3).
 *
 *  `eval` / `evalI` / `execT` / `execZ` appear here ONLY as ground truth — every one of them is
 *  instrumented (SpatialEvents.scala), so the strongest possible no-evaluation gate is available and
 *  used: run a pipeline stage inside `EffortSink.count` and assert the event vector is EMPTY.  A single
 *  interpreter dispatch anywhere under the analysis would show up. */
class SpatialPipelineCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  // ================================================================================================
  //  fixtures
  // ================================================================================================
  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  def lit(ps: PathValue*): Space = Space.Literal(sv(ps*))
  def cp(items: String*): Path = Path.Constant(p(items*))
  val M = SpaceMention("m")
  val R = SpaceMention("r")
  val H = PathRef("h").known(1)
  val anon = SpaceMention("_")
  def deref(pr: PathRef): Path = Path.Deref(pr)

  /** THE HEADLINE RECURSION (the same routine `SpatialRecursionCheck` uses):
   *  `walk(m) = m.iter(h, r, {h} ∪ walk(r))` — one item consumed per call. */
  val walkPtr = RoutinePtr("walk")
  val walk = Routine(walkPtr, Vector.empty, Vector(M),
    Space.Iteration(Space.Mention(M), H, R,
      Space.Union(Space.Singleton(deref(H)), Space.Call(walkPtr, Vector.empty, Vector(Space.Mention(R))))))
  val walkTable: PartialFunction[RoutinePtr, Routine] = Map(walkPtr -> walk)

  val alphabet = Vector("a", "b", "c")
  def randInput(rng: java.util.Random, minLen: Int, maxLen: Int, maxPaths: Int): SpaceValue =
    val n = rng.nextInt(maxPaths + 1)
    SpaceValue((0 until n).map { _ =>
      val k = minLen + rng.nextInt(maxLen - minLen + 1)
      PathValue(List.fill(k)(alphabet(rng.nextInt(alphabet.length))))
    }.toSet)

  def runWith(s: Space, spaces: Map[SpaceMention, SpaceValue],
              paths: Map[PathRef, PathValue] = Map.empty,
              rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): SpaceValue =
    eval(s)(using PathContextMap(paths), SpaceContextMap(spaces), rc)

  /** THE NO-EVALUATION ORACLE.  Every executor in the tree is instrumented (SpatialEvents.scala), so
   *  an EMPTY event vector proves that no interpreter ran inside `body` — a far stronger gate than a
   *  throwing sentinel, which only catches the paths the sentinel happens to sit on.
   *
   *  It is applied to stages run with `ordinaryLower = false`.  The reason is a property of the
   *  PRE-EXISTING ordinary optimizer, not of this pipeline: `Lower.ConstantOps` (MORKL.scala:1613)
   *  *tries* `eval` on every node and folds the ones that do not throw, and `Lower.LiteralSpaceOps`
   *  calls `eval` on every literal-operand algebra node.  `Routine.optimized` is therefore a partial
   *  evaluator, and a stage that calls it cannot be event-free.  The test
   *  "the ORDINARY optimizer is a partial evaluator" below pins that attribution down. */
  def noEvaluation[A](label: String)(body: => A): A =
    val (a, ev) = EffortSink.count(body)
    assertEquals(ev.total, 0L, s"$label EVALUATED its subject: ${ev.show}")
    a

  /** the same annotations with the ordinary rule list off, so the pipeline is purely spatial */
  def strict(ann: SpatialAnnotations): SpatialAnnotations = ann.copy(ordinaryLower = false)

  // ================================================================================================
  //  1.  SCOPE — what makes a fact conditional
  // ================================================================================================
  test("scope: no annotation is UNCONDITIONAL; a ⊤ annotation still is; a real one is CONDITIONAL") {
    assertEquals(SpatialAnnotations.open().scope, FactScope.Unconditional)
    // declaring ⊤ excludes no input, so it must not turn an unconditional rewrite into a guarded one
    val top = SpatialAnnotations(spaces = Map(M -> SpatialType.top))
    assertEquals(top.scope, FactScope.Unconditional, s"⊤ is not a precondition: ${top.scope.show}")
    assertEquals(SpatialAnnotations(pathLens = Map(H -> Lower.LenBounds.unknown)).scope,
                 FactScope.Unconditional)
    // a real input type, a known constant path, and a length window each restrict
    assert(SpatialAnnotations(spaces = Map(M -> SpatialRecursion.lengthAnnotation(1, 4))).scope.conditional)
    assert(SpatialAnnotations(paths = Map(H -> p("a"))).scope.conditional)
    assert(SpatialAnnotations(pathLens = Map(H -> Lower.LenBounds(1, 1))).scope.conditional)
  }

  /** THE EMPTY SPACE IS NOT THE EPSILON SPACE — and they `pretty`-print identically (`{}`), because
   *  `PathValue(Nil).show` is the empty string.  This cost me a misread of a `Refuted` witness, so it is
   *  pinned here: a "every path has exactly one item" contract ADMITS `∅` (vacuously) and REJECTS
   *  `{ε}` (the empty path has zero items).  A test that confuses them tests nothing. */
  test("∅ and {ε} are different values, and a ∀-path length contract separates them") {
    val one = SpatialRecursion.lengthAnnotation(1, 1)
    val nothing = SpaceValue(Set.empty)
    val epsOnly = sv(PathValue(Nil))
    assertEquals(nothing.pretty, epsOnly.pretty, "they really do render the same — hence this test")
    assert(nothing != epsOnly)
    assert(SpatialTyping.accepts(nothing, one), s"∅ satisfies a ∀-path claim vacuously: ${one.show}")
    assert(!SpatialTyping.accepts(epsOnly, one), "{ε} has a zero-item path, so it violates it")
    assert(SpatialTyping.accepts(sv(p("a")), one))
    assert(!SpatialTyping.accepts(sv(p("a", "b")), one))
    assert(SpatialTyping.accepts(nothing, SpatialType.reduce(one)), "and the reducer keeps that")
  }

  test("analyzeRoutine agrees with the standalone `infer` and indexes every occurrence") {
    val body = Space.Union(Space.Intersection(lit(p("a")), lit(p("a"))), lit(p("b")))
    val r = Routine(RoutinePtr("t"), Vector.empty, Vector.empty, body)
    val a = noEvaluation("analyzeRoutine")(SpatialPipeline.analyzeRoutine(r, SpatialAnnotations.open()))
    val direct = SpatialTyping.infer(body)
    // the decorated root meets the authoritative query, so it is never WEAKER than `infer`
    assert(SpatialType.leq(a.result, direct) || a.result == direct,
           s"decorated root ${a.result.show} must be below the query ${direct.show}")
    assert(a.unconditional)
    assert(a.consistent)
    assertEquals(a.decorated.at(NodeId(Vector.empty)).map(_.expression), Some(body))
    assertEquals(a.decorated.at(NodeId(Vector(0))).map(_.expression),
                 Some(Space.Intersection(lit(p("a")), lit(p("a")))))
    assert(a.facts.contains(Fact.MaximumCardinality(2)), s"root facts ${a.facts}")
  }

  test("a CONTRADICTORY annotation licenses NO rewrite (bottom is a vacuous ∀-input claim)") {
    // "every path has exactly 2 items" ∧ "the value is {a}" cannot both hold
    val bad = SpatialType(Shape.of(sv(p("a"))), SpaceType.closed(2L -> Ivl(1, 1)))
    val r = Routine(RoutinePtr("t"), Vector.empty, Vector(M), Space.Mention(M))
    val ann = SpatialAnnotations(spaces = Map(M -> bad))
    val a = SpatialPipeline.analyzeRoutine(r, ann)
    assert(!a.consistent, s"expected bottom, got ${a.result.show}")
    val g = SpatialPipeline.optimizeGuarded(r, a)
    assertEquals(g.applied, Vector.empty, "no rewrite may be derived from bottom")
    assertEquals(g.residual.body, g.fallback.body)
    assert(g.notes.exists(_.contains("bottom")), g.notes.mkString("; "))
  }

  // ================================================================================================
  //  2.  THE ARTIFACT — unconditional vs guarded
  // ================================================================================================
  /** An emptiness proof that is UNCONDITIONAL (`M` is free and untyped) and that no `Lower` rule can
   *  make: the two operands are wrapped by DIFFERENT constant prefixes, so no path can be in both.
   *  `Lower`'s literal folders cannot touch it (neither operand is a `Literal`) and `Lower.SizeEmpty`
   *  reads only `sizeBounds`, which does not model prefix disjointness. */
  val prefixDisjoint: Space =
    Space.Intersection(Space.Wrap(Space.Mention(M), cp("x")), Space.Wrap(Space.Mention(M), cp("y")))

  val M2 = SpaceMention("m2")

  /** `x ∖ x = ∅` for an ARBITRARY open `x` — measured below to be a spatial-only win: the ordinary
   *  rule list leaves all three nodes standing. */
  val selfSubtract: Space = Space.Subtraction(Space.Mention(M), Space.Mention(M))

  test("UNCONDITIONAL facts produce an EMPTY precondition, so `applicableTo` is vacuously true") {
    // the ROOT must stay open, or the whole term folds to a constant and the point is lost
    val body = Space.Union(Space.Mention(M2), selfSubtract)
    val r = Routine(RoutinePtr("u"), Vector.empty, Vector(M, M2), body)
    val a = SpatialPipeline.analyzeRoutine(r, SpatialAnnotations.open())
    val g = SpatialPipeline.optimizeGuarded(r, a)
    println(s"\n[unconditional] spatial  ${g.residual.body.show}")
    println(s"[unconditional] ordinary ${g.fallback.body.show}")
    assert(!g.guarded, s"unconditional facts must not produce a guard: ${g.show}")
    assert(g.applied.exists(_.isInstanceOf[Rewrite.EliminateEmpty]), g.show)
    val spec = g.asSpecialized
    assertEquals(spec.precondition, Map.empty[SpaceMention, SpatialType])
    assert(spec.applicableTo(Map.empty), "an empty precondition admits every input")
    assertEquals(spec.residual.body, g.residual.body, "the safe artifact carries the REAL residual")
    // ---- differentially equal for EVERY input, which is what "unconditional" means -------------
    val rng = new java.util.Random(9182736L)
    for _ <- 0 until 200 do
      val v = randInput(rng, 0, 3, 5)
      val w = randInput(rng, 0, 3, 5)
      assertEquals(runWith(g.residual.body, Map(M -> v, M2 -> w)),
                   runWith(body, Map(M -> v, M2 -> w)),
                   s"unconditional residual disagrees on ${v.pretty} / ${w.pretty}")
    // ---- and the ordinary optimizer alone cannot do it ----------------------------------------
    assert(g.changed, s"the analysis proved something but nothing changed: ${g.show}")
    assert(SpatialPipeline.nodeCount(g.residual.body) < SpatialPipeline.nodeCount(g.fallback.body),
      s"the spatial residual must be smaller: ${g.residual.body.show} vs ${g.fallback.body.show}")
  }

  /** WHERE THE SPATIAL TIER ACTUALLY WINS over the ordinary optimizer, on OPEN terms (a closed term is
   *  fully folded by `Lower.ConstantOps`' partial evaluator, so nothing can be learned there).  This
   *  prints the comparison and asserts that at least one row is a spatial-only win — which is
   *  review.md finding 7's "spatial facts change the ordinary optimized program", unconditionally. */
  test("spatial-only UNCONDITIONAL wins over the ordinary optimizer, on open terms") {
    val cases = Vector[(String, Space, Vector[SpaceMention])](
      ("prefix-disjoint ∩", prefixDisjoint, Vector(M)),
      ("x ∖ x", selfSubtract, Vector(M)),
      // a CONTROL: this one is genuinely NOT empty, so a tier that "proved" it would be unsound
      ("∩ with its own tails (live)", Space.Intersection(Space.Wrap(Space.Mention(M), cp("x")),
                                               Space.TailsUnion(Space.Wrap(Space.Mention(M), cp("x")))),
        Vector(M)),
      // EMPTY, and neither tier proves it: the body is a constant singleton, so the iteration yields
      // at most one path and a window starting at index 4 cannot select anything.  A gap, recorded.
      ("range past a proved size", Space.Range(
        Space.Iteration(Space.Mention(M), H, anon, Space.Singleton(cp("k"))), 5, 6), Vector(M)),
      ("iterate an empty source", Space.Iteration(prefixDisjoint, H, R, Space.Mention(R)), Vector(M)),
      ("∅-restricted", Space.Restriction(Space.Mention(M2), prefixDisjoint), Vector(M, M2)),
    )
    var wins = 0
    println("\n[spatial-vs-ordinary]")
    for (name, body, ms) <- cases do
      val r = Routine(RoutinePtr("w"), Vector.empty, ms, body)
      val g = SpatialPipeline.optimizeGuarded(r, SpatialPipeline.analyzeRoutine(r, SpatialAnnotations.open()))
      val sp = SpatialPipeline.nodeCount(g.residual.body)
      val or = SpatialPipeline.nodeCount(g.fallback.body)
      val win = sp < or
      if win then wins += 1
      println(f"  $name%-26s spatial=$sp%3d  ordinary=$or%3d  ${if win then "SPATIAL WINS" else "tie"}" +
              f"   ${g.residual.body.show.replace('\n', ' ').take(52)}")
      assert(!g.guarded, s"$name must stay unconditional")
      // whatever happened, it must be correct for EVERY input
      val rng = new java.util.Random(555L)
      for _ <- 0 until 60 do
        val env = ms.map(_ -> randInput(rng, 0, 3, 4)).toMap
        assertEquals(runWith(g.residual.body, env), runWith(body, env), s"$name on $env")
    assert(wins >= 1, "no unconditional spatial-only win was found on these six open terms")
    println(s"  => $wins of ${cases.size} are spatial-only wins")
  }

  test("the ORDINARY optimizer is a PARTIAL EVALUATOR — which is why the no-eval gate is scoped") {
    // this is an attribution test, not a complaint: `Lower.ConstantOps` tries `eval` on every node
    val closed = Space.Union(lit(p("a")), lit(p("b")))
    val r = Routine(RoutinePtr("closed"), Vector.empty, Vector.empty, closed)
    val (_, viaLower) = EffortSink.count(r.optimized)
    assert(viaLower.total > 0L,
      "Lower.ConstantOps/LiteralSpaceOps fold by EVALUATING closed subterms; if this ever becomes " +
      "event-free the gate below can be tightened to the whole pipeline")
    println(s"\n[attribution] Routine.optimized on a closed term counts ${viaLower.showComponents}")
    // with the ordinary rule list off, the whole pipeline is event-free
    val ann = strict(SpatialAnnotations.open())
    val a = noEvaluation("analyze")(SpatialPipeline.analyzeRoutine(r, ann))
    val g = noEvaluation("optimizeGuarded (spatial only)")(SpatialPipeline.optimizeGuarded(r, a))
    for b <- Backend.values.toVector do
      noEvaluation(s"lower/${b.slug} (spatial only)")(SpatialPipeline.lower(g, b, ann))
    // and the spatially folded body is the same value the partial evaluator computes
    assertEquals(runWith(g.residual.body, Map.empty), runWith(closed, Map.empty))
  }

  test("CONDITIONAL facts produce a GUARDED artifact whose fallback is the ordinary optimizer") {
    val ann = SpatialAnnotations(spaces = Map(M -> SpatialRecursion.lengthAnnotation(1, 4)),
                                 routines = walkTable)
    val a = SpatialPipeline.analyzeRoutine(walk, ann)
    assert(a.scope.conditional, a.scope.show)
    val g = SpatialPipeline.optimizeGuarded(walk, a)
    assert(g.guarded, s"a declared input type must produce a guard: ${g.show}")
    assertEquals(g.spacePrecondition.keySet, Set(M))
    assert(g.pathPreconditionRepresentable, "this precondition has no path channel")
    // the fallback is the ORDINARY optimizer's output: choosing it costs nothing relative to not
    // having run the pipeline at all
    assertEquals(g.fallback.body, walk.optimized(using walkTable).body)
    // the dispatcher: conforming input -> residual, violating input -> fallback
    val ok = sv(p("a", "b"), p("c"))
    val tooLong = sv(p("a", "b", "c", "d", "e"))
    assert(g.applicableTo(Map(M -> ok)), "a 2-item-max input satisfies maxLen 4")
    assert(!g.applicableTo(Map(M -> tooLong)), "a 5-item input violates maxLen 4")
    assertEquals(g.choose(Map(M -> ok)).body, g.residual.body)
    assertEquals(g.choose(Map(M -> tooLong)).body, g.fallback.body)
    assert(!g.applicableTo(Map.empty), "a missing argument must not be admitted")
  }

  test("a PATH precondition cannot be represented by `SpecializedRoutine`, so that view degrades") {
    // `peel(p0, m) = heads(m) ∪ peel(p0, m(p0))` — the bound depends on P0's LENGTH
    val P0 = PathRef("p0")
    val peelPtr = RoutinePtr("peel")
    val heads = Space.Iteration(Space.Mention(M), H, anon, Space.Singleton(deref(H)))
    val peel = Routine(peelPtr, Vector(P0), Vector(M),
      Space.Union(heads, Space.Call(peelPtr, Vector(deref(P0)),
                                    Vector(Space.Unwrap(Space.Mention(M), deref(P0))))))
    val ann = SpatialAnnotations(spaces = Map(M -> SpatialRecursion.lengthAnnotation(1, 4)),
                                 pathLens = Map(P0 -> Lower.LenBounds(1, 1)),
                                 routines = Map(peelPtr -> peel))
    val a = SpatialPipeline.analyzeRoutine(peel, ann)
    val g = SpatialPipeline.optimizeGuarded(peel, a)
    assert(g.guarded)
    assert(!g.pathPreconditionRepresentable)
    val spec = g.asSpecialized
    // the ONE thing that must never happen: a conditionally-valid body behind an empty precondition
    if spec.precondition.isEmpty then
      assertEquals(spec.residual.body, g.fallback.body,
        "an artifact with an empty precondition MUST be the unconditional fallback, never the residual")
      assertEquals(spec.facts, Vector.empty[Fact],
        "facts derived under a condition must not travel on an unconditional artifact")
    assert(g.notes.exists(_.contains("PATH channel")) || g.applied.isEmpty, g.notes.mkString("; "))
    // the full-fidelity artifact still dispatches on the path channel
    assert(g.applicableTo(Map(M -> sv(p("a", "b"))), Map(P0 -> p("a"))))
    assert(!g.applicableTo(Map(M -> sv(p("a", "b"))), Map(P0 -> p("a", "b"))))
  }

  // ================================================================================================
  //  3.  END TO END #1 — whispers §6: maxLen  =>  Call-free code
  // ================================================================================================
  test("END TO END: maxLen 4 => a Call-free lowered routine, differentially equal, 0 CallEntry events") {
    val ann = SpatialAnnotations(spaces = Map(M -> SpatialRecursion.lengthAnnotation(1, 4)),
                                 routines = walkTable)
    // the derivation itself — analysis, measure, summaries, unrolling — is EVENT-FREE
    val sa = noEvaluation("analyzeRoutine")(SpatialPipeline.analyzeRoutine(walk, strict(ann)))
    noEvaluation("optimizeGuarded (spatial only)")(SpatialPipeline.optimizeGuarded(walk, sa))
    noEvaluation("residualiseBounded")(SpatialPipeline.residualiseBounded(walk, strict(ann)))
    // the artifact the ordinary pipeline would install (the `Lower` rule list included)
    val a = SpatialPipeline.analyzeRoutine(walk, ann)
    val g = SpatialPipeline.optimizeGuarded(walk, a)
    val l = SpatialPipeline.lower(g, Backend.Trie, ann)

    assert(g.applied.exists(_.isInstanceOf[Rewrite.Residualise]),
           s"the bounded recursion must be residualised: ${g.show}")
    assert(SpatialPipeline.isCallFree(g.residual.body), s"residual still has a Call: ${g.residual.body.show}")
    assert(!SpatialPipeline.isCallFree(walk.body), "the original really does contain a Call")
    assert(l.callFree, "the lowered routine must be Call-free")

    val origNodes = SpatialPipeline.nodeCount(walk.body)
    val resNodes = SpatialPipeline.nodeCount(g.residual.body)
    println(s"\n[E2E-1 walk] ${g.applied.map(_.show).mkString("; ")}")
    println(s"[E2E-1 walk] nodes $origNodes -> $resNodes; lowered(${l.backend.slug}) ${l.nodes} nodes")

    // ---- differential on inputs SATISFYING the precondition -----------------------------------
    val rng = new java.util.Random(20260807L)
    var checked = 0
    var origCalls = 0L
    var resCalls = 0L
    for _ <- 0 until 300 do
      val v = randInput(rng, 1, 4, 6)
      assert(g.applicableTo(Map(M -> v)), s"generator produced a non-conforming input ${v.pretty}")
      val (expect, e1) = EffortSink.count(runWith(Space.Call(walkPtr, Vector.empty, Vector(Space.Mention(M))),
                                                  Map(M -> v), rc = walkTable))
      val (got, e2) = EffortSink.count(runWith(l.body, Map(M -> v)))
      assertEquals(got, expect, s"the lowered routine disagrees on the conforming input ${v.pretty}")
      origCalls += e1(EffortEvent.CallEntry)
      resCalls += e2(EffortEvent.CallEntry)
      checked += 1
    assertEquals(checked, 300)
    println(s"[E2E-1 walk] $checked conforming inputs agree; CallEntry events $origCalls -> $resCalls")
    assert(origCalls > 0L, "the original must actually make calls")
    assertEquals(resCalls, 0L, "the lowered routine must make NO call at run time")
  }

  // ================================================================================================
  //  4.  END TO END #2 — exact graph constant folding
  // ================================================================================================
  test("END TO END: an exactly-pinned subterm folds to a constant, and the graph shrinks") {
    // A FREE MENTION with a declared type.  No `Lower` rule can fold it (it is not a `Literal`), and
    // the value comes out of the SHAPE domain — `exactValue` reads the pinned trie and re-checks it
    // against full γ-membership.  Nothing is evaluated.
    val body = Space.Union(Space.Mention(M), Space.Wrap(Space.Mention(M), cp("p")))
    val r = Routine(RoutinePtr("fold"), Vector.empty, Vector(M), body)
    val pinned = sv(p("a"), p("b"))
    val ann = SpatialAnnotations(spaces = Map(M -> SpatialType.of(pinned)))
    val a = noEvaluation("analyze")(SpatialPipeline.analyzeRoutine(r, ann))
    assert(a.candidates.exists(_.spec.isInstanceOf[SpatialSpecialization.GraphConstantFold]),
           s"the root must be pinned: ${a.result.show} / ${a.candidates.map(_.show)}")
    noEvaluation("optimizeGuarded (spatial only)")(
      SpatialPipeline.optimizeGuarded(r, SpatialPipeline.analyzeRoutine(r, strict(ann))))
    noEvaluation("lower/graph (spatial only)")(SpatialPipeline.run(r, strict(ann), Backend.Graph))

    val g = SpatialPipeline.optimizeGuarded(r, a)
    val l = SpatialPipeline.lower(g, Backend.Graph, ann)
    assert(g.guarded, "the fold is CONDITIONAL on the declared input type")

    val truth = runWith(body, Map(M -> pinned))
    l.body match
      case Space.Literal(v) => assertEquals(v, truth, "the folded constant must BE the value")
      case other => fail(s"expected a folded Literal, got ${other.show}")
    // the graph really is smaller than the one the UNANALYSED program lowers to
    val before = SpatialPipeline.graphNodeCount(morkl.optimize(transpile(g.fallback)))
    val after = l.graphNodes.getOrElse(fail("the graph backend must produce a graph"))
    println(s"\n[E2E-2 fold] ${l.applied.map(_.show).mkString("; ")}")
    println(s"[E2E-2 fold] graph slots $before -> $after; consumed ${l.consumed.map(_.show).mkString(", ")}")
    assert(after < before, s"the lowered graph must be smaller: $before -> $after")
    assert(l.consumed.exists(_.isInstanceOf[SpatialSpecialization.GraphConstantFold]),
           s"the graph lowering must record the candidate as CONSUMED: ${l.consumed}")
    // ---- and it is only used where the precondition holds -------------------------------------
    assert(g.applicableTo(Map(M -> pinned)))
    assertEquals(runGraphT(l.graph.get).toSpaceValue, truth)
    val other = sv(p("z"))
    assert(!g.applicableTo(Map(M -> other)), "an input outside the precondition must be rejected")
    assertEquals(g.choose(Map(M -> other)).body, g.fallback.body)
    assertNotEquals(runWith(l.body, Map(M -> other)), runWith(body, Map(M -> other)),
      "the residual really is WRONG outside the precondition — which is why the guard exists")
    assertEquals(runWith(g.choose(Map(M -> other)).body, Map(M -> other)), runWith(body, Map(M -> other)))
  }

  test("constant folding is NOT evaluation: an unpinned subterm is left alone") {
    // a Range window keeps an unknown SUBSET of its source, so nothing is pinned
    val body = Space.Range(lit(p("a"), p("b"), p("c")), 1, 3)
    val r = Routine(RoutinePtr("rng"), Vector.empty, Vector.empty, body)
    val a = SpatialPipeline.analyzeRoutine(r, SpatialAnnotations.open())
    assertEquals(SpatialFacts.exactValue(a.result), None,
                 s"a partial Range must not be pinned: ${a.result.show}")
    val g = SpatialPipeline.optimizeGuarded(r, a)
    assert(!g.applied.exists(_.isInstanceOf[Rewrite.ConstantFold]), g.show)
    // the bound is still derived: at most two of the three paths survive
    assertEquals(a.result.size.hi, 2L, s"the window bound must be derived: ${a.result.show}")
  }

  // ================================================================================================
  //  5.  END TO END #3 — bounded trie unrolling over a PROVED head set
  // ================================================================================================
  test("END TO END: an Iteration over a proved head set unrolls, and LoopBodyEntry drops to 0") {
    val src = lit(p("a", "1"), p("a", "2"), p("b", "3"))
    // the body reads a FREE mention, so the term is not pinned to a constant — otherwise the stage-2
    // constant fold subsumes the loop entirely (which is the better rewrite, and is tested above)
    val body = Space.Iteration(src, H, R,
      Space.Wrap(Space.Intersection(Space.Mention(R), Space.Mention(M)), deref(H)))
    val r = Routine(RoutinePtr("iter"), Vector.empty, Vector(M), body)
    // `ordinaryLower = false`: the point is what the SPATIAL lowering does to the loop, and the
    // ordinary rule list would otherwise partial-evaluate this closed term away entirely
    val ann = strict(SpatialAnnotations.open())
    val a = noEvaluation("analyze")(SpatialPipeline.analyzeRoutine(r, ann))
    val srcFacts = a.factsAt(NodeId(Vector(0)))
    assert(srcFacts.exists { case Fact.ExactHeadSet(hs) => hs == Set("a", "b"); case _ => false },
           s"the source's head set must be PROVED exactly {a,b}: $srcFacts")

    val g = noEvaluation("optimize")(SpatialPipeline.optimizeGuarded(r, a))
    val l = noEvaluation("lower")(SpatialPipeline.lower(g, Backend.Trie, ann))
    assert(l.applied.exists(_.isInstanceOf[Rewrite.UnrollHeads]),
           s"the trie lowering must consume the head set: ${l.show}\n${l.applied.map(_.show)}")
    assert(l.consumed.exists(_.isInstanceOf[SpatialSpecialization.TrieUnroll]) || l.consumed.nonEmpty,
           s"a candidate must be recorded as consumed: ${l.consumed}")

    val mv = sv(p("1"), p("3"), p("9"))
    val truth = runWith(body, Map(M -> mv))
    val (got, ev) = EffortSink.count(runWith(l.body, Map(M -> mv)))
    val (_, ev0) = EffortSink.count(runWith(body, Map(M -> mv)))
    assertEquals(got, truth, s"the unrolled body must denote the same space: ${l.body.show}")
    println(s"\n[E2E-3 unroll] ${l.applied.map(_.show).mkString("; ")}")
    println(s"[E2E-3 unroll] ${body.show.replace('\n', ' ')}\n           => ${l.body.show.replace('\n', ' ')}")
    println(s"[E2E-3 unroll] LoopBodyEntry ${ev0(EffortEvent.LoopBodyEntry)} -> ${ev(EffortEvent.LoopBodyEntry)}" +
            s";  total work ${ev0.work} -> ${ev.work}, alloc ${ev0.alloc} -> ${ev.alloc}")
    assertEquals(ev0(EffortEvent.LoopBodyEntry), 2L, "the original runs one body per head group")
    assertEquals(ev(EffortEvent.LoopBodyEntry), 0L, "the unrolled body runs no dynamic group at all")
    // the pinned source means nothing is duplicated, so this must be a STRICT improvement
    assert(ev.work <= ev0.work, s"the unroll must not cost more work: ${ev0.work} -> ${ev.work}")
    assert(ev.alloc <= ev0.alloc, s"the unroll must not allocate more: ${ev0.alloc} -> ${ev.alloc}")
    val gr = morkl.optimize(transpile(l.routine))
    val grNaive = morkl.optimize(transpile(Routine(r.name, r.refs, r.mentions, body)))
    val (gotG, evG) = EffortSink.count(runGraphT(gr, mentions = Map(M.s -> iLiteral(mv))))
    val (_, evG0) = EffortSink.count(runGraphT(grNaive, mentions = Map(M.s -> iLiteral(mv))))
    assertEquals(gotG.toSpaceValue, truth, "the unrolled graph must agree")
    println(s"[E2E-3 unroll] graph slots after CSE: unrolled ${SpatialPipeline.graphNodeCount(gr)}, " +
            s"original ${SpatialPipeline.graphNodeCount(grNaive)}; EXECUTED slots " +
            s"${evG0(EffortEvent.GraphNodeDispatch)} -> ${evG(EffortEvent.GraphNodeDispatch)}, " +
            s"frames ${evG0(EffortEvent.GraphFrameAllocation)} -> ${evG(EffortEvent.GraphFrameAllocation)}")
    assert(evG(EffortEvent.LoopBodyEntry) == 0L, "no loop body may execute in the unrolled graph")
    assert(evG(EffortEvent.GraphFrameAllocation) <= evG0(EffortEvent.GraphFrameAllocation),
           "the unrolled graph must not allocate more executor frames")
    // and the candidate is REFUSED when the source trie is not pinned (only its head set is known)
    val openSrc = Space.Union(Space.Mention(M2), lit(p("a", "1"), p("b", "2")))
    val openBody = Space.Iteration(Space.Restriction(openSrc, lit(p("a"), p("b"))), H, R,
                                   Space.Wrap(Space.Mention(R), deref(H)))
    val r2 = Routine(RoutinePtr("open"), Vector.empty, Vector(M2), openBody)
    val l2 = SpatialPipeline.lower(
      SpatialPipeline.optimizeGuarded(r2, SpatialPipeline.analyzeRoutine(r2, ann)), Backend.Trie, ann)
    assert(!l2.applied.exists(_.isInstanceOf[Rewrite.UnrollHeads]),
      s"an unpinned source must NOT be unrolled (it would duplicate the source): ${l2.applied.map(_.show)}")
    // a random differential, since the substitution is the risky part
    val rng = new java.util.Random(31337L)
    for _ <- 0 until 200 do
      val v = randInput(rng, 0, 2, 5)
      assertEquals(runWith(l.body, Map(M -> v)), runWith(body, Map(M -> v)),
                   s"unrolled body disagrees on ${v.pretty}")
  }

  test("head unrolling is REFUSED when the body would capture the binder") {
    // the body rebinds `h` and `r`, so substituting them would capture
    val src = lit(p("a", "1"), p("b", "2"))
    val inner = Space.Iteration(Space.Mention(R), H, R, Space.Singleton(deref(H)))
    val body = Space.Iteration(src, H, R, inner)
    val r = Routine(RoutinePtr("cap"), Vector.empty, Vector.empty, body)
    val ann = SpatialAnnotations.open()
    val a = SpatialPipeline.analyzeRoutine(r, ann)
    val l = SpatialPipeline.lower(SpatialPipeline.optimizeGuarded(r, a), Backend.Trie, ann)
    assert(!l.applied.exists { case Rewrite.UnrollHeads(id, _) => id == NodeId(Vector.empty); case _ => false },
           s"the outer iteration must not be unrolled: ${l.applied.map(_.show)}")
    // whatever the pipeline did, it must still be correct
    assertEquals(runWith(l.body, Map.empty), runWith(body, Map.empty))
  }

  // ================================================================================================
  //  6.  END TO END #4 — zipper pre-focus on a common prefix
  // ================================================================================================
  test("END TO END: a common prefix SELECTS zipper pre-focus, and the rewrite is an identity") {
    // a FREE mention keeps the body from folding to a constant — a concrete body has no fusion to
    // steer, and the lowering declines the candidate there (see the "already concrete" test below)
    val body = Space.Union(Space.Wrap(Space.Intersection(lit(p("x"), p("y")), Space.Mention(M)),
                                      cp("Cell", "0")),
                           Space.Wrap(lit(p("z")), cp("Cell", "1")))
    val r = Routine(RoutinePtr("pf"), Vector.empty, Vector(M), body)
    val ann = strict(SpatialAnnotations.open())     // keep the partial evaluator out of the way
    val a = noEvaluation("analyze")(SpatialPipeline.analyzeRoutine(r, ann))
    val cpx = SpatialFacts.commonPrefix(a.result)
    assertEquals(cpx.items, List("Cell"), s"the spine must be proved: ${cpx.show} of ${a.result.show}")
    assert(a.candidates.exists(_.spec == SpatialSpecialization.ZipperPrefocus(PathValue(List("Cell")))),
           s"the pre-focus candidate must be offered: ${a.candidates.map(_.show)}")

    val g = noEvaluation("optimize")(SpatialPipeline.optimizeGuarded(r, a))
    val lz = noEvaluation("lower/zipper")(SpatialPipeline.lower(g, Backend.Zipper, ann))
    val lr = noEvaluation("lower/reference")(SpatialPipeline.lower(g, Backend.Reference, ann))
    assert(lz.consumed.contains(SpatialSpecialization.ZipperPrefocus(PathValue(List("Cell")))),
           s"the ZIPPER lowering must consume the pre-focus: ${lz.show}")
    assert(lr.consumed.isEmpty, s"the REFERENCE lowering has no structural candidate: ${lr.show}")

    // ---- an identity, for EVERY input ---------------------------------------------------------
    val rng = new java.util.Random(8080L)
    for _ <- 0 until 200 do
      val v = randInput(rng, 0, 2, 4)
      val truth = runWith(g.residual.body, Map(M -> v))
      assertEquals(runWith(lz.body, Map(M -> v)), truth, s"pre-focus changed the meaning on ${v.pretty}")
      assertEquals(execZ(lz.body)(using ic = Map(M -> iLiteral(v))).toSpaceValue, truth,
                   s"pre-focus disagrees on the ZIPPER executor for ${v.pretty}")
    val mv = sv(p("x"), p("q"))
    val (_, e0) = EffortSink.count(execZ(g.residual.body)(using ic = Map(M -> iLiteral(mv))))
    val (_, e1) = EffortSink.count(execZ(lz.body)(using ic = Map(M -> iLiteral(mv))))
    println(s"\n[E2E-4 prefocus] spine ${cpx.show}")
    println(s"[E2E-4 prefocus] execZ ZipperCursorRead ${e0(EffortEvent.ZipperCursorRead)} -> " +
            s"${e1(EffortEvent.ZipperCursorRead)}, ZipperBuild ${e0(EffortEvent.ZipperBuild)} -> " +
            s"${e1(EffortEvent.ZipperBuild)}, materialize nodes " +
            s"${e0(EffortEvent.ZipperMaterializeNode)} -> ${e1(EffortEvent.ZipperMaterializeNode)} " +
            "(MEASURED and reported; this candidate is not asserted to be a win — see the report)")
  }

  test("zipper pre-focus is DECLINED on an already-concrete body (it would only add work)") {
    val body = Space.Union(Space.Wrap(lit(p("x"), p("y")), cp("Cell", "0")),
                           Space.Wrap(lit(p("z")), cp("Cell", "1")))
    val r = Routine(RoutinePtr("pfc"), Vector.empty, Vector.empty, body)
    val ann = strict(SpatialAnnotations.open())
    val g = SpatialPipeline.optimizeGuarded(r, SpatialPipeline.analyzeRoutine(r, ann))
    assert(g.residual.body.isInstanceOf[Space.Literal], s"stage 2 must pin it: ${g.residual.body.show}")
    val lz = SpatialPipeline.lower(g, Backend.Zipper, ann)
    assertEquals(lz.consumed, Vector.empty[SpatialSpecialization],
      s"a concrete body lifts to `Lit` and materialises with zero cursor reads: ${lz.show}")
    assert(lz.notes.exists(_.contains("already a concrete literal")), lz.notes.mkString("; "))
    val (_, ez) = EffortSink.count(execZ(lz.body))
    assertEquals(ez(EffortEvent.ZipperCursorRead), 0L, "a `Lit` cursor is read zero times")
    println(s"[E2E-4 prefocus] declined on a concrete body; execZ cursor reads " +
            s"${ez(EffortEvent.ZipperCursorRead)}")
  }

  // ================================================================================================
  //  7.  REWRITING ONLY PROVED CALL SITES
  // ================================================================================================
  test("only the call sites PROVED to satisfy the precondition are redirected") {
    val ann = SpatialAnnotations(spaces = Map(M -> SpatialRecursion.lengthAnnotation(1, 4)),
                                 routines = walkTable)
    val g = SpatialPipeline.optimizeGuarded(walk, SpatialPipeline.analyzeRoutine(walk, ann))
    val specPtr = RoutinePtr("walk$spec")
    // site 1: a literal argument whose every path has 2 items -> PROVED; site 2: an open mention -> not
    val proved = Space.Call(walkPtr, Vector.empty, Vector(lit(p("a", "b"), p("c", "d"))))
    val open = Space.Call(walkPtr, Vector.empty, Vector(Space.Mention(SpaceMention("unknown"))))
    val host = Space.Union(proved, open)
    val (out, ok, no) = noEvaluation("specialiseProvedCallSites")(
      SpatialPipeline.specialiseProvedCallSites(host, walkPtr, specPtr, g, ann))
    println(s"\n[call-sites] $ok proved, $no left general: ${out.show.replace('\n', ' ').take(140)}")
    assertEquals(ok, 1, s"exactly one site is provable: ${out.show}")
    assertEquals(no, 1, s"the open site must keep the general routine: ${out.show}")
    // and the redirected site is differentially equal
    val table: PartialFunction[RoutinePtr, Routine] = Map(walkPtr -> walk, specPtr -> g.residual)
    assertEquals(runWith(out, Map(SpaceMention("unknown") -> sv(p("q"))), rc = table),
                 runWith(host, Map(SpaceMention("unknown") -> sv(p("q"))), rc = walkTable))
  }

  // ================================================================================================
  //  8.  THE HOOK FOR `Routine.optimized`
  // ================================================================================================
  test("the ordinary-optimizer hook rewrites with UNCONDITIONAL facts only, and preserves meaning") {
    // `{len 2} ∩ {len 3} = ∅` — a length-disjointness proof the syntactic `Lower.SizeEmpty` cannot make
    val dead = Space.Intersection(Space.Wrap(lit(p("a")), cp("x")),
                                  Space.Wrap(lit(p("a", "b")), cp("x")))
    val body = Space.Union(lit(p("keep")), dead)
    val rewritten = noEvaluation("unconditionalRewrite")(SpatialPipeline.unconditionalRewrite(body))
    println(s"\n[hook] ${body.show} => ${rewritten.show}")
    assertNotEquals(rewritten, body, "the hook must consume the emptiness proof")
    assertEquals(runWith(rewritten, Map.empty), runWith(body, Map.empty))
    // it is idempotent, and it is a no-op on a program with nothing to prove
    assertEquals(SpatialPipeline.unconditionalRewrite(rewritten), rewritten)
    val plain = Space.Union(Space.Mention(M), lit(p("a")))
    assertEquals(SpatialPipeline.unconditionalRewrite(plain), plain)
    // the cheap configuration must not be UNSOUND, only weaker
    val cheap = SpatialPipeline.unconditionalRewriteCheap(body)
    assertEquals(runWith(cheap, Map.empty), runWith(body, Map.empty))
    // it consumes an INTERPROCEDURAL emptiness proof too, without any input annotation
    val callee = Routine(RoutinePtr("nil"), Vector.empty, Vector.empty, Space.Empty)
    val rc: PartialFunction[RoutinePtr, Routine] = Map(callee.name -> callee)
    val viaCall = Space.Union(lit(p("keep")), Space.Call(callee.name, Vector.empty, Vector.empty))
    val rc2 = SpatialPipeline.unconditionalRewrite(viaCall, rc)
    assertEquals(runWith(rc2, Map.empty, rc = rc), runWith(viaCall, Map.empty, rc = rc))
  }

  // ================================================================================================
  //  9.  POSITIONAL REWRITING
  // ================================================================================================
  test("replaceAt / subtermAt agree with the decorated analysis' NodeIds, on every operator") {
    val terms = Vector[Space](
      Space.Union(lit(p("a")), lit(p("b"))),
      Space.Intersection(lit(p("a")), lit(p("b"))),
      Space.Subtraction(lit(p("a")), lit(p("b"))),
      Space.Restriction(lit(p("a", "b")), lit(p("a"))),
      Space.Raffination(lit(p("a", "b")), lit(p("a"))),
      Space.Composition(lit(p("a")), lit(p("b"))),
      Space.Wrap(lit(p("a")), cp("w")),
      Space.Unwrap(lit(p("w", "a")), cp("w")),
      Space.TailsUnion(lit(p("a", "b"))),
      Space.TailsIntersection(lit(p("a", "b"), p("a", "c"))),
      Space.Range(lit(p("a"), p("b")), 1, 2),
      Space.Iteration(lit(p("a", "b")), H, R, Space.Mention(R)),
      Space.Fixpoint(lit(p("a")), M, Space.Mention(M)),
      Space.Call(walkPtr, Vector.empty, Vector(lit(p("a", "b")))),
    )
    var seen = 0
    for t <- terms do
      val a = SpatialPipeline.analyzeTerm(t, SpatialAnnotations.open(walkTable))
      for n <- a.decorated.nodes do
        seen += 1
        assertEquals(SpatialPipeline.subtermAt(t, n.id.position), Some(n.expression),
                     s"NodeId ${n.id.show} of ${t.show} does not address its own expression")
        val marker = lit(p("#marker#"))
        val replaced = SpatialPipeline.replaceAt(t, n.id.position, marker)
        assert(replaced.nonEmpty, s"replaceAt failed at ${n.id.show} of ${t.show}")
        assertEquals(SpatialPipeline.subtermAt(replaced.get, n.id.position), Some(marker))
        assertEquals(SpatialPipeline.nodeCount(replaced.get) - SpatialPipeline.nodeCount(marker),
                     SpatialPipeline.nodeCount(t) - SpatialPipeline.nodeCount(n.expression),
                     s"replaceAt changed the surrounding term at ${n.id.show} of ${t.show}")
    println(s"\n[positions] ${terms.size} operators, $seen decorated nodes addressed and replaced")
    assert(seen >= terms.size * 2)

    // out-of-range positions are refused, never guessed
    assertEquals(SpatialPipeline.replaceAt(lit(p("a")), Vector(0), Space.Empty), None)
    assertEquals(SpatialPipeline.subtermAt(Space.Union(lit(p("a")), lit(p("b"))), Vector(5)), None)
  }

  // ================================================================================================
  //  10.  BACKEND SELECTION
  // ================================================================================================
  test("selectBackend compares the four per-backend intervals over the SAME facts") {
    val body = Space.Iteration(lit(p("a", "1"), p("b", "2"), p("c", "3")), H, R,
                               Space.Wrap(Space.Mention(R), deref(H)))
    val ann = SpatialAnnotations.open()
    val (best, scores) = noEvaluation("selectBackend")(SpatialPipeline.selectBackend(body, ann))
    println("\n[select] " + scores.toVector.sortBy(_._1.ordinal)
      .map((b, s) => f"${b.slug}=${s}%.0f").mkString("  ") + s"  => ${best.slug}")
    assertEquals(scores.size, 4, "every executable must be priced")
    assert(scores.values.forall(_ >= 0.0))
    assertEquals(best, Backend.values.toVector.minBy(b => (scores(b), b.ordinal)), "deterministic argmin")
    // the per-backend map on the analysis is the same set of keys
    val a = SpatialPipeline.analyzeTerm(body, ann)
    assertEquals(a.backendCost.keySet, Backend.values.toSet)
  }

  test("runAll lowers ONE analysis onto every backend, and every backend is differentially equal") {
    val body = Space.Union(Space.Wrap(lit(p("x"), p("y")), cp("Cell")),
                           Space.Subtraction(lit(p("Cell", "z")), lit(p("Cell", "z"))))
    val r = Routine(RoutinePtr("all"), Vector.empty, Vector.empty, body)
    val ann = strict(SpatialAnnotations.open())
    val all = noEvaluation("runAll")(SpatialPipeline.runAll(r, ann))
    val truth = runWith(body, Map.empty)
    println("\n[runAll]")
    for b <- Backend.values.toVector do
      val l = all(b)
      println("  " + l.show.replace("\n", "\n  "))
      assertEquals(runWith(l.body, Map.empty), truth, s"${b.slug} lowering changed the meaning")
      assertEquals(evalI(l.body).toSpaceValue, truth, s"${b.slug} lowering disagrees on evalI")
      if b == Backend.Zipper then assertEquals(execZ(l.body).toSpaceValue, truth)
      if b == Backend.Graph then l.graph.foreach(g => assertEquals(runGraphT(g).toSpaceValue, truth))
    assertEquals(all.keySet, Backend.values.toSet)
  }

  // ================================================================================================
  //  11.  NO EVALUATION, MECHANICALLY
  // ================================================================================================
  test("NO EVALUATION: every pipeline stage on a term whose grounded atom THROWS if it is run") {
    val bomb: Space = Space.GroundedSS(lit(p("a")),
      _ => throw RuntimeException("the pipeline evaluated its subject"))
    // the sentinel is live
    intercept[RuntimeException] { eval(bomb) }

    val body = Space.Union(Space.Wrap(bomb, cp("k")), lit(p("k", "z")))
    val r = Routine(RoutinePtr("bomb"), Vector.empty, Vector.empty, body)
    val ann = strict(SpatialAnnotations.open())
    val a = noEvaluation("analyzeRoutine")(SpatialPipeline.analyzeRoutine(r, ann))
    val g = noEvaluation("optimizeGuarded")(SpatialPipeline.optimizeGuarded(r, a))
    for b <- Backend.values.toVector do
      noEvaluation(s"lower/${b.slug}")(SpatialPipeline.lower(g, b, ann))
    noEvaluation("selectBackend")(SpatialPipeline.selectBackend(body, ann))
    noEvaluation("profile")(a.profile)
    noEvaluation("backendCost")(a.backendCost)
    noEvaluation("run")(SpatialPipeline.run(r, ann, Backend.Graph))
    // ⊤ is the only honest answer for a grounded function, and the bound is still USEFUL through
    // the union's other arm
    assert(a.result.shape.possiblyNonEmpty)
    println(s"\n[no-eval] bomb term analysed to ${a.result.show}")
  }

  test("NO EVALUATION: the same on a grounded PATH function") {
    val pbomb: Space = Space.GroundedPS(cp("a"),
      _ => throw RuntimeException("the pipeline evaluated its subject"))
    val r = Routine(RoutinePtr("pbomb"), Vector.empty, Vector.empty,
                    Space.Intersection(pbomb, lit(p("a"))))
    val ann = strict(SpatialAnnotations.open())
    val a = noEvaluation("analyze")(SpatialPipeline.analyzeRoutine(r, ann))
    noEvaluation("optimize")(SpatialPipeline.optimizeGuarded(r, a))
    // the graph backend cannot lower a grounded function; it must SAY so, not throw
    val l = noEvaluation("lower/graph")(SpatialPipeline.lower(
      SpatialPipeline.optimizeGuarded(r, a), Backend.Graph, ann))
    assert(l.graph.isEmpty, "transpile has no node for a grounded function")
    assert(l.notes.exists(n => n.contains("transpile")), l.notes.mkString("; "))
    println(s"[no-eval] grounded-path term: ${l.notes.mkString("; ").take(120)}")
  }
end SpatialPipelineCheck
