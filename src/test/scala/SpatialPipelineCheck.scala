package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** THE PIPELINE, unit by unit and end to end.
 *
 *  `eval` / `evalI` / `execT` / `execZ` appear here ONLY as ground truth — every one of them is
 *  instrumented (SpatialEvents.scala), so the strongest possible no-evaluation gate is available and
 *  used: run a pipeline stage inside `EffortSink.count` and assert the event vector is EMPTY.  A single
 *  interpreter dispatch anywhere under the analysis would show up. */
class SpatialPipelineCheck extends FunSuite, CalibrationProbe:
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
  /** An emptiness proof that is UNCONDITIONAL (`M` is free and untyped): the two operands are wrapped
   *  by DIFFERENT constant prefixes, so no path can be in both.
   *
   *  It is NOT a spatial-only win, and the comment here used to claim it was.  The "spatial-vs-ordinary"
   *  test below measures it as a TIE — the ordinary rule list reaches `Empty` too, through the
   *  `Wrap`/`Unwrap` prefix algebra — so it is kept as a case where the two tiers AGREE.  The
   *  spatial-only win on this fixture list is `selfSubtract`. */
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
    // the SPATIAL tier had to be what fired: `x ∖ x = ∅` is not in the ordinary rule list.  Which
    // rewrite carries it moved when the relational frontier became a rewrite consumer — the dead arm
    // used to be replaced by `Empty` and the union left standing (`EliminateEmpty`), and the frontier
    // now proves `Union(m2, x∖x) = m2` outright (`FrontierIdentity`).  Either is the proof being
    // consumed; what must not happen is neither.
    assert(g.applied.exists {
             case _: Rewrite.EliminateEmpty | _: Rewrite.FrontierIdentity => true
             case _ => false }, g.show)
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
   *  the "spatial facts change the ordinary optimized program", unconditionally. */
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
    // `optimizedPlain` and not `optimized`: the fallback is the program with NO spatial input at all,
    // and `optimized` now runs the unconditional spatial tier itself (`SpatialHook`)
    assertEquals(g.fallback.body, walk.optimizedPlain(using walkTable).body)
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
    // and the function `Routine.optimized` actually calls is itself EVENT-FREE — the hook adds no
    // evaluation to the compilation path; what evaluates there is the pre-existing `Lower.ConstantOps`
    val bomb: Space = Space.Union(Space.Mention(M),
      Space.GroundedSS(lit(p("a")), _ => throw RuntimeException("the hook evaluated its subject")))
    assertEquals(noEvaluation("SpatialHook.rewrite")(SpatialHook.rewrite(bomb, rc)), bomb)
  }

  // ================================================================================================
  //  8b.  THE HOOK, THROUGH `Routine.optimized` ITSELF — integration, meaning, and COST
  // ================================================================================================

  /** THE REPRESENTATIVE ROUTINES the suite actually compiles: the two datalog shapes, both
   *  Game-of-Life routines, the n-queens board and the 3×3 sliding-puzzle explorer.  `optimized` is
   *  called on these (or on routines their size) all over the test tree, so they are the population
   *  whose compile time the hook is allowed to spend. */
  def costCases: Vector[(String, Routine, PartialFunction[RoutinePtr, Routine])] =
    val gol = new GoL.Rules(0, 6)
    val board = NQueens.board(8)
    val puz = Sliding.puzzle(3, 3)
    Vector(
      ("walk (self-recursive)", walk, walkTable),
      ("aunts (datalog)", Routines.aunt_query_routine, Syntax.mod(Routines.child_routine)),
      ("transitive (datalog)", Routines.transitive_routine, PartialFunction.empty),
      ("reachable (datalog)", Routines.reachable_routine, PartialFunction.empty),
      ("gol/neigh", gol.defs(RoutinePtr("neigh")), gol.defs),
      ("gol/nextStep", gol.defs(RoutinePtr("nextStep")), gol.defs),
      ("nqueens place(8)", Routine(RoutinePtr("place"), Vector.empty, Vector.empty, board.program),
        board.defs),
      ("puzzle3x3/superpose", puz.superpose, puz.defs),
      ("puzzle3x3/explore", puz.explore, puz.defs),
    )

  /** THE COST GATE.  `Routine.optimized` is on the hot compilation path of the whole suite, so the
   *  hook's price is measured — per routine, with the ordinary rule list alone (`optimizedPlain`) as
   *  the baseline, interleaved and median-of-five after warming BOTH paths — and the numbers are
   *  printed rather than argued about.  Both directions are reported: what the call cost, and how many
   *  nodes the final body actually lost, because a hook that is cheap and never wins is not worth its
   *  risk either.
   *
   *  What it prints, measured, and stated plainly because it is not the flattering answer: on the nine
   *  CLOSED cornerstone routines the hook costs single-digit milliseconds and saves ZERO nodes — the
   *  ordinary partial evaluator (`Lower.ConstantOps`) already folds everything the spatial tier proves
   *  there.  The two OPEN rows at the end are where it pays: a free mention gives the partial evaluator
   *  nothing to fold, and the spatial proof is then the only one available. */
  test("COST: what the spatial hook adds to `Routine.optimized`, per representative routine") {
    def median(xs: Vector[Double]): Double = xs.sorted.apply(xs.size / 2)
    // two OPEN bodies (free mentions, nothing to partially evaluate) so the table shows the win too.
    // `x ∖ x` is the win the "spatial-only wins" test above measures; `prefix-disjoint ∩` is NOT one —
    // the ordinary list folds disjoint constant prefixes itself, and that test prints it as a tie.
    val openCases = Vector[(String, Routine, PartialFunction[RoutinePtr, Routine])](
      ("open: x ∖ x arm", Routine(RoutinePtr("o1"), Vector.empty, Vector(M, M2),
        Space.Union(Space.Mention(M2), selfSubtract)), PartialFunction.empty),
      ("open: iterate x ∖ x", Routine(RoutinePtr("o2"), Vector.empty, Vector(M),
        Space.Iteration(selfSubtract, H, R, Space.Mention(R))), PartialFunction.empty),
    )
    println("\n[hook-cost]  routine                     nodes   plain ms  hooked ms     delta  nodes saved")
    var worstAbs = 0.0
    var worstRatio = 0.0
    var worstRatioBig = 0.0
    var totalPlain = 0.0
    var totalHooked = 0.0
    var fired = 0
    var savedOpen = 0
    for (name, r, rc) <- costCases ++ openCases do
      given PartialFunction[RoutinePtr, Routine] = rc
      val n = SpatialPipeline.nodeCount(r.body)
      for _ <- 0 until 4 do { r.optimizedPlain; r.optimized }          // warm BOTH paths
      val ps = Vector.newBuilder[Double]; val hs = Vector.newBuilder[Double]
      val before = SpatialHook.stats
      var pOut: Routine = null; var hOut: Routine = null
      for _ <- 0 until 5 do
        val t0 = System.nanoTime(); pOut = r.optimizedPlain; ps += (System.nanoTime() - t0) / 1e6
        val t1 = System.nanoTime(); hOut = r.optimized;      hs += (System.nanoTime() - t1) / 1e6
      val plain = median(ps.result()); val hooked = median(hs.result())
      val after = SpatialHook.stats
      if after.changed > before.changed then fired += 1
      val dn = SpatialPipeline.nodeCount(pOut.body) - SpatialPipeline.nodeCount(hOut.body)
      if name.startsWith("open") then savedOpen += dn
      worstAbs = worstAbs max (hooked - plain)
      totalPlain += plain; totalHooked += hooked
      if plain > 1.0 then worstRatio = worstRatio max (hooked / plain)
      if plain > 20.0 then worstRatioBig = worstRatioBig max (hooked / plain)
      println(f"  $name%-28s $n%5d  $plain%9.2f $hooked%9.2f  ${hooked - plain}%+8.2f   " +
              (if after.skipped > before.skipped then "over budget" else f"-$dn%d"))
      // the ordinary rules run AFTER the hook, so a BIGGER result would mean the spatial rewrite
      // fought them — the one outcome that would make this a pessimisation instead of a win
      assert(dn >= 0, s"$name: the hooked body is BIGGER by ${-dn} nodes")
    println(f"  => worst delta ${worstAbs}%.1f ms;  worst ratio ${worstRatio}%.1fx on a >1 ms call, " +
            f"${worstRatioBig}%.2fx on a >20 ms call;  whole table ${totalHooked}%.0f/${totalPlain}%.0f ms " +
            f"= ${totalHooked / totalPlain}%.3fx;  $fired of ${costCases.size + openCases.size} bodies rewritten")
    println(s"  => process total ${SpatialHook.stats.show}")
    // THE BUDGETS — measured numbers with headroom, not aspirations, and deliberately three of them
    // because one number would flatter the hook.  The relative cost of a SMALL call is genuinely bad
    // (a 2 ms `optimized` of `gol/nextStep` becomes ~15-20 ms, i.e. up to ~8x) and is left published
    // rather than gated away: what bounds it is the absolute delta, since 20 ms of compile time is not
    // a compile-time problem.  What must not regress is the delta on a call that is already expensive,
    // and the total over the table — those two are gated tightly.
    assert(worstAbs < 150.0, f"the hook added ${worstAbs}%.1f ms to a single `optimized` call")
    assert(worstRatioBig < 1.5, f"the hook multiplied a >20 ms `optimized` call by ${worstRatioBig}%.2f")
    assert(totalHooked / totalPlain < 1.25,
           f"the hook cost ${100 * (totalHooked / totalPlain - 1)}%.0f%% of the whole table's compile time")
    assert(savedOpen >= 4, s"the hook saved only $savedOpen nodes on the two open bodies")
  }

  /** THE INTEGRATION TEST the review asks for: not "the pipeline can rewrite this term", which
   *  section 8 already showed, but "`Routine.optimized` — the method the whole tree compiles through —
   *  now consumes the spatial proof".  Every assertion here goes through `r.optimized`.
   *
   *  The subject is `x ∖ x` under a FREE mention: `Lower.ConstantOps`' partial evaluator cannot touch it
   *  (there is nothing to evaluate — `M` is unbound), and no syntactic rule in the list recognises the
   *  idempotence law, which the printed `plain` line demonstrates rather than claims. */
  test("INTEGRATION: `Routine.optimized` itself consumes the unconditional emptiness proof") {
    val body = Space.Union(Space.Mention(M2), selfSubtract)
    val r = Routine(RoutinePtr("hooked"), Vector.empty, Vector(M, M2), body)
    val hooked = r.optimized
    val plain = r.optimizedPlain
    println(s"\n[integration] plain   ${plain.body.show}")
    println(s"[integration] hooked  ${hooked.body.show}")
    assertNotEquals(hooked.body, plain.body,
      "`optimized` must consume the spatial proof the ordinary rule list cannot make")
    // THE WHOLE UNION GOES, not just its dead arm.  The previous expectation was
    // `Union(m2, Empty)`: the spatial tier proved `x ∖ x = ∅` and stopped there, because nothing in
    // the ordinary list has an `x ∪ ∅ = x` rule.  The relational frontier now decides the union
    // itself — `{Left}`, i.e. the result IS the left operand — so the residual is `m2`.
    assertEquals(hooked.body, Space.Mention(M2): Space,
      "the union must collapse to its live arm, not merely have its dead arm zeroed")
    assert(SpatialPipeline.nodeCount(hooked.body) < SpatialPipeline.nodeCount(plain.body),
           s"${hooked.body.show} vs ${plain.body.show}")
    // the routine's IDENTITY is untouched — the hook rewrites the body, nothing else
    assertEquals(hooked.name, r.name); assertEquals(hooked.mentions, r.mentions)
    assertEquals(hooked.refs, r.refs)
    // MEANING PRESERVED on every input, against the original AND against the plain optimizer
    val rng = new java.util.Random(20250807L)
    for _ <- 0 until 300 do
      val e = Map(M -> randInput(rng, 0, 3, 5), M2 -> randInput(rng, 0, 3, 5))
      assertEquals(runWith(hooked.body, e), runWith(body, e), s"hooked body disagrees on $e")
      assertEquals(runWith(hooked.body, e), runWith(plain.body, e))
    // the switch really switches: with the tier off, `optimized` IS `optimizedPlain`
    SpatialHook.withEnabled(false) {
      assertEquals(r.optimized.body, plain.body, "`-Dmorkl.spatialHook=false` must restore the old path")
    }
    // and the whole optimizer is idempotent with the hook in it
    assertEquals(Routine(r.name, r.refs, r.mentions, hooked.body).optimized.body, hooked.body)
    // A ROOT-level proof goes all the way: the body itself is ∅, so the routine compiles to nothing
    val allDead = Routine(RoutinePtr("dead"), Vector.empty, Vector(M), selfSubtract)
    println(s"[integration] root-empty plain ${allDead.optimizedPlain.body.show} " +
            s"=> hooked ${allDead.optimized.body.show}")
    assertEquals(allDead.optimizedPlain.body, selfSubtract, "the ordinary list leaves it standing")
    assertEquals(allDead.optimized.body, Space.Empty: Space)
    for _ <- 0 until 100 do
      val e = Map(M -> randInput(rng, 0, 3, 5))
      assertEquals(runWith(allDead.optimized.body, e), runWith(selfSubtract, e))
  }

  test("INTEGRATION: the hook fires through `optimized` INTERPROCEDURALLY, and never on a big body") {
    // an emptiness proof that needs the routine table: the callee denotes ∅, so the union arm goes
    val nil = Routine(RoutinePtr("nil"), Vector.empty, Vector(M),
                      Space.Subtraction(Space.Mention(M), Space.Mention(M)))
    val rc: PartialFunction[RoutinePtr, Routine] = Map(nil.name -> nil)
    val host = Routine(RoutinePtr("host"), Vector.empty, Vector(M2),
                       Space.Union(Space.Mention(M2), Space.Wrap(Space.Call(nil.name, Vector.empty,
                                                                           Vector(Space.Mention(M2))), cp("k"))))
    val hooked = host.optimized(using rc)
    println(s"\n[interprocedural] ${host.body.show}  =>  ${hooked.body.show}")
    // as above: the arm is eliminated AND the union with it, because the frontier decides `{Left}`
    assertEquals(hooked.body, Space.Mention(M2): Space,
                 s"the ∅ callee's arm must be eliminated: ${hooked.body.show}")
    val rng = new java.util.Random(31337L)
    for _ <- 0 until 100 do
      val e = Map(M2 -> randInput(rng, 0, 3, 4))
      assertEquals(runWith(hooked.body, e, rc = rc), runWith(host.body, e, rc = rc))
    // THE SIZE BUDGET: a body past `maxBodyNodes` is handed through unanalysed, and that is recorded
    val big = Vector.fill(40)(Space.Subtraction(Space.Mention(M), Space.Mention(M)): Space)
      .reduce((a, b) => Space.Union(a, b))
    val n = SpatialPipeline.nodeCount(big)
    val was = SpatialHook.maxBodyNodes
    try
      SpatialHook.maxBodyNodes = n - 1
      val before = SpatialHook.stats
      val out = Routine(RoutinePtr("big"), Vector.empty, Vector(M), big).optimized
      assert(SpatialHook.stats.skipped > before.skipped, "the size budget must be recorded, not silent")
      assertEquals(out.body, Routine(RoutinePtr("big"), Vector.empty, Vector(M), big).optimizedPlain.body,
                   "over budget, `optimized` must be exactly the ordinary rule list")
      SpatialHook.maxBodyNodes = n + 1
      val small = Routine(RoutinePtr("big"), Vector.empty, Vector(M), big).optimized
      assertEquals(small.body, Space.Empty: Space, s"under budget, all 40 arms are ∅: ${small.body.show}")
      println(s"[budget] $n nodes: over budget => ${SpatialPipeline.nodeCount(out.body)} nodes, " +
              s"under budget => ${SpatialPipeline.nodeCount(small.body)}")
    finally SpatialHook.maxBodyNodes = was
  }

  /** THE SOUNDNESS GATE FOR THE NEW CONFIG KNOB.  `shapeDepth`/`shapeWidth` are per-analysis now
   *  (`SpatialAnalysis.narrow`), and the width half is hand-written spill logic — the same recipe
   *  `Shape.mk` uses, but a second copy of it, so it is gated directly rather than trusted.
   *
   *  The property is the only one that matters: narrowing may LOSE precision and may not lose values.
   *  Both readings are checked — γ, with witnesses (`Shape.contains`), and the abstract strong order
   *  (`Shape.leqStrong`, which is what `SpatialType.leq` publishes). */
  test("the per-analysis trie caps only WEAKEN: γ(sh) ⊆ γ(narrow(sh, cfg)) on random shapes") {
    val rng = new java.util.Random(4242L)
    val cfgs = Vector(SpatialConfig.cheap,
                      SpatialConfig.default.copy(shapeDepth = 1, shapeWidth = 1),
                      SpatialConfig.default.copy(shapeWidth = 2),
                      SpatialConfig.default.copy(shapeDepth = 2, shapeWidth = 3))
    var checked = 0; var narrowed = 0; var admitted = 0
    for _ <- 0 until 250 do
      val v = randInput(rng, 0, 4, 8)
      val w = randInput(rng, 0, 3, 4)
      val shapes = Vector(Shape.of(v), Shape.weaken(Shape.of(v)),
                          Shape.unionTransfer(Shape.of(v), Shape.of(w)),
                          Shape.joinAlternatives(Shape.of(v), Shape.of(w)),
                          SpatialTyping.infer(Space.Union(lit(v.paths.toSeq*), Space.Mention(M))).shape)
      for sh <- shapes; cfg <- cfgs do
        val n = SpatialAnalysis.narrow(sh, cfg)
        checked += 1
        if n != sh then narrowed += 1
        for u <- Vector(v, w, SpaceValue(Set.empty), sv(PathValue(Nil))) do
          if Shape.contains(sh, u) then
            admitted += 1
            assert(Shape.contains(n, u),
                   s"narrow(${sh.show}, ${cfg.shapeDepth}x${cfg.shapeWidth}) = ${n.show} DROPPED " +
                   s"${u.pretty}, which the original admits")
        // THE FAILURE MESSAGE NAMES THE CHANNEL, and that is not decoration: this gate found the
        // certificate tier's `Cert.of` canonicalisation bug, and a bare "not above it"
        // sent the first two diagnosis attempts at the certificate when the channel was `otherTail`
        // and the certificate comparison was already returning `true`.
        assert(Shape.leqStrong(sh, n),
               s"narrow(${sh.show}) = ${n.show} is not above it in the strong order; " +
               s"channels: ${Shape.LeqShapeWhy.show(Shape.leqStrongMask(sh, n)).mkString(",")}; " +
               s"cert left=${sh.langLevel.show} right=${n.cert.show} " +
               s"Cert.leq=${Cert.leq(sh.langLevel, n.cert)}")
    println(s"\n[narrow] $checked (shape, config) pairs, $narrowed actually narrowed, " +
            s"$admitted γ-witnesses preserved, strong order holds in every case")
    assert(narrowed > checked / 10, s"only $narrowed of $checked pairs narrowed — the test is inert")
  }

  /** THE SOUNDNESS GATE FOR THE HOOK — programs × inputs, against `eval`.
   *
   *  The hook is a new rewriting stage on the path every compilation takes, so it gets the same kind of
   *  gate the law pipeline has (`CorpusLawValidation`): the fuzzed 1000-program corpus, each program
   *  compiled through `Routine.optimized` and evaluated against `eval` of the ORIGINAL on random input
   *  environments.  `eval` is ground truth here, not analysis input.
   *
   *  It also compares against `optimizedPlain` on every program, which is what makes it a gate on the
   *  hook specifically rather than on the optimizer as a whole: a disagreement between the two is
   *  attributable to the spatial tier and to nothing else.
   *  Tunables: `-Dhookvalid.progs` (default 250), `-Dhookvalid.m` (envs per program, default 25). */
  test("SOUNDNESS: the hooked `Routine.optimized` agrees with `eval` on the fuzzed corpus") {
    val progLimit = sys.props.get("hookvalid.progs").map(_.toInt).getOrElse(250)
    val perProg = sys.props.get("hookvalid.m").map(_.toInt).getOrElse(25)   // envs per program
    val recs = Corpus.load(progLimit)
    val maxS = 3; val maxP = 3
    val sNames = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until maxP).map(j => PathRef("p" + j)).toVector
    val A = SpaceFuzzer.alphabet
    val rng = new java.util.Random(90210L)
    def randPath0(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def smallTrie(): SpaceValue = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath0()).toSet)
    val envs = Array.fill(perProg)((Array.fill(maxS)(smallTrie()), Array.fill(maxP)(randPath0())))
    var checks = 0L; var differ = 0; var nodesPlain = 0L; var nodesHooked = 0L
    // the per-program ceiling on a predicted-cost regression, and the aggregate accumulators
    val RegressionBudget = 1.5
    var totalWorkHooked = 0.0; var totalWorkPlain = 0.0; var worstRegression = 1.0
    val inputsOpen = SpatialAnnotations.open().costInputs
    def hi(i: Ivl): Double = if i.hi >= Ivl.INF then Double.PositiveInfinity else i.hi.toDouble
    var finitePairs = 0
    val before = SpatialHook.stats
    val t0 = System.nanoTime()
    for r <- recs do
      val routine = Routine(RoutinePtr("main"), pNames.take(r.nPath), sNames.take(r.nSpace), r.prog)
      val hooked = routine.optimized
      val plain = routine.optimizedPlain
      if hooked.body != plain.body then differ += 1
      nodesPlain += SpatialPipeline.nodeCount(plain.body)
      nodesHooked += SpatialPipeline.nodeCount(hooked.body)
      for (sv, pv) <- envs do
        val pc: PathContext = PathContextMap((0 until r.nPath).map(j => pNames(j) -> pv(j)).toMap)
        val sc = SpaceContextMap((0 until r.nSpace).map(i => sNames(i) -> sv(i)).toMap)
        val ref = eval(r.prog)(using pc, sc, PartialFunction.empty)
        assertEquals(eval(hooked.body)(using pc, sc, PartialFunction.empty), ref,
          s"HOOK BUG: the spatially rewritten program disagrees with eval\n  prog:   ${r.prog.show}\n" +
          s"  hooked: ${hooked.body.show}")
        assertEquals(eval(plain.body)(using pc, sc, PartialFunction.empty), ref,
          s"the ORDINARY optimizer disagrees (not the hook's fault, but it must be known)")
        checks += 1
      // AND THE HOOK MAY NOT MAKE THE PROGRAM MORE EXPENSIVE.  The contract used to be "never more
      // NODES", and node count is the wrong metric for it: a spatial constant-fold can turn a loop
      // branch into a loop-INVARIANT one, `Lower.IterUnion_Indep` then hoists it out with the
      // constant-time `headedGuard` factor, and the term grows by the ~12 nodes of the guard while
      // the branch stops being recomputed once per head.  That is `docs/design_plan.md` §5.1's
      // headline optimisation, and the old assertion called it a regression (2 of 400 corpus
      // programs, e.g. idx 76: 40 -> 52 nodes, entirely the guard).
      //
      // The contract that says what was meant is the PREDICTED COST, which is what the cost model is
      // for.  Both forms are priced on the SAME facts with the same backend, and the contract has two
      // halves, because a per-program equality is not what "the hook earns its cost" means:
      //
      //  AGGREGATE   the hook must lower the TOTAL predicted work over the corpus.  Asserted after
      //              the loop; that is the claim that it is worth running at all.
      //  PER-PROGRAM no single program may get worse by more than `RegressionBudget` on any
      //              component.  A rewrite that is locally an improvement can SHIFT work between
      //              components through the downstream rules — eliminating a provably-empty union
      //              branch removes the union `IterUnion_Indep` was hoisting through — and what must
      //              never happen is a GROWTH-CLASS regression, which a factor this small cannot
      //              hide.  Measured worst over the 400-program corpus: 1.33x on `alloc`.
      locally {
        // OPEN inputs: a program whose bound is infinite on either side is not evidence either way — the
        // contract is stated over the programs the analysis can bound (counted and printed)
        val h = CostSem.analyze(hooked.body, inputsOpen, Backend.Trie)
        val pl = CostSem.analyze(plain.body, inputsOpen, Backend.Trie)
        if hi(h.work).isFinite && hi(pl.work).isFinite then
          totalWorkHooked += hi(h.work)
          totalWorkPlain += hi(pl.work)
          finitePairs += 1
        for (name, a, b) <- Vector(("work", h.work, pl.work), ("alloc", h.alloc, pl.alloc),
                                   ("rounds", h.rounds, pl.rounds), ("touch", h.touch, pl.touch)) if hi(a).isFinite && hi(b).isFinite do
          val (av, bv) = (hi(a), hi(b))
          val ratio = av / math.max(bv, 1.0)
          if av > bv then worstRegression = worstRegression max ratio
          assert(av <= bv || ratio <= RegressionBudget,
                 f"the hooked program's predicted $name regressed by $ratio%.2fx (> $RegressionBudget%.2f): " +
                 f"$av%.0f vs $bv%.0f\n  ${r.prog.show}")
      }
    val after = SpatialHook.stats
    println(f"\n[hook-corpus] ${recs.size} programs x $perProg envs = $checks%d differential checks against " +
            f"eval; the hook changed $differ programs; nodes $nodesPlain -> $nodesHooked; " +
            f"${(after.nanos - before.nanos) / 1e6}%.0f ms of analysis over ${after.calls - before.calls} " +
            f"calls; wall ${(System.nanoTime() - t0) / 1e9}%.1f s")
    assertEquals(checks, recs.size.toLong * perProg)
    // the hook swallows an analysis failure by design (a compile-time hook may lose an optimization,
    // not a compile) — which is exactly why the count is asserted here rather than trusted
    assertEquals(after.raised - before.raised, 0L,
                 s"the hook's analysis RAISED on the corpus: ${after.lastError}")
    println(f"[hook-corpus] predicted trie work (upper endpoints, open inputs) over the $finitePairs programs bounded on both sides: plain $totalWorkPlain%.0f -> " +
            f"hooked $totalWorkHooked%.0f (${100.0 * (totalWorkPlain - totalWorkHooked) / math.max(totalWorkPlain, 1.0)}%.1f%% better); " +
            f"worst single-program regression ${worstRegression}%.2fx of a permitted $RegressionBudget%.2f")
    assert(finitePairs > 0, "no corpus program is bounded on both sides under open inputs — the contract has no subject")
    assert(differ > 0 && nodesHooked < nodesPlain,
           s"the hook changed nothing on $progLimit corpus programs — it is not earning its cost " +
           s"(nodes $nodesPlain -> $nodesHooked over $differ changed programs)")
    assert(totalWorkHooked <= totalWorkPlain,
           f"THE AGGREGATE CONTRACT: the hook must not raise the total predicted work over the bounded corpus, " +
           f"got hooked $totalWorkHooked%.0f against plain $totalWorkPlain%.0f")
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
  //  10.  BACKEND COMPARISON  (selection is a NON-GOAL)
  // ================================================================================================
  test("compareBackends reports four per-component INTERVALS over the SAME facts and names no winner") {
    val body = Space.Iteration(lit(p("a", "1"), p("b", "2"), p("c", "3")), H, R,
                               Space.Wrap(Space.Mention(R), deref(H)))
    val ann = SpatialAnnotations.open()
    val cmp = noEvaluation("compareBackends")(SpatialPipeline.compareBackends(body, ann))
    println("\n" + cmp.show)
    assertEquals(cmp.brackets.keySet, Backend.values.toSet, "every executable must be priced")
    // an INTERVAL per component per backend, ordered and non-negative
    for b <- Backend.values.toVector; c <- SpatialPipeline.BackendComparison.Components do
      val (lo, hi) = cmp.brackets(b).numeric(c)
      assert(lo >= 0.0 && lo <= hi, s"${b.slug}/$c: malformed interval [$lo, $hi]")
    // DOMINANCE IS A PROOF, NOT A RANKING: it must be irreflexive, asymmetric and transitive, and it
    // must never fire on overlapping intervals.
    for a <- Backend.values.toVector do assert(!cmp.dominates(a, a), "dominance must be irreflexive")
    for (x, y) <- cmp.dominated do
      assert(!cmp.dominates(y, x), s"dominance must be asymmetric: ${x.slug} and ${y.slug}")
      for c <- SpatialPipeline.BackendComparison.Components do
        val (_, xhi) = cmp.brackets(x).numeric(c); val (ylo, _) = cmp.brackets(y).numeric(c)
        assert(xhi < ylo, s"${x.slug} < ${y.slug} claimed while $c overlaps: $xhi >= $ylo")
    // `unanimous` is the ONLY place a backend is named, and only when it dominates all three others
    cmp.unanimous.foreach(w =>
      assert(Backend.values.forall(b => b == w || cmp.dominates(w, b)),
             s"unanimous named ${w.slug} without dominating every other backend"))
    // the per-backend map on the analysis is the same set of keys
    val a = SpatialPipeline.analyzeTerm(body, ann)
    assertEquals(a.backendCost.keySet, Backend.values.toSet)
  }

  test("there is no automatic backend selection API left to be over-confident with") {
    // The regression that keeps item 8 resolved: a scalar score over four incommensurable components,
    // and an argmin over it, must not come back.  `compareBackends` returns intervals; `unanimous` is
    // the only namer and it is gated on disjointness.
    val src = scala.io.Source.fromFile("src/main/scala/SpatialPipeline.scala")
    val text = try src.mkString finally src.close()
    for banned <- Vector("def selectBackend", "def chooseBackend", "case class BackendChoice",
                         "p.work + p.alloc + p.rounds + p.touch") do
      assert(!text.contains(banned), s"SpatialPipeline.scala still defines `$banned`")
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
    noEvaluation("compareBackends")(SpatialPipeline.compareBackends(body, ann))
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

  // ================================================================================================
  //  THE CORNERSTONES, ON THE FORM THAT RUNS
  //
  //  Every number below is measured on `Routine.optimized`'s body (spatial hook + `Lower` rules) or on
  //  an `SC.reduce` residual — never on the definitional term.  A definitional estimate answers a
  //  question nobody asked: one runs the optimized backend, so one should price the optimized program.
  // ================================================================================================

  /** the six named cornerstones, with their inputs DECLARED and never their outputs */
  /** the cornerstones' input VALUES — the closed-program setting `cornerstones` declares by TYPE */
  lazy val cornerstoneValues: Map[String, Map[SpaceMention, SpaceValue]] =
    val rr = new scala.util.Random(12)
    val tempCells = (0 until 16)
      .map(i => PathValue(NOAA.bits(i, 4) :+ Vector("VC", "C", "N", "W", "VW")(rr.nextInt(5)))).toSet
    val live = Set((1, 0), (1, 1), (1, 2))
    val puz = Sliding.puzzle(4, 4)
    val edges = SpaceValue(Set(p("0", "1"), p("1", "2"), p("2", "3")))
    Map(
      "aunt" -> AuntQuery.context.asInstanceOf[SpaceContextMap].m,
      "temperature" -> Map(SpaceMention("world") -> SpaceValue(tempCells)),
      "gol" -> Map(SpaceMention("field") -> GoL.field(live)),
      "puzzle15" -> Map(SpaceMention("frontier") -> SpaceValue(Set(puz.initial))),
      "nqueens4" -> Map.empty,
      "datalog-sn" -> Map(SpaceMention("edges") -> edges))

  def cornerstones: Vector[(String, Routine, SpatialAnnotations)] =
    val rr = new scala.util.Random(12)
    val tempCells = (0 until 16)
      .map(i => PathValue(NOAA.bits(i, 4) :+ Vector("VC", "C", "N", "W", "VW")(rr.nextInt(5)))).toSet
    val world = Space.Mention(SpaceMention("world"))
    val temperature = Space.Union(Space.Restriction(world, Space.Literal(NOAA.interval(0, 4, 4))),
                                  Space.Restriction(world, Space.Literal(NOAA.interval(12, 16, 4))))
    val live = Set((1, 0), (1, 1), (1, 2))
    val golRules = GoL.rulesFor(live)
    val puz = Sliding.puzzle(4, 4)
    val queens = NQueens.board(4)
    val edges = SpaceValue(Set(p("0", "1"), p("1", "2"), p("2", "3")))
    def join(r: Space, s: Space): Space = r.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
    val snTC = Routine(RoutinePtr("sn_tc"), Vector.empty,
                       Vector(SpaceMention("e"), SpaceMention("all"), SpaceMention("delta")),
                       S"all" \/ Space.Call(RoutinePtr("sn_tc"), Vector.empty,
                         Vector(S"e", S"all" \/ (join(S"delta", S"e") \ S"all"), join(S"delta", S"e") \ S"all")))
    /** an input mention DECLARED at exactly its value's spatial type — the honest closed-program setting */
    def declared(kv: (SpaceMention, SpaceValue)*): Map[SpaceMention, SpatialType] =
      kv.iterator.map((m, v) => m -> SpatialType.of(v)).toMap
    def rt(name: String, ms: Vector[SpaceMention], body: Space,
           spaces: Map[SpaceMention, SpatialType] = Map.empty,
           rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty)
        : (String, Routine, SpatialAnnotations) =
      (name, Routine(RoutinePtr(name), Vector.empty, ms, body),
       SpatialAnnotations(spaces = spaces, routines = rc))
    Vector(
      rt("aunt", Vector.empty, Routines.aunt_query_routine.body,
         AuntQuery.context.asInstanceOf[SpaceContextMap].m.view
           .mapValues(SpatialType.of).toMap,
         Syntax.mod(Routines.child_routine)),
      rt("temperature", Vector(SpaceMention("world")), temperature,
         declared(SpaceMention("world") -> SpaceValue(tempCells))),
      rt("gol", Vector(SpaceMention("field")),
         Space.Call(RoutinePtr("nextStep"), Vector.empty, Vector(Space.Mention(SpaceMention("field")))),
         declared(SpaceMention("field") -> GoL.field(live)), golRules.defs),
      rt("puzzle15", Vector(SpaceMention("frontier")), puz.expandStep(Space.Mention(SpaceMention("frontier"))),
         declared(SpaceMention("frontier") -> SpaceValue(Set(puz.initial))), puz.defs),
      rt("nqueens4", Vector.empty, queens.program, Map.empty, queens.defs),
      rt("datalog-sn", Vector(SpaceMention("edges")),
         Space.Call(RoutinePtr("sn_tc"), Vector.empty,
           Vector(Space.Mention(SpaceMention("edges")), Space.Mention(SpaceMention("edges")),
                  Space.Mention(SpaceMention("edges")))),
         declared(SpaceMention("edges") -> edges), Syntax.mod(snTC)))

  /** a cornerstone is CLOSED, TERMINATING and NON-GROUNDED: every one of the six is known to execute
   *  and terminate (`SpatialEventsCheck` runs all six under `EffortSink.count`), and none contains a
   *  grounded host function.  That is precisely the class the review says may not produce an
   *  infinite estimate. */
  def hasGrounded(s: Space): Boolean =
    var found = false
    def go(x: Space): Unit =
      if !found then
        x match
          case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => found = true
          case _ => SizeZ3.children(x).foreach(go)
    go(s)
    found

  test("ITEM 5 INVARIANT: no infinite OR ASTRONOMICAL estimate on a closed terminating cornerstone") {
    // THE INVARIANT REPLACES THE ALLOW-LIST.  `SpatialEventsCheck.unboundedCornerstones` names two
    // expected failures (`datalog-sn` and `puzzle15`) and asserts the observed set EQUALS them; the review
    // item 5 says that is the wrong shape of test — `[0, inf]` on a closed terminating non-grounded
    // program is a FAILED RESULT, not semantic uncertainty — so here the requirement is stated positively
    // and gated.  Both former failures now come out finite, for the two reasons the review names: the
    // rest-chain FRAME LAW (`Σ K_d`, not `Π K_d`) for `puzzle15`, and the interprocedural
    // LEAST-FIXPOINT UNIVERSE SUMMARY for `datalog-sn`.
    // AND "INFINITE" INCLUDES "ASTRONOMICAL", which is the other half of the same review paragraph:
    // "Replacing infinity with `8e55` is not meaningful progress.  A bound that cannot distinguish the
    // real execution from tens of orders of magnitude more work is unusable for optimization, backend
    // selection, or capacity planning and SHOULD FAIL THE GATE JUST AS AN INFINITE BOUND DOES."  The
    // ceiling and its derivation are `ProductRequirement.Astronomical` (10^12 — 16 TB of allocation, or
    // ~17 minutes of primitive steps); it is a statement about machines, not about this repository, and it
    // is not read off any measurement here.
    println("\n[item5] the infinity ledger, ON THE OPTIMIZED BODY (Routine.optimized)")
    // THE GATE IS THE CLOSED PROGRAM: inputs declared by their VALUES (what "closed" means).  The
    // type-only declaration (`SpatialType.of(value)`, the fixture the other tests use) is REPORTED beside
    // it: a 16-cell board declared as a type keeps its per-cell fibres but not the functional dependence
    // between cells, and puzzle15's fifteen compositions multiply what the type cannot correlate.
    val ceiling = ProductRequirement.Astronomical
    var infinite = Vector.empty[String]
    var astronomical = Vector.empty[String]
    var typeOnlyInfinite = Vector.empty[String]
    var rows = 0
    for (name, r, ann) <- cornerstones do
      given PartialFunction[RoutinePtr, Routine] = ann.routines
      assert(!hasGrounded(r.body), s"$name is not grounded-free; it does not belong in this class")
      val t0 = System.nanoTime()
      val opt = r.optimized
      val exactInputs = CostSem.Inputs(values = cornerstoneValues(name))
      val reports = Backend.values.iterator.map(b => b -> SpatialPipeline.priceInputs(opt, exactInputs, ann.routines, b)).toMap
      val typeOnly = SpatialPipeline.costOfOptimized(r, ann)
      for b <- Backend.values.toVector if !typeOnly(b).finite && !(name == "datalog-sn" && b == Backend.Graph) do
        typeOnlyInfinite :+= s"$name/${b.slug}"
      val ms = (System.nanoTime() - t0) / 1e6
      for b <- Backend.values.toVector do
        val rep = reports(b)
        rows += 1
        // THE ONE BACKEND THAT CANNOT RUN THIS PROGRAM: execT has no stabilised-argument rule, so datalog's
        // argument-changing recursion does not terminate on the operation graph (the A1 differential skips
        // its graph leg for the same reason).  ⊤ is the honest answer there and is reported, not gated.
        val cannotRun = name == "datalog-sn" && b == Backend.Graph
        if cannotRun then println(s"  ~~ $name/${b.slug}: not gated — the graph executor cannot run an argument-changing recursion (no stationary-argument rule); reported ⊤")
        else if !rep.finite then
          infinite = infinite :+ s"$name/${b.slug}: ${EffortEvent.calibratedComponents.filter(c => rep.component(c).hi >= Ivl.INF).mkString(" ")}"
        else
          val big = EffortEvent.calibratedComponents.map(c => c -> rep.component(c).hi.toDouble).filter((_, v) => v >= ceiling)
          if big.nonEmpty then
            astronomical = astronomical :+
              s"$name/${b.slug}: ${big.map((k, v) => f"$k=$v%.3e").mkString(" ")}"
      val worst = Backend.values.toVector.filterNot(b => reports(b).finite).map(_.slug)
      println(f"  $name%-12s ${if worst.isEmpty then "ALL FINITE" else "INFINITE on " + worst.mkString(",")}%-28s " +
              f"${ms}%7.0f ms   ${reports(Backend.Trie).derivation.size} derivation nodes; ${reports(Backend.Trie).domain.show.linesIterator.next()}")
      println(f"      trie   ${reports(Backend.Trie).bounds.showComponents}")
      println(f"      zipper ${reports(Backend.Zipper).bounds.showComponents}")
      println(f"      graph  ${reports(Backend.Graph).bounds.showComponents}")
    println(s"  => $rows (cornerstone, backend) estimates; ${infinite.size} infinite, " +
            f"${astronomical.size} finite but at or above the $ceiling%.0e ceiling")
    println(s"  => under a TYPE-ONLY declaration (reported, not gated): ${if typeOnlyInfinite.isEmpty then "all finite" else typeOnlyInfinite.length + " infinite: " + typeOnlyInfinite.mkString(", ")}")
    for x <- infinite do println(s"  !! INFINITE     $x")
    for x <- astronomical do println(s"  !! ASTRONOMICAL $x")
    assert(infinite.isEmpty,
           s"infinite estimates on closed, terminating, non-grounded cornerstones: ${infinite.mkString("; ")}")
    assert(astronomical.isEmpty,
           f"estimates at or above the $ceiling%.0e ceiling on closed, terminating, non-grounded " +
           "cornerstones — a finite bound that describes no executable computation is the same failed " +
           s"result as `inf`, and the review requires it to fail the same way:\n    " +
           astronomical.mkString("\n    "))
  }

  test("ITEM 5: the two former allow-list entries, with the law that bounds each") {
    // Named specifically, because these are the two the previous generation exempted.
    val byName = cornerstones.map(c => c._1 -> c).toMap
    for name <- Vector("puzzle15", "datalog-sn") do
      val (_, r, ann) = byName(name)
      given PartialFunction[RoutinePtr, Routine] = ann.routines
      val rep =
        if name == "puzzle15" then CostSem.analyze(r.optimized.body, CostSem.Inputs(values = cornerstoneValues(name)), Backend.Trie, ann.routines)
        else SpatialPipeline.costOfOptimized(r, ann)(Backend.Trie)
      println(s"\n[item5/$name] rounds = ${rep.rounds.show}   work = ${rep.work.show}  (${if name == "puzzle15" then "inputs declared by value" else "inputs declared by type"})")
      // THE RULE THAT BOUNDS EACH IS IN THE DERIVATION DAG, not in a prose assumption: puzzle15's rounds
      // are the per-head loop entries of its rest-chained iterations (one `Iteration` rule per level, priced
      // from the fibres), datalog's are the recursion run to its stationary argument tuple (`Call/stationary`)
      // or the equivalent `Fixpoint` rounds of the lowered form.
      val rendered = rep.derivation.render()
      val rules = rendered.linesIterator.map(_.trim).filter(l => l.startsWith("Iteration") || l.startsWith("Fixpoint") || l.startsWith("Call")).toVector.distinct
      println(s"  rules: ${rules.take(6).mkString(" | ")}")
      assert(rep.finite, s"$name is still infinite: ${rep.bounds.showComponents}")
      assert(rules.nonEmpty, s"$name came out finite but its derivation names no loop, fixpoint or call rule")
      for n <- rep.notes do println(s"  ! ${n.take(300)}")
  }

  test("DERIVATION: every cornerstone interval carries a rule, and the certificate is deterministic") {
    // the requirement: "Attach a derivation DAG to each reported interval: rule, input
    // facts, backend parameter, widening event, and resulting bound" with a DETERMINISTIC renderer.
    println("\n[derivation] the certificates on the OPTIMIZED bodies")
    for (name, r, ann) <- cornerstones do
      given PartialFunction[RoutinePtr, Routine] = ann.routines
      val a = SpatialPipeline.costOfOptimized(r, ann)
      val b = SpatialPipeline.costOfOptimized(r, ann)
      for be <- Backend.values.toVector do
        val (ra, rb) = (a(be), b(be))
        assertEquals(ra.derivation.render(), rb.derivation.render(), s"$name/${be.slug}: the certificate is not deterministic")
        assertEquals(ra.bounds, rb.bounds, s"$name/${be.slug}: the bounds are not deterministic")
        def check(d: Derivation): Unit =
          assert(d.rule.nonEmpty, s"$name/${be.slug}: an interval without a rule")
          // the zipper prices control flow through its evalI fallback: those nodes are trie rules, and say so
          assert(d.backend == be || (be == Backend.Zipper && d.backend == Backend.Trie), s"$name/${be.slug}: a derivation node priced for ${d.backend.slug}")
          d.children.foreach(check)
        check(ra.derivation)
      println(f"  $name%-12s trie ${a(Backend.Trie).derivation.size}%6d nodes, ${a(Backend.Trie).domain.widenings.length}%3d widenings; " +
              f"zipper ${a(Backend.Zipper).derivation.size}%6d; graph ${a(Backend.Graph).derivation.size}%6d")
  }

  test("ITEM 8: the cost analysis consumes the DECLARED inputs — declared vs undeclared, on the same body") {
    // the requirement: "Let cost analysis consume the existing NodeId-indexed result."  The A4 analysis
    // is one interpreter over the declared inputs: with the inputs declared it prices the body from their
    // summaries; with nothing declared every input is ⊤ and the same body can only be bounded coarsely.
    // Declared bounds are never worse than undeclared ones, and strictly better somewhere per cornerstone.
    println("\n[item8] declared vs undeclared inputs, on the SAME optimized body")
    val byName = cornerstones.map(c => c._1 -> c).toMap
    var improved = 0
    for name <- Vector("gol", "aunt", "temperature", "puzzle15") do
      val (_, r, ann) = byName(name)
      given PartialFunction[RoutinePtr, Routine] = ann.routines
      val declared = SpatialPipeline.costOfOptimized(r, ann)
      val undeclared = SpatialPipeline.costOfOptimized(r, ann.copy(spaces = Map.empty))
      var strict = false
      for b <- Vector(Backend.Trie, Backend.Zipper) do
        val (d, u) = (declared(b), undeclared(b))
        println(f"  $name%-12s ${b.slug}%-8s declared   ${d.bounds.showComponents}")
        println(f"  ${""}%-12s ${""}%-8s undeclared ${u.bounds.showComponents}")
        for c <- EffortEvent.calibratedComponents do
          assert(d.component(c).hi <= u.component(c).hi,
                 s"$name/${b.slug}: declaring the inputs made $c WORSE (${d.component(c).show} vs ${u.component(c).show})")
          if d.component(c).hi < u.component(c).hi then strict = true
      if strict then improved += 1
    assertEquals(improved, 4, "declaring the inputs must tighten every cornerstone somewhere")
  }

  test("ITEM 8: the comparison keeps every component and declares the oracle gap instead of ranking") {
    // The predecessor scored `work + alloc + rounds + touch` at a valuation and took an argmin.  Two
    // things are asserted here in its place: (1) all four components survive as INTERVALS, and
    // (2) the reference backend's `touch` — a declared MODEL with no counted oracle — has a lower
    // endpoint of 0, which is exactly why nothing can be proved to dominate it on that component and
    // why a `best` would have been over-confident.
    val big = SpaceValue((0 until 64).map(i => p("k" + (i % 8), "v" + i)).toSet)
    val body = Space.Intersection(Space.Union(Space.Literal(big), Space.Literal(big)),
                                  Space.Literal(SpaceValue(Set(p("k0", "v0")))))
    val ann = SpatialAnnotations.open()
    val cmp = noEvaluation("compareBackends")(SpatialPipeline.compareBackends(body, ann))
    println("\n" + cmp.show)
    val modelled = Backend.values.toVector.filter(b => cmp.brackets(b).touchModelled).toSet
    assertEquals(modelled, Set(Backend.Reference),
                 s"exactly the reference backend's `touch` is a declared model, got $modelled")
    assertEquals(cmp.brackets(Backend.Reference).numeric(EffortComponent.Touch)._1, 0.0,
                 "a modelled `touch` must keep a ZERO lower endpoint — that is the declared gap")
    assert(Backend.values.forall(b => !cmp.dominates(b, Backend.Reference)),
           "nothing may be proved to dominate the reference backend while its `touch` lower is 0")
    // and on the form that runs
    val r = Routine(RoutinePtr("sel"), Vector.empty, Vector.empty, body)
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
    val onOpt = SpatialPipeline.compareBackendsOptimized(r, ann)
    println("[compare] on Routine.optimized's body:\n" + onOpt.show)
    assertEquals(onOpt.form, CostForm.Optimized)
  }

  test("ITEM 2 SLOPES: restriction by a fixed prefix is depth-only, not linear in the selected subtree") {
    // the requirement: "These tests must show constant or depth-only restriction and sharing cases
    // rather than merely contain the run below a linear upper bound."  The generator is geometric: one
    // FIXED length-2 prefix restricting a subtree that doubles.  A linear predicted slope is a FAILURE
    // here even though it would "contain" the run.
    def selected(n: Int): Space =
      Space.Literal(SpaceValue((0 until n).map(i => p("A", "B", "leaf" + i)).toSet))
    val prefixes = Space.Literal(sv(p("A", "B")))
    val ann = SpatialAnnotations.open()
    println("\n[slope] restriction by ONE fixed present prefix of length 2, selected subtree doubling")
    var prev = -1.0
    var slopes = Vector.empty[Double]
    for n <- Vector(8, 16, 32, 64, 128, 256) do
      val body = Space.Restriction(selected(n), prefixes)
      val rep = CostSem.analyze(body, ann.costInputs, Backend.Trie)
      val (alloc, touch, work) = (rep.alloc.hi.toDouble, rep.touch.hi.toDouble, rep.work.hi.toDouble)
      println(f"  n=$n%4d  alloc=${alloc}%8.0f  touch=${touch}%10.0f  work=${work}%6.0f")
      if prev >= 0 then slopes = slopes :+ math.log((alloc + 1) / (prev + 1)) / math.log(2)
      prev = alloc
    println(f"  => predicted alloc slopes log2(C(2n)+1 / C(n)+1): ${slopes.map(s => f"$s%.2f").mkString(", ")}")
    // A LINEAR predicted allocation would give slopes near 1.0.  The whole-subtree accept — a terminal
    // right prefix takes X_u by pointer — must make it 0.
    assert(slopes.forall(_ < 0.25),
           s"predicted restriction allocation grows with the SELECTED SUBTREE (slopes ${slopes.mkString(", ")}); " +
           "the terminal-prefix accept-by-pointer case is not reaching the cost model")
  }

  test("ITEM 2 SLOPES: a disjoint intersection and a subset union stay flat as both sides grow") {
    def deep(head: String, n: Int): Space =
      Space.Literal(SpaceValue((0 until n).map(i => p(head, "x" + i)).toSet))
    val ann = SpatialAnnotations.open()
    println("\n[slope] disjoint-head intersection and subset union")
    var interPrev = -1.0; var unionPrev = -1.0
    var interSlopes = Vector.empty[Double]; var unionSlopes = Vector.empty[Double]
    for n <- Vector(8, 16, 32, 64, 128) do
      val l = deep("L", n); val r = deep("R", n)
      def price(s: Space): (Double, Double) =
        val rep = CostSem.analyze(s, ann.costInputs, Backend.Trie)
        (rep.alloc.hi.toDouble, rep.touch.hi.toDouble)
      val ip = price(Space.Intersection(l, r))
      val up = price(Space.Union(l, l))            // the subset/absorption case: `x ∪ x`
      println(f"  n=$n%4d  disjoint ∩ alloc=${ip._1}%8.0f touch=${ip._2}%10.0f   " +
              f"x∪x alloc=${up._1}%8.0f touch=${up._2}%10.0f")
      if interPrev >= 0 then interSlopes = interSlopes :+ math.log((ip._1 + 1) / (interPrev + 1)) / math.log(2)
      if unionPrev >= 0 then unionSlopes = unionSlopes :+ math.log((up._1 + 1) / (unionPrev + 1)) / math.log(2)
      interPrev = ip._1; unionPrev = up._1
    println(f"  => ∩ slopes ${interSlopes.map(s => f"$s%.2f").mkString(", ")};  " +
            f"x∪x slopes ${unionSlopes.map(s => f"$s%.2f").mkString(", ")}")
    assert(interSlopes.forall(_ < 0.25),
           s"a PROVABLY DISJOINT intersection's predicted allocation grows with the operands " +
           s"(${interSlopes.mkString(", ")}) — disjoint-reject is not reaching the cost model")
    assert(unionSlopes.forall(_ < 0.25),
           s"`x ∪ x` predicted allocation grows with |x| (${unionSlopes.mkString(", ")})")
  }

  test("ITEM 2: the case-returning algebra — an equal-but-distinct restriction allocates nothing, at every size") {
    // `X <| Y` with `Y` an equal but DISTINCT object: the two denote the same set, so the algebraic result
    // is `Identity` and no node is rebuilt — but the pointer-identity short circuit does not fire, so the
    // frontier is descended.  The A4 semantics prices exactly that: the touch grows with the frontier, the
    // allocation stays at zero.  (The predecessor compared against a counterfactual model with the
    // identity cases removed; the counted executor has no such mode, so the claim is made on the executor
    // that exists.)
    def cube(b: Int): Space =
      val alpha = (0 until b).map("s" + _)
      Space.Literal(SpaceValue((for x <- alpha; y <- alpha; z <- alpha yield PathValue(List(x, y, z))).toSet))
    val ann = SpatialAnnotations.open()
    println("\n[identity] X <| Y with Y an equal-but-distinct object")
    var allocs = Vector.empty[Long]; var touches = Vector.empty[Long]
    for n <- Vector(2, 4, 6) do
      val body = Space.Restriction(cube(n), cube(n))
      val rep = CostSem.analyze(body, ann.costInputs, Backend.Trie)
      allocs :+= rep.alloc.hi; touches :+= rep.touch.hi
      evalI(body)                                   // warm: the two literal tries are built once, then looked up
      val ev = EffortSink.events(evalI(body))
      assert(rep.contains(ev), s"n=$n: counted ${ev.showComponents} escapes ${rep.bounds.showComponents}")
      println(f"  n=$n%4d  alloc=${rep.alloc.show}%-10s touch=${rep.touch.show}%-14s counted alloc=${ev.component(EffortComponent.Alloc)} touch=${ev.component(EffortComponent.Touch)}")
    assert(allocs.forall(_ == 0L), s"the identity-propagating restriction must allocate nothing: ${allocs.mkString(", ")}")
    assert(touches.last > touches.head, s"the frontier must GROW for the comparison to mean anything: ${touches.mkString(", ")}")
  }
end SpatialPipelineCheck
