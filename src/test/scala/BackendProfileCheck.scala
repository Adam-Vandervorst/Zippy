package morkl

import munit.FunSuite
import scala.collection.immutable.IntMap

/** THE BACKEND PROFILE'S DERIVATIONS, AND THE OPERAND-STRUCTURE FACT, CHECKED IN THE REPOSITORY.
 *
 *  This file exists because an audit of the previous round found that three of its load-bearing
 *  claims rested on nothing a reader could re-run:
 *
 *    * "`spineDepth` is `FrontierConfig.PatriciaBits` exactly at `R = 2, W = 32` — which is the
 *      check that these are the same quantities and not lookalikes." There was no check.
 *      `spineDepth` had **zero call sites** and no test mentioned any profile symbol.
 *    * "counted probes and slots are identical at `fan = 1` and `fan = 8` for every `k` from 3 to
 *      256", and "on the worst-case key family the arity-only formula is EXACT from k=3 to k=31".
 *      Both were measured — but by a script in a scratch directory, with no captured output and
 *      nothing committed, so the tree asserted a measurement it could not reproduce.
 *    * `OperandShape.DistinctSingleKey` "is the shape every cornerstone loop has". It is not; see
 *      the last test, which says which loops it actually fires on.
 *
 *  A measurement quoted in a comment is a claim. This file is the measurement.
 */
class BackendProfileCheck extends FunSuite, CalibrationProbe:
  import Space.*

  private val p2 = BackendProfile.intMapPatricia2

  // ---- the derivations, against the constants they replace --------------------------------------
  test("spineDepth at R=2, W=32 IS FrontierConfig.PatriciaBits — the same quantity, not a lookalike") {
    assertEquals(p2.repr.spineDepth, FrontierConfig.PatriciaBits,
      s"spineDepth = ${p2.repr.spineDepth} but PatriciaBits = ${FrontierConfig.PatriciaBits}; if " +
      "these drift apart then migrating a constant to the derived helper changed the model")
    assertEquals(p2.repr.lgArity, 1L, "lg 2")
    // and the projections' values, so a lowering's arithmetic is pinned rather than imagined
    val a256 = BackendProfile.array256.repr
    assertEquals(a256.lgArity, 8L, "lg 256")
    assertEquals(a256.spineDepth, 32L / 8L + 1L, "a byte-wide node consumes 8 bits per level")
    assertEquals(BackendProfile.hamt64Popcount.repr.lgArity, 6L, "lg 64")
  }

  test("spineNodes at R=2 is exactly the literal `2*m` it replaced") {
    for m <- Vector(0L, 1L, 2L, 7L, 64L, 1024L) do
      assertEquals(p2.repr.spineNodes(Sym.c(m)), Sym.normalize(Sym.c(2) * Sym.c(m)),
        s"spineNodes($m) must be 2*$m at R = 2")
    // and it is SMALLER for a wider node, which is the whole point of the parameterisation
    val wide = BackendProfile.array256.repr.spineNodes(Sym.c(1000))
    val narrow = p2.repr.spineNodes(Sym.c(1000))
    assert(Sym.evalAt(wide, Map.empty) < Sym.evalAt(narrow, Map.empty),
      s"a 256-ary spine over 1000 keys should need fewer physical nodes than a 2-ary one: " +
      s"${wide.show} vs ${narrow.show}")
  }

  test("carryDepth is a PATH-COMPRESSION artefact — it vanishes for a fixed-stride node") {
    assertEquals(p2.repr.carryDepth, p2.repr.keyWidthBits,
      "a compressed structure can skip bit positions, so an operand is carried up to W levels")
    val a256 = BackendProfile.array256.repr
    assertEquals(a256.carryDepth, a256.spineDepth,
      "a fixed-stride node consumes exactly lg R bits per level and cannot skip one, so the carry " +
      "is just the spine depth — this is the term the 256-ary lowering deletes")
    assert(a256.carryDepth < p2.repr.carryDepth, "and it is strictly smaller")
  }

  test("a PROJECTION may not license a floor, and the gated profile may") {
    assert(p2.claimsFloor, "the counted-against-this-tree profile, pricing its own events, may")
    for proj <- BackendProfile.projections do
      assert(!proj.claimsFloor,
             s"${proj.repr.name} is Declared — it describes code this tree does not contain, so a " +
             "MUST-count derived from it would be a claim about a program nobody has run")
    // and a handoff withdraws the licence even for the gated profile
    assert(!p2.pricingFor(Backend.Zipper).claimsFloor,
           "across a control-flow handoff the formulas and the counted stream belong to different " +
           "executables, so a floor read off one is not a floor for the other")
  }

  // ---- 1B.1: THE HANDOFF IS WIRED, AND THIS IS WHAT "WIRED" MEANS -------------------------------
  //
  // `PricingTarget` was previously a predicate with no consumer: `SpatialCost.go`'s fallback arm
  // handed the subterm to `Backends.of(Trie, phase)`, a singleton whose profile reports
  // `eventsOf == Trie`, so `claimsFloor` was TRUE across exactly the handoff it exists to make
  // false.  These four tests are the contract the wiring has to satisfy, and each fails if a
  // different part of it is undone.

  test("1B.1a. every plain backend instance targets its OWN counted stream and may claim a floor") {
    for m <- Backends.all do
      assertEquals(m.eventsOf, m.backend,
        s"${m.name}: a plain instance must target its own events; only Backends.handoff retargets")
      assertEquals(m.profile.target.eventsOf, m.backend,
        s"${m.name}: `profile` is not derived from `eventsOf` — the retarget cannot reach the profile")
      assert(m.profile.claimsFloor,
        s"${m.name}: a gated profile pricing its own events must be able to license a MUST-count, " +
        "or every lower endpoint in the tree is withdrawn")
  }

  test("1B.1b. Backends.handoff returns a RETARGETED instance whose profile refuses a floor") {
    for phase <- Vector(ExecutionPhase.Warm, ExecutionPhase.Cold) do
      val h = Backends.handoff(Backend.Trie, phase, Backend.Zipper)
      assertEquals(h.backend, Backend.Trie, "the formulas are still the trie's")
      assertEquals(h.eventsOf, Backend.Zipper, "but the counted stream is the zipper's")
      assert(h.profile.target.handedOff, "the profile does not report the handoff")
      assert(!h.profile.claimsFloor,
        "the handoff instance still claims a floor — this is the exact defect 1B.1 fixes.  A " +
        "must-count read off `evalI`'s source would be charged into `execZ`'s total, and " +
        "`materialize` can return a `Lit` by pointer, so `execZ` can allocate strictly less.")
      assert(h.name.contains("->"), s"the handoff instance is not distinguishable by name: ${h.name}")
      assertNotEquals(h.asInstanceOf[AnyRef], Backends.of(Backend.Trie, phase).asInstanceOf[AnyRef],
        "handoff returned the plain singleton, so the retarget did nothing")
  }

  test("1B.1c. handoff REFUSES a pair it has no instance for, instead of degrading") {
    // The failure mode must not be reachable by adding a second `controlFlowFallback`: a silent
    // fall back to `Backends.of` would restore the bug for the new consumer.
    val e = intercept[IllegalArgumentException](
      Backends.handoff(Backend.Trie, ExecutionPhase.Warm, Backend.Graph))
    assert(e.getMessage.contains("no instance prices"), e.getMessage)
    // an identity "handoff" is not a handoff and is allowed through to the plain instance
    assertEquals(Backends.handoff(Backend.Trie, ExecutionPhase.Warm, Backend.Trie).eventsOf,
                 Backend.Trie)
  }

  test("1B.1e. the PREMISE of `inheritsHandoffFloor`, MEASURED: execZ >= evalI on a handed-off term") {
    // `ZipperCost.inheritsHandoffFloor` is a claim about `transpileZ`'s SOURCE: it is a total, eager
    // structural walk with no short-circuit, so a control-flow subterm is always reached and
    // `evalI` is always run on it IN FULL.  If that is true, every event `evalI(T)` must emit is
    // emitted during `execZ`'s run, and `evalI`'s floor for T is a floor for `execZ`'s total.
    //
    // THE ROOT IS THE CONTROL-FLOW NODE in every case below, so the handed-off subterm IS the whole
    // program and the attribution is unambiguous.  Comparing a term with a FUSED outer operator
    // would be the wrong measurement: there `transpileZ` hands off only the inner node, `execZ`
    // fuses the rest, and `execZ` legitimately touches fewer nodes than `evalI` does for the whole
    // term — measured, `Union(Iteration(…), lit)` gives touch 7 against 5.  That is the fusion win,
    // not a floor violation.
    //
    // THE CACHES ARE WARMED FIRST, and that is not hygiene, it is the difference between a right
    // and a wrong answer: `iLiteralCache`/`iLiteralStrCache`/`iConstStrCache` (IntTrie.scala) are
    // append-only for the life of the JVM, so whichever executor runs first pays the decode
    // allocations.  The first version of this measurement ran `evalI` then `execZ` cold and reported
    // `alloc 47 -> 35`, i.e. an apparent floor VIOLATION that was entirely the cache warming.
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
    def pv(items: String*): PathValue = PathValue(items.toList)
    def slit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
    val src = slit(pv("a", "1"), pv("a", "2"), pv("b", "3"), pv("c", "4"))
    val cases: Vector[(String, Space)] = Vector(
      "iteration" -> Space.Iteration(src, PathRef("y"), SpaceMention("r"),
                       Space.Union(Space.Mention(SpaceMention("r")),
                                   Space.Singleton(Path.Deref(PathRef("y"))))),
      "fixpoint"  -> Space.Fixpoint(slit(pv("a")), SpaceMention("rec"),
                       Space.Union(Space.Mention(SpaceMention("rec")), slit(pv("b")))),
      "fold"      -> Space.Fold(src, Path.Constant(pv("k")), PathRef("acc"), PathRef("sym"),
                       SpaceMention("r"), Space.Mention(SpaceMention("r")),
                       Path.Concat(Path.Deref(PathRef("acc")), Path.Deref(PathRef("sym")))),
    )
    assert(Backends.zipperWarm.inheritsHandoffFloor,
      "ZipperCost no longer declares `inheritsHandoffFloor`, so this measurement pins nothing")
    for (label, t) <- cases do
      assert(SpatialCost.isControlFlowForTest(t),
        s"$label is not a control-flow term, so `transpileZ` does not hand it off and this case " +
        "measures the wrong thing")
      evalI(t); execZ(t)                                    // warm the process-wide decode memos
      val (_, ei) = EffortSink.count(evalI(t))
      val (_, ez) = EffortSink.count(execZ(t))
      // order-stability, so a future cache cannot make this read differently by running the other way
      val (_, ez2) = EffortSink.count(execZ(t))
      val (_, ei2) = EffortSink.count(evalI(t))
      assertEquals(ei.showComponents, ei2.showComponents, s"$label: evalI is not order-stable warm")
      assertEquals(ez.showComponents, ez2.showComponents, s"$label: execZ is not order-stable warm")
      println(f"HANDOFF: $label%-10s evalI [${ei.showComponents}]  execZ [${ez.showComponents}]")
      for c <- EffortComponent.values if c != EffortComponent.Explain do
        assert(ez.component(c) >= ei.component(c),
          s"$label/$c: execZ counted ${ez.component(c)} where evalI counted ${ei.component(c)}.  " +
          "`ZipperCost.inheritsHandoffFloor` claims `transpileZ` runs `evalI` IN FULL on a " +
          "handed-off subterm, so every event evalI must emit is emitted here too.  A strict " +
          "decrease refutes that — check `transpileZ` for a short-circuit or a lazy operand — and " +
          "until it is explained the override must be withdrawn, because the floor it licenses " +
          "would be a claim about a run that did not happen.")
  }

  test("1B.1d. the model `go` hands control flow to is the retargeted one, for every fallback") {
    // Read off the models rather than asserted about one of them: any model declaring a
    // `controlFlowFallback` must have a handoff instance, and that instance must refuse a floor.
    val withFallback = Backends.all.filter(_.controlFlowFallback.isDefined)
    assert(withFallback.nonEmpty,
      "no model declares a controlFlowFallback, so this test is vacuous — `ZipperCost` used to")
    for m <- withFallback; fb <- m.controlFlowFallback do
      val h = Backends.handoff(fb, m.phase, m.backend)
      assert(!h.profile.claimsFloor,
        s"${m.name} hands control flow to ${fb.slug}, and that handoff instance (${h.name}) still " +
        "claims a floor")
  }

  // ---- the OPERAND-STRUCTURE FACT, measured -----------------------------------------------------
  /** `k` single-key non-terminal operands on pairwise distinct keys, each carrying `fan`
   *  grandchildren — exactly what `ITrie.wrap` hands `ITrie.joinAll` under a head-retagged loop. */
  private def tipOperands(k: Int, fan: Int, key: Int => Int): Seq[ITrie] =
    (0 until k).map { i =>
      val payload = ITrie(false, IntMap.from((0 until fan).map(j =>
        (i * 104729 + j * 7919) -> ITrie(true, IntMap.empty))))
      ITrie(false, IntMap.singleton(key(i), payload))
    }

  private def counted(ops: Seq[ITrie]): (Long, Long) =
    val ev = EffortSink.count { ITrie.joinAll(ops) }._2
    (ev(EffortEvent.NaryOperandProbe), ev(EffortEvent.NaryScratchSlot))

  test("THE FAN IS IRRELEVANT — the descent never enters the operand values") {
    // This is the fact `OperandShape.DistinctSingleKey` licenses, and the reason `nd(body)` must
    // not appear in the arity-only formula.  If the counts moved with `fan`, the formula would be
    // wrong and the `iteration` rows it closed would be unsound.
    var mismatched = Vector.empty[String]
    for k <- Vector(3, 4, 8, 16, 24, 26, 32, 64, 128, 256) do
      val a = counted(tipOperands(k, 1, i => 1000 + i))
      for fan <- Vector(2, 8, 32) do
        val b = counted(tipOperands(k, fan, i => 1000 + i))
        if a != b then mismatched = mismatched :+ s"k=$k fan=1 gives $a but fan=$fan gives $b"
    assertEquals(mismatched, Vector.empty[String],
      s"the counted cost DEPENDS on the operand payload: ${mismatched.take(6).mkString("; ")} — " +
      "which would mean the descent does enter the values and the arity-only bound is unsound")
  }

  test("the arity-only formula BOUNDS the counted run, and is EXACT on the worst-case key family") {
    // the model's own numbers, reached through a CostModel instance so the test cannot drift from
    // the formulas the transfers use
    // reached through the model instance the transfers use, so the test cannot drift from them
    val M = Backends.of(Backend.Trie, ExecutionPhase.Warm)

    var bad = Vector.empty[String]
    var exact = 0
    var checked = 0
    // `2^i` keys force the DEGENERATE Patricia chain, which is the worst case the bound is
    // derived for; contiguous keys give a balanced tree, where it is sound with slack.
    for (label, key) <- Vector[(String, Int => Int)](("pow2", i => 1 << i), ("dense", i => 1000 + i))
        k <- Vector(3, 4, 8, 16, 24, 26, 31) do
      val (cp, cs) = counted(tipOperands(k, 4, key))
      val (fp, fs) = (M.tipJoinProbes(k), M.tipJoinScratch(k))
      checked += 1
      if cp > fp then bad = bad :+ s"$label k=$k: counted $cp probes > formula $fp"
      if cs > fs then bad = bad :+ s"$label k=$k: counted $cs slots > formula $fs"
      if label == "pow2" && cp == fp then exact += 1
    assertEquals(bad, Vector.empty[String],
      s"the arity-only bound DOES NOT CONTAIN the run: ${bad.take(6).mkString("; ")}")
    assert(exact >= 6,
      s"expected the probe formula to be EXACT on the degenerate-chain family at every k tried, " +
      s"got $exact of 7 — if this drops, the bound has become loose and the claim that it is exact " +
      "on the worst case no longer holds")
    println(s"PROFILE: $checked (family, k) points; probe formula exact on $exact of 7 pow2 points")
  }

  // ---- and the honest scope of the syntactic side condition ------------------------------------
  test("OperandShape.ofLoopBody: WHICH loop bodies it actually fires on") {
    val h = PathRef("h").known(1)
    val t = SpaceMention("t")
    val a: Space = Mention(SpaceMention("a"))
    val inner: Space = Mention(t)
    // FIRES: the head-retagging shape — a Wrap whose path derefs the loop symbol
    assertEquals(OperandShape.ofLoopBody(Wrap(inner, Path.Deref(h)), h),
                 OperandShape.DistinctSingleKey)
    assertEquals(OperandShape.ofLoopBody(Wrap(inner, Path.Concat(Path.Deref(h), Path.Deref(h))), h),
                 OperandShape.DistinctSingleKey, "the FIRST item is what keys the outer node")
    // DOES NOT FIRE, and each of these is a real cornerstone body shape.  The previous round's
    // claim that this is "the shape every cornerstone loop has" was wrong: `gol/nextStep`'s bodies
    // are an Iteration, a Subtraction and a Call, and only the INNERMOST level of `nqueens.place`
    // is a head-retagging wrap.
    val unknown: Vector[(String, Space)] = Vector(
      "a constant-keyed wrap (every group under ONE key — the br == 0 arm)"
        -> Wrap(inner, Path.Constant(PathValue(List("k")))),
      "a wrap by a DIFFERENT reference"
        -> Wrap(inner, Path.Deref(PathRef("other").known(1))),
      "a nested Iteration (gol/nextStep)"
        -> Iteration(inner, PathRef("g").known(1), SpaceMention("u"), Mention(SpaceMention("u"))),
      "a Subtraction (gol/nextStep's `exactly`)" -> Subtraction(inner, a),
      "a Call (gol/nextStep)" -> Call(RoutinePtr("f"), Vector.empty, Vector(inner)),
      "a bare mention" -> inner,
    )
    val wrong = unknown.filter((_, b) => OperandShape.ofLoopBody(b, h) != OperandShape.Unknown)
    assertEquals(wrong.map(_._1), Vector.empty[String],
      s"the fact fired on a body that does NOT produce single-key operands: ${wrong.map(_._1)} — " +
      "each of these would make the arity-only bound describe a descent that does enter the values")
  }
end BackendProfileCheck
