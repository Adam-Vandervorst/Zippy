package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==============================================================================================
 *  THE EFFORT ORACLE AND THE CALIBRATION TABLE.
 *
 *  The complaint was precise: "the effort model has no 'actual steps' oracle, so tightness is not
 *  measurable", and four concrete attribution errors followed from that.  This suite is the answer:
 *
 *   1. the event vocabulary is closed and every event has a real emitter;
 *   2. the disabled sink's cost is MEASURED, not asserted — per hook AND at executor level, with the
 *      workload's hook count in hand so the measurement is an accounting, not a hope;
 *   3. the hooks are wired where they claim to be (hand-computed exact counts per executor);
 *   4. each of the four attribution errors is now a passing regression;
 *   5. CONTAINMENT (`lower <= actual <= upper`) of the counted events in the intervals the A4 analysis
 *      (`CostSem`) derives, over the fuzzer corpus and the six cornerstones' OPTIMIZED bodies, on every
 *      backend — the gate; USEFULNESS (interval width per tier) is reported, not gated, at milestone M1;
 *   6. the derivation certificate is deterministic and every cornerstone bound is finite and below the
 *      astronomical ceiling.
 *
 *  EXECUTORS ARE GROUND TRUTH HERE AND NOWHERE ELSE.  Every `eval`/`evalI`/`execT`/`execZ` call below
 *  is a test oracle.  The analysis under test (`SpatialCost.analyze`) never runs the program — the
 *  last test in this file pins that with a grounded closure that throws if executed.
 *
 *  COVERAGE, HONESTLY.  ALL FOUR backends have counted runs — Reference (`eval`),
 *  Trie (`evalI`), Graph (`execT`) and Zipper (`execZ`) — and all four COMPONENTS are calibrated,
 *  `touch` included, because IntTrie.scala and IntTrieOps.scala are instrumented now.  There are NO
 *  STRUCTURAL EXCLUSIONS: the zipper's `evalI` fallback is priced and measured rather than dropped.
 *  Two things are excluded, both NAMED and both asserted to be exactly what they claim:
 *
 *   - `reference/touch`, because `eval` does its element work inside `scala.collection.immutable.Set`
 *     and the standard library carries no hooks.  The exclusion is declared by the MODEL
 *     (`CostModel.touchNoOracle`), and `the declared touch-oracle gap is exactly one backend` asserts
 *     that only `ReferenceCost` declares it.
 *   - the cornerstones whose predicted interval is genuinely UNBOUNDED, listed by name with their
 *     reason in `unboundedCornerstones`, which the cornerstone test checks for exact agreement with
 *     what the analysis actually produces (an unexpected unbounded FAILS, and so does a fixed one). */
class SpatialEventsCheck extends FunSuite, CalibrationProbe:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
  /** k distinct one-item paths */
  def litN(k: Int, pre: String = "i"): Space = Space.Literal(SpaceValue((0 until k).map(i => p(pre + i)).toSet))
  /** k distinct two-item paths under one head */
  def litDeep(k: Int, pre: String = "h"): Space = Space.Literal(SpaceValue((0 until k).map(i => p(pre, "x" + i)).toSet))
  def headsOf(s: Space): Space =
    Space.Iteration(s, PathRef("h").known(1), SpaceMention("_"), Space.Singleton(Path.Deref(PathRef("h").known(1))))

  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  val emptyPc: PathContext = PathContextMap(Map.empty)
  val emptySc: SpaceContext = SpaceContextMap(Map.empty)

  // ==============================================================================================
  // 1. THE VOCABULARY
  // ==============================================================================================

  test("the event vocabulary is closed: every event has an emitter and exactly one component") {
    val all = EffortEvent.values.toVector
    assert(all.nonEmpty)
    for e <- all do
      assert(e.emitter.nonEmpty, s"$e names no emitting executor")
      val named = e.emitter.split(',').map(_.trim).toVector
      assert(named.nonEmpty && named.forall(EffortEvent.executables.contains),
             s"$e's emitter '${e.emitter}' names something outside ${EffortEvent.executables.mkString("/")}")
    // the four CALIBRATED components partition the non-explanatory events
    val calibrated = EffortEvent.calibratedComponents.flatMap(EffortEvent.ofComponent)
    val explain = EffortEvent.ofComponent(EffortComponent.Explain)
    assertEquals((calibrated ++ explain).sortBy(_.ordinal), all.sortBy(_.ordinal))
    assertEquals(calibrated.intersect(explain), Vector.empty, "an event may not be both counted and explanatory")
    assertEquals(calibrated.distinct.length, calibrated.length, "no event may fall in two components")
    // every calibrated component must actually have events, and every executable must emit something
    for c <- EffortEvent.calibratedComponents do
      assert(EffortEvent.ofComponent(c).nonEmpty, s"component $c has no events")
    for x <- EffortEvent.executables do
      assert(all.exists(_.emitter.split(',').map(_.trim).contains(x)), s"no event names $x as an emitter")
    println(s"EVENTS: ${all.length} events — ${calibrated.length} calibrated, ${explain.length} explanatory")
    for c <- EffortComponent.values do
      println(s"EVENTS:   ${c}: ${EffortEvent.ofComponent(c).map(_.toString).mkString(", ")}")
  }

  test("the declared touch-oracle gap is exactly one backend, and it names its reason") {
    val gaps = Backends.all.filter(_.touchNoOracle.isDefined)
    assertEquals(gaps.map(_.backend).distinct, Vector(Backend.Reference),
                 s"only the reference model may declare a touch-oracle gap; got ${gaps.map(_.name)}")
    assertEquals(gaps.length, 2, "both phases of the reference model declare it")
    for g <- gaps do
      assert(g.touchNoOracle.exists(_.contains("Set")), g.touchNoOracle.toString)
    // and the three trie-shaped backends claim their touch IS counted
    for m <- Backends.all if m.backend != Backend.Reference do
      assertEquals(m.touchNoOracle, None, s"${m.name} must have a counted touch oracle")
    println(s"EVENTS: declared touch-oracle gaps: ${gaps.map(_.name).mkString(", ")} — " +
            gaps.headOption.flatMap(_.touchNoOracle).getOrElse(""))
  }

  /** the gaps this suite EXPECTS `OracleGap.declared` to contain, exact in both directions.  A new gap
   *  must be declared before it can appear, and a closed one must be removed. */
  val expectedGaps: Set[String] = Set("REF-SET", "INTMAP-SPINE", "RANGE-SORT", "INTERN-ITEM",
                                      "ZIPPER-ROUNDS")

  test("ORACLE COVERAGE: every (executable, component) is COUNTED or a DECLARED gap, and no gap is a hole") {
    // the fifth product requirement, and the reason it is a requirement: "an oracle-coverage
    // assertion that every backend loop and allocation category is either counted or deliberately outside
    // the advertised unit ... today only the touch gap is asserted while the four gaps in
    // SpatialEvents.scala are prose, not assertions."  A paragraph cannot fail.  This does.
    println("EVENTS: declared oracle gaps —")
    for g <- OracleGap.declared do
      println("EVENTS:   " + g.show)
      println("EVENTS:     where: " + g.where)
      println("EVENTS:     bound: " + g.bound.take(220))
      println("EVENTS:     owner: " + g.owner)
    // (a) the list is exact in both directions, so a gap cannot appear or vanish silently
    assertEquals(OracleGap.declared.map(_.id).toSet, expectedGaps,
                 s"the declared oracle-gap set changed: ${OracleGap.declared.map(_.id).sorted}")
    assertEquals(OracleGap.declared.map(_.id).distinct.length, OracleGap.declared.length, "duplicate gap id")
    // (b) every entry is well formed: a real executable, a calibrated component, and a STATED bound.
    //     "The gap is bounded, not open-ended" is only a claim if the bounding function is written down.
    for g <- OracleGap.declared do
      assert(g.execs.nonEmpty && g.execs.subsetOf(EffortEvent.executables.toSet), g.show)
      assert(g.comps.nonEmpty && g.comps.subsetOf(EffortEvent.calibratedComponents.toSet), g.show)
      assert(g.bound.length > 40, s"${g.id} declares a gap with no stated bound: ${g.bound}")
      assert(g.owner.nonEmpty && g.where.nonEmpty, g.show)
    // (c) THE COVERAGE MATRIX.  Every (executable, calibrated component) pair must be reached by an
    //     emitting event or by a declared gap.  This is the assertion that found ZIPPER-ROUNDS.
    var uncovered = Vector.empty[String]
    var byEvent = 0; var byGap = Vector.empty[String]
    for x <- EffortEvent.executables; c <- EffortEvent.calibratedComponents do
      val emitters = EffortEvent.ofComponent(c).filter(_.emitter.split(',').map(_.trim).contains(x))
      val gaps = OracleGap.forExec(x, c)
      if emitters.nonEmpty then byEvent += 1
      else if gaps.nonEmpty then byGap :+= s"$x/$c via ${gaps.map(_.id).mkString(",")}"
      else uncovered :+= s"$x/$c"
    println(s"EVENTS: coverage matrix — $byEvent of ${EffortEvent.executables.length * 4} " +
            s"(executable, component) pairs are COUNTED by an emitter; ${byGap.length} are covered by a " +
            s"declared gap: ${byGap.mkString("; ")}")
    assertEquals(uncovered, Vector.empty[String],
                 "an (executable, component) pair with NO emitting event and NO declared oracle gap — " +
                 "the advertised unit claims a number nothing measures: " + uncovered.mkString(", "))
    // (d) NO DECLARED GAP MAY BE A HOLE.  `Unbounded` means real executed work that no event counts and
    //     no named factor of a counted quantity bounds — neither counted NOR deliberately outside the
    //     advertised unit, which is exactly what the requirement forbids.
    val holes = OracleGap.declared.filter(_.status == GapStatus.Unbounded)
    assertEquals(holes.map(_.id), Vector.empty[String],
                 "declared oracle gap(s) that are UNBOUNDED — a gap with no bounding factor is a hole in " +
                 "the advertised unit, not an exclusion from it:\n  " +
                 holes.map(g => s"${g.id}: ${g.where} [owner ${g.owner}]").mkString("\n  "))
    // (e) and the n-ary operand/scratch category is COUNTED rather than declared, asserted positively so
    //     it cannot be dropped from the event vocabulary and from the gap list at the same time.
    for (e, c) <- Vector(EffortEvent.NaryOperandProbe -> EffortComponent.Work,
                         EffortEvent.NaryScratchSlot -> EffortComponent.Alloc) do
      assertEquals(e.component, c, s"$e must stay in $c or the n-ary category loses its oracle")
      assert(e.emitter.split(',').map(_.trim).toSet == Set("evalI", "execT", "execZ"),
             s"$e must be emitted by every trie-shaped executable: ${e.emitter}")
      assert(!OracleGap.declared.exists(_.id == "NARY-SCRATCH"),
             "the n-ary operand/scratch category is counted; it must not also be declared as a gap")
  }

  test("the sink counts, nests, and is off again afterwards") {
    assert(!EffortSink.isCounting, "no region may be open before a test arms one")
    val (v, ev) = EffortSink.count(eval(lit(p("a"), p("b"))))
    assertEquals(v.paths.size, 2)
    assertEquals(ev(EffortEvent.AstDispatch), 1L, ev.show)
    assert(!EffortSink.isCounting, "the region must close")
    // a nested region shadows the outer one (documented behaviour)
    val (outer, oe) = EffortSink.count {
      val (_, inner) = EffortSink.count(eval(lit(p("a"))))
      assertEquals(inner(EffortEvent.AstDispatch), 1L)
      eval(lit(p("a")))
    }
    assertEquals(oe(EffortEvent.AstDispatch), 1L, s"the outer region excludes the inner one: ${oe.show}")
    assertEquals(outer.paths.size, 1)
    assert(!EffortSink.isCounting)
  }

  // ==============================================================================================
  // 2. THE DISABLED PATH — MEASURED
  // ==============================================================================================

  test("BENCHMARK: the disarmed sink's cost is measured, not asserted") {
    // (a) the per-hook cost in a tight loop with nothing to hide it behind — the worst case.
    val n = 100_000_000
    def bare(): Long = { var i = 0; var acc = 0L; while i < n do { acc += i; i += 1 }; acc }
    def guarded(): Long =
      var i = 0; var acc = 0L
      while i < n do { effort(EffortEvent.AstDispatch); acc += i; i += 1 }
      acc
    assertEquals(bare(), guarded())                                    // and warm the JIT
    def best(body: => Long): Double =
      var b = Double.MaxValue
      for _ <- 0 until 5 do
        val t0 = java.lang.System.nanoTime(); val r = body; val d = (java.lang.System.nanoTime() - t0).toDouble
        assert(r >= 0L)
        if d < b then b = d
      b
    val tBare = best(bare()); val tGuard = best(guarded())
    val nsPerHook = (tGuard - tBare) / n
    // The difference lands AT THE MEASUREMENT FLOOR and its sign flips between runs (a guarded loop
    // measuring faster than the bare one is noise, not a speed-up).  Report the signed number, then use
    // its magnitude as a conservative stand-in for the accounting below, and assert only the thing a
    // static load plus a not-taken branch must satisfy: well under one nanosecond.
    val hookNs = math.abs(nsPerHook)
    println(f"EVENTS: disarmed hook cost in a tight loop: ${nsPerHook}%+.4f ns/hook " +
            f"(bare ${tBare / 1e6}%.1f ms vs guarded ${tGuard / 1e6}%.1f ms over $n iterations)" +
            (if nsPerHook < 0 then " — negative, i.e. below the measurement floor" else ""))
    // WALL CLOCK IS REPORTED HERE, NOT GATED — the same conclusion as `SpatialAcceptance.5c`, and
    // for the same measured reason.  This is a NANOSECOND-scale difference of two 100M-iteration
    // loops: its own comment already says the sign flips between runs because it sits at the
    // measurement floor.  MEASURED: it passes when the suite runs alone and fails when the corpus
    // sweeps are running beside it on 16 cores, which makes it a statement about machine load.  A
    // red gate that a quiet re-run turns green teaches a reader to re-run rather than to look.
    //
    // THE DETERMINISTIC GATE IS THE ONE BELOW IT: a disarmed sink must emit NO EVENTS AT ALL, which
    // is a counted fact, identical on every machine, and is what "disarmed" actually means.  The
    // nanosecond figure stays in the printout, with a loud note past the old ceiling.
    if hookNs >= 1.0 then
      Loaders.note(f"[events] disarmed hook measured ${nsPerHook}%+.4f ns/hook, past the 1 ns " +
                   "informational ceiling — wall clock is not gated here (see the comment above); " +
                   "the counted gate is that a disarmed sink emits no events")
    // the counted invariant, unconditionally: with the sink off, nothing is recorded.
    locally {
      assert(!EffortSink.armed,
             "this benchmark measures the DISARMED path and the sink is armed — the numbers above " +
             "describe something else entirely")
      val probe = new EffortSink.Counter
      var i = 0; var acc = 0L
      while i < 1_000_000 do { effort(EffortEvent.AstDispatch); acc += i; i += 1 }
      assert(acc >= 0L)
      assertEquals(probe.snapshot, Events.zero,
                   "a DISARMED sink recorded events — that is what this benchmark is really about, " +
                   "and unlike the nanosecond figure it is the same answer on every machine")
    }

    // (b) executor-level: the same warm workload with the sink off and on.
    val prog = Space.Iteration(litDeep(64), PathRef("h").known(1), SpaceMention("t"),
                               Space.Union(Space.Mention(SpaceMention("t")), Space.TailsUnion(S"t")))
    def runN(k: Int): Unit = { var i = 0; while i < k do { eval(prog)(using emptyPc, emptySc, noRc); i += 1 } }
    runN(2000)
    def bestMs(k: Int)(body: => Unit): Double =
      var b = Double.MaxValue
      for _ <- 0 until 5 do
        val t0 = java.lang.System.nanoTime(); body; val d = (java.lang.System.nanoTime() - t0) / 1e6
        if d < b then b = d
      b
    val off = bestMs(2000)(runN(2000))
    val on = bestMs(2000)(EffortSink.count(runN(2000)))
    val (_, oneRun) = EffortSink.count(eval(prog)(using emptyPc, emptySc, noRc))
    println(f"EVENTS: eval x2000 disarmed ${off}%.2f ms, armed ${on}%.2f ms (armed/disarmed ${on / off}%.2fx); " +
            f"${oneRun.total} events per run")

    // (c) THE NEW HOOKS: the ITrie/Patricia algebra is the hot path of every trie-shaped executor and
    //     of CorpusValidation, so its disarmed cost is the one that matters.  This is an ACCOUNTING,
    //     not a hope: measure the workload disarmed, count its hooks in one armed run, and multiply by
    //     the per-hook cost measured in (a).
    val ta = ITrie.fromSpaceValue(SpaceValue((0 until 400).map(i => p("h" + (i % 20), "x" + i)).toSet))
    val tb = ITrie.fromSpaceValue(SpaceValue((0 until 400).map(i => p("h" + (i % 20), "y" + i)).toSet))
    def trieWork(k: Int): Int =
      var i = 0; var acc = 0
      while i < k do
        acc += ITrie.union(ta, tb).nodeCount + ITrie.intersection(ta, tb).nodeCount +
               ITrie.subtraction(ta, tb).nodeCount + ITrie.restriction(ta, ITrie.head(tb)).nodeCount
        i += 1
      acc
    trieWork(200)                                                    // warm the JIT
    def bestTrie(k: Int): Double =
      var b = Double.MaxValue
      for _ <- 0 until 5 do
        val t0 = java.lang.System.nanoTime(); val r = trieWork(k); val d = (java.lang.System.nanoTime() - t0) / 1e6
        assert(r > 0)
        if d < b then b = d
      b
    val tOff = bestTrie(200)
    val tOn = { var b = Double.MaxValue
                for _ <- 0 until 5 do
                  val t0 = java.lang.System.nanoTime(); EffortSink.count(trieWork(200)); val d = (java.lang.System.nanoTime() - t0) / 1e6
                  if d < b then b = d
                b }
    val (_, trieEv) = EffortSink.count(trieWork(1))
    val hooksPerRun = trieEv.total.toDouble + trieEv(EffortEvent.ReusedSubtrie) + trieEv(EffortEvent.ReusedSpace)
    val accountedMs = hooksPerRun * 200.0 * hookNs / 1e6
    val sharePct = 100.0 * accountedMs / tOff
    println(f"EVENTS: ITrie algebra x200 disarmed ${tOff}%.2f ms, armed ${tOn}%.2f ms " +
            f"(armed/disarmed ${tOn / tOff}%.2fx); ${hooksPerRun.toLong} hooks per run")
    println(f"EVENTS: ACCOUNTED disarmed overhead = ${hooksPerRun.toLong} hooks x 200 x ${hookNs}%.4f ns " +
            f"= ${accountedMs}%.3f ms of ${tOff}%.2f ms measured = ${sharePct}%.2f%% of the workload")
    // the ASSERTIONS: the disarmed hooks must be a rounding error on the hot path, and counting must
    // stay cheap enough to use as an oracle.  Both thresholds are far above what is measured above.
    assert(sharePct < 5.0, f"disarmed hooks account for ${sharePct}%.2f%% of the ITrie hot path")
    assert(on < off * 20.0, f"counting is too expensive to use as an oracle: ${on / off}%.1fx")
    assert(tOn < tOff * 20.0, f"counting the trie algebra is too expensive: ${tOn / tOff}%.1fx")
  }

  // ==============================================================================================
  // 3. WIRING — hand-computed exact counts
  // ==============================================================================================

  test("eval's hooks are where they claim to be (exact hand-computed counts)") {
    // 3 Space nodes: the Union and its two Literals; no PathValue is built by a Set union
    val (_, u) = EffortSink.count(eval(Space.Union(litN(8, "a"), litN(8, "b"))))
    assertEquals(u(EffortEvent.AstDispatch), 3L, u.show)
    assertEquals(u(EffortEvent.FreshPath), 0L, s"a Set union allocates no PathValue: ${u.show}")

    // a Singleton: 1 AstDispatch, 1 PathDispatch (a Constant is one Path subterm), 1 FreshPath
    val (_, s1) = EffortSink.count(eval(Space.Singleton(Path.Constant(p("a", "b")))))
    assertEquals(s1(EffortEvent.AstDispatch), 1L)
    assertEquals(s1(EffortEvent.PathDispatch), 1L)
    assertEquals(s1(EffortEvent.FreshPath), 1L)
    // a Concat path is three subterms
    val (_, s2) = EffortSink.count(eval(Space.Singleton(Path.Concat(Path.Constant(p("a")), Path.Constant(p("b"))))))
    assertEquals(s2(EffortEvent.PathDispatch), 3L, s2.show)
    assertEquals(SpatialCost.pathNodeCount(Path.Concat(Path.Constant(p("a")), Path.Constant(p("b")))), 3L)
    assertEquals(SpatialCost.pathSlotCount(Path.Deref(PathRef("x"))), 0L, "a Deref reuses the prologue slot")

    // a 4-head iteration: 4 LoopBodyEntry, and the group split builds 2 paths per source path
    val four = lit(p("a", "0"), p("b", "0"), p("c", "0"), p("d", "0"))
    val (hv, it) = EffortSink.count(eval(headsOf(four)))
    assertEquals(hv.paths.size, 4)
    assertEquals(it(EffortEvent.LoopBodyEntry), 4L, it.show)
    assertEquals(it(EffortEvent.FreshPath), 4L * 2 + 4L, s"2 per source path in the group split + 1 per body: ${it.show}")
    assertEquals(it(EffortEvent.AstDispatch), 1L + 1L + 4L, s"Iteration + Literal + one body node per group: ${it.show}")
    // one head, four tails: ONE frame, same number of split allocations
    val one = lit(p("a", "0"), p("a", "1"), p("a", "2"), p("a", "3"))
    val (_, it1) = EffortSink.count(eval(headsOf(one)))
    assertEquals(it1(EffortEvent.LoopBodyEntry), 1L, it1.show)
    assertEquals(it1(EffortEvent.FreshPath), 4L * 2 + 1L, it1.show)

    // a fixpoint counts the TERMINATING round too
    val r = SpaceMention("r")
    val fix = Space.Fixpoint(lit(p("a")), r, Space.Union(Space.Mention(r), lit(p("b"))))
    val (fv, fe) = EffortSink.count(eval(fix))
    assertEquals(fv.paths.size, 2)
    assert(fe(EffortEvent.FixpointRound) >= 2L, s"at least the changing round and the terminating one: ${fe.show}")
    println(s"EVENTS: fixpoint rounds counted = ${fe(EffortEvent.FixpointRound)}")

    // a Call counts one CallEntry per entry
    val rp = RoutinePtr("f"); val xs = SpaceMention("xs")
    val body = Space.Union(Space.Mention(xs), Space.Call(rp, Vector.empty, Vector(Space.TailsUnion(Space.Mention(xs)))))
    val rt: PartialFunction[RoutinePtr, Routine] = { case q if q == rp => Routine(rp, Vector.empty, Vector(xs), body) }
    val (cv, ce) = EffortSink.count(eval(Space.Call(rp, Vector.empty, Vector(lit(p("a", "b", "c")))))(using emptyPc, emptySc, rt))
    assertEquals(cv.paths.size, 4, "the suffix closure of one 3-item path, plus itself")
    assert(ce(EffortEvent.CallEntry) >= 1L, ce.show)
    println(s"EVENTS: recursive call entries counted = ${ce(EffortEvent.CallEntry)} for maxlen 3")
  }

  test("evalI's and the ITrie algebra's hooks are where they claim to be (exact hand-computed counts)") {
    // These are the three sources the review says were uncounted: evalI dispatches, ITrie /
    // IntTrieOps per-node descent, and trie-node allocation.
    val la = litN(8, "ta"); val lb = litN(8, "tb")
    evalI(la); evalI(lb)                                               // fill the iLiteral memo cache
    val (uv, u) = EffortSink.count(evalI(Space.Union(la, lb)))
    assertEquals(uv.size, 16)
    assertEquals(u(EffortEvent.TrieDispatch), 3L, s"Union + two Literals: ${u.show}")
    assertEquals(u(EffortEvent.TrieOpEntry), 0L, s"evalI emits no TrieOpEntry — its dispatch covers it: ${u.show}")
    assertEquals(u(EffortEvent.FreshTrieNode), 1L, s"one merged root node; the 8+8 children are SHARED: ${u.show}")
    assertEquals(u(EffortEvent.TrieNodeVisit), 1L, s"the keys are disjoint, so no recursive descent: ${u.show}")
    // THE PATRICIA ENVELOPE the cost model's `tPer = 3` rests on: a simultaneous descent over children
    // maps of m and n keys visits at most 2(m+n) Patricia nodes (a Patricia tree over k keys has <= 2k-1).
    assert(u(EffortEvent.PatriciaVisit) >= 1L, u.show)
    assert(u(EffortEvent.PatriciaVisit) <= 2L * (8L + 8L),
           s"the 2(m+n) Patricia envelope is violated: ${u(EffortEvent.PatriciaVisit)} > 32 — ${u.show}")
    println(s"EVENTS: evalI union of two 8-path literals: ${u.show}")

    // THE N-ARY OPERAND LOOPS, hand-computed exactly (the first P0).  `ITrie.liveDistinct`
    // compares each operand against the DISTINCT ones buffered before it and its buffer starts at 4 slots,
    // so the counts below are arithmetic, not observations:
    //
    //   joinAll(x, y)     x != y      probes 0 + 1 = 1;   buffer max(4, 4*2) = 8 slots
    //   joinAll(x, x, x)              probes 0 + 1 + 1 = 2; buffer max(4, 4*1) = 4 slots
    //   meetAll(x, empty)             the empty PRE-SCAN stops on the second operand: 2 probes, 0 slots
    //
    // and below three DISTINCT operands there is no descent at all — `joinAll` delegates to the pairwise
    // union — so these are the whole n-ary event bill for each call.
    val nx = ITrie.fromSpaceValue(SpaceValue(Set(p("n", "x"))))
    val ny = ITrie.fromSpaceValue(SpaceValue(Set(p("n", "y"))))
    val n2 = EffortSink.events(ITrie.joinAll(Vector(nx, ny)))
    assertEquals(n2(EffortEvent.NaryOperandProbe), 1L, s"one identity comparison for two operands: ${n2.show}")
    assertEquals(n2(EffortEvent.NaryScratchSlot), 8L, s"the dedup buffer's slots: ${n2.show}")
    val ndup = EffortSink.count(ITrie.joinAll(Vector(nx, nx, nx)))
    assert(ndup._1 eq nx, "three copies of one operand join to that operand, by pointer")
    assertEquals(ndup._2(EffortEvent.NaryOperandProbe), 2L,
                 s"two duplicates, each found on the first comparison: ${ndup._2.show}")
    assertEquals(ndup._2(EffortEvent.NaryScratchSlot), 4L, s"one distinct operand buffered: ${ndup._2.show}")
    assertEquals(ndup._2(EffortEvent.FreshTrieNode), 0L,
                 s"a pointer answer materialises nothing: ${ndup._2.show}")
    val nempty = EffortSink.events(ITrie.meetAll(Vector(nx, ITrie.empty)))
    assertEquals(nempty(EffortEvent.NaryOperandProbe), 2L,
                 s"the empty pre-scan stops at the empty operand: ${nempty.show}")
    assertEquals(nempty(EffortEvent.NaryScratchSlot), 0L,
                 s"an annihilated meet buffers nothing: ${nempty.show}")


    // a Singleton allocates EXACTLY one node per path item (`epsilon` is a shared val)
    val (_, s2) = EffortSink.count(evalI(Space.Singleton(Path.Constant(p("a", "b")))))
    assertEquals(s2(EffortEvent.TrieDispatch), 1L)
    assertEquals(s2(EffortEvent.TriePathDispatch), 1L, s"one Path subterm: ${s2.show}")
    assertEquals(s2(EffortEvent.FreshTrieNode), 2L, s"one node per item: ${s2.show}")

    // an Unwrap is pure navigation: one visit per level, no allocation
    val sv = SpaceValue(Set(p("a", "x"), p("a", "y"), p("b", "z")))
    val ic = Map(SpaceMention("s0") -> ITrie.fromSpaceValue(sv))
    val (_, un) = EffortSink.count(evalI(Space.Unwrap(Space.Mention(SpaceMention("s0")), "a"))(using emptyPc, ic, noRc))
    assertEquals(un(EffortEvent.TrieDispatch), 2L, s"Unwrap + Mention: ${un.show}")
    assertEquals(un(EffortEvent.FreshTrieNode), 0L, s"the focused subtrie is SHARED: ${un.show}")
    assertEquals(un(EffortEvent.TrieNodeVisit), 2L, s"one unwrap entry per level (|p| = 1, plus the base): ${un.show}")

    // a pointer-identity short circuit is counted, and allocates nothing
    val (_, eq0) = EffortSink.count(
      evalI(Space.Union(Space.Mention(SpaceMention("s0")), Space.Mention(SpaceMention("s0"))))(using emptyPc, ic, noRc))
    assertEquals(eq0(EffortEvent.ReusedSubtrie), 1L, s"a eq b in ITrie.union: ${eq0.show}")
    assertEquals(eq0(EffortEvent.FreshTrieNode), 0L, eq0.show)

    // evalI's own dynamic frames
    val four = lit(p("a", "0"), p("b", "0"), p("c", "0"), p("d", "0"))
    val (_, it) = EffortSink.count(evalI(headsOf(four)))
    assertEquals(it(EffortEvent.LoopBodyEntry), 4L, s"four head groups: ${it.show}")
    val r = SpaceMention("r")
    val (_, fe) = EffortSink.count(evalI(Space.Fixpoint(lit(p("a")), r, Space.Union(Space.Mention(r), lit(p("b"))))))
    assert(fe(EffortEvent.FixpointRound) >= 2L, s"the changing round and the terminating one: ${fe.show}")
    val rp = RoutinePtr("f"); val xs = SpaceMention("xs")
    val bodyR = Space.Union(Space.Mention(xs), Space.Call(rp, Vector.empty, Vector(Space.TailsUnion(Space.Mention(xs)))))
    val rt: PartialFunction[RoutinePtr, Routine] = { case q if q == rp => Routine(rp, Vector.empty, Vector(xs), bodyR) }
    val (_, ce) = EffortSink.count(evalI(Space.Call(rp, Vector.empty, Vector(lit(p("a", "b", "c")))))(using emptyPc, Map.empty, rt))
    assert(ce(EffortEvent.CallEntry) >= 1L, ce.show)
    println(s"EVENTS: evalI rounds — loop=${it(EffortEvent.LoopBodyEntry)} " +
            s"fix=${fe(EffortEvent.FixpointRound)} calls=${ce(EffortEvent.CallEntry)}")
  }

  test("the REFERENCE evaluator emits no trie events at all — the reason its touch has no oracle") {
    // This is the justification for `ReferenceCost.touchNoOracle`, checked rather than asserted in
    // prose: `eval` works over Set[PathValue] and never enters the ITrie algebra, so no counted event
    // can ever stand in for its element work.
    val sv = SpaceValue(Set(p("a", "x"), p("a", "y"), p("b", "z")))
    val progs = Vector[Space](
      Space.Union(litN(16, "ra"), litN(16, "rb")),
      Space.Composition(litN(8, "rc"), litN(8, "rd")),
      Space.Restriction(Space.Literal(sv), litN(4, "re")),
      Space.Range(litN(16, "rf"), 0, 3),
      headsOf(Space.Literal(sv)),
      Space.Fixpoint(litN(4, "rg"), SpaceMention("q"),
                     Space.Union(Space.Mention(SpaceMention("q")), litN(2, "rh"))))
    for prog <- progs do
      eval(prog)(using emptyPc, emptySc, noRc)
      val (_, ev) = EffortSink.count(eval(prog)(using emptyPc, emptySc, noRc))
      assertEquals(ev.touch, 0L, s"eval counted trie touches: ${ev.show} for ${prog.show.take(60)}")
      assertEquals(ev(EffortEvent.FreshTrieNode), 0L, ev.show)
      assertEquals(ev(EffortEvent.TrieDispatch), 0L, ev.show)
    println(s"EVENTS: ${progs.length} reference programs counted 0 trie events — reference/touch has no oracle by " +
            "construction, not by omission")
  }

  test("execT's and execZ's hooks are where they claim to be") {
    val prog = Space.Union(Space.Mention(SpaceMention("s0")), Space.TailsUnion(Space.Mention(SpaceMention("s0"))))
    val sv = SpaceValue(Set(p("a", "x"), p("a", "y"), p("b", "z")))
    val g = transpile(Routine(RoutinePtr("m"), Vector.empty, Vector(SpaceMention("s0")), prog))
    val slots = g.nodes.length
    runGraphT(g, Map.empty, Map("s0" -> ITrie.fromSpaceValue(sv)))         // warm the caches
    val (gv, ge) = EffortSink.count(runGraphT(g, Map.empty, Map("s0" -> ITrie.fromSpaceValue(sv))))
    assertEquals(ge(EffortEvent.GraphNodeDispatch), slots.toLong,
                 s"one dispatch per graph slot ($slots slots): ${ge.show}")
    assertEquals(ge(EffortEvent.GraphFrameAllocation), 1L, s"only the top-level frame: ${ge.show}")

    // execZ: one ZipperBuild per Space node, and NO fallback for pure local algebra
    val (zv, ze) = EffortSink.count(execZ(prog)(using emptyPc, Map(SpaceMention("s0") -> ITrie.fromSpaceValue(sv)), noRc))
    assertEquals(zv.toSpaceValue, gv.toSpaceValue, "the two executors must still agree while counted")
    assertEquals(ze(EffortEvent.ZipperBuild), 4L, s"Union + Mention + TailsUnion + Mention: ${ze.show}")
    assertEquals(ze(EffortEvent.ZipperFallbackToEvalI), 0L, s"local algebra fuses: ${ze.show}")
    assert(ze(EffortEvent.ZipperCursorRead) > 0L, ze.show)
    assert(ze(EffortEvent.FreshNode) > 0L, s"materialize allocates the result nodes: ${ze.show}")
    assertEquals(ze(EffortEvent.ZipperMaterializeNode), ze(EffortEvent.FreshNode),
                 "one fresh node per materialised node")

    // control flow does NOT fuse: the fallback is counted
    val loop = headsOf(Space.Mention(SpaceMention("s0")))
    val (_, zl) = EffortSink.count(execZ(loop)(using emptyPc, Map(SpaceMention("s0") -> ITrie.fromSpaceValue(sv)), noRc))
    assertEquals(zl(EffortEvent.ZipperFallbackToEvalI), 1L, s"the Iteration goes through evalI: ${zl.show}")
    println(s"EVENTS: execT ${ge.showComponents} | execZ ${ze.showComponents} | execZ(loop) ${zl.showComponents}")
  }


  // ==============================================================================================
  // 4. CALIBRATION AGAINST THE A4 ANALYSIS — the corpus and the cornerstones
  // ==============================================================================================

  /** one containment row: a counted component against the analysis' interval */
  final case class Row(label: String, backend: Backend, comp: EffortComponent, actual: Long, lo: Long, hi: Long):
    def contains: Boolean = lo <= actual && actual <= hi
    def width: Double = (hi.toDouble + 1) / (lo.toDouble + 1)
    def show: String = f"$label%-28s ${backend.slug}%-9s $comp%-6s actual=$actual%9d in [${Ivl(lo, hi).show}]  ${if contains then "OK" else "OUT"}"

  def rowsOf(label: String, rep: CostReport, ev: Events): Vector[Row] =
    EffortEvent.calibratedComponents.map(c => Row(label, rep.backend, c, ev.component(c), rep.component(c).lo, rep.component(c).hi))

  def usefulness(title: String, rs: Vector[Row]): Unit =
    println(s"CALIBRATION: USEFULNESS — $title (${rs.length} rows; reported, not gated at M1)")
    for b <- Backend.values; c <- EffortEvent.calibratedComponents do
      val mine = rs.filter(r => r.backend == b && r.comp == c)
      if mine.nonEmpty then
        val ws = mine.map(_.width).sorted
        val tier = ProductRequirement.tierOf(b.slug, c)
        val worst = ws.last
        val verdict = tier match
          case Some(t) if t.width.isInfinite => "not gated"
          case Some(t) => if worst <= t.width then s"USEFUL (${t.name})" else s"NOT USEFUL for ${t.name} (worst width ${f"$worst%.1f"} > ${t.width})"
          case None => "no tier"
        println(f"CALIBRATION:   ${b.slug}%-9s $c%-6s p50=${ws(ws.length / 2)}%8.2f p95=${ws((ws.length * 95) / 100 min (ws.length - 1))}%8.2f worst=$worst%12.2f  $verdict")

  val sNames: Vector[SpaceMention] = (0 until 3).map(i => SpaceMention("s" + i)).toVector

  test("CALIBRATION: the fuzzer corpus — every counted execution inside the analysis' interval, four backends") {
    val recs = Corpus.load(sys.props.get("cal.progs").map(_.toInt).getOrElse(200))
    val A = SpaceFuzzer.alphabet
    val rng = new java.util.Random(20260807)
    def randPath() = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def smallTrie() = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath()).toSet)
    var rows = Vector.empty[Row]; var bad = Vector.empty[String]; var n = 0; var graphless = 0
    for r <- recs if r.nPath == 0 do
      val svs = sNames.take(r.nSpace).map(_ -> smallTrie()).toMap
      val pc = PathContextMap(Map.empty); val sc = SpaceContextMap(svs)
      val ic = svs.view.mapValues(ITrie.fromSpaceValue).toMap
      val inputs = CostSem.Inputs(values = svs)
      eval(r.prog)(using pc, sc, noRc); val re = EffortSink.events(eval(r.prog)(using pc, sc, noRc))
      evalI(r.prog)(using pc, ic, noRc); val te = EffortSink.events(evalI(r.prog)(using pc, ic, noRc))
      execZ(r.prog)(using pc, ic, noRc); val ze = EffortSink.events(execZ(r.prog)(using pc, ic, noRc))
      def one(b: Backend, ev: Events, rep: CostReport): Unit =
        rows ++= rowsOf(s"corpus#$n", rep, ev)
        val v = rep.bounds.violations(ev)
        if v.nonEmpty then bad :+= s"corpus#$n/${b.slug}: ${v.mkString("; ")}\n    prog = ${r.prog.show.replace('\n', ' ').take(200)}"
      one(Backend.Reference, re, CostSem.analyze(r.prog, inputs, Backend.Reference))
      one(Backend.Trie, te, CostSem.analyze(r.prog, inputs, Backend.Trie))
      one(Backend.Zipper, ze, CostSem.analyze(r.prog, inputs, Backend.Zipper))
      try
        val g = transpile(Routine(RoutinePtr("m"), Vector.empty, svs.keys.toVector, r.prog))
        val ments = ic.map((k, v) => k.s -> v)
        runGraphT(g, Map.empty, ments); val ge = EffortSink.events(runGraphT(g, Map.empty, ments))
        one(Backend.Graph, ge, CostSem.analyzeGraph(g, inputs))
      catch case _: NotImplementedError | _: MatchError => graphless += 1
      n += 1
    println(s"CALIBRATION: corpus — $n programs, ${rows.length} rows, ${bad.length} containment failures, $graphless without a graph")
    bad.take(8).foreach(b => println("CALIBRATION: OUT " + b))
    usefulness("corpus, exact declarations", rows)
    assertEquals(bad.length, 0, s"containment failures:\n${bad.take(10).mkString("\n")}")
  }

  /** the six cornerstones, inputs DECLARED (their exact values here — the honest closed-program
   *  setting), priced on `Routine.optimized`'s body */
  def cornerstones: Vector[(String, Routine, Map[SpaceMention, SpaceValue], PartialFunction[RoutinePtr, Routine])] =
    val rr = new scala.util.Random(12)
    val tempCells = (0 until 16).map(i => PathValue(NOAA.bits(i, 4) :+ Vector("VC", "C", "N", "W", "VW")(rr.nextInt(5)))).toSet
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
    def rt(name: String, ms: Vector[SpaceMention], body: Space, spaces: Map[SpaceMention, SpaceValue],
           rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty) =
      (name, Routine(RoutinePtr(name), Vector.empty, ms, body), spaces, rc)
    Vector(
      rt("aunt", Vector.empty, Routines.aunt_query_routine.body, AuntQuery.context.asInstanceOf[SpaceContextMap].m, Syntax.mod(Routines.child_routine)),
      rt("temperature", Vector(SpaceMention("world")), temperature, Map(SpaceMention("world") -> SpaceValue(tempCells))),
      rt("gol", Vector(SpaceMention("field")), Space.Call(RoutinePtr("nextStep"), Vector.empty, Vector(Space.Mention(SpaceMention("field")))),
         Map(SpaceMention("field") -> GoL.field(live)), golRules.defs),
      rt("puzzle15", Vector(SpaceMention("frontier")), puz.expandStep(Space.Mention(SpaceMention("frontier"))),
         Map(SpaceMention("frontier") -> SpaceValue(Set(puz.initial))), puz.defs),
      rt("nqueens4", Vector.empty, queens.program, Map.empty, queens.defs),
      rt("datalog-sn", Vector(SpaceMention("edges")),
         Space.Call(RoutinePtr("sn_tc"), Vector.empty, Vector(Space.Mention(SpaceMention("edges")), Space.Mention(SpaceMention("edges")), Space.Mention(SpaceMention("edges")))),
         Map(SpaceMention("edges") -> edges), Syntax.mod(snTC)))

  test("CALIBRATION: the six cornerstones on the OPTIMIZED body — contained, finite, below the ceiling") {
    var rows = Vector.empty[Row]; var bad = Vector.empty[String]; var hard = Vector.empty[String]
    for (name, r, spaces, rc) <- cornerstones do
      given PartialFunction[RoutinePtr, Routine] = rc
      val opt = r.optimized
      val body = opt.body
      val pc = PathContextMap(Map.empty); val sc = SpaceContextMap(spaces)
      val ic = spaces.view.mapValues(ITrie.fromSpaceValue).toMap
      val inputs = CostSem.Inputs(values = spaces)
      eval(body)(using pc, sc, rc); val re = EffortSink.events(eval(body)(using pc, sc, rc))
      evalI(body)(using pc, ic, rc); val te = EffortSink.events(evalI(body)(using pc, ic, rc))
      execZ(body)(using pc, ic, rc); val ze = EffortSink.events(execZ(body)(using pc, ic, rc))
      val t0 = java.lang.System.nanoTime()
      val reps = Vector(Backend.Reference -> re, Backend.Trie -> te, Backend.Zipper -> ze).map((b, ev) => (b, ev, CostSem.analyze(body, inputs, b, rc)))
      val ms = (java.lang.System.nanoTime() - t0) / 1e6
      for (b, ev, rep) <- reps do
        rows ++= rowsOf(name, rep, ev)
        val v = rep.bounds.violations(ev)
        if v.nonEmpty then bad :+= s"$name/${b.slug}: ${v.mkString("; ")}"
        if !rep.finite then hard :+= s"$name/${b.slug}: INFINITE ${rep.bounds.showComponents}"
        else if rep.magnitude >= ProductRequirement.Astronomical.toLong then hard :+= s"$name/${b.slug}: ASTRONOMICAL ${rep.bounds.showComponents}"
        println(f"CALIBRATION: $name%-12s ${b.slug}%-9s ${rep.bounds.showComponents}  counted ${ev.showComponents}  ${if v.isEmpty then "OK" else "OUT"}  ${rep.domain.show.linesIterator.next()}")
      // TIMING, not CALIBRATION: a wall-clock figure is not a counted column and must not enter the
      // determinism diff (check_determinism.sh compares every CALIBRATION line of two runs)
      println(f"TIMING:      $name%-12s analysed in ${ms}%.0f ms; ${reps.head._3.derivation.size} derivation nodes")
    usefulness("cornerstones, optimized bodies, exact declarations", rows)
    assert(hard.isEmpty, s"infinite or astronomical estimates on closed cornerstones:\n${hard.mkString("\n")}")
    assertEquals(bad, Vector.empty[String], "containment failures on the cornerstones")
  }

  test("CALIBRATION: the cornerstone derivations are deterministic across two analyses") {
    for (name, r, spaces, rc) <- cornerstones.take(3) do
      given PartialFunction[RoutinePtr, Routine] = rc
      val body = r.optimized.body
      val inputs = CostSem.Inputs(values = spaces)
      val a = CostSem.analyze(body, inputs, Backend.Trie, rc).derivation.render()
      val b = CostSem.analyze(body, inputs, Backend.Trie, rc).derivation.render()
      assertEquals(a, b, s"$name: the certificate is not deterministic")
    println("CALIBRATION: three cornerstone certificates render identically twice")
  }

  // ==============================================================================================
  // 5. COLD vs WARM, AND NO EVALUATION
  // ==============================================================================================

  test("COLD vs WARM: a cold literal is priced as its construction, a warm one as a lookup") {
    val v = SpaceValue((0 until 40).map(i => p(s"c$i", "x")).toSet)
    val prog = Space.Union(Space.Literal(v), Space.Mention(SpaceMention("s0")))
    val inputs = CostSem.Inputs(values = Map(SpaceMention("s0") -> SpaceValue(Set(p("q")))))
    val warm = CostSem.analyze(prog, inputs, Backend.Trie, phase = ExecutionPhase.Warm)
    val cold = CostSem.analyze(prog, inputs, Backend.Trie, phase = ExecutionPhase.Cold)
    assert(cold.alloc.hi > warm.alloc.hi, s"cold ${cold.bounds.showComponents} vs warm ${warm.bounds.showComponents}")
    // and the counted cold run (a fresh SpaceValue object, unknown to the cache) is inside the cold interval
    val fresh = SpaceValue((0 until 40).map(i => p(s"c$i", "x")).toSet)
    val progFresh = Space.Union(Space.Literal(fresh), Space.Mention(SpaceMention("s0")))
    val ic = Map(SpaceMention("s0") -> ITrie.fromSpaceValue(SpaceValue(Set(p("q")))))
    val coldRep = CostSem.analyze(progFresh, inputs, Backend.Trie, phase = ExecutionPhase.Cold)
    val ev = EffortSink.events(evalI(progFresh)(using emptyPc, ic, noRc))
    assert(coldRep.bounds.contains(ev), s"cold run ${ev.show} not in ${coldRep.bounds.show}")
    val warmEv = EffortSink.events(evalI(progFresh)(using emptyPc, ic, noRc))
    assert(warm.bounds.contains(warmEv), s"warm run ${warmEv.show} not in ${warm.bounds.show}")
    println(s"EVENTS: cold ${cold.bounds.showComponents} | warm ${warm.bounds.showComponents}")
  }

  test("NO EVALUATION IN THE ANALYSIS: a bomb subterm is never run by the cost analysis") {
    val bomb = Space.GroundedSS(Space.Mention(SpaceMention("s0")), _ => throw new AssertionError("evaluated"))
    val prog = Space.Union(Space.TailsUnion(bomb), Space.Literal(SpaceValue(Set(p("a")))))
    val inputs = CostSem.Inputs(values = Map(SpaceMention("s0") -> SpaceValue(Set(p("b")))))
    for b <- Backend.values.filterNot(_ == Backend.Graph) do
      val rep = CostSem.analyze(prog, inputs, b)
      assert(rep.notes.exists(_.contains("grounded")), rep.notes.toString)
    println("EVENTS: bomb subterm priced without evaluation on three backends")
  }
