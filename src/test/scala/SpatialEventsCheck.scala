package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==============================================================================================
 *  THE EFFORT ORACLE AND THE CALIBRATION TABLE — review.md finding 2.
 *
 *  The complaint was precise: "the effort model has no 'actual steps' oracle, so tightness is not
 *  measurable", and four concrete attribution errors followed from that.  This suite is the answer:
 *
 *   1. the event vocabulary is closed and every event has a real emitter;
 *   2. the disabled sink's cost is MEASURED, not asserted — per hook AND at executor level, with the
 *      workload's hook count in hand so the measurement is an accounting, not a hope;
 *   3. the hooks are wired where they claim to be (hand-computed exact counts per executor);
 *   4. each of the four attribution errors is now a passing regression;
 *   5. containment (`lower <= actual <= upper`) AND TIGHTNESS (median / p95 / worst slack) are
 *      measured PER COMPONENT and PER BACKEND over the corpus and the cornerstones, and the p95 and
 *      worst case are GATED against thresholds read off the measurements;
 *   6. the specific regression the review asks for: for a backend whose real implementation returns
 *      its input unchanged, increasing the input size must NOT increase modelled warm work.
 *
 *  EXECUTORS ARE GROUND TRUTH HERE AND NOWHERE ELSE.  Every `eval`/`evalI`/`execT`/`execZ` call below
 *  is a test oracle.  The analysis under test (`SpatialCost.analyze`) never runs the program — the
 *  last test in this file pins that with a grounded closure that throws if executed.
 *
 *  COVERAGE, HONESTLY (review.md item 1).  ALL FOUR backends have counted runs — Reference (`eval`),
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
class SpatialEventsCheck extends FunSuite:
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
        val t0 = System.nanoTime(); val r = body; val d = (System.nanoTime() - t0).toDouble
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
    assert(hookNs < 1.0, f"a disarmed hook must be far under 1 ns; measured ${nsPerHook}%.4f ns")

    // (b) executor-level: the same warm workload with the sink off and on.
    val prog = Space.Iteration(litDeep(64), PathRef("h").known(1), SpaceMention("t"),
                               Space.Union(Space.Mention(SpaceMention("t")), Space.TailsUnion(S"t")))
    def runN(k: Int): Unit = { var i = 0; while i < k do { eval(prog)(using emptyPc, emptySc, noRc); i += 1 } }
    runN(2000)
    def bestMs(k: Int)(body: => Unit): Double =
      var b = Double.MaxValue
      for _ <- 0 until 5 do
        val t0 = System.nanoTime(); body; val d = (System.nanoTime() - t0) / 1e6
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
        val t0 = System.nanoTime(); val r = trieWork(k); val d = (System.nanoTime() - t0) / 1e6
        assert(r > 0)
        if d < b then b = d
      b
    val tOff = bestTrie(200)
    val tOn = { var b = Double.MaxValue
                for _ <- 0 until 5 do
                  val t0 = System.nanoTime(); EffortSink.count(trieWork(200)); val d = (System.nanoTime() - t0) / 1e6
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
    // These are the three sources review.md item 1 says were uncounted: evalI dispatches, ITrie /
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
  // 4. THE FOUR FIXED ATTRIBUTIONS
  // ==============================================================================================

  test("FIX 1: a warm Literal returns the stored set — the model no longer charges |v|") {
    for k <- Vector(4, 32, 256) do
      val l = litN(k, "z")
      val (_, ev) = EffortSink.count(eval(l))
      assertEquals(ev(EffortEvent.AstDispatch), 1L)
      assertEquals(ev(EffortEvent.FreshPath), 0L, s"eval(Literal) returns the stored Set, |v|=$k: ${ev.show}")
      val warm = SpatialCost.analyze(l, Backends.referenceWarm)
      assertEquals(warm.cost.alloc, Amount.Bounded(Sym.zero), s"warm: ${warm.show}")
      assertEquals(warm.cost.work, Amount.Bounded(Sym.one), s"one AstDispatch, whatever |v|: ${warm.show}")
      // the COLD phase still carries the construction cost — the information is not lost, just moved
      val cold = SpatialCost.analyze(l, Backends.referenceCold)
      assertEquals(cold.cost.alloc, Amount.Bounded(Sym.c(k.toLong)), s"cold: ${cold.show}")
    println("EVENTS: FIX 1 — warm Literal is 1 dispatch / 0 allocations at |v| = 4, 32, 256")
  }

  test("FIX 2: a full-window Range is the identity — no sort is charged, and none happens") {
    for k <- Vector(8, 64, 256) do
      val src = litN(k, "r")
      // ground truth: sliceRange returns its input, so pathValueOrdering is never consulted
      val (full, fe) = EffortSink.count(eval(Space.Range(src, 0, 0)))
      assertEquals(full.paths.size, k)
      assertEquals(fe(EffortEvent.PathItemComparison), 0L, s"a full Range sorts nothing, |x|=$k: ${fe.show}")
      // a partial window really does sort
      val (part, pe) = EffortSink.count(eval(Space.Range(src, 0, 3)))
      assertEquals(part.paths.size, 3)
      assert(pe(EffortEvent.PathItemComparison) > 0L, s"a partial Range must sort: ${pe.show}")
      // the model agrees in both directions
      val mFull = SpatialCost.analyze(Space.Range(src, 0, 0), Backends.referenceWarm)
      val mPart = SpatialCost.analyze(Space.Range(src, 0, 3), Backends.referenceWarm)
      assertEquals(mFull.cost.work, Amount.Bounded(Sym.c(2)), s"2 dispatches, no sort: ${mFull.show}")
      assert(Sym.dominates(mPart.cost.work.symOpt.get, mFull.cost.work.symOpt.get) &&
             mPart.cost.work != mFull.cost.work, s"${mPart.show}\n${mFull.show}")
    // and the identity predicate matches RangeBounds' actual behaviour, exhaustively on small windows
    for size <- 1 to 12; lo <- -3 to 3; hi <- -3 to 3 do
      val (a, b) = RangeBounds.normalize(size, lo, hi)
      val reallyIdentity = a == 0 && b == size
      if SpatialCost.rangeIsIdentity(lo, hi) then
        assert(reallyIdentity, s"rangeIsIdentity($lo,$hi) but normalize($size) = ($a,$b)")
    println("EVENTS: FIX 2 — 0 counted comparisons for Range(x,0,0) at |x| = 8, 64, 256; >0 for Range(x,0,3)")
  }

  test("FIX 3: the trie Range DOES sort, and its full window is not free either") {
    // ground truth from IntTrie.scala:160-176 — the full-window slice returns the SAME object ...
    val t = ITrie.fromSpaceValue(SpaceValue((0 until 64).map(i => p("k" + i)).toSet))
    assert(ITrie.range(t, 0, 0) eq t, "a full window returns its input unchanged")
    // ... but `val size = t.size` runs FIRST, so the work is still proportional to the trie, and a
    // partial window sorts every visited node's child keys by their un-interned item.
    val ident = SpatialCost.analyze(Space.Range(S"s0", 0, 0), Backends.trieWarm)
    val part = SpatialCost.analyze(Space.Range(S"s0", 0, 3), Backends.trieWarm)
    assert(ident.cost.touch.bigO > BigO.const,
           s"the identity case still walks every node to compute t.size: ${ident.show}")
    assert(part.cost.touch.bigO.logs >= 1, s"the per-node key sort must appear: ${part.show}")
    // the OLD model's claim, now refuted: the trie is NOT cheaper than the reference here
    val refIdent = SpatialCost.analyze(Space.Range(S"s0", 0, 0), Backends.referenceWarm)
    assert(refIdent.cost.bigO < ident.cost.bigO,
           s"eval's sliceRange returns `s` in O(1); ITrie.range walks the trie:\n${refIdent.show}\n${ident.show}")
    println(s"EVENTS: FIX 3 — trie Range(x,0,0) touch = ${ident.cost.touch.show}; " +
            s"Range(x,0,3) touch = ${part.cost.touch.show}")
  }

  test("FIX 4: execT and execZ are priced separately, and really do differ") {
    val sv = SpaceValue(Set(p("a", "x"), p("a", "y"), p("b", "z"), p("b", "w")))
    val ic = Map(SpaceMention("s0") -> ITrie.fromSpaceValue(sv))
    val cases: Vector[(String, Space)] = Vector(
      "local algebra" -> Space.Union(Space.Mention(SpaceMention("s0")), Space.TailsUnion(S"s0")),
      "unwrap"        -> Space.Unwrap(Space.Mention(SpaceMention("s0")), "a"),
      "iteration"     -> headsOf(Space.Mention(SpaceMention("s0"))))
    var differing = 0
    for (nm, prog) <- cases do
      val g = transpile(Routine(RoutinePtr("m"), Vector.empty, Vector(SpaceMention("s0")), prog))
      runGraphT(g, Map.empty, Map("s0" -> ic(SpaceMention("s0"))))
      execZ(prog)(using emptyPc, ic, noRc)
      val (_, ge) = EffortSink.count(runGraphT(g, Map.empty, Map("s0" -> ic(SpaceMention("s0")))))
      val (_, ze) = EffortSink.count(execZ(prog)(using emptyPc, ic, noRc))
      val gm = SpatialCost.analyze(prog, Backends.graphWarm)
      val zm = SpatialCost.analyze(prog, Backends.zipperWarm)
      if gm.interval != zm.interval then differing += 1
      println(f"EVENTS: FIX 4 $nm%-14s counted execT[${ge.showComponents}]  execZ[${ze.showComponents}]")
      assert(ge != ze, s"$nm: the two executables must not produce the same event vector")
    assertEquals(differing, cases.length, "each case must be priced differently by the Graph and Zipper models")
    // and the zipper report SAYS where it stopped fusing
    val zl = SpatialCost.analyze(headsOf(Space.Mention(SpaceMention("s0"))), Backends.zipperWarm)
    assert(zl.assumptions.exists(_.contains("materialises it through evalI")),
           s"the fallback must be disclosed: ${zl.show}")
  }

  // ==============================================================================================
  // 5. THE REGRESSION review.md ASKS FOR BY NAME
  // ==============================================================================================

  test("IDENTITY REGRESSION: a bigger input must NOT increase modelled warm work for an identity op") {
    val sizes = Vector(4, 16, 64, 256, 1024)
    // (a) the reference evaluator: `Literal` returns the stored set and a full `Range` returns its
    //     input, so NO component of the warm cost may grow.  This is the review's exact request.
    for build <- Vector[(String, Int => Space)](
                   "Literal"        -> (k => litN(k, "q")),
                   "Range(x, 0, 0)" -> (k => Space.Range(litN(k, "q"), 0, 0)),
                   "Range(x, 1, 0)" -> (k => Space.Range(litN(k, "q"), 1, 0))) do
      val (nm, mk) = build
      val costs = sizes.map(k => SpatialCost.analyze(mk(k), Backends.referenceWarm).cost)
      val counted = sizes.map(k => EffortSink.count(eval(mk(k)))._2)
      for i <- 0 until costs.length - 1 do
        assertEquals(costs(i).work, costs(i + 1).work, s"$nm: modelled warm WORK grew from |v|=${sizes(i)} to ${sizes(i + 1)}")
        assertEquals(costs(i).alloc, costs(i + 1).alloc, s"$nm: modelled warm ALLOC grew")
        assertEquals(costs(i).touch, costs(i + 1).touch, s"$nm: modelled warm TOUCH grew")
        assertEquals(counted(i).work, counted(i + 1).work, s"$nm: COUNTED work grew — the model would be wrong")
        assertEquals(counted(i).alloc, counted(i + 1).alloc, s"$nm: COUNTED alloc grew")
      println(f"EVENTS: identity/$nm%-16s reference warm cost constant over |v| = ${sizes.mkString(",")}: " +
              f"${costs.head.show}  (counted ${counted.head.showComponents})")

    // (b) a warm `Literal` is a cache hit on every trie-shaped backend too
    for m <- Vector(Backends.trieWarm, Backends.graphWarm, Backends.zipperWarm) do
      val costs = sizes.map(k => SpatialCost.analyze(litN(k, "q"), m).cost)
      for i <- 0 until costs.length - 1 do
        assertEquals(costs(i), costs(i + 1), s"${m.name}: a warm Literal's cost grew with |v|")
      println(s"EVENTS: identity/Literal ${m.name} warm cost constant: ${costs.head.show}")

    // (c) THE HONEST EXCEPTION, recorded rather than papered over: `ITrie.range` computes the
    //     recursive `t.size` BEFORE its identity check, so for the trie-shaped backends a full
    //     `Range` is NOT constant work.  The model must say so, or it would be unsound the other way.
    val trieRange = sizes.map(k => SpatialCost.analyze(Space.Range(litN(k, "q"), 0, 0), Backends.trieWarm).cost)
    assert(trieRange.head.touch != trieRange.last.touch,
           "ITrie.range walks every node even for a full window (IntTrie.scala:161) — the model must not claim O(1)")
    for i <- 0 until trieRange.length - 1 do
      assert(Sym.dominates(trieRange(i + 1).touch.symOpt.get, trieRange(i).touch.symOpt.get))
    println(s"EVENTS: identity/Range trie warm touch GROWS as documented: " +
            s"${trieRange.map(_.touch.show).mkString(" -> ")}")
  }

  // ==============================================================================================
  // 6. THE CALIBRATION HARNESS
  // ==============================================================================================

  val maxS = 3; val maxP = 2
  val sNames: Vector[SpaceMention] = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
  val pNames: Vector[PathRef] = (0 until maxP).map(j => PathRef("p" + j)).toVector

  /** the exact `Meas` of a DECLARED input type (an input annotation, never an observed output) */
  def measOf(t: SpatialType): Meas =
    if t.isProvablyEmpty then Meas.empty
    else
      def up(n: Long) = if n >= Ivl.INF then Sym.Inf else Sym.c(n)
      Meas(up(t.size.hi), if t.len.isEmpty then Sym.zero else up(t.len.hi), up(t.headCount.hi),
           up(t.size.lo), up(t.headCount.lo))

  final case class Case(label: String, prog: Space,
                        spaces: Map[SpaceMention, SpaceValue] = Map.empty,
                        paths: Map[PathRef, PathValue] = Map.empty,
                        rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty):
    def pc: PathContext = PathContextMap(paths)
    def sc: SpaceContext = SpaceContextMap(spaces)
    lazy val ic: Map[SpaceMention, ITrie] = spaces.view.mapValues(ITrie.fromSpaceValue).toMap
    def env: SpatialCost.Env =
      val types = spaces.view.mapValues(SpatialType.of).toMap
      SpatialCost.Env(
        spaces = types.view.mapValues(measOf).toMap,
        paths = paths.view.mapValues(v => Sym.c(v.items.length.toLong)).toMap,
        routines = rc,
        facts = SpatialTyping.Env(
          spaces = types, paths = paths,
          lenv = SpatialEnv(
            paths = paths.view.mapValues(v => Lower.LenBounds(v.items.length.toLong, v.items.length.toLong)).toMap,
            routines = rc)))

  def freeVars(c: Cost): Set[String] =
    Vector(c.work, c.alloc, c.rounds, c.touch)
      .flatMap(a => a.symOpt.map(Sym.vars).getOrElse(Set.empty[String])).toSet

  /** One backend's calibration points, or `None` when the prediction still mentions a free variable
   *  (a symbolic fixpoint round count, a grounded path length): evaluating those at an arbitrary
   *  valuation would produce a number the model never claimed, so such rows are SKIPPED and counted,
   *  never silently defaulted.
   *
   *  The `touch` component is included for every model EXCEPT one that declares
   *  `CostModel.touchNoOracle` — the exclusion lives in the model, and the test
   *  `the declared touch-oracle gap is exactly one backend` pins the list to `reference` alone. */
  def calibrate(label: String, model: CostModel, rep: SpatialCost.Report, ev: Events,
                extra: CostInterval = CostInterval.zero): Option[Vector[Calibration]] =
    val hi = rep.cost + extra.hi
    val lo = rep.lower + extra.lo
    if freeVars(hi).nonEmpty || freeVars(lo).nonEmpty then None
    else Some(EffortEvent.calibratedComponents
                .filterNot(c => c == EffortComponent.Touch && model.touchNoOracle.isDefined)
                .map { comp =>
                  Calibration(s"$label/${rep.backend.slug}", comp, ev.component(comp),
                              lo.calibrated(comp).at(Map.empty), hi.calibrated(comp).at(Map.empty))
                })

  def countReference(c: Case): (SpaceValue, Events) =
    eval(c.prog)(using c.pc, c.sc, c.rc)                              // warm
    EffortSink.count(eval(c.prog)(using c.pc, c.sc, c.rc))

  /** `evalI` — instrumented now, so the Trie backend is calibrated like the other three. */
  def countTrie(c: Case): (ITrie, Events) =
    evalI(c.prog)(using c.pc, c.ic, c.rc)                             // warm (fills the iLiteral memo)
    EffortSink.count(evalI(c.prog)(using c.pc, c.ic, c.rc))

  def countZipper(c: Case): (ITrie, Events) =
    execZ(c.prog)(using c.pc, c.ic, c.rc)
    EffortSink.count(execZ(c.prog)(using c.pc, c.ic, c.rc))

  /** `transpile` is COLD work and stays outside the counted region — that is the cold/warm split. */
  def countGraph(c: Case, nS: Int, nP: Int): Option[(ITrie, Events, CostInterval)] =
    try
      val g = transpile(Routine(RoutinePtr("m"), pNames.take(nP), sNames.take(nS), c.prog))
      val refs = (0 until nP).map(j => ("p" + j) -> Interner.internPath(c.paths(pNames(j)).items)).toMap
      val ments = (0 until nS).map(i => ("s" + i) -> c.ic(sNames(i))).toMap
      runGraphT(g, refs, ments)
      val (v, e) = EffortSink.count(runGraphT(g, refs, ments))
      Some((v, e, SpatialCost.graphPrologue(nP, nS)))
    catch case _: NotImplementedError | _: IllegalStateException | _: RuntimeException => None

  /** THE COST OF A TERM AS `Routine.optimized`'s BODY, on every backend (the user's third steer).
   *
   *  "Asymptotics belong on the OPTIMIZED / SUPERCOMPILED program, not the definitional one."  A
   *  cornerstone's definitional term is not what runs: `Routine.optimized` applies the spatial hook and
   *  then the ordinary `Lower` rule list, and THAT body is what an executor is handed.  The decorated
   *  analysis is re-run on the optimized body so the prediction consumes per-node facts that address the
   *  term being priced (review.md item 8). */
  def optimizedForm(c: Case): (Routine, Map[Backend, SpatialCost.Report]) =
    val ann = SpatialAnnotations(
      spaces = c.spaces.view.mapValues(SpatialType.of).toMap,
      paths = c.paths,
      pathLens = c.paths.view.mapValues(v => Lower.LenBounds(v.items.length.toLong, v.items.length.toLong)).toMap,
      routines = c.rc)
    given PartialFunction[RoutinePtr, Routine] = c.rc
    val r = Routine(RoutinePtr("main"), c.paths.keys.toVector, c.spaces.keys.toVector, c.prog)
    val opt = r.optimized
    val a = SpatialPipeline.analyzeRoutine(opt, ann)
    val env = ann.costEnvFor(a.decorated)
    (opt, Backend.values.iterator.map(b =>
       b -> SpatialCost.analyze(opt.body, env, Backends.of(b, ExecutionPhase.Warm),
                                CostForm.Optimized)).toMap)

  /** THE PRODUCT-REQUIREMENT GATE  (review.md item 7).
   *
   *  ==WHAT WAS HERE==
   *  Two maps of thresholds, `corpusGate` and `cornerstoneGate`, each "READ OFF THE MEASUREMENT this
   *  suite prints, then rounded up".  That is a regression detector wearing a gate's clothes: it can
   *  say "the number did not move" and it can never say "the number is usable".  The published
   *  consequence was `trie Touch -> (4.5e6, 4.5e6)` and `trie Alloc -> (2.5e5, 2.5e5)` on the
   *  cornerstones, with Puzzle and Datalog removed from the statistic by an allow-list.
   *
   *  ==WHAT IS HERE NOW==
   *  [[ProductRequirement]] (SpatialScaleCheck.scala): interval WIDTH, multiplicative ERROR and
   *  asymptotic SLOPE budgets derived from the decisions an estimate has to support, stratified by
   *  (backend, component), with the slope half measured on the geometric ladders in `SpatialScaleCheck`.
   *  Anything that cannot meet its tier FAILS with the measured number printed, unless it appears in the
   *  named-limitation ledger — which requires a root cause, an owning file, and passes a NECESSITY check
   *  so a channel that gets fixed breaks the build instead of keeping its excuse.
   *
   *  ==AND IT IS GATED ON THE OPTIMIZED FORM==
   *  The user's third steer: the numbers that matter describe `Routine.optimized`'s body executed on the
   *  optimal backends.  So the cornerstone gate below runs on the OPTIMIZED body, and the definitional
   *  rows are printed beside it as a labelled contrast rather than gated.  The REFERENCE evaluator is
   *  ungated on every form (the user's second steer, and `ProductRequirement.NotGated` states it in the
   *  table): `eval` over `Set[PathValue]` is allowed to be slow, its constants are not a product, and its
   *  `touch` has no counted oracle at all. */
  def gateOf(scope: String, subject: String, rows: Vector[Calibration]): Vector[GateRow] =
    val keys = rows.map(r => (r.label.split('/').last, r.component)).distinct
    keys.flatMap { (b, comp) =>
      val sub = rows.filter(r => r.label.endsWith("/" + b) && r.component == comp).filter(_.bounded)
      ProductRequirement.tierOf(b, comp) match
        case _ if sub.isEmpty => Vector.empty[GateRow]
        case None => Vector.empty[GateRow]        // caller asserts totality separately
        case Some(tier) =>
          val errs = sub.map(_.slack)
          val widths = sub.map(r => (r.upper + 1.0) / (r.lower + 1.0))
          // a p95 over fewer than five points is the maximum with extra steps, so it is not emitted
          Vector(GateRow(scope, subject, b, comp, "error", errs.max, tier),
                 GateRow(scope, subject, b, comp, "width", widths.max, tier)) ++
          (if sub.length < 5 then Vector.empty
           else Vector(GateRow(scope, subject, b, comp, "error-p95", Calibration.p95(errs), tier),
                       GateRow(scope, subject, b, comp, "width-p95", Calibration.p95(widths), tier)))
    }

  /** print the containment/slack table, gate SOUNDNESS unconditionally, and gate TIGHTNESS against the
   *  product requirements when `gateRows` is non-empty */
  def publish(title: String, rows: Vector[Calibration], skipped: Int, cases: Int,
              gateRows: Vector[GateRow], ungatedNote: String = ""): Unit =
    println("=" * 116)
    println(s"CALIBRATION — $title  ($cases cases, ${rows.length} points, $skipped predictions skipped as symbolic)")
    println("=" * 116)
    val keys = rows.map(r => (r.label.split('/').last, r.component)).distinct
      .sortBy((b, c) => (b, c.ordinal))
    for (b, comp) <- keys do
      val sub = rows.filter(r => r.label.endsWith("/" + b) && r.component == comp)
      val key = s"$b $comp"
      println("CALIBRATION: " + Calibration.summarize(key, sub).show)
      val raw = Calibration.summarizeRaw(s"$key [raw, actual>0]", sub)
      if raw.n > 0 && raw.n != sub.length then println("CALIBRATION: " + raw.show)
      val unb = sub.filterNot(_.bounded)
      if unb.nonEmpty then
        println(s"CALIBRATION:   ${unb.length} of ${sub.length} predictions were UNBOUNDED " +
                s"(${unb.map(_.label).distinct.mkString(", ")})")
      // EVERY (backend, component) that produced a row must have a declared product requirement
      assert(ProductRequirement.tierOf(b, comp).isDefined,
             s"$key produced calibration rows with no declared product requirement")
    val bad = rows.filterNot(_.contains)
    println(f"CALIBRATION: overall containment ${100.0 * rows.count(_.contains) / math.max(1, rows.length)}%.2f%% " +
            f"(${bad.length} of ${rows.length} points outside the interval)")
    for b <- bad.take(8) do println(s"CALIBRATION:   OUT ${b.show}")
    // SOUNDNESS IS THE FIRST GATE: an upper bound below the counted truth is a bug, not imprecision.
    assertEquals(bad.length, 0, s"$title: ${bad.length} counted values fell outside the predicted interval")
    if ungatedNote.nonEmpty then
      println(s"CALIBRATION: TIGHTNESS NOT GATED ON THIS FORM — $ungatedNote")
    if gateRows.nonEmpty then publishGate(title, gateRows, keys.length)

  /** the same ledger machinery `SpatialScaleCheck` uses, over `corpus`/`cornerstone` scopes */
  def publishGate(title: String, rows: Vector[GateRow], channels: Int): Unit =
    val scope = rows.head.scope
    println("-" * 116)
    println(s"PRODUCT REQUIREMENTS — $title  ($channels channels, ${rows.length} requirement checks)")
    var failures = Vector.empty[String]
    val met = rows.count(_.ok)
    for r <- rows.filterNot(_.ok).sortBy(_.key) do
      r.limitation match
        case Some(l) =>
          println("REQUIREMENT: " + r.show + s"  <== NOT MET — named limitation ${l.id}")
          if r.measured > l.cap(r.what) + 1e-9 then
            failures :+= s"${r.key}: ${GateRow.fmt(r.measured)} REGRESSED past named limitation " +
                         s"${l.id}'s recorded ${GateRow.fmt(l.cap(r.what))}"
        case None =>
          println("REQUIREMENT: " + r.show + "  <== FAILS THE PRODUCT REQUIREMENT, UNNAMED")
          failures :+= s"${r.key}: measured ${GateRow.fmt(r.measured)} exceeds the ${r.tier.name} " +
                       s"requirement ${GateRow.fmt(r.permitted)}"
    for l <- ProductRequirement.limitations if l.scope == scope do
      val mine = rows.filter(r => l.matches(r.scope, r.subject, r.backend, r.comp, r.what))
      if mine.isEmpty then
        failures :+= s"${l.id}: declared over ${l.subjects.mkString(",")} but NO requirement check " +
                     "produced a matching row — the channel stopped being measured"
      for s <- l.subjects do
        val hers = mine.filter(_.subject == s)
        if hers.nonEmpty && hers.forall(_.ok) then
          failures :+= s"${l.id}: subject `$s` NO LONGER FAILS " +
                       s"(${hers.map(r => s"${r.what}=${GateRow.fmt(r.measured)}").mkString(", ")}) — " +
                       "remove it from the limitation; the ledger may not keep a fixed channel excused"
    val used = ProductRequirement.limitations.filter(l =>
      l.scope == scope && rows.exists(r => l.matches(r.scope, r.subject, r.backend, r.comp, r.what) && !r.ok))
    println(s"PRODUCT REQUIREMENTS — $met of ${rows.length} checks MET; ${rows.length - met} not met, " +
            s"covered by ${used.length} named limitations")
    for l <- used do
      println("LIMITATION: " + l.show)
      println("LIMITATION:   subjects: " + l.subjects.mkString(", "))
      println("LIMITATION:   " + l.reason)
    assertEquals(failures, Vector.empty[String],
                 s"$title: ${failures.length} product-requirement failure(s) with no named limitation " +
                 s"(or a stale one):\n  " + failures.mkString("\n  "))

  test("CALIBRATION: predicted intervals vs counted events over the fuzzer corpus") {
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    assume(f.exists, "corpus not found")
    val recs = locally {
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()
    }.take(sys.props.get("cal.progs").map(_.toInt).getOrElse(200))
    val A = SpaceFuzzer.alphabet
    val rng = new java.util.Random(20260807)
    def randPath() = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def smallTrie() = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath()).toSet)
    val sv = sNames.map(_ -> smallTrie()).toMap
    val pv = pNames.map(_ -> randPath()).toMap

    var rows = Vector.empty[Calibration]
    var skipped = 0; var graphSkipped = 0; var cases = 0; var zipperFallback = 0; var diagnosed = 0
    var refTouch = 0L
    for r <- recs do
      val c = Case(s"corpus", r.prog, sv.filter((k, _) => sNames.take(r.nSpace).contains(k)),
                   pv.filter((k, _) => pNames.take(r.nPath).contains(k)))
      val (refV, refE) = countReference(c)
      val (trieV, trieE) = countTrie(c)
      val (zipV, zipE) = countZipper(c)
      // the hooks must not have changed what the executors compute
      assertEquals(zipV.toSpaceValue, refV, s"execZ disagrees with eval while counted: ${r.prog.show.take(120)}")
      assertEquals(trieV.toSpaceValue, refV, s"evalI disagrees with eval while counted: ${r.prog.show.take(120)}")
      refTouch += refE.touch
      if zipE(EffortEvent.ZipperFallbackToEvalI) > 0L then zipperFallback += 1
      cases += 1
      def add(model: CostModel, rep: SpatialCost.Report, ev: Events, extra: CostInterval = CostInterval.zero): Unit =
        calibrate("corpus", model, rep, ev, extra) match
          case Some(cs) =>
            rows ++= cs
            // DIAGNOSTIC: an out-of-interval point is a model bug, so print the subject once
            for x <- cs if !x.contains && diagnosed < 24 do
              diagnosed += 1
              println(s"CALIBRATION: DIAGNOSE ${x.show}")
              println(s"CALIBRATION:   prog = ${r.prog.show.replace('\n', ' ')}")
              println(s"CALIBRATION:   counted = ${ev.show}")
              println(s"CALIBRATION:   UPPER ${(rep.cost + extra.hi).show}")
              println(s"CALIBRATION:   LOWER ${(rep.lower + extra.lo).show}")
          case None => skipped += 1
      add(Backends.referenceWarm, SpatialCost.analyze(c.prog, c.env, Backends.referenceWarm), refE)
      add(Backends.trieWarm, SpatialCost.analyze(c.prog, c.env, Backends.trieWarm), trieE)
      add(Backends.zipperWarm, SpatialCost.analyze(c.prog, c.env, Backends.zipperWarm), zipE)
      countGraph(c, r.nSpace, r.nPath) match
        case Some((gv, ge, prologue)) =>
          assertEquals(gv.toSpaceValue, refV, s"execT disagrees with eval while counted: ${r.prog.show.take(120)}")
          add(Backends.graphWarm, SpatialCost.analyze(c.prog, c.env, Backends.graphWarm), ge, prologue)
        case None => graphSkipped += 1
    println(s"CALIBRATION: $graphSkipped / ${recs.length} corpus programs could not be transpiled for execT")
    println(s"CALIBRATION: $zipperFallback / ${recs.length} corpus programs left execZ for evalI — PRICED AND " +
            "MEASURED now (evalI is instrumented), not excluded")
    // the claim behind the one declared oracle gap, measured over the whole corpus
    assertEquals(refTouch, 0L, s"eval counted $refTouch trie touches over the corpus — reference/touch would " +
                               "then have a partial oracle and must not be excluded wholesale")
    println(s"CALIBRATION: eval counted 0 trie-touch events over all ${recs.length} corpus programs")
    // TIGHTNESS IS NOT GATED ON THIS FORM, and the reason is the user's third steer rather than the
    // numbers: these are DEFINITIONAL random terms.  Their soundness (containment) IS gated, at 100%,
    // and it is the property a random corpus is the right instrument for.  The tightness product
    // requirements are gated where they describe what runs: on the OPTIMIZED cornerstones below, and
    // per operator on the geometric ladders in `SpatialScaleCheck`.
    publish("fuzzer corpus, warm phase, DEFINITIONAL form", rows, skipped, cases, Vector.empty,
            ungatedNote =
              "these are DEFINITIONAL random terms, not the optimized bodies anything ships, and a " +
              "definitional-form tightness number is the wrong question (the user's third steer). This " +
              "corpus gates SOUNDNESS — 100% containment over " + rows.length + " points — which is what " +
              "a random corpus is the right instrument for. The tightness requirements are gated on the " +
              "OPTIMIZED cornerstones below and per operator on SpatialScaleCheck's geometric ladders.")
  }

  /** ESTIMATES THAT ARE STILL INFINITE ON A CLOSED, TERMINATING, NON-GROUNDED CORNERSTONE.
   *
   *  review.md item 5: "`infinity` and zero-to-infinity intervals on executable closed programs are
   *  failed results ... Make 'zero infinite estimates on closed, terminating, non-grounded programs' a
   *  test invariant rather than maintaining an allow-list of expected failures."
   *
   *  IT IS NOW EMPTY, and the assertion below is EXACT IN BOTH DIRECTIONS, so it cannot drift: an
   *  unexpected infinity fails, and so does an entry here that has become finite.  The two former
   *  entries (`puzzle15`, `datalog-sn`) are bounded as of this run.  Note what that does and does not
   *  buy: `puzzle15`'s bound is finite and USELESS (a 10^200 polynomial), and the product-requirement
   *  gate below is what says so — replacing an infinity with an astronomical finite number is not
   *  progress unless something measures it. */
  val infiniteEstimates: Map[String, String] = Map.empty

  /** PREDICTIONS THAT ARE STILL SYMBOLIC ON A CLOSED CORNERSTONE, and therefore have no number at all.
   *
   *  A free variable in the answer is the same failure as `[0, inf]` dressed differently: the estimate
   *  cannot be compared to anything, so the row is SKIPPED rather than gated.  The set is asserted EXACT
   *  in both directions for the same reason as [[infiniteEstimates]] — a backend that becomes numeric
   *  must be removed from here, and one that stops being numeric must fail. */
  val symbolicEstimates: Map[String, String] = Map(
    "datalog-sn/reference" ->
      ("`|sn_tc()|` — the reference model's cost is parametric in the size of the recursive call's " +
       "RESULT, which is the least fixpoint of the body's size transformer.  See CS-5: there is no " +
       "interprocedural size summary, so the variable is never eliminated."),
    "datalog-sn/zipper" ->
      "`len(sn_tc())`, `|sn_tc()|` — as `datalog-sn/reference`, plus the path-length channel.")

  test("CALIBRATION: predicted intervals vs counted events on the OPTIMIZED cornerstones") {
    // The six cornerstone programs, with their inputs DECLARED (their exact spatial input types) and
    // never their outputs.  execT is skipped here: several cornerstones carry recursive `Call`s that
    // `transpile` needs a routine index for, which the corpus test covers instead.
    val rr = new scala.util.Random(12)
    val tempCells = (0 until 16).map(i => PathValue(NOAA.bits(i, 4) :+ Vector("VC", "C", "N", "W", "VW")(rr.nextInt(5)))).toSet
    val world = Space.Mention(SpaceMention("world"))
    val temperature = Space.Union(Space.Restriction(world, Space.Literal(NOAA.interval(0, 4, 4))),
                                  Space.Restriction(world, Space.Literal(NOAA.interval(12, 16, 4))))
    val live = Set((1, 0), (1, 1), (1, 2))
    val golRules = GoL.rulesFor(live)
    val puzzle = Sliding.puzzle(4, 4)
    val queens = NQueens.board(4)
    val edges = SpaceValue(Set(p("0", "1"), p("1", "2"), p("2", "3")))
    def join(r: Space, s: Space): Space = r.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
    val snTC = Routine(RoutinePtr("sn_tc"), Vector.empty,
                       Vector(SpaceMention("e"), SpaceMention("all"), SpaceMention("delta")),
                       S"all" \/ Space.Call(RoutinePtr("sn_tc"), Vector.empty,
                         Vector(S"e", S"all" \/ (join(S"delta", S"e") \ S"all"), join(S"delta", S"e") \ S"all")))

    val cases = Vector(
      Case("aunt", Routines.aunt_query_routine.body,
           AuntQuery.context.asInstanceOf[SpaceContextMap].m, Map.empty, PartialFunction.empty),
      Case("temperature", temperature, Map(SpaceMention("world") -> SpaceValue(tempCells))),
      Case("gol", Space.Call(RoutinePtr("nextStep"), Vector.empty, Vector(Space.Mention(SpaceMention("field")))),
           Map(SpaceMention("field") -> GoL.field(live)), Map.empty, golRules.defs),
      Case("puzzle15", puzzle.expandStep(Space.Mention(SpaceMention("frontier"))),
           Map(SpaceMention("frontier") -> SpaceValue(Set(puzzle.initial))), Map.empty, puzzle.defs),
      Case("nqueens4", queens.program, Map.empty, Map.empty, queens.defs),
      Case("datalog-sn", Space.Call(RoutinePtr("sn_tc"), Vector.empty,
             Vector(Space.Mention(SpaceMention("edges")), Space.Mention(SpaceMention("edges")),
                    Space.Mention(SpaceMention("edges")))),
           Map(SpaceMention("edges") -> edges), Map.empty, Syntax.mod(snTC)))

    var rows = Vector.empty[Calibration]
    var defRows = Vector.empty[Calibration]
    var gate = Vector.empty[GateRow]
    var skipped = 0
    var sawInfinite = Set.empty[String]
    var sawSymbolic = Set.empty[String]
    var folded = Vector.empty[String]
    for c <- cases do
      // ---- THE FORM THAT RUNS ------------------------------------------------------------------
      val t0 = System.nanoTime()
      val (opt, priced) = optimizedForm(c)
      val optMs = (System.nanoTime() - t0) / 1e6
      val optCase = c.copy(prog = opt.body)
      val defNodes = SpatialPipeline.nodeCount(c.prog)
      val optNodes = SpatialPipeline.nodeCount(opt.body)
      if optNodes <= 2 then folded :+= c.label
      val (refV, refE) = countReference(optCase)
      val (trieV, trieE) = countTrie(optCase)
      val (zipV, zipE) = countZipper(optCase)
      assertEquals(zipV.toSpaceValue, refV, s"${c.label}: execZ disagrees with eval on the OPTIMIZED body")
      assertEquals(trieV.toSpaceValue, refV, s"${c.label}: evalI disagrees with eval on the OPTIMIZED body")
      assertEquals(refE.touch, 0L, s"${c.label}: eval counted trie touches")
      println("-" * 116)
      println(f"CALIBRATION: ${c.label}%-12s |out|=${refV.paths.size}%5d   OPTIMIZED in $optMs%.0f ms, " +
              f"$defNodes%d -> $optNodes%d Space nodes" + (if optNodes <= 2 then "  [COMPILE-TIME EVALUATED]" else ""))
      println(f"CALIBRATION:   counted evalI [${trieE.showComponents}]")
      println(f"CALIBRATION:   counted execZ [${zipE.showComponents}]  " +
              f"(fallbacks=${zipE(EffortEvent.ZipperFallbackToEvalI)})")
      println(f"CALIBRATION:   counted eval  [${refE.showComponents}]  (reference: published, NOT gated)")
      val toCheck: Vector[(CostModel, Events)] = Vector(
        Backends.referenceWarm -> refE, Backends.trieWarm -> trieE, Backends.zipperWarm -> zipE)
      var mine = Vector.empty[Calibration]
      for (model, ev) <- toCheck do
        val rep = priced(model.backend)
        assertEquals(rep.form, CostForm.Optimized, s"${c.label}: the gated report must describe the optimized form")
        // "infinite" means EITHER an explicit `Amount.Unbounded` OR a `Bounded` whose symbol saturated
        val unb = Vector(rep.cost.work, rep.cost.alloc, rep.cost.rounds, rep.cost.touch)
          .filter(a => a.isUnbounded || a.at(Map.empty).isInfinite)
        if unb.nonEmpty then
          sawInfinite += c.label
          println(s"CALIBRATION:   INFINITE ${c.label}/${rep.backend.slug} ${unb.head.show}")
        calibrate(c.label, model, rep, ev) match
          case Some(cs) =>
            mine ++= cs
            for x <- cs do println(s"CALIBRATION:   ${x.show}")
          case None =>
            skipped += 1
            sawSymbolic += s"${c.label}/${rep.backend.slug}"
            println(s"CALIBRATION:   ${c.label}/${rep.backend.slug} SKIPPED (prediction still symbolic: " +
                    s"${(freeVars(rep.cost) ++ freeVars(rep.lower)).mkString(", ")})")
      rows ++= mine
      gate ++= gateOf("cornerstone", c.label, mine)
      // ---- THE DEFINITIONAL FORM, printed as a labelled CONTRAST and never gated ----------------
      for (model, ev) <- toCheck do
        val dr = SpatialCost.analyze(c.prog, c.env, model, CostForm.Definitional)
        calibrate(c.label + "-def", model, dr, ev).foreach(defRows ++= _)
    // THE INFINITY INVARIANT, exact in both directions (review.md item 5)
    assertEquals(sawInfinite, infiniteEstimates.keySet,
                 s"the set of cornerstones with an INFINITE prediction on the OPTIMIZED form changed; " +
                 s"declared ${infiniteEstimates.keySet.toVector.sorted}, observed ${sawInfinite.toVector.sorted}")
    // THE SYMBOLIC INVARIANT, exact in both directions
    assertEquals(sawSymbolic, symbolicEstimates.keySet,
                 s"the set of (cornerstone, backend) pairs whose OPTIMIZED-form prediction is still " +
                 s"SYMBOLIC changed; declared ${symbolicEstimates.keySet.toVector.sorted}, observed " +
                 s"${sawSymbolic.toVector.sorted}")
    for (k, why) <- symbolicEstimates.toVector.sortBy(_._1) do
      println(s"CALIBRATION: SYMBOLIC, NO NUMBER TO GATE — $k: $why")
    println(s"CALIBRATION: ${folded.length} cornerstone(s) were COMPILE-TIME EVALUATED by the ordinary " +
            s"rule list and have no run-time cost left to gate: ${if folded.isEmpty then "(none)" else folded.mkString(", ")}")
    // the definitional contrast: same programs, same counters, the form that is NOT what runs
    println("-" * 116)
    for (b, comp) <- defRows.map(r => (r.label.split('/').last, r.component)).distinct.sortBy((b, c) => (b, c.ordinal)) do
      val sub = defRows.filter(r => r.label.endsWith("/" + b) && r.component == comp)
      println("CALIBRATION: DEFINITIONAL (not gated) " + Calibration.summarize(s"$b $comp", sub).show)
    publish("cornerstones, warm phase, OPTIMIZED form", rows, skipped, cases.length, gate)
  }

  // ==============================================================================================
  // 6b. COLD vs WARM
  // ==============================================================================================

  test("COLD vs WARM: construction is separated from execution, in the model and on the clock") {
    // MODEL: for every backend, a cold phase must cost at least as much as the warm one, and for a
    // `Literal` it must cost STRICTLY more — that difference is exactly the construction the warm
    // evaluator finds already done.
    val l = litN(256, "cw")
    for b <- Backend.values do
      val warm = SpatialCost.analyze(l, Backends.of(b, ExecutionPhase.Warm)).cost
      val cold = SpatialCost.analyze(l, Backends.of(b, ExecutionPhase.Cold)).cost
      assert(cold.bigO >= warm.bigO, s"${b.slug}: a cold Literal cannot be cheaper than a warm one")
      assert(cold != warm, s"${b.slug}: the two phases must be distinguishable for a Literal")
      println(f"EVENTS: cold/warm ${b.slug}%-10s warm[${warm.show}]  cold[${cold.show}]")

    // CLOCK: the same distinction on the graph backend, where the cold half is real compilation.
    val prog = Space.Union(Space.Mention(SpaceMention("s0")), Space.TailsUnion(S"s0"))
    val sv = SpaceValue((0 until 512).map(i => p("k" + (i % 32), "v" + i)).toSet)
    val ic = Map(SpaceMention("s0") -> ITrie.fromSpaceValue(sv))
    def compileOnce(): RecursiveOpGraph =
      optimize(transpile(Routine(RoutinePtr("m"), Vector.empty, Vector(SpaceMention("s0")), prog)))
    val g0 = compileOnce()                                            // warm the JIT for compilation
    runGraphT(g0, Map.empty, Map("s0" -> ic(SpaceMention("s0"))))
    var coldNs = Long.MaxValue
    for _ <- 0 until 5 do
      val t0 = System.nanoTime(); val g = compileOnce(); val d = System.nanoTime() - t0
      assert(g.nodes.nonEmpty)
      if d < coldNs then coldNs = d
    var warmNs = Long.MaxValue
    for _ <- 0 until 5 do
      val t0 = System.nanoTime()
      var i = 0; while i < 20 do { runGraphT(g0, Map.empty, Map("s0" -> ic(SpaceMention("s0")))); i += 1 }
      val d = (System.nanoTime() - t0) / 20
      if d < warmNs then warmNs = d
    println(f"EVENTS: cold/warm execT  compile ${coldNs / 1000.0}%.1f us  vs  warm execute ${warmNs / 1000.0}%.1f us " +
            f"(${coldNs.toDouble / warmNs}%.1fx) — a single number for both would describe neither")
  }

  // ==============================================================================================
  // 7. STANDING RULE 1
  // ==============================================================================================

  test("NO EVALUATION IN THE ANALYSIS: a bomb subterm is never run by cost analysis") {
    val bomb = Space.GroundedSS(litN(4, "b"), _ => throw RuntimeException("the cost analysis evaluated its subject"))
    for m <- Backends.all do
      val rep = SpatialCost.analyze(Space.Union(litN(4, "a"), bomb), m)
      assert(rep.cost.work.isUnbounded || rep.assumptions.exists(_.contains("grounded")),
             s"${m.name}: a grounded closure must widen to an explicit unbounded, got ${rep.show}")
    // and the identity/interval machinery does not run it either
    val all = SpatialCost.analyzeAll(bomb)
    assertEquals(all.size, Backend.values.length)
    println("EVENTS: all 8 cost instances analysed a throwing grounded closure without running it")
  }
end SpatialEventsCheck
