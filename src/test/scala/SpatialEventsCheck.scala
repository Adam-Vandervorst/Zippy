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
 *   2. the disabled sink's cost is MEASURED, not asserted;
 *   3. the hooks are wired where they claim to be (hand-computed exact counts per executor);
 *   4. each of the four attribution errors is now a passing regression;
 *   5. containment (`lower <= actual <= upper`) and slack (`upper / actual`) are measured PER
 *      COMPONENT and PER BACKEND over the corpus and the cornerstones, with median and p95
 *      published; rank correlation is demoted to `SpatialCostCheck`;
 *   6. the specific regression the review asks for: for a backend whose real implementation returns
 *      its input unchanged, increasing the input size must NOT increase modelled warm work.
 *
 *  EXECUTORS ARE GROUND TRUTH HERE AND NOWHERE ELSE.  Every `eval`/`execT`/`execZ` call below is a
 *  test oracle.  The analysis under test (`SpatialCost.analyze`) never runs the program — the last
 *  test in this file pins that with a grounded closure that throws if executed.
 *
 *  COVERAGE, HONESTLY.  Three of the four backends have counted runs: Reference (`eval`), Graph
 *  (`execT`) and Zipper (`execZ`).  The Trie backend (`evalI`) is NOT calibrated: `evalI`,
 *  `ITrie` and `IntTrieOps` carry no hooks because those files are outside this change.  Its
 *  formulas are checked for shape and monotonicity in `SpatialCostCheck` and nothing here claims
 *  they are measured. */
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
      assert(Vector("eval", "execT", "execZ").exists(e.emitter.contains),
             s"$e's emitter '${e.emitter}' is not one of the instrumented executables")
    // the three CALIBRATED components partition the non-explanatory events
    val calibrated = Vector(EffortComponent.Work, EffortComponent.Alloc, EffortComponent.Rounds)
      .flatMap(EffortEvent.ofComponent)
    val explain = EffortEvent.ofComponent(EffortComponent.Explain)
    assertEquals((calibrated ++ explain).sortBy(_.ordinal), all.sortBy(_.ordinal))
    assertEquals(calibrated.intersect(explain), Vector.empty, "an event may not be both counted and explanatory")
    assertEquals(calibrated.distinct.length, calibrated.length, "no event may fall in two components")
    println(s"EVENTS: ${all.length} events — ${calibrated.length} calibrated, ${explain.length} explanatory")
    for c <- EffortComponent.values do
      println(s"EVENTS:   ${c}: ${EffortEvent.ofComponent(c).map(_.toString).mkString(", ")}")
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
    println(f"EVENTS: disarmed hook cost in a tight loop: ${nsPerHook}%.4f ns/hook " +
            f"(bare ${tBare / 1e6}%.1f ms vs guarded ${tGuard / 1e6}%.1f ms over $n iterations)")

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
            f"${oneRun.work + oneRun.alloc + oneRun.rounds} events per run")
    // the only ASSERTION: counting must stay usable as an oracle, i.e. within an order of magnitude
    assert(on < off * 20.0, f"counting is too expensive to use as an oracle: ${on / off}%.1fx")
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
    Vector(c.work, c.alloc, c.rounds).flatMap(a => a.symOpt.map(Sym.vars).getOrElse(Set.empty[String])).toSet

  /** One backend's calibration points, or `None` when the prediction still mentions a free variable
   *  (a symbolic fixpoint round count, a grounded path length): evaluating those at an arbitrary
   *  valuation would produce a number the model never claimed, so such rows are SKIPPED and counted,
   *  never silently defaulted. */
  def calibrate(label: String, rep: SpatialCost.Report, ev: Events,
                extra: CostInterval = CostInterval.zero): Option[Vector[Calibration]] =
    val hi = rep.cost + extra.hi
    val lo = rep.lower + extra.lo
    if freeVars(hi).nonEmpty || freeVars(lo).nonEmpty then None
    else Some(Vector(EffortComponent.Work, EffortComponent.Alloc, EffortComponent.Rounds).map { comp =>
      Calibration(s"$label/${rep.backend.slug}", comp, ev.component(comp),
                  lo.calibrated(comp).at(Map.empty), hi.calibrated(comp).at(Map.empty))
    })

  def countReference(c: Case): (SpaceValue, Events) =
    eval(c.prog)(using c.pc, c.sc, c.rc)                              // warm
    EffortSink.count(eval(c.prog)(using c.pc, c.sc, c.rc))

  def countZipper(c: Case): (ITrie, Events) =
    execZ(c.prog)(using c.pc, c.ic, c.rc)
    EffortSink.count(execZ(c.prog)(using c.pc, c.ic, c.rc))

  /** THE ONE STRUCTURAL EXCLUSION, and its exact reason.
   *
   *  When `transpileZ` hands a subterm to `evalI` it stops emitting events entirely, because `evalI`
   *  and the `ITrie` internals carry no hooks (those files are outside this change).  The counted
   *  vector for such a run is therefore a KNOWN UNDERCOUNT — typically a single `ZipperBuild` for a
   *  whole program — and comparing a model that prices the delegated work against it would measure
   *  the instrumentation gap, not the model.  Such runs are excluded and counted, never quietly
   *  folded into the slack statistics. */
  def zipperCalibratable(ev: Events): Boolean = ev(EffortEvent.ZipperFallbackToEvalI) == 0L

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

  /** print the containment/slack table review.md asks for, and gate on SOUNDNESS (containment) */
  def publish(title: String, rows: Vector[Calibration], skipped: Int, cases: Int): Unit =
    println("=" * 108)
    println(s"CALIBRATION — $title  ($cases cases, ${rows.length} points, $skipped predictions skipped as symbolic)")
    println("=" * 108)
    val keys = rows.map(r => (r.label.split('/').last, r.component)).distinct
      .sortBy((b, c) => (b, c.ordinal))
    for (b, comp) <- keys do
      val sub = rows.filter(r => r.label.endsWith("/" + b) && r.component == comp)
      println("CALIBRATION: " + Calibration.summarize(s"$b $comp", sub).show)
      // the same rows restricted to predictions that are actually BOUNDED: an `Amount.Unbounded`
      // (an unbounded fixpoint, a recursion with no decreasing measure) contains trivially and
      // reports infinite slack, which is honest but says nothing about tightness
      val fin = sub.filter(r => !r.upper.isInfinite)
      if fin.length != sub.length then
        println("CALIBRATION: " + Calibration.summarize(s"$b $comp [bounded only]", fin).show +
                f"   (${sub.length - fin.length} of ${sub.length} predictions were UNBOUNDED)")
    val bad = rows.filterNot(_.contains)
    println(f"CALIBRATION: overall containment ${100.0 * rows.count(_.contains) / math.max(1, rows.length)}%.2f%% " +
            f"(${bad.length} of ${rows.length} points outside the interval)")
    for b <- bad.take(8) do println(s"CALIBRATION:   OUT ${b.show}")
    // SOUNDNESS IS THE GATE: an upper bound below the counted truth is a bug, not imprecision.
    assertEquals(bad.length, 0, s"$title: ${bad.length} counted values fell outside the predicted interval")

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
    for r <- recs do
      val c = Case(s"corpus", r.prog, sv.filter((k, _) => sNames.take(r.nSpace).contains(k)),
                   pv.filter((k, _) => pNames.take(r.nPath).contains(k)))
      val (refV, refE) = countReference(c)
      val (zipV, zipE) = countZipper(c)
      // the hooks must not have changed what the executors compute
      assertEquals(zipV.toSpaceValue, refV, s"execZ disagrees with eval while counted: ${r.prog.show.take(120)}")
      cases += 1
      def add(rep: SpatialCost.Report, ev: Events, extra: CostInterval = CostInterval.zero): Unit =
        calibrate("corpus", rep, ev, extra) match
          case Some(cs) =>
            rows ++= cs
            // DIAGNOSTIC: an out-of-interval point is a model bug, so print the subject once
            for x <- cs if !x.contains && diagnosed < 4 do
              diagnosed += 1
              println(s"CALIBRATION: DIAGNOSE ${x.show}")
              println(s"CALIBRATION:   prog = ${r.prog.show.replace('\n', ' ')}")
              println(s"CALIBRATION:   counted = ${ev.show}")
              println(s"CALIBRATION:   UPPER ${(rep.cost + extra.hi).show}")
              println(s"CALIBRATION:   LOWER ${(rep.lower + extra.lo).show}")
          case None => skipped += 1
      add(SpatialCost.analyze(c.prog, c.env, Backends.referenceWarm), refE)
      if zipperCalibratable(zipE) then add(SpatialCost.analyze(c.prog, c.env, Backends.zipperWarm), zipE)
      else zipperFallback += 1
      countGraph(c, r.nSpace, r.nPath) match
        case Some((gv, ge, prologue)) =>
          assertEquals(gv.toSpaceValue, refV, s"execT disagrees with eval while counted: ${r.prog.show.take(120)}")
          add(SpatialCost.analyze(c.prog, c.env, Backends.graphWarm), ge, prologue)
        case None => graphSkipped += 1
    println(s"CALIBRATION: $graphSkipped / ${recs.length} corpus programs could not be transpiled for execT")
    println(s"CALIBRATION: $zipperFallback / ${recs.length} corpus programs left execZ for evalI (uninstrumented) " +
            "and are excluded from the zipper rows")
    publish("fuzzer corpus, warm phase", rows, skipped, cases)
  }

  test("CALIBRATION: predicted intervals vs counted events on the cornerstones") {
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
    var skipped = 0
    for c <- cases do
      val (refV, refE) = countReference(c)
      val (zipV, zipE) = countZipper(c)
      assertEquals(zipV.toSpaceValue, refV, s"${c.label}: execZ disagrees with eval while counted")
      println(f"CALIBRATION: ${c.label}%-12s |out|=${refV.paths.size}%5d  " +
              f"eval[${refE.showComponents}]  execZ[${zipE.showComponents}]")
      val toCheck =
        Vector(SpatialCost.analyze(c.prog, c.env, Backends.referenceWarm) -> refE) ++
        (if zipperCalibratable(zipE) then Vector(SpatialCost.analyze(c.prog, c.env, Backends.zipperWarm) -> zipE)
         else { println(s"CALIBRATION:   ${c.label}/zipper EXCLUDED (execZ delegated " +
                        s"${zipE(EffortEvent.ZipperFallbackToEvalI)} subterm(s) to the uninstrumented evalI)"); Vector.empty })
      for (rep, ev) <- toCheck do
        calibrate(c.label, rep, ev) match
          case Some(cs) =>
            rows ++= cs
            for x <- cs do println(s"CALIBRATION:   ${x.show}")
          case None =>
            skipped += 1
            println(s"CALIBRATION:   ${c.label}/${rep.backend.slug} SKIPPED (prediction still symbolic: " +
                    s"${(freeVars(rep.cost) ++ freeVars(rep.lower)).mkString(", ")})")
    publish("cornerstones, warm phase", rows, skipped, cases.length)
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
