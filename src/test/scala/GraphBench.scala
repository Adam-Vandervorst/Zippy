import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Op-graph backend benchmarks: the reference interpreter (eval), the best interpreter (evalI),
 *  the original eval-based op-graph executor (exec), and the trie-native one (execT) on the
 *  transpiled graph and on the OPTIMIZED graph (push_out + optimize_sharing).  Graphs are built
 *  once (compile time); only run time is measured.  Appended to BENCHMARKS.md. */
class GraphBench extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def bench(warm: Int, reps: Int)(f: => Any): Double =
    for _ <- 0 until warm do f
    var best = Double.MaxValue
    for _ <- 0 until reps do { val t0 = System.nanoTime(); f; val dt = (System.nanoTime() - t0) / 1e6; if dt < best then best = dt }
    best

  val out = new StringBuilder
  def emit(s: String): Unit = { out.append(s).append('\n'); Loaders.note(s) }
  val compileRows = scala.collection.mutable.ArrayBuffer.empty[String]
  val crVals = scala.collection.mutable.ArrayBuffer.empty[Double]   // comp+run per benchmark, for the geomean
  val rVals  = scala.collection.mutable.ArrayBuffer.empty[Double]   // run-only per benchmark (pure eval speed)

  /** label, the Space program, mention inputs (set + trie), call index (set + graph), routine env */
  case class Bench(label: String, prog: Space,
                   mset: Map[String, SpaceValue], rc: PartialFunction[RoutinePtr, Routine],
                   gindex: PartialFunction[String, RecursiveOpGraph], warm: Int = 3, reps: Int = 7)

  def run(b: Bench): Unit =
    val mtrie = b.mset.map((k, v) => k -> ITrie.fromSpaceValue(v))            // by name, for runGraphT
    val sc = SpaceContextMap(b.mset.map((k, v) => SpaceMention(k) -> v))
    val ic = b.mset.map((k, v) => SpaceMention(k) -> ITrie.fromSpaceValue(v))  // by SpaceMention, for evalI
    val ref = eval(b.prog)(using PathContextMap(Map.empty), sc, b.rc)
    // transpile the program as a routine whose mentions are exactly the resident inputs, so the
    // ExtractSpaceMention slots exist for the graph executors to fill.
    val main = Routine(RoutinePtr("main"), Vector.empty, b.mset.keys.toVector.map(SpaceMention(_)), b.prog)
    val g = transpile(main)
    val go = optimize(g)
    // the executor-ready graph: all (non-recursive) Calls inlined into the graph, then optimized.
    // build it under a Profiler so COMPILE time is accounted per pass, separate from run time.
    // Warm the compile path first (JIT) so the measured build reflects STEADY-STATE cost — the same
    // best-of-N discipline the run column already uses; a once-cold compile mostly measures JIT warmup.
    val prof = Profiler.on
    for _ <- 0 until 3 do optimize(transpile(Routine(main.name, main.refs, main.mentions, inlineCalls(b.prog, b.rc))))
    val inlined = prof.timed("inline")(inlineCalls(b.prog, b.rc))
    val gio = optimize(prof.timed("transpile")(transpile(Routine(main.name, main.refs, main.mentions, inlined))), Deadline.never, prof)
    // correctness: every path agrees with the reference
    assertEquals(evalI(b.prog)(using PathContextMap(Map.empty), ic, b.rc).toSpaceValue, ref, s"${b.label}: evalI")
    assertEquals(runGraph(g, mentions = b.mset, index = b.gindex), ref, s"${b.label}: exec")
    assertEquals(runGraphT(g, mentions = mtrie, index = b.gindex).toSpaceValue, ref, s"${b.label}: execT")
    assertEquals(runGraphT(go, mentions = mtrie, index = b.gindex).toSpaceValue, ref, s"${b.label}: execT(optimize)")
    assertEquals(runGraphT(gio, mentions = mtrie).toSpaceValue, ref, s"${b.label}: execT(inline+opt)")
    val tEvalI = bench(b.warm, b.reps)(evalI(b.prog)(using PathContextMap(Map.empty), ic, b.rc))
    val tExec  = bench(b.warm, b.reps)(runGraph(g, mentions = b.mset, index = b.gindex))
    val tExecT = bench(b.warm, b.reps)(runGraphT(g, mentions = mtrie, index = b.gindex))
    val tExecTO = bench(b.warm, b.reps)(runGraphT(go, mentions = mtrie, index = b.gindex))
    val tExecTio = bench(b.warm, b.reps)(runGraphT(gio, mentions = mtrie))
    val away = if optimizedAway(gio) then " *" else ""   // whole program evaluated to a constant at compile time
    emit(f"| ${b.label}%-20s$away | $tEvalI%8.1f | $tExec%8.1f | $tExecT%8.1f | $tExecTO%9.1f | $tExecTio%13.1f | ${tExecTio / tEvalI}%8.2f |")
    // compile-time accounting (executor-ready form): time + IMPROVEMENT per pass, and compile+run total
    val pm = prof.millis; val pc = prof.counts
    def p(k: String) = pm.getOrElse(k, 0.0)
    val cTot = prof.totalMillis
    compileRows += f"| ${b.label}%-20s | ${p("transpile")}%9.2f | ${p("push_out")}%8.2f | ${pc.getOrElse("push_out", 0L)}%7d | ${p("optimize_sharing")}%9.2f | ${pc.getOrElse("optimize_sharing", 0L)}%7d | $cTot%8.2f | ${cTot + tExecTio}%9.2f |"
    crVals += (cTot + tExecTio); rVals += tExecTio
    Loaders.note(s"[opt-iters ${b.label}] ${pc.getOrElse("opt_iters", 0L)}")

  test("GRAPH BENCHMARKS: exec vs execT vs evalI".tag(SlowTag.Slow)) {
    emit("\n## Op-graph backend benchmark (" + java.time.LocalDate.now + ")\n")
    emit("eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =")
    emit("push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph")
    emit("then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last")
    emit("column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).")
    emit("Game of Life is now pure (precomputed number relations + Range counting), so it is included.")
    emit("Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);")
    emit("for it execT(opt) is the executor-ready form.\n")
    emit("| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |")
    emit("|---|---:|---:|---:|---:|---:|---:|")

    // aunt query (synthetic families of growing size)
    for n <- Seq(150, 400) do
      val r = new scala.util.Random(n); val ps = collection.mutable.Set.empty[PathValue]
      def sym(xs: String*) = PathValue(xs.map(PathItem.Symbol(_)).toList)
      for i <- 1 until n do { val p = r.nextInt(i); ps += sym("parent", p.toString, i.toString); ps += sym("child", i.toString, p.toString) }
      for i <- 0 until n do { if r.nextBoolean() then ps += sym("female", i.toString) else ps += sym("male", i.toString) }
      val fam = SpaceValue(ps.toSet); val ppl = SpaceValue((0 until n).map(i => sym(i.toString)).toSet)
      run(Bench(s"aunt n=$n", Routines.aunt_query_routine.body,
        Map("family" -> fam, "people" -> ppl), Syntax.mod(Routines.aunt_query_routine), PartialFunction.empty))

    // n-queens place(n,n)
    for n <- Seq(6, 7) do
      val b = NQueens.board(n)
      run(Bench(s"n-queens n=$n", b.program, Map.empty, b.defs, { case "aoe" => transpile(b.aoe_routine) }, warm = 2, reps = 5))

    // temperature: spatial trie-prefix + bucket query over the resident grid
    for bits <- Seq(12, 14) do
      val rr = new scala.util.Random(bits)
      val cells = (0 until (1 << bits)).map(i => PathValue(NOAA.bits(i, bits) :+ PathItem.Symbol(Vector("VC","C","N","W","VW")(rr.nextInt(5))))).toSet
      val world = Literal(SpaceValue(cells))
      val q = Union(Restriction(world, Literal(NOAA.interval(0, (1 << bits) / 8, bits))), Restriction(world, ss"VW"))
      run(Bench(s"temperature ${1 << bits}", q, Map.empty, PartialFunction.empty, PartialFunction.empty))

    // game of life — now pure (precomputed succ/decr/idr relations + Range counting); fully lowers.
    // one B3/S23 step over a random 12x12 field; nextStep calls neigh (resolved via gindex).
    locally {
      val rnd = new scala.util.Random(42)
      val live = (for x <- 0 until 12; y <- 0 until 12 if rnd.nextInt(100) < 35 yield (x, y)).toSet
      val rules = GoL.rulesFor(live ++ GoL.step(live))
      val call = Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Literal(GoL.field(live))))
      val gindex: PartialFunction[String, RecursiveOpGraph] = Map(
        "nextStep" -> transpile(rules.defs(RoutinePtr("nextStep"))),
        "neigh"    -> transpile(rules.defs(RoutinePtr("neigh"))))
      run(Bench("gol step 12x12", call, Map.empty, rules.defs, gindex, warm = 2, reps = 5))

      // GoL grid-as-ARGUMENT variant: the field is a runtime input (Mention), so ONE compiled graph
      // runs ANY grid.  Unlike the compiled-in literal above (which recompiles per grid), compile is
      // paid ONCE and amortizes across steps: comp+run over K steps = compile/K + run -> run.
      val argProg = Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Mention(SpaceMention("field"))))
      val argMain = Routine(RoutinePtr("main"), Vector.empty, Vector(SpaceMention("field")), argProg)
      def buildArg = optimize(transpile(Routine(argMain.name, argMain.refs, argMain.mentions, inlineCalls(argProg, rules.defs))))
      for _ <- 0 until 3 do buildArg
      val prof = Profiler.on
      val gio = optimize(prof.timed("transpile")(transpile(Routine(argMain.name, argMain.refs, argMain.mentions, inlineCalls(argProg, rules.defs)))), Deadline.never, prof)
      val fieldT = Map("field" -> ITrie.fromSpaceValue(GoL.field(live)))
      val ref = evalI(argProg)(using PathContextMap(Map.empty), Map(SpaceMention("field") -> ITrie.fromSpaceValue(GoL.field(live))), rules.defs).toSpaceValue
      assertEquals(runGraphT(gio, mentions = fieldT).toSpaceValue, ref, "gol grid-arg")
      val tRun = bench(3, 7)(runGraphT(gio, mentions = fieldT)); val tComp = prof.totalMillis
      emit(f"\n**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):")
      emit(f"compile = $tComp%.2f ms ONCE, run = $tRun%.3f ms/step.  Amortized comp+run over K steps =")
      emit(f"compile/K + run → $tRun%.3f ms (vs the compiled-in literal, recompiled per grid: ${tComp + tRun}%.2f ms each).\n")
    }

    // union_iter (shows the optimizer hoisting; mentions xs, ys)
    locally {
      val xs = SpaceValue((0 until 400).map(i => PathValue(List(PathItem.Symbol((i % 30).toString), PathItem.Symbol(i.toString)))).toSet)
      val ys = SpaceValue((0 until 400).map(i => PathValue(List(PathItem.Symbol((i % 20).toString), PathItem.Symbol(s"y$i")))).toSet)
      run(Bench("union_iter", Routines.union_iter_routine.body,
        Map("xs" -> xs, "ys" -> ys), Syntax.mod(Routines.union_iter_routine), PartialFunction.empty))
    }

    // datalog transitive closure — the self-recursion is LOWERED to a Fixpoint subgraph, so the
    // transpiled routine is already Call-free (no inlining needed). execT(opt) is the ready form.
    for size <- Seq(40, 80) do
      val rr = new scala.util.Random(size)
      val edges = SpaceValue((0 until size * 2).map(_ =>
        PathValue(List(PathItem.Symbol(rr.nextInt(size).toString), PathItem.Symbol(rr.nextInt(size).toString)))).toSet)
      val rc = Syntax.mod(Routines.transitive_routine)
      val call = Space.Call(RoutinePtr("transitive"), Vector(), Vector(Literal(edges)))
      val ref = eval(call)(using PathContextMap(Map.empty), SpaceContextMap(Map.empty), rc)
      val ic: Map[SpaceMention, ITrie] = Map.empty
      val et = Map("edges" -> ITrie.fromSpaceValue(edges))
      val prof = Profiler.on
      for _ <- 0 until 3 do optimize(transpile(Routines.transitive_routine))   // warm compile JIT (steady state)
      val g = prof.timed("transpile")(transpile(Routines.transitive_routine))   // self-recursion -> Fixpoint
      val go = optimize(g, Deadline.never, prof)
      assertEquals(evalI(call)(using PathContextMap(Map.empty), ic, rc).toSpaceValue, ref, s"datalog $size: evalI")
      assertEquals(runGraphT(g, mentions = et).toSpaceValue, ref, s"datalog $size: execT")
      assertEquals(runGraphT(go, mentions = et).toSpaceValue, ref, s"datalog $size: execT(opt)")
      val tEvalI = bench(3, 7)(evalI(call)(using PathContextMap(Map.empty), ic, rc))
      val tExecT = bench(3, 7)(runGraphT(g, mentions = et))
      val tExecTO = bench(3, 7)(runGraphT(go, mentions = et))
      emit(f"| datalog tc n=$size%-9d | $tEvalI%8.1f | ${"—"}%8s | $tExecT%8.1f | $tExecTO%9.1f | $tExecTO%13.1f | ${tExecTO / tEvalI}%8.2f |")
      val pm = prof.millis; val pc = prof.counts; def p(k: String) = pm.getOrElse(k, 0.0); val cTot = prof.totalMillis
      compileRows += f"| datalog tc n=$size%-9d | ${p("transpile")}%9.2f | ${p("push_out")}%8.2f | ${pc.getOrElse("push_out", 0L)}%7d | ${p("optimize_sharing")}%9.2f | ${pc.getOrElse("optimize_sharing", 0L)}%7d | $cTot%8.2f | ${cTot + tExecTO}%9.2f |"
      crVals += (cTot + tExecTO); rVals += tExecTO

    // ---- compile-time accounting (bounded; reported separately from — and combined with — runtime) ----
    emit("\n### Compile time + improvement per pass (executor-ready build)\n")
    emit("One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`")
    emit("= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`")
    emit("is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above")
    emit("means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.\n")
    emit("| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |")
    emit("|---|---:|---:|---:|---:|---:|---:|---:|")
    compileRows.foreach(emit)

    def geomean(xs: collection.Seq[Double]) = math.exp(xs.iterator.map(v => math.log(math.max(v, 1e-3))).sum / xs.size)
    val geo = geomean(crVals); val geoR = geomean(rVals)
    val tag = s"literalByRef=${Tuning.literalByRef} patriciaOps=${Tuning.patriciaOps}"
    System.out.println(f"GEOMEAN comp+run = $geo%.4f ms ; run-only = $geoR%.4f ms over ${crVals.size} benchmarks  [$tag]")
    emit(f"\n**comp+run geomean = $geo%.3f ms ; run-only geomean = $geoR%.3f ms** over ${crVals.size} benchmarks ($tag).")

    val f = new java.io.File(Loaders.repoRoot, "BENCHMARKS.md")
    val w = new java.io.FileWriter(f, true); try w.write(out.toString) finally w.close()
  }
end GraphBench


/** A/B benchmark isolating loop-invariant SUBGRAPH hoisting: the *only* difference between the two
 *  columns is `push_out`'s `hoistSubgraphs` flag (everything else — inline, CSE, executor — is held
 *  fixed).  Programs have a loop-invariant inner iteration inside an outer loop; with hoisting it
 *  runs once, without it runs once per outer iteration. */
class SubgraphHoistBench extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def bench(warm: Int, reps: Int)(f: => Any): Double =
    for _ <- 0 until warm do f
    var best = Double.MaxValue
    for _ <- 0 until reps do { val t0 = System.nanoTime(); f; val dt = (System.nanoTime() - t0) / 1e6; if dt < best then best = dt }
    best

  val out = new StringBuilder
  def emit(s: String): Unit = { out.append(s).append('\n'); Loaders.note(s) }
  def hd(n: String): Path = Path.Deref(PathRef(n))

  test("SUBGRAPH HOISTING A/B: optimize hoist off vs on".tag(SlowTag.Slow)) {
    emit("\n## Loop-invariant subgraph hoisting — A/B (" + java.time.LocalDate.now + ")\n")
    emit("Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY")
    emit("difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner")
    emit("iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,")
    emit("without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)")
    emit("and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop")
    emit("WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its")
    emit("overall max depth is fixed by a different branch; n-queens has no invariant inner loop.\n")
    emit("| program | exec off ms | exec on ms | speedup | depth off | depth on |")
    emit("|---|---:|---:|---:|---:|---:|")

    def maxDepth(x: RecursiveOpGraph): Int =
      val subs = x.nodes.collect { case Right(sg) => maxDepth(sg) }
      if subs.isEmpty then 0 else 1 + subs.max

    def row(label: String, main: Routine, mset: Map[String, SpaceValue], rc: PartialFunction[RoutinePtr, Routine]): Unit =
      val inlined = Routine(main.name, main.refs, main.mentions, inlineCalls(main.body, rc))
      val g = transpile(inlined)
      val gOff = optimize(g, hoistSubgraphs = false)
      val gOn  = optimize(g, hoistSubgraphs = true)
      val mt = mset.map((k, v) => k -> ITrie.fromSpaceValue(v))
      val ref = eval(main.body)(using PathContextMap(Map.empty), SpaceContextMap(mset.map((k, v) => SpaceMention(k) -> v)), rc)
      assertEquals(runGraphT(gOff, mentions = mt).toSpaceValue, ref, s"$label: hoist-off wrong")
      assertEquals(runGraphT(gOn, mentions = mt).toSpaceValue, ref, s"$label: hoist-on wrong")
      val tOff = bench(1, 3)(runGraphT(gOff, mentions = mt))
      val tOn  = bench(1, 3)(runGraphT(gOn, mentions = mt))
      emit(f"| $label%-22s | $tOff%9.2f | $tOn%9.2f | ${tOff / math.max(tOn, 1e-3)}%6.1fx | ${maxDepth(gOff)}%5d | ${maxDepth(gOn)}%5d |")

    // synthetic: an invariant inner iteration inside an outer loop that genuinely runs N times
    // (DISTINCT heads, so the outer groups into N and the inner loop runs N times without hoisting)
    for n <- Seq(150, 400) do
      val innerLit = SpaceValue((0 until 60).map(i => PathValue(List(PathItem.Symbol("k"), PathItem.Symbol(i.toString)))).toSet)
      val inner: Space = Iteration(Literal(innerLit), PathRef("y"), SpaceMention("s"), Composition(Singleton(hd("y")), S"s"))
      val src = SpaceValue((0 until n).map(i => PathValue(List(PathItem.Symbol(i.toString)))).toSet)   // distinct heads
      val main = R"o"(S"src") := Iteration(S"src", PathRef("x"), SpaceMention("r"), Union(inner, Singleton(hd("x"))))
      row(s"invariant-inner N=$n", main, Map("src" -> src), PartialFunction.empty)

    // sliding expandStep 3x3: all_moves (and its sub-iterations) are loop-invariant in the explore loop
    locally {
      val p = Sliding.puzzle(3, 3)
      val frontier = SpaceValue(Set(p.initial))
      val main = R"step"(S"frontier") := p.expandStep(S"frontier")
      row("sliding expandStep 3x3", main, Map("frontier" -> frontier), Syntax.mod(p.superpose, p.collapse))
    }

    // n-queens place(6) (nested iterations + inlined aoe)
    locally {
      val b = NQueens.board(6)
      row("n-queens place(6)", R"q"() := b.program, Map.empty, b.defs)
    }

    val f = new java.io.File(Loaders.repoRoot, "BENCHMARKS.md")
    val w = new java.io.FileWriter(f, true); try w.write(out.toString) finally w.close()
  }
end SubgraphHoistBench


/** The optimization (push_out LICM + optimize_sharing CSE) measured across all six SC example
 *  domains.  Each program is first made Call-free with `lowerCalls` (acyclic Calls inlined,
 *  union-saturating recursion lowered to a Fixpoint), then we time `execT` on the UNOPTIMIZED vs
 *  OPTIMIZED graph (absolute ms + relative speedup), and isolate the loop-invariant SUBGRAPH-hoisting
 *  contribution (optimize with hoisting off vs on).  All six domains — Game of Life now included,
 *  since its arithmetic was made pure (precomputed number relations + `Range` counting) — fully lower. */
class SCOptBench extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def bench(reps: Int)(f: => Any): Double =
    f  // warm
    var best = Double.MaxValue
    for _ <- 0 until reps do { val t0 = System.nanoTime(); f; val dt = (System.nanoTime() - t0) / 1e6; if dt < best then best = dt }
    best

  val out = new StringBuilder
  def emit(s: String): Unit = { out.append(s).append('\n'); Loaders.note(s) }

  test("SC OPTIMIZATION BENCHMARK: all six domains".tag(SlowTag.Slow)) {
    emit("\n## Optimization across all SC domains (" + java.time.LocalDate.now + ")\n")
    emit("Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating")
    emit("recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d")
    emit("graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the")
    emit("loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/")
    emit("decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.\n")
    emit("| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |")
    emit("|---|---:|---:|---:|---:|---:|---:|")

    /** Lower the routine Call-free, then time execT unopt / opt / opt-without-subgraph-hoist. */
    def run(label: String, main: Routine, mset: Map[String, SpaceValue], rc: PartialFunction[RoutinePtr, Routine]): Unit =
      val (top, residual) = lowerCalls(main, rc)
      assert(residual.isEmpty, s"$label: unexpected residual ${residual.keys.map(_.s)}")
      val g = transpile(Routine(main.name, main.refs, main.mentions, top))
      val gOpt = optimize(g)                                  // push_out (hoist on) + CSE
      val gOptNo = optimize(g, hoistSubgraphs = false)         // same, subgraph hoisting disabled
      val mt = mset.map((k, v) => k -> ITrie.fromSpaceValue(v))
      val ic = mset.map((k, v) => SpaceMention(k) -> ITrie.fromSpaceValue(v))
      // reference via evalI (the interned-trie interpreter; evalI == eval is established across the
      // suite) — fast enough for the large royal92 genealogy, where the Set-based `eval` is slow.
      val ref = evalI(main.body)(using PathContextMap(Map.empty), ic, rc).toSpaceValue
      assertEquals(runGraphT(g, mentions = mt).toSpaceValue, ref, s"$label: unopt")
      assertEquals(runGraphT(gOpt, mentions = mt).toSpaceValue, ref, s"$label: opt")
      assertEquals(runGraphT(gOptNo, mentions = mt).toSpaceValue, ref, s"$label: opt-no-hoist")
      val tEvalI = bench(9)(evalI(main.body)(using PathContextMap(Map.empty), ic, rc))
      val tUn = bench(9)(runGraphT(g, mentions = mt))
      val tOpt = bench(9)(runGraphT(gOpt, mentions = mt))
      val tNo = bench(9)(runGraphT(gOptNo, mentions = mt))
      emit(f"| $label%-18s | $tEvalI%8.2f | $tUn%9.2f | $tOpt%9.2f | ${tUn / math.max(tOpt, 1e-3)}%6.1fx | $tNo%9.2f | ${tNo / math.max(tOpt, 1e-3)}%5.1fx |")

    // 1. aunt — the lot.metta genealogy (iter pipeline over people, family invariant in the loop)
    val fam = AuntQuery.context.resolve(SpaceMention("family")); val ppl = AuntQuery.context.resolve(SpaceMention("people"))
    run("aunt (lot.metta)", Routines.aunt_query_routine, Map("family" -> fam, "people" -> ppl), PartialFunction.empty)

    // 1b. aunt — royal92 genealogy (~3000 people, ~11.6k facts; the lot.metta fixture is too small)
    locally {
      val royalCandidates = Seq(sys.props.getOrElse("royal92.metta", "royal92_simple.metta"),
                                "royal92_simple.metta", "/Users/michaelpolyntsov/Zippy/royal92_simple.metta")
      Loaders.resolve(royalCandidates*).flatMap(f => Loaders.mettaFamily(f.getPath)) match
        case Some(r92) =>
          run("aunt (royal92)", Routines.aunt_query_routine, Map("family" -> r92.family, "people" -> r92.people), PartialFunction.empty)
        case None => emit("(royal92_simple.metta not found — aunt(royal92) row skipped)")
    }

    // 2. n-queens n=7 (nested iterk + inlined aoe; invariant add/sub/upto literal tables)
    val nq = NQueens.board(7)
    run("n-queens n=7", R"q"() := nq.program, Map.empty, nq.defs)

    // 3. temperature — prefix-interval + band restriction over a 4096-cell grid literal
    locally {
      val rr = new scala.util.Random(12)
      val cells = (0 until 4096).map(i => PathValue(NOAA.bits(i, 12) :+ PathItem.Symbol(Vector("VC","C","N","W","VW")(rr.nextInt(5))))).toSet
      val world = Literal(SpaceValue(cells))
      val q = Union(Restriction(world, Literal(NOAA.interval(0, 512, 12))), Restriction(world, ss"VW"))
      run("temperature 4096", R"t"() := q, Map.empty, PartialFunction.empty)
    }

    // 4. datalog — transitive closure (self-recursion lowered to a Fixpoint) on a random graph
    locally {
      val rr = new scala.util.Random(80)
      val edges = SpaceValue((0 until 160).map(_ =>
        PathValue(List(PathItem.Symbol(rr.nextInt(80).toString), PathItem.Symbol(rr.nextInt(80).toString)))).toSet)
      // bind edges via a Literal so main.body is closed for eval/evalI reference
      val body = Routines.transitive_routine.body match
        case Space.Union(_, Space.Call(_, _, Vector(next))) =>
          Space.Fixpoint(Literal(edges), SpaceMention("edges"), next)
        case _ => fail("transitive shape")
      run("datalog tc (n=80)", R"tc"() := body, Map.empty, PartialFunction.empty)
    }

    // 5. sliding 3x3 expandStep (inlined superpose/collapse; invariant all_moves sub-iteration)
    locally {
      val p = Sliding.puzzle(3, 3)
      run("sliding 3x3 step", R"step"(S"frontier") := p.expandStep(S"frontier"),
        Map("frontier" -> SpaceValue(Set(p.initial))), Syntax.mod(p.superpose, p.collapse))
    }

    // 6. Game of Life — now PURE (precomputed succ/decr/idr number relations + Range counting).
    //    One B3/S23 step over a random 12x12 field; the number relations and field("Cell") are
    //    loop-invariant in the per-cell iterations, so the optimizer has real hoisting to do.
    locally {
      val rnd = new scala.util.Random(42)
      val live = (for x <- 0 until 12; y <- 0 until 12 if rnd.nextInt(100) < 35 yield (x, y)).toSet
      val rules = GoL.rulesFor(live ++ GoL.step(live))
      val call = Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Literal(GoL.field(live))))
      run("gol step 12x12", R"g"() := call, Map.empty, rules.defs)
    }

    val f = new java.io.File(Loaders.repoRoot, "BENCHMARKS.md")
    val w = new java.io.FileWriter(f, true); try w.write(out.toString) finally w.close()
  }
end SCOptBench


/** Pipeline-stage ablation: for each example, the time to EVALUATE it through five increasingly-
 *  compiled paths — (1) `eval` on the raw definition (Set reference), (2) `evalI` on the definition
 *  (interned-trie interpreter), (3) `evalI` on the SUPERCOMPILED residual, (4) `execT` on the
 *  lower→transpile→optimize op-graph (no SC), (5) `execT` on the SC-then-graph-optimized graph.
 *  Inputs are modest so the slow Set `eval` and supercompilation are feasible.  Each stage is
 *  verified against the reference and reported in ms (— = stage not applicable / over budget). */
class AblationStages extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def best(reps: Int)(f: => Any): Double =
    f; var b = Double.MaxValue
    for _ <- 0 until reps do { val t0 = System.nanoTime(); f; val dt = (System.nanoTime() - t0) / 1e6; if dt < b then b = dt }
    b
  def tryMs(reps: Int)(f: => Any): Option[Double] = scala.util.Try(best(reps)(f)).toOption

  val out = new StringBuilder
  def emit(s: String): Unit = { out.append(s).append('\n'); Loaders.note(s) }

  /** config = a closed/parameterised Space; mset = resident mention inputs; defs = routine env. */
  def row(label: String, config: Space, mset: Map[String, SpaceValue], defs: PartialFunction[RoutinePtr, Routine]): Unit =
    val sc = SpaceContextMap(mset.map((k, v) => SpaceMention(k) -> v))
    val ic = mset.map((k, v) => SpaceMention(k) -> ITrie.fromSpaceValue(v))
    val mt = mset.map((k, v) => k -> ITrie.fromSpaceValue(v))
    val ments = mset.keys.toVector.map(SpaceMention(_))
    val ref = eval(config)(using PathContextMap(Map.empty), sc, defs)
    // (1) eval on the raw definition
    val tEval = tryMs(3)(eval(config)(using PathContextMap(Map.empty), sc, defs))
    // (2) evalI on the definition
    val tEvalI = tryMs(5) { assertEquals(evalI(config)(using PathContextMap(Map.empty), ic, defs).toSpaceValue, ref, s"$label evalI"); evalI(config)(using PathContextMap(Map.empty), ic, defs) }
    // (3) evalI on the supercompiled residual
    val scRes = scala.util.Try(SC.supercompile(config, defs)).toOption
    val tEvalISC = scRes.flatMap { res => tryMs(5) {
      assertEquals(evalI(res.top)(using PathContextMap(Map.empty), ic, res.env).toSpaceValue, ref, s"$label evalI∘SC"); evalI(res.top)(using PathContextMap(Map.empty), ic, res.env) } }
    // (4) execT on lower→transpile→optimize (no SC)
    val tExecOpt = tryMs(5) {
      val (top, residual) = lowerCalls(Routine(RoutinePtr("m"), Vector.empty, ments, config), defs)
      val g = optimize(transpile(Routine(RoutinePtr("m"), Vector.empty, ments, top)))
      assertEquals(runGraphT(g, mentions = mt).toSpaceValue, ref, s"$label execT∘opt"); runGraphT(g, mentions = mt) }
    // (5) execT on SC-then-graph-optimized
    val tExecSCOpt = scRes.flatMap { res => tryMs(5) {
      val (top, _) = lowerCalls(Routine(RoutinePtr("m"), Vector.empty, ments, res.top), res.env)
      val g = optimize(transpile(Routine(RoutinePtr("m"), Vector.empty, ments, top)))
      assertEquals(runGraphT(g, mentions = mt).toSpaceValue, ref, s"$label execT∘SC∘opt"); runGraphT(g, mentions = mt) } }
    def c(o: Option[Double]) = o.map(v => f"$v%8.3f").getOrElse(f"${"—"}%8s")
    emit(f"| $label%-18s | ${c(tEval)} | ${c(tEvalI)} | ${c(tEvalISC)} | ${c(tExecOpt)} | ${c(tExecSCOpt)} |")

  test("ABLATION: pipeline stages (eval → evalI → SC → opt-graph → SC+opt-graph)".tag(SlowTag.Slow)) {
    emit("\n## Pipeline-stage ablation (" + java.time.LocalDate.now + ")\n")
    emit("Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest")
    emit("inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set")
    emit("reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled")
    emit("residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then")
    emit("graph-optimize.  All stages verified equal to the reference.\n")
    emit("| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |")
    emit("|---|---:|---:|---:|---:|---:|")

    // aunt (lot.metta fixture — small)
    locally {
      val fam = AuntQuery.context.resolve(SpaceMention("family")); val ppl = AuntQuery.context.resolve(SpaceMention("people"))
      row("aunt (lot)", Space.Call(RoutinePtr("aunts"), Vector(), Vector(S"family", S"people")),
        Map("family" -> fam, "people" -> ppl), Syntax.mod(Routines.aunt_query_routine))
    }
    // datalog transitive closure (small graph, closed).  Use the Fixpoint form (equivalent to the
    // recursive `transitive` Call, but Call-free) so the op-graph execT stages lower too — the generic
    // lowerCalls leaves the top-level entry call to a recursive routine as a residual Call.
    locally {
      val rr = new scala.util.Random(7)
      val edges = SpaceValue((0 until 30).map(_ => PathValue(List(PathItem.Symbol(rr.nextInt(15).toString), PathItem.Symbol(rr.nextInt(15).toString)))).toSet)
      val cfg = Routines.transitive_routine.body match
        case Space.Union(_, Space.Call(_, _, Vector(next))) => Space.Fixpoint(Literal(edges), SpaceMention("edges"), next)
        case _ => fail("transitive shape")
      row("datalog tc (n=15)", cfg, Map.empty, PartialFunction.empty)
    }
    // game of life (glider, closed)
    locally {
      val glider = Set((1, 0), (2, 1), (0, 2), (1, 2), (2, 2))
      val rules = GoL.rulesFor(glider ++ GoL.step(glider))
      row("gol step (glider)", Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Literal(GoL.field(glider)))), Map.empty, rules.defs)
    }
    // sliding 3x3 — one expansion from the initial state
    locally {
      val p = Sliding.puzzle(3, 3)
      row("sliding 3x3 step", p.expandStep(Singleton(Path.Constant(p.initial))), Map.empty, Syntax.mod(p.superpose, p.collapse))
    }
    // n-queens n=6 (the deforestation case)
    locally {
      val b = NQueens.board(6)
      row("n-queens n=6", b.program, Map.empty, b.defs)
    }
    // temperature (small grid, closed, no Calls)
    locally {
      val rr = new scala.util.Random(9)
      val cells = (0 until 1024).map(i => PathValue(NOAA.bits(i, 10) :+ PathItem.Symbol(Vector("VC","C","N","W","VW")(rr.nextInt(5))))).toSet
      val world = Literal(SpaceValue(cells))
      row("temperature 1024", Union(Restriction(world, Literal(NOAA.interval(0, 128, 10))), Restriction(world, ss"VW")), Map.empty, PartialFunction.empty)
    }

    val f = new java.io.File(Loaders.repoRoot, "BENCHMARKS.md")
    val w = new java.io.FileWriter(f, true); try w.write(out.toString) finally w.close()
  }
end AblationStages
