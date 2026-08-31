package morkl

import munit.FunSuite

/** Runtime + node-size census of the saved corpus over 1000 inputs, then supercompile the 5 slowest
 *  programs and re-time them (original vs SC'd) under every evaluator: the Set reference `eval`, the
 *  trie interpreters `evalI`/`evalT`, and the optimized op-graph `execT`. */
class CorpusRuntimes extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(90, "min")
  val maxS = 3; val maxP = 2
  val sNames = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
  val pNames = (0 until maxP).map(j => PathRef("p" + j)).toVector
  val A = SpaceFuzzer.alphabet
  def randPath(rng: java.util.Random): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
  def smallTrie(rng: java.util.Random): SpaceValue = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath(rng)).toSet)
  // ONE OWNER (SpatialPipeline.nodeCount): the copy this replaces was missing `Raffination`.
  def nodes(s: Space): Int = SpatialPipeline.nodeCount(s)
  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  def best(reps: Int)(body: => Unit): Double = { body; var b = Double.MaxValue; for _ <- 0 until reps do { val t = System.nanoTime(); body; val d = (System.nanoTime() - t) / 1e6; if d < b then b = d }; b }

  test("corpus runtimes + SC of the 5 slowest".tag(SlowTag.Slow)) {
    val M = sys.props.get("rt.m").map(_.toInt).getOrElse(1000)
    val recs = locally {
      Corpus.load()
    }
    val rng = new java.util.Random(424242)
    final case class Env(sv: Array[SpaceValue], st: Array[Trie], si: Array[ITrie], pv: Array[PathValue], pi: Array[List[Int]])
    val envs: Array[Env] = Array.fill(M) { val sv = Array.fill(maxS)(smallTrie(rng)); val pv = Array.fill(maxP)(randPath(rng))
      Env(sv, sv.map(Trie.fromSpaceValue), sv.map(ITrie.fromSpaceValue), pv, pv.map(p => Interner.internPath(p.items))) }
    def icK(ns: Int, k: Int) = (0 until ns).map(i => sNames(i) -> envs(k).si(i)).toMap
    def pcK(np: Int, k: Int): PathContext = PathContextMap((0 until np).map(j => pNames(j) -> envs(k).pv(j)).toMap)

    // ---- step 1: per-program runtime (evalI over M inputs) + node size ----
    for w <- recs.indices.take(100); k <- 0 until M do evalI(recs(w).prog)(using pcK(recs(w).nPath, k), icK(recs(w).nSpace, k), noRc)  // warm JIT
    val rows = recs.iterator.zipWithIndex.map { (r, i) =>
      val t0 = System.nanoTime(); var k = 0
      while k < M do { evalI(r.prog)(using pcK(r.nPath, k), icK(r.nSpace, k), noRc); k += 1 }
      (i, r, (System.nanoTime() - t0) / 1e6, nodes(r.prog))
    }.toVector
    val sb = new StringBuilder
    // PROVENANCE FIRST.  A CSV of milliseconds with no machine, toolchain or configuration on it
    // cannot be reproduced or compared with a later one; `#`-prefixed lines are a comment to every
    // reader of this file (the plotting scripts skip them).
    sb.append(s"# corpus_runtimes.csv — ${RunEnvironment.oneLine(Seq("rows" -> recs.size.toString, "envs-per-program" -> M.toString, "seed" -> "424242"))}\n")
    sb.append("idx,nodes,nSpace,nPath,uniqueOut,evalI_ms_per1000\n")
    for (i, r, ms, nd) <- rows do sb.append(f"$i,$nd,${r.nSpace},${r.nPath},${r.uniqueOut},$ms%.3f\n")
    locally { val w = new java.io.FileWriter(new java.io.File(Loaders.repoRoot, "corpus_runtimes.csv")); try w.write(sb.toString) finally w.close() }
    val tot = rows.map(_._3).sum; val nd = rows.map(_._4.toDouble).sorted; val ms = rows.map(_._3).sorted
    def pct(v: Vector[Double], p: Double) = v(math.min(v.size - 1, (p * v.size).toInt))
    System.out.println(f"RUNTIMES: ${recs.size} programs x $M inputs, total evalI ${tot}%.0f ms.")
    System.out.println(f"  nodes/program: min ${nd.head}%.0f median ${pct(nd, .5)}%.0f mean ${nd.sum / nd.size}%.1f p90 ${pct(nd, .9)}%.0f max ${nd.last}%.0f")
    System.out.println(f"  evalI ms/1000-inputs: median ${pct(ms, .5)}%.3f mean ${tot / ms.size}%.3f p90 ${pct(ms, .9)}%.3f max ${ms.last}%.3f")

    // ---- top 5 slowest ----
    val top5 = rows.sortBy(-_._3).take(5)
    System.out.println("\nTOP 5 LONGEST-RUNNING PROGRAMS (by evalI over 1000 inputs):")
    for ((i, r, msv, ndv), rank) <- top5.zipWithIndex do
      System.out.println(f"\n#${rank + 1}: corpus idx=$i  nodes=$ndv  ns=${r.nSpace} np=${r.nPath}  uniqueOut=${r.uniqueOut}  evalI=${msv}%.1f ms/1000")
      System.out.println("   " + r.prog.show.replaceAll("\\s+", " ").trim)

    // ---- step 2: supercompile each, re-run, time every evaluator (orig vs SC'd) ----
    System.out.println("\nSUPERCOMPILED top-5 re-timed over 1000 inputs (ms, best of 3; total over all inputs):")
    for ((i, r, _, ndv), rank) <- top5.zipWithIndex do
      val ns = r.nSpace; val np = r.nPath; val prog = r.prog
      val res = scala.util.Try(SC.supercompile(prog, noRc)).toOption
      // precompute per-input contexts (so timing measures the evaluator, not map building)
      val ics = Array.tabulate(M)(k => icK(ns, k)); val pcs = Array.tabulate(M)(k => pcK(np, k))
      val scs = Array.tabulate(M)(k => SpaceContextMap((0 until ns).map(x => sNames(x) -> envs(k).sv(x)).toMap))
      val tcs = Array.tabulate(M)(k => (0 until ns).map(x => sNames(x) -> envs(k).st(x)).toMap)
      val gRefs = Array.tabulate(M)(k => (0 until np).map(j => ("p" + j) -> envs(k).pi(j)).toMap)
      val gMents = Array.tabulate(M)(k => (0 until ns).map(x => ("s" + x) -> envs(k).si(x)).toMap)
      def compile(p: Space, env: PartialFunction[RoutinePtr, Routine]) =
        val (lowered, _) = lowerCalls(Routine(RoutinePtr("m"), pNames.take(np), sNames.take(ns), p), env)
        optimize(transpile(Routine(RoutinePtr("m"), pNames.take(np), sNames.take(ns), lowered)))
      def row(label: String, p: Space, env: PartialFunction[RoutinePtr, Routine]): String =
        val g = scala.util.Try(compile(p, env)).toOption
        val tEval  = best(3) { var k = 0; while k < M do { eval(p)(using pcs(k), scs(k), env); k += 1 } }
        val tEvalI = best(3) { var k = 0; while k < M do { evalI(p)(using pcs(k), ics(k), env); k += 1 } }
        val tEvalT = best(3) { var k = 0; while k < M do { evalT(p)(using pcs(k), tcs(k), env); k += 1 } }
        val tExecT = g.map(gg => best(3) { var k = 0; while k < M do { runGraphT(gg, refs = gRefs(k), mentions = gMents(k)); k += 1 } }).getOrElse(Double.NaN)
        val tExecZ = best(3) { var k = 0; while k < M do { execZ(p)(using pcs(k), ics(k), env); k += 1 } }
        f"  $label%-16s nodes=${nodes(p)}%4d  eval ${tEval}%8.1f  evalI ${tEvalI}%7.1f  evalT ${tEvalT}%7.1f  execT(opt) ${tExecT}%7.1f  execZ ${tExecZ}%7.1f"
      System.out.println(f"\n#${rank + 1} (corpus idx=$i):")
      System.out.println(row("original", prog, noRc))
      res match
        case Some(r2) =>
          // sanity: SC preserved semantics on a sample input
          assertEquals(evalI(r2.top)(using pcs(0), ics(0), r2.env).toSpaceValue, evalI(prog)(using pcs(0), ics(0), noRc).toSpaceValue, s"SC changed semantics for idx=$i")
          System.out.println(row("supercompiled", r2.top, r2.env))
        case None => System.out.println("  supercompiled     (SC failed / over budget)")
    assert(top5.size == 5)
  }
end CorpusRuntimes
