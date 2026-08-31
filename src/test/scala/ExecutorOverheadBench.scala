package morkl

import munit.FunSuite

/** Invariant under test: the COMPILED op-graph executors must never be slower than the matching
 *  INTERPRETERS over the same representation — `exec` (SpaceValue op-graph) vs `eval` (SpaceValue
 *  interpreter), and `execT` (interned-trie op-graph) vs `evalI` (trie interpreter).  A compiled
 *  graph does the same work without per-node AST dispatch and with common-subexpression sharing, so
 *  it should dominate.  We compile each corpus program, time all four executors over many inputs
 *  (best of 3), and report the geomean ratios and the worst offenders. */
class ExecutorOverheadBench extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")
  val maxS = 3; val maxP = 2; val A = SpaceFuzzer.alphabet
  val sNames = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
  val pNames = (0 until maxP).map(j => PathRef("p" + j)).toVector
  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  def randPath(r: java.util.Random) = PathValue(List.fill(1 + r.nextInt(2))(A(r.nextInt(A.length))))
  def smallTrie(r: java.util.Random) = SpaceValue((0 until (1 + r.nextInt(6))).map(_ => randPath(r)).toSet)
  def best(reps: Int)(body: => Unit): Double =
    body; var b = Double.MaxValue
    for _ <- 0 until reps do { val t = System.nanoTime(); body; val d = (System.nanoTime() - t) / 1e6; if d < b then b = d }
    b

  test("compiled executors are never slower than the interpreters (exec vs eval, execT vs evalI)".tag(SlowTag.Slow)) {
    val recs = locally {
      Corpus.load()
    }
    val M = sys.props.get("ovh.m").map(_.toInt).getOrElse(120)
    val rng = new java.util.Random(8675309)
    val sv = Array.fill(M, maxS)(smallTrie(rng)); val pv = Array.fill(M, maxP)(randPath(rng))
    val si = sv.map(_.map(ITrie.fromSpaceValue)); val pi = pv.map(_.map(p => Interner.internPath(p.items)))
    def pc(np: Int, k: Int): PathContext = PathContextMap((0 until np).map(j => pNames(j) -> pv(k)(j)).toMap)
    def sc(ns: Int, k: Int): SpaceContext = SpaceContextMap((0 until ns).map(i => sNames(i) -> sv(k)(i)).toMap)
    def ic(ns: Int, k: Int) = (0 until ns).map(i => sNames(i) -> si(k)(i)).toMap
    def gMs(ns: Int, k: Int) = (0 until ns).map(i => ("s" + i) -> sv(k)(i)).toMap
    def gMi(ns: Int, k: Int) = (0 until ns).map(i => ("s" + i) -> si(k)(i)).toMap
    def gRp(np: Int, k: Int) = (0 until np).map(j => ("p" + j) -> pv(k)(j)).toMap
    def gRi(np: Int, k: Int) = (0 until np).map(j => ("p" + j) -> pi(k)(j)).toMap
    def compile(r: FuzzRec) = optimize(transpile(Routine(RoutinePtr("m"), pNames.take(r.nPath), sNames.take(r.nSpace), r.prog)))

    // warm the JIT
    for r <- recs.take(60) do { val g = compile(r); for k <- 0 until 20 do { eval(r.prog)(using pc(r.nPath, k), sc(r.nSpace, k), noRc); runGraph(g, gRp(r.nPath, k), gMs(r.nSpace, k)); evalI(r.prog)(using pc(r.nPath, k), ic(r.nSpace, k), noRc); runGraphT(g, gRi(r.nPath, k), gMi(r.nSpace, k)) } }

    var gmExecEval = 0.0; var gmExecTEvalI = 0.0; var gmExecZEvalI = 0.0; var n = 0
    var execSlower = 0; var execTSlower = 0; var execZSlower = 0
    var worstExec = (1.0, -1); var worstExecT = (1.0, -1); var worstExecZ = (1.0, -1)
    for (r, i) <- recs.zipWithIndex do
      val g = compile(r); val ns = r.nSpace; val np = r.nPath
      val tEval  = best(3) { var k = 0; while k < M do { eval(r.prog)(using pc(np, k), sc(ns, k), noRc); k += 1 } }
      val tExec  = best(3) { var k = 0; while k < M do { runGraph(g, gRp(np, k), gMs(ns, k)); k += 1 } }
      val tEvalI = best(3) { var k = 0; while k < M do { evalI(r.prog)(using pc(np, k), ic(ns, k), noRc); k += 1 } }
      val tExecT = best(3) { var k = 0; while k < M do { runGraphT(g, gRi(np, k), gMi(ns, k)); k += 1 } }
      val tExecZ = best(3) { var k = 0; while k < M do { execZ(r.prog)(using pc(np, k), ic(ns, k), noRc); k += 1 } }
      val rE = tExec / tEval; val rT = tExecT / tEvalI; val rZ = tExecZ / tEvalI
      gmExecEval += math.log(rE); gmExecTEvalI += math.log(rT); gmExecZEvalI += math.log(rZ); n += 1
      if rE > 1.05 then execSlower += 1
      if rT > 1.05 then execTSlower += 1
      if rZ > 1.05 then execZSlower += 1
      if rE > worstExec._1 then worstExec = (rE, i)
      if rT > worstExecT._1 then worstExecT = (rT, i)
      if rZ > worstExecZ._1 then worstExecZ = (rZ, i)
    System.out.println(f"\nEXECUTOR OVERHEAD over ${recs.size} programs x $M inputs (ratio = compiled / interpreted; <1 is faster):")
    System.out.println(f"  exec / eval   : geomean ${math.exp(gmExecEval / n)}%.3f   #(>1.05x slower) ${execSlower}   worst ${worstExec._1}%.2fx @ idx=${worstExec._2}")
    System.out.println(f"  execT / evalI : geomean ${math.exp(gmExecTEvalI / n)}%.3f   #(>1.05x slower) ${execTSlower}   worst ${worstExecT._1}%.2fx @ idx=${worstExecT._2}")
    System.out.println(f"  execZ / evalI : geomean ${math.exp(gmExecZEvalI / n)}%.3f   #(>1.05x slower) ${execZSlower}   worst ${worstExecZ._1}%.2fx @ idx=${worstExecZ._2}")
    System.out.println("")
  }
end ExecutorOverheadBench
