package morkl

import munit.FunSuite

/** Differential validation: every executor must agree on every (program, input) pair.  Loads the saved
 *  1000-program corpus and runs each program on 1000 random multi-argument input environments, asserting
 *    eval  ==  evalI  ==  evalT  ==  exec(graph)  ==  execT(graph)  ==  execT(optimize(graph))
 *  where `eval` (Set reference) is the oracle.  Programs have free space args s0.. (bound via the space
 *  context / graph mentions) and path args p0.. (bound via the path context / graph refs). */
class CorpusValidation extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(90, "min")
  val maxS = 3; val maxP = 2
  val sNames = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
  val pNames = (0 until maxP).map(j => PathRef("p" + j)).toVector
  val A = SpaceFuzzer.alphabet

  def randPath(rng: java.util.Random): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
  def smallTrie(rng: java.util.Random): SpaceValue = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath(rng)).toSet)

  test("validate all executors on 1000 programs x 1000 random spaces".tag(SlowTag.Slow)) {
    val M = sys.props.get("valid.m").map(_.toInt).getOrElse(1000)            // # input environments
    val progLimit = sys.props.get("valid.progs").map(_.toInt).getOrElse(Int.MaxValue)
    // load the saved corpus
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    assert(f.exists, s"corpus not found at ${f.getPath} — run the corpus test first")
    val recs0 = locally {
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]]
      catch case e: java.io.InvalidClassException =>
        throw new AssertionError("corpus_1000.ser is STALE (serialized classes changed) — rerun morkl.ProgramExpressivity to regenerate it", e)
      finally ois.close()
    }
    val recs = recs0.take(progLimit)

    // precompute M input environments in every representation (independent of the program)
    val rng = new java.util.Random(424242)
    final case class Env(sv: Array[SpaceValue], st: Array[Trie], si: Array[ITrie], pv: Array[PathValue], pi: Array[List[Int]])
    val envs: Array[Env] = Array.fill(M) {
      val sv = Array.fill(maxS)(smallTrie(rng)); val pv = Array.fill(maxP)(randPath(rng))
      Env(sv, sv.map(Trie.fromSpaceValue), sv.map(ITrie.fromSpaceValue), pv, pv.map(p => Interner.internPath(p.items)))
    }
    val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty

    var checks = 0L; var compileMs = 0.0
    val t0 = System.nanoTime()
    for (r, pi) <- recs.iterator.zipWithIndex do
      val ns = r.nSpace; val np = r.nPath; val prog = r.prog
      val c0 = System.nanoTime()
      val g = transpile(Routine(RoutinePtr("main"), pNames.take(np), sNames.take(ns), prog))
      val go = optimize(g)
      compileMs += (System.nanoTime() - c0) / 1e6
      var k = 0
      while k < M do
        val e = envs(k)
        val pc: PathContext = PathContextMap((0 until np).map(j => pNames(j) -> e.pv(j)).toMap)
        val sc = SpaceContextMap((0 until ns).map(i => sNames(i) -> e.sv(i)).toMap)
        val ref = eval(prog)(using pc, sc, noRc)                                        // oracle
        val ic = (0 until ns).map(i => sNames(i) -> e.si(i)).toMap
        val tc = (0 until ns).map(i => sNames(i) -> e.st(i)).toMap
        val gRefs = (0 until np).map(j => ("p" + j) -> e.pv(j)).toMap
        val gMents = (0 until ns).map(i => ("s" + i) -> e.sv(i)).toMap
        val gtRefs = (0 until np).map(j => ("p" + j) -> e.pi(j)).toMap
        val gtMents = (0 until ns).map(i => ("s" + i) -> e.si(i)).toMap
        def msg(who: String) = s"$who disagrees on prog #$pi (ns=$ns np=$np) env #$k\n  ${prog.show.replaceAll("\\s+", " ")}"
        assertEquals(evalI(prog)(using pc, ic, noRc).toSpaceValue, ref, msg("evalI"))
        assertEquals(evalT(prog)(using pc, tc, noRc).toSpaceValue, ref, msg("evalT"))
        assertEquals(runGraph(g, refs = gRefs, mentions = gMents), ref, msg("exec"))
        assertEquals(runGraphT(g, refs = gtRefs, mentions = gtMents).toSpaceValue, ref, msg("execT"))
        assertEquals(runGraphT(go, refs = gtRefs, mentions = gtMents).toSpaceValue, ref, msg("execT(opt)"))
        assertEquals(execZ(prog)(using pc, ic, noRc).toSpaceValue, ref, msg("execZ"))
        checks += 1; k += 1
    val secs = (System.nanoTime() - t0) / 1e9
    System.out.println(f"VALIDATE: ${recs.size} programs x $M inputs = $checks pairs, 7 executors each agree; " +
      f"compile ${compileMs}%.0fms total, ${secs}%.1fs")
    assertEquals(checks, recs.size.toLong * M)
  }
end CorpusValidation
