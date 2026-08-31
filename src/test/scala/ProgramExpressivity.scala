package morkl

import munit.FunSuite
import scala.collection.mutable

/** A saved program plus its argument signature (top-level so it serializes without capturing a test). */
@SerialVersionUID(1L) final case class FuzzRec(prog: Space, nSpace: Int, nPath: Int, uniqueOut: Int)

/** Expressivity census with a VARIABLE number of space and path arguments per program, plus a
 *  per-argument RESPONSIVENESS measurement.  Each program is a function of `ns` space args (1..3,
 *  tries) and `np` path args (0..2, paths).  We run a fixed shared bank of 100 multi-argument input
 *  environments and record, per program:
 *    uniqueOut         distinct outputs over the 100 environments (1..100)
 *    respSpace/respPath how many of its space / path args it RESPONDS to — i.e. varying that one arg
 *                      (holding the others fixed at environment 0) changes the output
 *    respFrac          (respSpace+respPath)/(ns+np)  — the responsiveness parameter in [0,1]
 *    entropy, nEmpty, avgSize, nodes
 *  `expr.respMin` (default 0) optionally rejects programs responding to fewer than that many args. */
class ProgramExpressivity extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(60, "min")
  val argM = SpaceFuzzer.argM
  val A = SpaceFuzzer.alphabet
  val maxS = 3; val maxP = 2; val K = 100; val probe = 40

  def randPath(rng: java.util.Random): PathValue = PathValue(List.fill(1 + rng.nextInt(3))(A(rng.nextInt(A.length))))
  def smallTrie(rng: java.util.Random): SpaceValue = SpaceValue((0 until (1 + rng.nextInt(8))).map(_ => randPath(rng)).toSet)
  // ONE OWNER (SpatialPipeline.nodeCount).  The copy this replaces had no arm for TailsUnion, Range,
  // Raffination, TailsIntersection or Fixpoint, so those subtrees counted as leaves — and this counter
  // IS the corpus accept filter (`nodes >= 12`), so the miscount decided the corpus population.
  def nodes(s: Space): Int = SpatialPipeline.nodeCount(s)

  test("expressivity: variable args + responsiveness over 100 inputs".tag(SlowTag.Slow)) {
    val N = sys.props.get("expr.n").map(_.toInt).getOrElse(100000)
    val respMin = sys.props.get("expr.respMin").map(_.toInt).getOrElse(0)
    val sNames = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until maxP).map(j => PathRef("p" + j)).toVector
    // shared bank: K environments, each with a value for every possible arg slot
    val brng = new java.util.Random(99)
    val spaceBank: Array[Array[ITrie]] = Array.fill(maxS)(Array.fill(K)(ITrie.fromSpaceValue(smallTrie(brng))))
    val pathBank: Array[Array[PathValue]] = Array.fill(maxP)(Array.fill(K)(randPath(brng)))

    val rng = new java.util.Random(7)
    val sb = new StringBuilder
    sb.append(s"# expressivity.csv — ${RunEnvironment.oneLine(Seq("target" -> N.toString, "bank" -> K.toString, "seed" -> "12345"))}\n")
    sb.append("uniqueOut,entropy,nEmpty,nSpace,nPath,respSpace,respPath,respFrac,avgSize,nodes\n")
    val t0 = System.nanoTime(); var got = 0; var draws = 0
    while got < N do
      draws += 1
      val ns = 1 + rng.nextInt(maxS)            // 1..3 space args
      val np = rng.nextInt(maxP + 1)            // 0..2 path args
      val sargs = sNames.take(ns); val pargs = pNames.take(np)
      val arg = SpaceFuzzer.argDist.sample(using rng)
      val prog = SpaceFuzzer.genProg(arg, 6, sargs, pargs).sample(using rng)
      if nodes(prog) >= 12 then
        def icAt(spaceIdx: Int => Int): Map[SpaceMention, ITrie] = (0 until ns).map(i => sargs(i) -> spaceBank(i)(spaceIdx(i))).toMap
        def pcAt(pathIdx: Int => Int): PathContext = PathContextMap((0 until np).map(j => pargs(j) -> pathBank(j)(pathIdx(j))).toMap)
        def run(ic: Map[SpaceMention, ITrie], pc: PathContext): SpaceValue =
          evalI(prog)(using pc, ic, PartialFunction.empty).toSpaceValue
        // main: environment k varies EVERY arg together
        val out = Array.tabulate(K)(k => run(icAt(_ => k), pcAt(_ => k)))
        val freq = mutable.HashMap.empty[SpaceValue, Int]; var nEmpty = 0; var totSize = 0L
        var k = 0; while k < K do { val o = out(k); freq.update(o, freq.getOrElse(o, 0) + 1); if o.paths.isEmpty then nEmpty += 1; totSize += o.paths.size; k += 1 }
        val uniqueOut = freq.size
        val entropy = freq.valuesIterator.map { c => val p = c.toDouble / K; -p * (math.log(p) / math.log(2)) }.sum
        // responsiveness: vary ONE arg over `probe` env values, hold the others at env 0
        val ic0 = icAt(_ => 0); val pc0 = pcAt(_ => 0)
        val respSpace = (0 until ns).count(i => (0 until probe).iterator.map(k => run(icAt(j => if j == i then k else 0), pc0)).toSet.size > 1)
        val respPath = (0 until np).count(j => (0 until probe).iterator.map(k => run(ic0, pcAt(l => if l == j then k else 0))).toSet.size > 1)
        val respArgs = respSpace + respPath
        if respArgs >= respMin then
          got += 1
          sb.append(f"$uniqueOut,$entropy%.4f,$nEmpty,$ns,$np,$respSpace,$respPath,${respArgs.toDouble / (ns + np)}%.4f,${totSize.toDouble / K}%.3f,${nodes(prog)}\n")
    val secs = (System.nanoTime() - t0) / 1e9
    // the repo root, not /tmp — see the note in ProgramStats
    val f = new java.io.File(Loaders.repoRoot, "expressivity.csv"); val w = new java.io.FileWriter(f)
    try w.write(sb.toString) finally w.close()
    System.out.println(f"EXPR2: N=$got of $draws draws (respMin=$respMin), bank=$K, args space 1..$maxS path 0..$maxP, ${secs}%.1fs -> ${f.getPath}")
    assertEquals(got, N)
  }

  test("corpus: 1000 input-sensitive, multi-valued programs saved to disk".tag(SlowTag.Slow)) {
    val target = sys.props.get("corpus.n").map(_.toInt).getOrElse(1000)
    val rprobe = 64                                       // values tried per arg when testing sensitivity
    val sNames = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until maxP).map(j => PathRef("p" + j)).toVector
    val brng = new java.util.Random(99)
    val spaceBank: Array[Array[ITrie]] = Array.fill(maxS)(Array.fill(K)(ITrie.fromSpaceValue(smallTrie(brng))))
    val pathBank: Array[Array[PathValue]] = Array.fill(maxP)(Array.fill(K)(randPath(brng)))
    def evalEnv(p: Space, ns: Int, np: Int, sIdx: Int => Int, pIdx: Int => Int): SpaceValue =
      evalI(p)(using PathContextMap((0 until np).map(j => pNames(j) -> pathBank(j)(pIdx(j))).toMap),
        (0 until ns).map(i => sNames(i) -> spaceBank(i)(sIdx(i))).toMap, PartialFunction.empty).toSpaceValue

    val rng = new java.util.Random(12345)
    val kept = mutable.ArrayBuffer.empty[FuzzRec]
    var draws = 0; val t0 = System.nanoTime()
    while kept.size < target do
      draws += 1
      val ns = 1 + rng.nextInt(maxS); val np = rng.nextInt(maxP + 1)
      val arg = SpaceFuzzer.argDist.sample(using rng)
      val prog = SpaceFuzzer.genProg(arg, 6, sNames.take(ns), pNames.take(np)).sample(using rng)
      if nodes(prog) >= 12 then
        // sensitive to EACH arg: vary just that arg (others at env 0), require >1 distinct output.
        // short-circuit on the first non-responsive arg.
        def sensS(i: Int) = (0 until rprobe).iterator.map(k => evalEnv(prog, ns, np, j => if j == i then k else 0, _ => 0)).toSet.size > 1
        def sensP(j: Int) = (0 until rprobe).iterator.map(k => evalEnv(prog, ns, np, _ => 0, l => if l == j then k else 0)).toSet.size > 1
        if (0 until ns).forall(sensS) && (0 until np).forall(sensP) then
          val uniqueOut = (0 until K).iterator.map(k => evalEnv(prog, ns, np, _ => k, _ => k)).toSet.size
          if uniqueOut >= 2 then kept += FuzzRec(prog, ns, np, uniqueOut)
    val secs = (System.nanoTime() - t0) / 1e9

    def show1(s: Space) = s.show.replaceAll("\\s+", " ").trim
    // human-readable corpus
    val txt = new StringBuilder
    txt.append(s"# ${kept.size} fuzzed MORKL programs; each is sensitive to EVERY argument and produces >=2 distinct outputs.\n")
    txt.append("# free args: s0,s1,.. = space (trie) inputs;  p0,p1,.. = path inputs.  bound iteration vars are h.../t...\n")
    txt.append("# columns: idx <TAB> nSpace <TAB> nPath <TAB> uniqueOut(of 100) <TAB> program(.show)\n")
    for (r, i) <- kept.zipWithIndex do txt.append(s"$i\t${r.nSpace}\t${r.nPath}\t${r.uniqueOut}\t${show1(r.prog)}\n")
    val tf = new java.io.File(Loaders.repoRoot, "corpus_1000.txt")
    locally { val w = new java.io.FileWriter(tf); try w.write(txt.toString) finally w.close() }
    // reloadable binary + round-trip verification
    val bf = new java.io.File(Loaders.repoRoot, "corpus_1000.ser"); var serOk = false
    try
      locally { val oos = new java.io.ObjectOutputStream(new java.io.FileOutputStream(bf)); try oos.writeObject(kept.toVector) finally oos.close() }
      val back = locally { val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(bf)); try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close() }
      val i = rng.nextInt(kept.size)
      val ok = back.size == kept.size && (0 until K).forall(k =>
        evalEnv(back(i).prog, back(i).nSpace, back(i).nPath, _ => k, _ => k) == evalEnv(kept(i).prog, kept(i).nSpace, kept(i).nPath, _ => k, _ => k))
      assert(ok, "deserialized program did not re-evaluate identically"); serOk = true
    catch case e: Throwable => System.out.println(s"CORPUS: binary serialization unavailable (${e.getClass.getSimpleName}); text corpus written")
    System.out.println(f"CORPUS: kept=${kept.size} of $draws draws (${100.0 * kept.size / draws}%.1f%% accepted), ${secs}%.1fs")
    System.out.println(s"CORPUS: text=${tf.getPath}  binary=${if serOk then bf.getPath + " (round-trip verified)" else "n/a"}")

    // ============================================================================================
    // THE CONSTRUCTOR CENSUS — the gate that keeps the corpus HONEST about its coverage.
    //
    // `FuzzRec` carries `@SerialVersionUID(1L)` and its shape does not change when the GENERATOR
    // changes, so the STALE guards in CorpusValidation / CorpusLawValidation / CorpusRuntimes (which
    // catch an `InvalidClassException`) do NOT fire when a new operator is added to `SpaceFuzzer`:
    // the old, coverage-poor corpus keeps loading silently and the new operator is never exercised.
    // That is exactly how `Raffination` and `TailsIntersection` — two CORE operators, supported by
    // every one of the seven executors — reached zero occurrences in a 1000-program corpus.
    //
    // This census makes it a TEST FAILURE instead: every constructor the generator can emit must
    // actually occur in the kept corpus.
    // ============================================================================================
    def census(s: Space): Map[String, Int] =
      val m = mutable.HashMap.empty[String, Int]
      def go(x: Space): Unit =
        val k = x.getClass.getSimpleName.stripSuffix("$")
        m.update(k, m.getOrElse(k, 0) + 1)
        SizeZ3.children(x).foreach(go)
      go(s); m.toMap
    val counts = mutable.HashMap.empty[String, Int]
    for r <- kept; (k, v) <- census(r.prog) do counts.update(k, counts.getOrElse(k, 0) + v)
    System.out.println("CORPUS census: " + counts.toVector.sortBy(-_._2).map((k, v) => s"$k=$v").mkString("  "))
    val required = Vector("Union", "Intersection", "Subtraction", "Raffination", "Restriction",
                          "Composition", "Wrap", "Unwrap", "TailsUnion", "TailsIntersection",
                          "Range", "Iteration", "Mention", "Literal", "Singleton")
    val absent = required.filter(k => counts.getOrElse(k, 0) == 0)
    assertEquals(absent, Vector.empty[String],
      s"the generator can emit these constructors and the corpus contains NONE of them — the corpus " +
      s"is stale, or a generator arm is unreachable: ${absent.mkString(", ")}")
    // AND THE IDENTITY WINDOW: `Range(x, lo, 0)` normalises to the whole space, so it is the arm that
    // exercises every backend's `rangeIsIdentity` fast path.  The old generator could never draw it.
    def fullWindows(s: Space): Int =
      (s match { case Space.Range(_, lo, hi) if (lo == 0 || lo == 1) && hi == 0 => 1; case _ => 0 }) +
        SizeZ3.children(s).map(fullWindows).sum
    val idWindows = kept.map(r => fullWindows(r.prog)).sum
    System.out.println(s"CORPUS census: full-window (identity) Range occurrences = $idWindows")
    assert(idWindows > 0, "no full-window Range in the corpus: every backend's identity fast path is unexercised")

    // show 3 randomly chosen programs
    val pick = scala.util.Random(2026).shuffle((0 until kept.size).toList).take(3)
    for i <- pick do
      val r = kept(i)
      val pdesc = if r.nPath == 0 then "(no path args)" else (0 until r.nPath).map("p" + _).mkString(", ")
      System.out.println(s"\nCORPUS-PICK #$i  | space args: ${(0 until r.nSpace).map("s" + _).mkString(", ")}  | path args: $pdesc  | uniqueOut=${r.uniqueOut}/100")
      System.out.println("  " + show1(r.prog))
    assertEquals(kept.size, target)
  }
end ProgramExpressivity
