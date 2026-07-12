package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Large-scale study of the SpaceZipper executor (`execZ`).
 *
 *  Two regimes are measured, both on HUGE interned tries (operands pre-interned ONCE and fed via
 *  `Mention`/`ic`, so timing reflects the OPERATION, not literal interning — and so the asymptotics are
 *  not masked by an unavoidable O(|input|) build that both executors would pay):
 *
 *   (A) FLAT set-algebra on huge tries at three node-sharing levels (1%, 50%, 90%).  Here the whole
 *       result must be materialized, so `execZ` and `evalI` do the same work; we expect `execZ` to carry
 *       a small CONSTANT-FACTOR overhead (a virtual-cursor wrapper per visited node vs. a bulk Patricia
 *       merge).  Sharing is the independent variable; we report it as both the path-overlap knob and the
 *       realized trie-node counts.
 *
 *   (B) SELECTIVE combinations — an outer pruning operator (∩ / \) over a large inner sub-expression.
 *       This is where the zipper is ASYMPTOTICALLY better: it fuses the whole expression into one pruned
 *       traversal and never materializes the parts of the inner expression the outer op discards, whereas
 *       the eager interpreter builds the full inner trie first.  We grow the input and show `execZ` stays
 *       ~flat (∝ result) while `evalI` grows ∝ input.
 *
 *  Plus scale + correctness on the two guiding queries (datalog transitive closure, the aunt query),
 *  which the user noted are easy to make large.  Those are control-flow heavy, so `execZ` routes them
 *  through the evalI "call" — there `execZ ≈ evalI`; the tests gate cross-executor agreement at scale. */
class ZipperScaleBench extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(40, "min")

  def best(reps: Int)(body: => Unit): Double =
    body; var b = Double.MaxValue
    for _ <- 0 until reps do { val t = System.nanoTime(); body; val d = (System.nanoTime() - t) / 1e6; if d < b then b = d }
    b

  // ---- deep-trie generation with controlled path overlap ------------------------------------------
  /** `n` distinct random paths of length `depth` over a `K`-symbol alphabet (small K ⇒ real prefix
   *  sharing and branching, so subtree pruning is observable). */
  def distinctDeep(rng: java.util.Random, n: Int, depth: Int, K: Int): IndexedSeq[PathValue] =
    val s = scala.collection.mutable.LinkedHashSet.empty[PathValue]
    while s.size < n do s += PathValue(List.tabulate(depth)(_ => rng.nextInt(K).toString))
    s.toIndexedSeq
  /** Two path-sets of size `nEach` sharing exactly `share` of their paths (rest disjoint). */
  def sharedPair(rng: java.util.Random, nEach: Int, depth: Int, K: Int, share: Double): (Set[PathValue], Set[PathValue]) =
    val nShared = math.round(nEach * share).toInt; val nPriv = nEach - nShared
    val pool = distinctDeep(rng, nShared + 2 * nPriv, depth, K)
    val shared = pool.slice(0, nShared).toSet
    (shared ++ pool.slice(nShared, nShared + nPriv), shared ++ pool.slice(nShared + nPriv, nShared + 2 * nPriv))

  val a = SpaceMention("a"); val b = SpaceMention("b"); val c = SpaceMention("c")
  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  val noPc: PathContext = PathContextMap(Map.empty)

  // ===============================================================================================
  // (A) FLAT set-algebra on huge tries at 1% / 50% / 90% node sharing
  // ===============================================================================================
  test("huge tries: ∪ / ∩ / \\ at 1%, 50%, 90% sharing — execZ vs evalI (full materialization)".tag(SlowTag.Slow)) {
    val rng = new java.util.Random(11l); val nEach = 30000; val depth = 12; val K = 4; val reps = 4
    val ops = Seq[(String, (Space, Space) => Space)](("∪", Union(_, _)), ("∩", Intersection(_, _)), ("\\", Subtraction(_, _)))
    System.out.println(f"\n=== FLAT set-algebra on huge tries (|A|=|B|=$nEach paths, depth $depth, alphabet $K), full materialization ===")
    System.out.println(f"${"share"}%6s ${"op"}%3s | ${"nodesA"}%8s ${"nodesB"}%8s ${"sharedNd"}%9s | ${"|out|"}%8s ${"outNodes"}%9s | ${"evalI"}%8s ${"execZ"}%8s | ${"execZ/evalI"}%11s")
    for share <- Seq(0.01, 0.50, 0.90) do
      val (sa, sb) = sharedPair(rng, nEach, depth, K, share)
      val iA = ITrie.fromSpaceValue(SpaceValue(sa)); val iB = ITrie.fromSpaceValue(SpaceValue(sb))
      val sharedNodes = ITrie.intersection(iA, iB).nodeCount
      given ic: Map[SpaceMention, ITrie] = Map(a -> iA, b -> iB)
      for (sym, op) <- ops do
        val expr = op(Mention(a), Mention(b))
        val rI = evalI(expr); val rZ = execZ(expr)
        assertEquals(rZ, rI, s"execZ != evalI for $sym at share=$share")
        val tI = best(reps)(evalI(expr)); val tZ = best(reps)(execZ(expr))
        System.out.println(f"${(share * 100).toInt}%5d%% $sym%3s | ${iA.nodeCount}%8d ${iB.nodeCount}%8d $sharedNodes%9d | ${rI.size}%8d ${rI.nodeCount}%9d | $tI%7.2f $tZ%7.2f | ${tZ / tI}%10.2fx")
    System.out.println("")
  }

  // ===============================================================================================
  // (B) SELECTIVE combination — the asymptotic regime: a small selective ∩ over a growing ∪.
  //     (A ∪ B) ∩ C with C ⊆ A small & localized.  Result = C (size fixed); evalI builds all of A∪B,
  //     execZ fuses and only ever descends the C-selected region.  We grow |A|,|B| and watch the gap.
  // ===============================================================================================
  test("asymptotic: selective (A∪B)∩C over GROWING tries — execZ stays ∝ result, evalI grows ∝ input".tag(SlowTag.Slow)) {
    val rng = new java.util.Random(99l); val depth = 12; val K = 4; val reps = 4
    System.out.println(f"\n=== SELECTIVE (A∪B)∩C : C⊆A fixed-small & localized (prefix 0.0.·); grow |A|=|B| ===")
    System.out.println(f"${"|A|=|B|"}%8s | ${"nodesA∪B"}%9s ${"|C|"}%5s ${"|out|"}%6s | ${"evalI"}%8s ${"execZ"}%8s | ${"execZ/evalI"}%11s ${"speedup"}%8s")
    for nEach <- Seq(10000, 40000, 160000) do
      val (sa, sb) = sharedPair(rng, nEach, depth, K, 0.30)
      val iA = ITrie.fromSpaceValue(SpaceValue(sa)); val iB = ITrie.fromSpaceValue(SpaceValue(sb))
      // C: up to 400 of A's paths under the localized prefix 0.0 (so C ⊆ A∪B, result = C, |out| fixed).
      val cPaths = sa.iterator.filter(p => p.items.take(2) == List("0", "0")).take(400).toSet
      val iC = ITrie.fromSpaceValue(SpaceValue(cPaths))
      given ic: Map[SpaceMention, ITrie] = Map(a -> iA, b -> iB, c -> iC)
      val expr = Intersection(Union(Mention(a), Mention(b)), Mention(c))
      val rI = evalI(expr); val rZ = execZ(expr)
      assertEquals(rZ, rI, s"execZ != evalI for selective combo at n=$nEach"); assertEquals(rZ, iC, "result should equal C")
      val tI = best(reps)(evalI(expr)); val tZ = best(reps)(execZ(expr))
      System.out.println(f"$nEach%8d | ${ITrie.union(iA, iB).nodeCount}%9d ${cPaths.size}%5d ${rI.size}%6d | $tI%7.2f $tZ%7.2f | ${tZ / tI}%10.2fx ${tI / tZ}%6.1fx")
    System.out.println("")
  }

  // ===============================================================================================
  // (B2) COMPOSITION + COMBINATIONS of the basic ops at 1% / 50% / 90% sharing (fixed huge size).
  //      Composition (A∘small) and full-materialization combos carry the constant overhead; the
  //      selective combo (A∪B)∩C prunes and wins — and the win is robust across all sharing levels.
  // ===============================================================================================
  test("huge tries: composition & combinations at 1%, 50%, 90% sharing — execZ vs evalI".tag(SlowTag.Slow)) {
    val rng = new java.util.Random(7l); val nEach = 30000; val depth = 12; val K = 4; val reps = 4
    val small = SpaceValue(distinctDeep(new java.util.Random(1l), 8, 3, K).toSet) // tiny right operand for ∘
    System.out.println(f"\n=== COMPOSITION & COMBINATIONS on huge tries (|A|=|B|=$nEach), execZ vs evalI ===")
    System.out.println(f"${"share"}%6s ${"expr"}%14s | ${"|out|"}%8s ${"outNodes"}%9s | ${"evalI"}%8s ${"execZ"}%8s | ${"execZ/evalI"}%11s")
    for share <- Seq(0.01, 0.50, 0.90) do
      val (sa, sb) = sharedPair(rng, nEach, depth, K, share)
      val iA = ITrie.fromSpaceValue(SpaceValue(sa)); val iB = ITrie.fromSpaceValue(SpaceValue(sb))
      val cPaths = sa.iterator.filter(_.items.take(2) == List("0", "0")).take(400).toSet
      val iC = ITrie.fromSpaceValue(SpaceValue(cPaths)); val iSmall = ITrie.fromSpaceValue(small)
      given ic: Map[SpaceMention, ITrie] = Map(a -> iA, b -> iB, c -> iC, SpaceMention("d") -> iSmall)
      val d = Mention(SpaceMention("d"))
      val combos = Seq[(String, Space)](
        "A∘small"        -> Composition(Mention(a), d),
        "(A∪B)∩C [sel]"  -> Intersection(Union(Mention(a), Mention(b)), Mention(c)),
        "A\\(A∩B)"        -> Subtraction(Mention(a), Intersection(Mention(a), Mention(b))),
        "(A∩B)∪(A\\B)"    -> Union(Intersection(Mention(a), Mention(b)), Subtraction(Mention(a), Mention(b))))
      for (lbl, expr) <- combos do
        val rI = evalI(expr); val rZ = execZ(expr)
        assertEquals(rZ, rI, s"execZ != evalI for $lbl at share=$share")
        val tI = best(reps)(evalI(expr)); val tZ = best(reps)(execZ(expr))
        System.out.println(f"${(share * 100).toInt}%5d%% $lbl%14s | ${rI.size}%8d ${rI.nodeCount}%9d | $tI%7.2f $tZ%7.2f | ${tZ / tI}%10.2fx")
    System.out.println("")
  }

  // ===============================================================================================
  // (C) DATALOG transitive closure at scale (control-flow ⇒ execZ routes via the evalI call).
  // ===============================================================================================
  test("datalog transitive closure at scale: execZ == evalI == eval; timing".tag(SlowTag.Slow)) {
    val (ttop, tres) = lowerCalls(Routines.transitive_routine, Syntax.mod(Routines.transitive_routine))
    assert(tres.isEmpty)
    val reps = 4
    System.out.println("\n=== DATALOG transitive closure (chain of N) — execZ routes through the evalI \"call\" ===")
    System.out.println(f"${"N"}%5s ${"|edges|"}%8s ${"|TC|"}%8s | ${"eval"}%9s ${"evalI"}%9s ${"execZ"}%9s")
    for n <- Seq(32, 64, 96) do
      val edges = SpaceValue((0 until n - 1).map(i => PathValue(List(i.toString, (i + 1).toString))).toSet)
      val ei = ITrie.fromSpaceValue(edges)
      val rEval = eval(ttop)(using sc = SpaceContextMap(Map(SpaceMention("edges") -> edges)))
      val rI = evalI(ttop)(using ic = Map(SpaceMention("edges") -> ei)).toSpaceValue
      val rZ = execZ(ttop)(using ic = Map(SpaceMention("edges") -> ei)).toSpaceValue
      assertEquals(rI, rEval, s"evalI != eval N=$n"); assertEquals(rZ, rEval, s"execZ != eval N=$n")
      val tEval = if n <= 64 then best(reps)(eval(ttop)(using sc = SpaceContextMap(Map(SpaceMention("edges") -> edges)))) else Double.NaN
      val tI = best(reps)(evalI(ttop)(using ic = Map(SpaceMention("edges") -> ei)))
      val tZ = best(reps)(execZ(ttop)(using ic = Map(SpaceMention("edges") -> ei)))
      System.out.println(f"$n%5d ${edges.paths.size}%8d ${rEval.paths.size}%8d | $tEval%8.2f $tI%8.2f $tZ%8.2f")
    System.out.println("")
  }

  // ===============================================================================================
  // (D) AUNT query at scale over a large synthetic family (control-flow + set-algebra).
  // ===============================================================================================
  test("aunt query at scale on a large synthetic family: execZ == evalI == eval".tag(SlowTag.Slow)) {
    val sym = (x: Int) => "p" + x
    /** Synthesize a family of N people: two parents from the previous generation, ~40% female. */
    def family(rng: java.util.Random, N: Int, genSize: Int): (SpaceValue, SpaceValue) =
      val paths = scala.collection.mutable.Set.empty[PathValue]
      for child <- genSize until N do
        val g = child / genSize
        val p1 = (g - 1) * genSize + rng.nextInt(genSize); val p2 = (g - 1) * genSize + rng.nextInt(genSize)
        for par <- Set(p1, p2) do
          paths += PathValue(List("parent", sym(child), sym(par)))   // child -> parent
          paths += PathValue(List("child", sym(par), sym(child)))    // parent -> child
      for person <- 0 until N if rng.nextInt(5) < 2 do paths += PathValue(List("female", sym(person)))
      (SpaceValue(paths.toSet), SpaceValue((0 until N).map(p => PathValue(List(sym(p)))).toSet))
    val defs = Syntax.mod(Routines.aunt_query_routine)
    val reps = 3
    System.out.println("\n=== AUNT query on a synthetic genealogy (execZ routes control-flow via the evalI \"call\") ===")
    System.out.println(f"${"people"}%7s ${"|family|"}%9s ${"|aunts|"}%8s | ${"eval"}%9s ${"evalI"}%9s ${"execZ"}%9s")
    for (np, gen) <- Seq((120, 20), (600, 60)) do
      val (fam, ppl) = family(new java.util.Random(7l + np), np, gen)
      val call = Space.Call(RoutinePtr("aunts"), Vector(), Vector(Space.Literal(fam), Space.Mention(SpaceMention("people"))))
      val sc0 = SpaceContextMap(Map(SpaceMention("people") -> ppl))
      val ic0 = Map(SpaceMention("people") -> ITrie.fromSpaceValue(ppl))
      val rEval = eval(call)(using sc = sc0, rc = defs)
      val rI = evalI(call)(using ic = ic0, rc = defs).toSpaceValue
      val rZ = execZ(call)(using ic = ic0, rc = defs).toSpaceValue
      assertEquals(rI, rEval, s"evalI != eval N=$np"); assertEquals(rZ, rEval, s"execZ != eval N=$np")
      val tEval = best(reps)(eval(call)(using sc = sc0, rc = defs))
      val tI = best(reps)(evalI(call)(using ic = ic0, rc = defs))
      val tZ = best(reps)(execZ(call)(using ic = ic0, rc = defs))
      System.out.println(f"$np%7d ${fam.paths.size}%9d ${rEval.paths.size}%8d | $tEval%8.2f $tI%8.2f $tZ%8.2f")
    System.out.println("")
  }

  // ===============================================================================================
  // (D2) AUNT query on the REAL royal92 genealogy (~3000 people, ~11.6k facts) — the production fixture.
  // ===============================================================================================
  test("aunt query on the REAL royal92 genealogy: execZ vs eval / evalI / execT(opt)".tag(SlowTag.Slow)) {
    val candidates = Seq(sys.props.getOrElse("royal92.metta", "royal92_simple.metta"),
                         "royal92_simple.metta", "/Users/michaelpolyntsov/Zippy/royal92_simple.metta")
    Loaders.resolve(candidates*).flatMap(f => Loaders.mettaFamily(f.getPath)) match
      case None => System.out.println("\n(royal92_simple.metta not found — aunt(royal92) execZ benchmark skipped)\n")
      case Some(r92) =>
        val fam = r92.family; val ppl = r92.people
        val iFam = ITrie.fromSpaceValue(fam); val iPpl = ITrie.fromSpaceValue(ppl)
        val body = Routines.aunt_query_routine.body
        val sc0 = SpaceContextMap(Map(SpaceMention("family") -> fam, SpaceMention("people") -> ppl))
        val ic0 = Map(SpaceMention("family") -> iFam, SpaceMention("people") -> iPpl)
        val (top, _) = lowerCalls(Routines.aunt_query_routine, PartialFunction.empty)
        val gOpt = optimize(transpile(Routine(RoutinePtr("aunts"), Vector.empty, Routines.aunt_query_routine.mentions, top)))
        val mt = Map("family" -> iFam, "people" -> iPpl)
        val rEval = eval(body)(using sc = sc0); val rI = evalI(body)(using ic = ic0).toSpaceValue
        val rZ = execZ(body)(using ic = ic0).toSpaceValue; val rT = runGraphT(gOpt, mentions = mt).toSpaceValue
        assertEquals(rI, rEval, "evalI != eval"); assertEquals(rZ, rEval, "execZ != eval"); assertEquals(rT, rEval, "execT != eval")
        val reps = 7
        val tEval = best(reps)(eval(body)(using sc = sc0)); val tI = best(reps)(evalI(body)(using ic = ic0))
        val tT = best(reps)(runGraphT(gOpt, mentions = mt)); val tZ = best(reps)(execZ(body)(using ic = ic0))
        System.out.println(f"\n=== AUNT on REAL royal92 (people=${ppl.paths.size}, |family|=${fam.paths.size} facts, |aunts|=${rEval.paths.size}) ===")
        System.out.println(f"${"eval"}%9s ${"evalI"}%9s ${"execT(opt)"}%11s ${"execZ"}%9s | ${"execZ/evalI"}%11s ${"execZ/eval"}%10s")
        System.out.println(f"$tEval%8.2f $tI%8.2f $tT%10.2f $tZ%8.2f | ${tZ / tI}%10.2fx ${tZ / tEval}%9.2fx\n")
  }

  // ===============================================================================================
  // (D3) NATIVE Range: the specialized ordered trie-slice vs the old path-materialization round-trip.
  // ===============================================================================================
  test("native ITrie.range vs path-materialization round-trip on a huge trie".tag(SlowTag.Slow)) {
    val rng = new java.util.Random(31l); val reps = 6
    val (sa, _) = sharedPair(rng, 120000, 12, 4, 0.0)
    val t = ITrie.fromSpaceValue(SpaceValue(sa)); val size = t.size
    def oldWay(lo: Int, hi: Int): ITrie = ITrie.fromPaths(sliceRange(ITrie.toPaths(t), lo, hi))
    System.out.println(f"\n=== Range over a $size-path trie: native ITrie.range vs fromPaths(sliceRange(toPaths)) ===")
    System.out.println(f"${"slice"}%16s | ${"|out|"}%7s | ${"old(materialize)"}%17s ${"native"}%8s | ${"speedup"}%8s")
    for (lbl, lo, hi) <- Seq(("front [1,100)", 1, 100), ("identity [0,0]", 0, 0), ("tail [-100,0]", -100, 0)) do
      val rN = ITrie.range(t, lo, hi); assertEquals(rN, oldWay(lo, hi), s"native range != old for $lbl")
      val tOld = best(reps)(oldWay(lo, hi)); val tNew = best(reps)(ITrie.range(t, lo, hi))
      System.out.println(f"$lbl%16s | ${rN.size}%7d | $tOld%16.2f $tNew%7.3f | ${tOld / math.max(tNew, 1e-3)}%6.1fx")
    System.out.println("")
  }

  // ===============================================================================================
  // (E) REFERENTIAL-IDENTITY short-circuit: x∩x=x, x∪x=x, x\x=∅ resolve in O(1) (no branch re-descended),
  //     and a shared sub-expression makes a huge op collapse instantly.
  // ===============================================================================================
  test("referential-identity short-circuit: x∩x / x∪x / x\\x are correct and instant".tag(SlowTag.Slow)) {
    val rng = new java.util.Random(5l)
    val (sa, _) = sharedPair(rng, 80000, 12, 4, 0.0)
    val iA = ITrie.fromSpaceValue(SpaceValue(sa))
    given ic: Map[SpaceMention, ITrie] = Map(a -> iA)
    // same Mention on both sides ⇒ transpileZ yields two Lit cursors over the SAME trie object ⇒ short-circuit.
    assertEquals(execZ(Intersection(Mention(a), Mention(a))), iA, "x∩x")
    assertEquals(execZ(Union(Mention(a), Mention(a))), iA, "x∪x")
    assertEquals(execZ(Subtraction(Mention(a), Mention(a))), ITrie.empty, "x\\x")
    // a shared sub-expression inside a bigger op: (A∪A)∩A must equal A and cost ~nothing (vs building A∪A).
    val expr = Intersection(Union(Mention(a), Mention(a)), Mention(a))
    assertEquals(execZ(expr), iA, "(A∪A)∩A")
    val reps = 6
    val tZ = best(reps)(execZ(Subtraction(Mention(a), Mention(a))))
    val tBuild = best(reps)(evalI(Subtraction(Mention(a), Mention(a))))
    System.out.println(f"\n=== identity short-circuit on an 80000-path trie: A\\A — execZ ${tZ}%.4f ms (O(1)) vs evalI ${tBuild}%.2f ms ===\n")
    assert(tZ < 0.05, s"x\\x should be ~instant, was $tZ ms")
  }

  // ===============================================================================================
  // (F) THREE-WAY intersection A∩B∩C — fused single traversal vs eager PAIRWISE (build A∩B, then ∩C).
  //     A,B overlap heavily (A∩B large ∝ N) but C diverges (A∩B∩C small & fixed).  The fused zipper
  //     never materializes the large A∩B intermediate — only the triple-common region — so as the
  //     pairwise intermediate grows the gap widens: asymptotically faster than pairwise.
  //     Sparse high-alphabet tries so divergence (and thus pruning) kicks in near the root.
  // ===============================================================================================
  test("three-way A∩B∩C: fused execZ beats eager pairwise as the A∩B intermediate grows".tag(SlowTag.Slow)) {
    val depth = 8; val K = 64; val reps = 5; val nS = 300; val nCOnly = 200; val pre = List("0", "0")
    def distinctUnder(rng: java.util.Random, n: Int): IndexedSeq[PathValue] =     // localized under `pre`
      val s = scala.collection.mutable.LinkedHashSet.empty[PathValue]
      while s.size < n do s += PathValue(pre ++ List.tabulate(depth - pre.size)(_ => rng.nextInt(K).toString))
      s.toIndexedSeq
    def distinctOff(rng: java.util.Random, n: Int): IndexedSeq[PathValue] =       // anywhere NOT under `pre`
      val s = scala.collection.mutable.LinkedHashSet.empty[PathValue]
      while s.size < n do
        val p = PathValue(List.tabulate(depth)(_ => rng.nextInt(K).toString))
        if p.items.take(2) != pre then s += p
      s.toIndexedSeq
    /** S (triple-common) and cOnly are LOCALIZED under `pre` and fixed-small; c12 (the A∩B-only mass,
     *  which the eager intermediate must build) lives OFF the prefix and grows.  So C lives entirely in
     *  a corner ⇒ the fused outer ∩ prunes to that corner at the root and never descends the c12 mass. */
    def threeway(rng: java.util.Random, nc12: Int): (Set[PathValue], Set[PathValue], Set[PathValue]) =
      val under = distinctUnder(rng, nS + nCOnly); val s = under.slice(0, nS).toSet; val cOnly = under.slice(nS, nS + nCOnly).toSet
      val off = distinctOff(rng, 3 * nc12); val c12 = off.slice(0, nc12).toSet
      (s ++ c12 ++ off.slice(nc12, 2 * nc12).toSet, s ++ c12 ++ off.slice(2 * nc12, 3 * nc12).toSet, s ++ cOnly)
    System.out.println(f"\n=== THREE-WAY A∩B∩C : C localized & fixed-small, A∩B (∝N, off-prefix) grows; A∩B∩C = $nS fixed ===")
    System.out.println(f"${"|c12|"}%7s | ${"|A∩B|"}%7s ${"|A∩B∩C|"}%8s | ${"pairwise"}%9s ${"execZ"}%8s | ${"execZ/pair"}%10s ${"speedup"}%8s")
    for nc12 <- Seq(2000, 16000, 64000) do
      val (sa, sb, scc) = threeway(new java.util.Random(3l + nc12), nc12)
      val iA = ITrie.fromSpaceValue(SpaceValue(sa)); val iB = ITrie.fromSpaceValue(SpaceValue(sb)); val iC = ITrie.fromSpaceValue(SpaceValue(scc))
      given ic: Map[SpaceMention, ITrie] = Map(a -> iA, b -> iB, c -> iC)
      val expr = Intersection(Intersection(Mention(a), Mention(b)), Mention(c))
      val rZ = execZ(expr); val pair = ITrie.intersection(ITrie.intersection(iA, iB), iC)
      assertEquals(rZ, pair, s"execZ != pairwise at nc12=$nc12")
      val ab = ITrie.intersection(iA, iB)
      val tPair = best(reps) { ITrie.intersection(ITrie.intersection(iA, iB), iC) }
      val tZ = best(reps)(execZ(expr))
      System.out.println(f"$nc12%7d | ${ab.size}%7d ${rZ.size}%8d | $tPair%8.2f $tZ%7.2f | ${tZ / tPair}%9.2fx ${tPair / tZ}%6.1fx")
    System.out.println("")
  }
end ZipperScaleBench
