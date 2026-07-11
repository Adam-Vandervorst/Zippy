import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Performance of recursion lowering (design_plan §5.5/§7.2): BEFORE the lowering a recursive program
 *  is a residual of `Call`s — the op-graph backend cannot compile a recursive Call, and naive
 *  interpretation of mutual recursion DIVERGES (e.g. f(∅)↔g(∅) loops forever).  AFTER the lowering it
 *  is a first-class `Space.Fixpoint` that (a) the interpreters evaluate by a converging fixpoint loop
 *  and (b) the op-graph compiles to a native `execT` Fixpoint subgraph over interned tries.
 *
 *  We measure, for the SAME lowered program, the three execution strategies — `eval` (Set reference),
 *  `evalI` (interned-trie interpreter), and `execT` (compiled op-graph, the post-lowering fast path) —
 *  across increasing input sizes, gating each row on all-executor agreement.  We also show the BEFORE
 *  state: interpreting the ORIGINAL recursive Calls, which diverges for mutual recursion. */
class RecursionLoweringBench extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def iT(sv: SpaceValue): ITrie = ITrie.fromSpaceValue(sv)
  def fixCount(s: Space): Int = collect(s)({ case f: Space.Fixpoint => f })._1.size
  def median(reps: Int)(body: => Unit): Double =
    for _ <- 0 until 2 do body                       // warmup to steady state
    val ts = (0 until reps).map { _ => val t = System.nanoTime(); body; (System.nanoTime() - t) / 1e6 }.sorted
    ts(ts.length / 2)
  /** run `f` on a daemon thread, returning Some(ms) if it finished within `ms`, else None (diverged). */
  def withTimeout(ms: Long)(f: => Unit): Option[Double] =
    @volatile var dur: Option[Double] = None
    val th = new Thread(() => { val t = System.nanoTime(); try { f; dur = Some((System.nanoTime() - t) / 1e6) } catch { case _: Throwable => () } })
    th.setDaemon(true); th.start(); th.join(ms)
    dur

  test("recursion lowering perf: interpret-the-Calls (before) vs lowered Fixpoint -> execT (after)".tag(SlowTag.Slow)) {
    val reps = 5

    // ===== 1) arg-changing MUTUAL recursion: f(x)=x ∪ g(x("h")), g(x)=x ∪ f(x) ⇒ f(x)=⋃ₖ x("h"ᵏ) =====
    val f = R"f"(S"x") := S"x" \/ R"g"(S"x"("h"))
    val g = R"g"(S"x") := S"x" \/ R"f"(S"x")
    val defs = Syntax.mod(f, g)
    val (mtop, mres) = lowerCalls(f, defs)
    assert(mres.isEmpty && fixCount(mtop) >= 1, s"mutual recursion must lower:\n${mtop.show}")
    val mGraph = optimize(transpile(Routine(RoutinePtr("main"), Vector.empty, Vector(SpaceMention("x")), mtop)))
    System.out.println("\n=== arg-changing MUTUAL recursion  f(x)=x ∪ g(x(\"h\")), g(x)=x ∪ f(x) ===")
    System.out.println("(BEFORE = interpret original Calls; AFTER = lowered Fixpoint)")
    System.out.println(f"${"depth"}%5s ${"width"}%5s ${"|out|"}%7s | ${"eval(low)"}%10s ${"evalI(low)"}%11s ${"execT(low)"}%11s ${"execZ(low)"}%11s | ${"BEFORE (orig Calls)"}%20s")
    for (d, m) <- Seq((10, 40), (20, 40), (40, 40), (20, 160)) do
      val x = SpaceValue((0 until m).map(i => PathValue(List.fill(d)(PathItem.Symbol("h")) :+ PathItem.Symbol("t" + i))).toSet)
      val xi = iT(x)
      val rEval = eval(mtop)(using sc = SpaceContextMap(Map(SpaceMention("x") -> x)))
      val rI = evalI(mtop)(using ic = Map(SpaceMention("x") -> xi)).toSpaceValue
      val rT = runGraphT(mGraph, mentions = Map("x" -> xi)).toSpaceValue
      val rZ = execZ(mtop)(using ic = Map(SpaceMention("x") -> xi)).toSpaceValue
      assertEquals(rI, rEval, s"evalI != eval d=$d"); assertEquals(rT, rEval, s"execT != eval d=$d"); assertEquals(rZ, rEval, s"execZ != eval d=$d")
      val tEval = median(reps)(eval(mtop)(using sc = SpaceContextMap(Map(SpaceMention("x") -> x))))
      val tI = median(reps)(evalI(mtop)(using ic = Map(SpaceMention("x") -> xi)))
      val tT = median(reps)(runGraphT(mGraph, mentions = Map("x" -> xi)))
      val tZ = median(reps)(execZ(mtop)(using ic = Map(SpaceMention("x") -> xi)))
      val before = if d == 10 && m == 40 then withTimeout(1500)(evalI(f.body)(using ic = Map(SpaceMention("x") -> xi), rc = defs)) else None
      val beforeStr = if d == 10 && m == 40 then before.map(b => f"$b%.1f ms").getOrElse("DIVERGES") else "(skipped)"
      System.out.println(f"$d%5d $m%5d ${rEval.paths.size}%7d | $tEval%9.2f  $tI%10.2f  $tT%10.2f  $tZ%10.2f | $beforeStr%20s")

    // ===== 2) SINGLE self-recursion: transitive closure over a chain of N nodes =====
    val (ttop, tres) = lowerCalls(Routines.transitive_routine, Syntax.mod(Routines.transitive_routine))
    assert(tres.isEmpty && fixCount(ttop) >= 1, s"transitive must lower:\n${ttop.show}")
    val tGraph = optimize(transpile(Routine(RoutinePtr("tc"), Vector.empty, Vector(SpaceMention("edges")), ttop)))
    System.out.println("\n=== SINGLE self-recursion  transitive closure (chain of N nodes) ===")
    System.out.println(f"${"N"}%5s ${"|edges|"}%8s ${"|TC|"}%7s | ${"eval(low)"}%10s ${"evalI(low)"}%11s ${"execT(low)"}%11s ${"execZ(low)"}%11s")
    for n <- Seq(8, 16, 32, 48) do
      val edges = SpaceValue((0 until n - 1).map(i => PathValue(List(PathItem.Symbol(i.toString), PathItem.Symbol((i + 1).toString)))).toSet)
      val ei = iT(edges)
      val rEval = eval(ttop)(using sc = SpaceContextMap(Map(SpaceMention("edges") -> edges)))
      val rI = evalI(ttop)(using ic = Map(SpaceMention("edges") -> ei)).toSpaceValue
      val rT = runGraphT(tGraph, mentions = Map("edges" -> ei)).toSpaceValue
      val rZ = execZ(ttop)(using ic = Map(SpaceMention("edges") -> ei)).toSpaceValue
      assertEquals(rI, rEval, s"evalI != eval N=$n"); assertEquals(rT, rEval, s"execT != eval N=$n"); assertEquals(rZ, rEval, s"execZ != eval N=$n")
      val tEval = median(reps)(eval(ttop)(using sc = SpaceContextMap(Map(SpaceMention("edges") -> edges))))
      val tI = median(reps)(evalI(ttop)(using ic = Map(SpaceMention("edges") -> ei)))
      val tT = median(reps)(runGraphT(tGraph, mentions = Map("edges" -> ei)))
      val tZ = median(reps)(execZ(ttop)(using ic = Map(SpaceMention("edges") -> ei)))
      System.out.println(f"$n%5d ${edges.paths.size}%8d ${rEval.paths.size}%7d | $tEval%9.2f  $tI%10.2f  $tT%10.2f  $tZ%10.2f")
    System.out.println("")
  }

  test("long benchmark: deep LOCAL-algebra over large tries (execZ fusion: no intermediate tries)".tag(SlowTag.Slow)) {
    val reps = 5
    val rng = new java.util.Random(20260627L); val A = SpaceFuzzer.alphabet
    def bigSV(npaths: Int, depth: Int): SpaceValue =
      SpaceValue((0 until npaths).map(_ => PathValue(List.fill(depth)(A(rng.nextInt(A.length))))).toSet)
    val ops = Vector[(Space, Space) => Space](Space.Union(_, _), Space.Intersection(_, _), Space.Subtraction(_, _))
    System.out.println("\n=== deep LOCAL-algebra: a depth-N nesting of ∪/∩/\\ over large tries (the zipper FUSES; no intermediate materialization) ===")
    System.out.println(f"${"depth"}%6s ${"trie"}%6s ${"|out|"}%7s | ${"eval"}%8s ${"evalI"}%8s ${"execT(opt)"}%11s ${"execZ"}%8s | ${"execZ/evalI"}%11s ${"execZ/eval"}%10s")
    for (n, sz, d) <- Seq((12, 1200, 4), (24, 2000, 5), (40, 3000, 5)) do
      val lits = (0 until n).map(_ => Space.Literal(bigSV(sz, d))).toVector
      val expr = lits.tail.zipWithIndex.foldLeft(lits.head: Space) { case (acc, (l, i)) => ops(i % ops.length)(acc, l) }
      val g = optimize(transpile(Routine(RoutinePtr("m"), Vector.empty, Vector.empty, expr)))
      val ref = eval(expr)
      assertEquals(execZ(expr).toSpaceValue, ref, s"execZ != eval (depth=$n)")
      assertEquals(runGraphT(g).toSpaceValue, ref, s"execT != eval (depth=$n)")
      val tEval = median(reps)(eval(expr))
      val tI = median(reps)(evalI(expr))
      val tT = median(reps)(runGraphT(g))
      val tZ = median(reps)(execZ(expr))
      System.out.println(f"$n%6d $sz%6d ${ref.paths.size}%7d | $tEval%7.2f $tI%8.2f $tT%10.2f $tZ%7.2f | ${tZ / tI}%10.2fx ${tZ / tEval}%9.2fx")
    System.out.println("")
  }
end RecursionLoweringBench
