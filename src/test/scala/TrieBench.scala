package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Benchmarks: reference Set evaluator `eval` vs trie evaluator `evalT`, with and without the
 *  supercompiler pass, scaled up across all six domains.  Each scenario asserts the two
 *  evaluators agree, then reports wall-clock (best-of-N after warmup).  Results are appended to
 *  docs/BENCHMARKS.md.  Tagged Slow; run with `sbt 'testOnly morkl.TrieBench'`. */
class TrieBench extends FunSuite:
  import Space.*

  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  val out = new StringBuilder
  def emit(line: String): Unit = { out.append(line).append('\n'); Loaders.note(line) }

  /** best-of-`reps` milliseconds after `warm` warmup runs */
  def bench(warm: Int, reps: Int)(f: => Any): Double =
    for _ <- 0 until warm do f
    var best = Double.MaxValue
    for _ <- 0 until reps do
      val t0 = System.nanoTime(); f; val dt = (System.nanoTime() - t0) / 1e6
      if dt < best then best = dt
    best

  // eval = reference Set; evalT = TreeMap[PathItem] trie; evalI = interned IntMap trie.
  case class Row(domain: String, scale: String, refMs: Double, trieMs: Double, iMs: Double, note: String):
    def suEval: Double = if iMs <= 0 then 0 else refMs / iMs   // evalI vs reference
    def suTrie: Double = if iMs <= 0 || trieMs <= 0 then 0 else trieMs / iMs  // evalI (IntMap) vs evalT (TreeMap)
    def line: String = f"| $domain%-16s | $scale%-20s | $refMs%9.1f | $trieMs%9.1f | $iMs%9.1f | ${suEval}%7.1fx | ${suTrie}%6.1fx | $note |"
  val rows = scala.collection.mutable.ArrayBuffer.empty[Row]

  /** time eval (Set) vs evalT (TreeMap trie) vs evalI (interned IntMap trie); assert all agree.
   *  Data via `tc`/`ic` is RESIDENT (pre-built), the realistic backing-store comparison. */
  def scenario(domain: String, scale: String, space: Space,
               tc: Map[SpaceMention, Trie] = Map.empty, rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
               note: String = "", warm: Int = 1, reps: Int = 3): Unit =
    val sc = SpaceContextMap(tc.map((k, v) => k -> v.toSpaceValue))
    val ic = tc.map((k, v) => k -> ITrie.fromSpaceValue(v.toSpaceValue))
    val refSV = eval(space)(using PathContextMap(Map.empty), sc, rc)
    assertEquals(evalT(space)(using PathContextMap(Map.empty), tc, rc).toSpaceValue, refSV, s"$domain/$scale: evalT disagrees")
    assertEquals(evalI(space)(using PathContextMap(Map.empty), ic, rc).toSpaceValue, refSV, s"$domain/$scale: evalI disagrees")
    val refMs = bench(warm, reps)(eval(space)(using PathContextMap(Map.empty), sc, rc))
    val trieMs = bench(warm, reps)(evalT(space)(using PathContextMap(Map.empty), tc, rc))
    val iMs = bench(warm, reps)(evalI(space)(using PathContextMap(Map.empty), ic, rc))
    val r = Row(domain, scale, refMs, trieMs, iMs, note)
    rows += r; emit(r.line)

  // ---- data generators ------------------------------------------------------
  def chainEdges(n: Int): SpaceValue =
    SpaceValue((0 until n).map(i => PathValue(List(i.toString, (i + 1).toString))).toSet)
  def randEdges(nodes: Int, edges: Int, seed: Int): SpaceValue =
    val r = new scala.util.Random(seed)
    SpaceValue((0 until edges).map(_ => PathValue(List(r.nextInt(nodes).toString, r.nextInt(nodes).toString))).toSet)
  def genFamily(n: Int, seed: Int): (SpaceValue, SpaceValue) =
    val r = new scala.util.Random(seed)
    val ps = scala.collection.mutable.Set.empty[PathValue]
    def sym(xs: String*) = PathValue(xs.toList)
    for i <- 1 until n do
      val par = r.nextInt(i)
      ps += sym("parent", par.toString, i.toString); ps += sym("child", i.toString, par.toString)
    for i <- 0 until n do { if r.nextBoolean() then ps += sym("female", i.toString) else ps += sym("male", i.toString); ps += sym("person", i.toString) }
    (SpaceValue(ps.toSet), SpaceValue((0 until n).map(i => sym(i.toString)).toSet))
  def randGrid(w: Int, density: Int, seed: Int): Set[(Int, Int)] =
    val r = new scala.util.Random(seed)
    (for x <- 0 until w; y <- 0 until w if r.nextInt(100) < density yield (x, y)).toSet

  test("BENCHMARKS: eval (Set) vs evalT (TreeMap trie) vs evalI (interned IntMap trie)".tag(SlowTag.Slow)) {
    // the heading and the provenance block are written by `BenchmarkReport`; `out` carries the BODY
    val reportSlug = "executor-scaling"
    val reportTitle = "Executor scaling: eval vs evalT vs evalI"
    val reportExtras = Seq(
      "timing" -> "best-of-N wall clock after warmup (see the per-row `warm`/`reps` in the source)",
      "interner" -> "WARM — `Interner` and the literal memo carry every id from earlier rows of the same run",
      "seed" -> "fixed per benchmark; the workloads are deterministic")
    emit("| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |")
    emit("|---|---|---:|---:|---:|---:|---:|---|")

    // 1. DATALOG transitive closure on chains (heavy composition/iteration fixpoint)
    for n <- Seq(16, 32, 64, 128) do
      val edges = chainEdges(n)
      val defs = Syntax.mod(Routines.transitive_routine)
      val call = Space.Call(RoutinePtr("transitive"), Vector(), Vector(Literal(edges)))
      scenario("datalog-TC", s"chain n=$n (|TC|=${n * (n + 1) / 2})", call, rc = defs)

    // 2. GRAPH/AUNT on synthetic families (iteration + restriction + intersection)
    for n <- Seq(150, 400, 800, 1600) do
      val (fam, ppl) = genFamily(n, n)
      val defs = Syntax.mod(Routines.aunt_query_routine)
      val call = Space.Call(RoutinePtr("aunts"), Vector(), Vector(Literal(fam), Mention(SpaceMention("people"))))
      val tc = Map(SpaceMention("people") -> Trie.fromSpaceValue(ppl))
      scenario("aunt-query", s"family n=$n", call, tc = tc, rc = defs,
        warm = if n >= 800 then 0 else 1, reps = if n >= 800 then 2 else 3)

    // 3. GAME OF LIFE: 2 steps on random grids of increasing size (pure: number relations + Range)
    for w <- Seq(16, 24, 32) do
      val live = randGrid(w, 32, w)
      val two = Space.Call(RoutinePtr("nextStep"), Vector(), Vector(
        Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Literal(GoL.field(live))))))
      scenario("game-of-life", s"${w}x$w 2 steps (${live.size} live)", two,
        rc = GoL.rulesFor(live ++ GoL.step(live) ++ GoL.steps(live, 2)).defs)

    // 4. TEMPERATURE: trie-prefix range + bucket queries; data RESIDENT (trie vs set), since a
    // spatial index is a backing store, not rebuilt per query — the trie's restriction is a
    // guided descent vs the reference's full scan.
    for bits <- Seq(10, 12, 14) do
      val r = new scala.util.Random(bits)
      val cells = (for i <- 0 until (1 << bits) yield
        PathValue(NOAA.bits(i, bits) :+ (Vector("VC", "C", "N", "W", "VW")(r.nextInt(5))))).toSet
      val world = Mention(SpaceMention("world"))
      val tc = Map(SpaceMention("world") -> Trie.fromSpaceValue(SpaceValue(cells)))
      val q = Union(Restriction(world, Literal(NOAA.interval(0, (1 << bits) / 8, bits))), Restriction(world, ss"VW"))
      scenario("temperature", s"${1 << bits} cells (resident)", q, tc = tc)

    // 5. SLIDING PUZZLE (PURE — no grounded functions). BFS bounded to a fixed depth so eval and
    // evalT both finish; the work is entirely in the algebra (superpose/collapse/moves).
    def boundedSpace(p: Sliding.Puzzle, depth: Int): Space =
      var acc: Space = Singleton(Path.Constant(p.initial)); var fr: Space = acc
      for _ <- 0 until depth do { fr = p.expandStep(fr); acc = Union(acc, fr) }
      acc
    for (r, c, depth) <- Seq((2, 2, 6), (3, 3, 4)) do
      val p = Sliding.puzzle(r, c)
      scenario("sliding-puzzle", s"${r}x$c depth $depth (pure)", boundedSpace(p, depth), rc = p.defs, warm = 0, reps = 2)

    // 6. N-QUEENS (PURE — no grounded functions). place(n,n) over precomputed literal tables.
    for n <- Seq(6, 7, 8) do
      val b = NQueens.board(n)
      scenario("n-queens", s"n=$n (${NQueens.known(n)} sols, pure)", b.program, rc = b.defs, warm = 0, reps = 2)

    // 7. JOIN-ALL / MEET-ALL microbenchmark on the INTERNED IntMap trie — n-ary ops vs pairwise
    // reduce. Columns: eval=reduce, evalI=n-ary, evalI/eval=speedup of the n-ary op.
    for (k, m) <- Seq((200, 200), (800, 300)) do
      val r = new scala.util.Random(k)
      val branches = (0 until k).map(b => ITrie.fromPaths((0 until m).map(i =>
        PathValue(List(b.toString, r.nextInt(m).toString))))).toVector
      assertEquals(ITrie.joinAll(branches), branches.reduce(ITrie.union))
      rows += Row("join-all", s"k=$k m=$m", bench(2, 5)(branches.reduce(ITrie.union)), -1.0, bench(2, 5)(ITrie.joinAll(branches)),
        "reduce(union) vs joinAll"); emit(rows.last.line)
    for (k, big) <- Seq((40, 400), (120, 600)) do
      val r = new scala.util.Random(k * 31)
      val core = ITrie.fromPaths((0 until big).map(i => PathValue(List("c", i.toString))))
      val larges = (0 until k - 1).map(_ => ITrie.union(core,
        ITrie.fromPaths((0 until 20).map(_ => PathValue(List("n", r.nextInt(big).toString)))))).toVector
      val tiny = ITrie.fromPaths(Vector(PathValue(List("c", "0"))))
      val mb = larges :+ tiny // tiny LAST: worst case for left-to-right reduce
      assertEquals(ITrie.meetAll(mb), mb.reduce(ITrie.intersection))
      rows += Row("meet-all", s"k=$k core=$big +tiny", bench(2, 5)(mb.reduce(ITrie.intersection)), -1.0, bench(2, 5)(ITrie.meetAll(mb)),
        "reduce(meet) vs meetAll"); emit(rows.last.line)

    // summary: geometric means of evalI/eval (vs reference) and evalI/evalT (IntMap vs TreeMap)
    val ex = rows.filterNot(r => Seq("join-all", "meet-all").contains(r.domain))
    def geomean(xs: Iterable[Double]) = math.exp(xs.filter(_ > 0).map(math.log).sum / xs.count(_ > 0))
    emit(f"\nGeometric-mean evalI speedup over the six example domains: ${geomean(ex.map(_.suEval))}%.1fx vs the")
    emit(f"reference Set, and ${geomean(ex.map(_.suTrie))}%.1fx vs the TreeMap trie (evalT). All six")
    emit("domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem")
    emit("is touched during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.\n")
    val avgSpeedup = geomean(ex.map(_.suEval))
    // REPLACE this section, never append one — see the note in GraphBench.  `BenchmarkReport` writes
    // the heading and the provenance block; `out` carries the body.
    BenchmarkReport.write(new java.io.File(Loaders.repoRoot, "docs/BENCHMARKS.md"),
                          reportSlug, reportTitle, out.toString, reportExtras)
    assert(avgSpeedup > 1.0, f"expected trie to be faster on average, got ${avgSpeedup}%.2fx")
  }
end TrieBench
