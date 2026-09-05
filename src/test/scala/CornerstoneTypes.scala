package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ABSTRACT INTERPRETATION OF THE SIX CORNERSTONES (aunt / datalog-sn / gol / puzzle15 /
 *  temperature / nqueens) — the same programs the equivalence pipeline certifies, run through all
 *  three analyses side by side with the ground truth:
 *
 *    size   tier-1 `Lower.sizeBounds`   vs tier-2 `SizeZ3`
 *    length tier-1 `Lower.lenBounds`    vs tier-2 `LenZ3`
 *    spatial `SpatialTypes.infer` — the per-length count classes, plus its two projections
 *
 *  Soundness and dominance are ASSERTED on every row (this is a gate, not just a printout); the
 *  numbers are printed as a table so the analyses can be compared per cornerstone. */
class CornerstoneTypes extends FunSuite:
  import Space.*
  import Lower.{LenBounds, SizeBounds}
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  val SINF = SizeBounds.INF
  val LINF = LenBounds.INF
  def fs(b: SizeBounds): String = s"[${b.lo}, ${if b.hi == SINF then "inf" else b.hi}]"
  def fl(b: LenBounds): String = if b.isEmpty then "EMPTY" else s"[${b.lo}, ${if b.hi == LINF then "inf" else b.hi}]"
  def histogram(v: SpaceValue): Map[Long, Long] =
    v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap

  /** run every analysis on one cornerstone, assert soundness + dominance, print the row.
   *  `expanded = true` analyses the STAGE-0 EXPANSION (`EquivPipeline.expand`: mentions resolved to
   *  literals, control flow unfolded to ground local algebra — the same artifact the proof pipeline
   *  certifies), gated by `eval(expanded) == eval(prog)`.  The un-expanded form is reported too:
   *  it is genuinely open (inputs live in the SpaceContext, four cornerstones have recursive Calls),
   *  so the analyses correctly answer "unknown" there — that contrast is the point. */
  def report(name: String, prog0: Space, sc: SpaceContext, rc: PartialFunction[RoutinePtr, Routine],
             expanded: Boolean = false): Unit =
    given SpaceContext = sc
    given PathContext = PathContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = rc
    val prog =
      if !expanded then prog0
      else
        val e = EquivPipeline.expand(prog0)
        assertEquals(eval(e), eval(prog0), s"$name: expansion changed the meaning")
        e
    val v = eval(prog)
    val h = histogram(v)
    val trueSize = v.paths.size.toLong
    val trueLens = h.keys.toVector.sorted

    // pass the routine table so Call nodes are analysed INTERPROCEDURALLY rather than widened
    val sb = Lower.sizeBounds(prog, rc)
    val lb = Lower.lenBounds(prog, rc)
    val st = SpatialTypes.infer(prog, SpatialEnv(routines = rc))
    val spSize = st.size
    val spLen = st.len

    // ---- soundness of every tier (this is the gate) ----
    assert(sb.lo <= trueSize && trueSize <= sb.hi, s"$name: size tier-1 ${fs(sb)} excludes $trueSize")
    for l <- trueLens do assert(lb.lo <= l && l <= lb.hi, s"$name: length tier-1 ${fl(lb)} excludes $l")
    for (l, n) <- h do
      val c = st.at(l)
      assert(c.lo <= n && n <= c.hi, s"$name: spatial class len $l = $n outside ${c.show}")
    assert(spSize.lo <= trueSize && trueSize <= spSize.hi, s"$name: spatial size ${fs(spSize)} excludes $trueSize")
    for l <- trueLens do assert(spLen.lo <= l && l <= spLen.hi, s"$name: spatial length ${fl(spLen)} excludes $l")

    val zs = if SizeZ3.available then Some(SizeZ3.boundsWithStatus(prog, timeoutSec = 25, rc)) else None
    val zl = if LenZ3.available then Some(LenZ3.boundsWithStatus(prog, timeoutSec = 25, rc)) else None
    zs.foreach { (z, s) =>
      if s == SizeZ3.Status.Solved || s.isInstanceOf[SizeZ3.Status.PartiallySolved] then
        assert(z.lo >= sb.lo && z.hi <= sb.hi, s"$name: SizeZ3 ${fs(z)} not inside baseline ${fs(sb)}")
        assert(z.lo <= trueSize && trueSize <= z.hi, s"$name: SizeZ3 ${fs(z)} excludes $trueSize")
    }
    zl.foreach { (z, s) =>
      if (s == SizeZ3.Status.Solved || s.isInstanceOf[SizeZ3.Status.PartiallySolved]) && !z.isEmpty then
        assert(z.lo >= lb.lo && z.hi <= lb.hi, s"$name: LenZ3 ${fl(z)} not inside baseline ${fl(lb)}")
        for l <- trueLens do assert(z.lo <= l && l <= z.hi, s"$name: LenZ3 ${fl(z)} excludes $l")
    }

    def statusOf(o: Option[(?, SizeZ3.Status)]): String = o match
      case None => "no-z3"
      case Some((_, SizeZ3.Status.Solved)) => "solved"
      case Some((_, SizeZ3.Status.ScopeLimited(r))) => s"scope-limited(${r.take(38)})"
      case Some((_, SizeZ3.Status.PartiallySolved(d))) => s"PARTIAL($d)"
      case Some((_, SizeZ3.Status.SolverFailed(d))) => s"solver-failed($d)"
      case Some((_, SizeZ3.Status.NoSolver)) => "no-z3"

    println(f"\n### $name%-12s  |eval| = $trueSize%-7d  true lengths = ${trueLens.mkString(",")}")
    println(f"    size    tier-1 ${fs(sb)}%-20s  z3 ${zs.map((z, _) => fs(z)).getOrElse("-")}%-20s ${statusOf(zs)}")
    println(f"    length  tier-1 ${fl(lb)}%-20s  z3 ${zl.map((z, _) => fl(z)).getOrElse("-")}%-20s ${statusOf(zl)}")
    println(f"    spatial size ${fs(spSize)}%-15s length ${fl(spLen)}%-15s classes ${st.show}")
    println(f"    truth   histogram (length -> count): ${trueLens.map(l => s"$l->${h(l)}").mkString(", ")}")

  // ---------------------------------------------------------------- the six cornerstones
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  def pv(items: String*): PathValue = PathValue(items.toList)
  def routineN(name: String, ms: String*)(body: Space): Routine =
    Routine(RoutinePtr(name), Vector.empty, ms.map(SpaceMention(_)).toVector, body)
  def callN(name: String, ms: Space*): Space = Space.Call(RoutinePtr(name), Vector.empty, ms.toVector)

  /** The sliding-puzzle reachable state space as a union-saturating `Space.Fixpoint`: start from
   *  the solved board and close under `expandStep` (the BFS successor relation), Call-free so the
   *  analyses see the fixpoint itself rather than an opaque recursive Call. */
  def puzzleFixpoint(rows: Int, cols: Int): Space =
    val p = Sliding.puzzle(rows, cols)
    val rec = SpaceMention("reach")
    val step = Space.Fixpoint(Space.Singleton(Path.Constant(p.initial)), rec,
                              Space.Union(Space.Mention(rec), p.expandStep(Space.Mention(rec))))
    // the puzzle's expandStep calls superpose/collapse — inline them so the term is Call-free
    val (lowered, residual) = lowerCalls(Routine(RoutinePtr("main"), Vector.empty, Vector.empty, step), p.defs)
    assert(residual.isEmpty, s"puzzle${rows * cols - 1}: unexpected residual ${residual.keys}")
    lowered

  /** all six, each reported twice: as written (open) and stage-0 expanded (ground local algebra) */
  def allSix(expanded: Boolean): Unit =

    // 1. aunt query — relational genealogy query over the family trie
    report("aunt", Routines.aunt_query_routine.body, AuntQuery.context, PartialFunction.empty, expanded)

    // 2. semi-naive datalog transitive closure (a recursive Call — control flow)
    locally {
      def join(r: Space, s: Space): Space = r.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
      val snTC = routineN("sn_tc", "e", "all", "delta") {
        S"all" \/ callN("sn_tc", S"e", S"all" \/ (join(S"delta", S"e") \ S"all"), join(S"delta", S"e") \ S"all") }
      val edges = sv(pv("0", "1"), pv("1", "2"), pv("2", "3"))
      report("datalog-sn", callN("sn_tc", Mention(SpaceMention("edges")), Mention(SpaceMention("edges")), Mention(SpaceMention("edges"))),
             SpaceContextMap(Map(SpaceMention("edges") -> edges)), Syntax.mod(snTC), expanded)
    }

    // 3. game of life — one step of the blinker (arithmetic via number relations)
    locally {
      val live = Set((1, 0), (1, 1), (1, 2))
      val rules = GoL.rulesFor(live)
      report("gol", Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Mention(SpaceMention("field")))),
             SpaceContextMap(Map(SpaceMention("field") -> GoL.field(live))), rules.defs, expanded)
    }

    // 4. 15-puzzle — one BFS expansion of the initial state
    locally {
      val p = Sliding.puzzle(4, 4)
      report("puzzle15", p.expandStep(Mention(SpaceMention("frontier"))),
             SpaceContextMap(Map(SpaceMention("frontier") -> SpaceValue(Set(p.initial)))), p.defs, expanded)
    }

    // 5. temperature — two prefix-range (cylinder) restrictions unioned
    locally {
      val rr = new scala.util.Random(12)
      val cells = (0 until 16).map(i => PathValue(NOAA.bits(i, 4) :+ (Vector("VC", "C", "N", "W", "VW")(rr.nextInt(5))))).toSet
      val world = Mention(SpaceMention("world"))
      val q = Union(Restriction(world, Literal(NOAA.interval(0, 4, 4))), Restriction(world, Literal(NOAA.interval(12, 16, 4))))
      report("temperature", q, SpaceContextMap(Map(SpaceMention("world") -> SpaceValue(cells))), PartialFunction.empty, expanded)
    }

    // 6. sliding puzzle, FULL expansion — the 2x2 "3-puzzle": BFS to a FIXPOINT, all 4!/2 = 12
    //    reachable states. Unlike puzzle15 (a single expansion) the analyses must reason about the
    //    WHOLE search, so this is the only cornerstone with an unbounded-iteration Space.Fixpoint.
    //    NOTE the two-argument `explore` routine is deliberately NOT lowered to a Fixpoint (both
    //    args change each step — the documented honest-residual case), so the closure is written
    //    directly in the union-saturating Fixpoint form, which denotes the same state space.
    report("puzzle3-full", puzzleFixpoint(2, 2), SpaceContextMap(Map.empty), PartialFunction.empty, expanded)

    // 7. n-queens — 4×4 board, nested placement iterations
    locally {
      val b = NQueens.board(4)
      report("nqueens", b.program, SpaceContextMap(Map.empty), b.defs, expanded)
    }

  test("cornerstones AS WRITTEN (open: inputs in the context, recursive Calls)") {
    println("=" * 100); println("CORNERSTONES AS WRITTEN — open forms"); println("=" * 100)
    allSix(expanded = false)
    println("\n" + "=" * 100)
  }

  test("cornerstones STAGE-0 EXPANDED (ground local algebra, eval-gated)") {
    println("=" * 100); println("CORNERSTONES EXPANDED — ground local algebra (EquivPipeline.expand)"); println("=" * 100)
    allSix(expanded = true)
    println("\n" + "=" * 100)
  }

  /** puzzle8 — the 3x3 8-puzzle's FULL reachable space as a Fixpoint.  The point is that the
   *  abstract interpretation is INDEPENDENT of the state-space size: it answers in milliseconds for
   *  181440 states exactly as it does for 12.  Soundness is checked against the KNOWN cardinality
   *  9!/2 = 181440 and the known path length 9 (one item per cell) — a mathematical fact about the
   *  puzzle, not something this test evaluates: computing it here takes over half an hour (the
   *  Slow `ExSlidingPuzzle` case already pins it by execution). */
  test("puzzle8 (3x3) FULL expansion: abstract interpretation is size-independent") {
    val prog = puzzleFixpoint(3, 3)
    val t0 = System.nanoTime()
    val sb = Lower.sizeBounds(prog); val lb = Lower.lenBounds(prog)
    val st = SpatialTypes.infer(prog)
    val ms = (System.nanoTime - t0) / 1000000
    println(s"\n### puzzle8-full (9!/2 = 181440 reachable states, 9 cells per state)")
    println(s"    size    tier-1 ${fs(sb)}   spatial ${fs(st.size)}")
    println(s"    length  tier-1 ${fl(lb)}   spatial ${fl(st.len)}   classes ${st.show}")
    println(s"    all three analyses answered in ${ms}ms — independent of the 181440-state space")
    val known = 181440L; val knownLen = 9L
    assert(sb.lo <= known && known <= sb.hi, s"size tier-1 ${fs(sb)} excludes the known $known")
    assert(st.size.lo <= known && known <= st.size.hi, s"spatial size ${fs(st.size)} excludes $known")
    assert(lb.lo <= knownLen && knownLen <= lb.hi, s"length tier-1 ${fl(lb)} excludes $knownLen")
    assert(st.len.lo <= knownLen && knownLen <= st.len.hi, s"spatial length ${fl(st.len)} excludes $knownLen")
    assert(st.at(knownLen).lo <= known && known <= st.at(knownLen).hi, s"spatial class $knownLen excludes $known")
  }

  /** The OPEN forms: the same cornerstones with their inputs left symbolic, which is where an
   *  input→output spatial type earns its keep (a closed program is just a ground fold). */
  test("open (input-symbolic) forms: what the analyses know WITHOUT the input value") {
    println("=" * 100)
    println("OPEN FORMS — inputs symbolic; spatial types under a DECLARED input type")
    println("=" * 100)

    // temperature with `world` symbolic, then with a declared input type
    val world = Mention(SpaceMention("world"))
    val q = Union(Restriction(world, Literal(NOAA.interval(0, 4, 4))), Restriction(world, Literal(NOAA.interval(12, 16, 4))))
    println(s"\n### temperature (open)  ${q.show.take(90)}...")
    println(s"    size    tier-1 ${fs(Lower.sizeBounds(q))}   length tier-1 ${fl(Lower.lenBounds(q))}")
    println(s"    spatial (no input type)     ${SpatialTypes.infer(q).show}")
    // the NOAA encoding is 4 address bits + 1 band item ⇒ every cell path has length 5
    val env = SpatialEnv(spaces = Map(SpaceMention("world") -> SpaceType.closed(5L -> Ivl(16, 16))))
    val t = SpatialTypes.infer(q, env)
    println(s"    spatial (world : 16 paths of length 5)  ${t.show}   size ${fs(t.size)}  length ${fl(t.len)}")
    val cells = (0 until 16).map(i => PathValue(NOAA.bits(i, 4) :+ "N")).toSet
    given SpaceContext = SpaceContextMap(Map(SpaceMention("world") -> SpaceValue(cells)))
    val truth = eval(q)
    println(s"    truth (one instantiation): ${truth.paths.size} paths, lengths ${histogram(truth).keys.toVector.sorted.mkString(",")}")
    for (l, n) <- histogram(truth) do
      assert(t.at(l).lo <= n && n <= t.at(l).hi, s"open temperature: class $l = $n outside ${t.at(l).show}")

    // aunt query with `family` symbolic
    val aunt = Routines.aunt_query_routine.body
    println(s"\n### aunt (open, family+people symbolic)")
    println(s"    size    tier-1 ${fs(Lower.sizeBounds(aunt))}   length tier-1 ${fl(Lower.lenBounds(aunt))}")
    println(s"    spatial (no input type)     ${SpatialTypes.infer(aunt).show}")
    val fam = AuntQuery.context.m(SpaceMention("family"))
    val fenv = SpatialEnv(spaces = Map(
      SpaceMention("family") -> SpaceType.of(fam),
      SpaceMention("people") -> SpaceType.closed(1L -> Ivl(2, 2))))
    val at = SpatialTypes.infer(aunt, fenv)
    println(s"    spatial (family : ${SpaceType.of(fam).show})")
    println(s"      => ${at.show}   size ${fs(at.size)}  length ${fl(at.len)}")
    println("\n" + "=" * 100)
  }
end CornerstoneTypes
