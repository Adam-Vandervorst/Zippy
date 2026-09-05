package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==============================================================================================
 *  A4 — RESOURCE BOUNDS AS ABSTRACTIONS OF THE COUNTED EXECUTION (gate suite 1 of 4).
 *
 *  tasks.md A4 acceptance: "zero containment failures under exhaustive small-model checks and
 *  randomized soundness hunts; the two known zipper counterexamples are covered as permanent
 *  regressions; all four spatial cost suites pass without workload-specific exceptions or stale
 *  expected formulae."
 *
 *  WHAT IS GATED HERE, AND WHAT IS REPORTED.  SOUNDNESS is the gate: every counted execution of every
 *  constructor on every backend lies inside the predicted interval, over an exhaustive small universe
 *  (exact and summarized declarations) and a randomized hunt.  USEFULNESS — the interval width per
 *  (backend, component) against the selection/budget tiers — is REPORTED per row and per tier; it is
 *  not a pass/fail here, because tasks.md M1 says "wide intervals are allowed at this milestone but are
 *  reported as not useful", and E1 is where usefulness becomes a published claim with its own gate.
 *  There is NO ledger of named exceptions: a containment failure fails, whatever its name.
 *  ============================================================================================== */
class SpatialCostCheck extends FunSuite, CalibrationProbe:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  val s0 = SpaceMention("s0"); val s1 = SpaceMention("s1")
  val S0 = Space.Mention(s0); val S1 = Space.Mention(s1)
  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty

  /** the small universe: paths over {a, b} of length ≤ 2, values of at most 3 paths */
  lazy val small: Vector[SpaceValue] =
    SpatialGamma.universe(Vector("a", "b"), 2).filter(_.paths.size <= 3)

  // ---- the oracle: every backend counted, one warm run first --------------------------------------------
  final case class Counted(reference: Events, trie: Events, graph: Option[Events], zipper: Events)
  def counted(prog: Space, spaces: Map[SpaceMention, SpaceValue], rc: PartialFunction[RoutinePtr, Routine] = noRc,
              graph: Option[RecursiveOpGraph] = None): Counted =
    val pc = PathContextMap(Map.empty); val sc = SpaceContextMap(spaces)
    val ic = spaces.view.mapValues(ITrie.fromSpaceValue).toMap
    eval(prog)(using pc, sc, rc); val r = EffortSink.events(eval(prog)(using pc, sc, rc))
    evalI(prog)(using pc, ic, rc); val t = EffortSink.events(evalI(prog)(using pc, ic, rc))
    execZ(prog)(using pc, ic, rc); val z = EffortSink.events(execZ(prog)(using pc, ic, rc))
    val g = graph.map { gg =>
      val ments = ic.map((k, v) => k.s -> v)
      runGraphT(gg, Map.empty, ments); EffortSink.events(runGraphT(gg, Map.empty, ments)) }
    Counted(r, t, g, z)

  /** one containment verdict per (backend); a failure names the events that escaped */
  final case class Row(label: String, backend: Backend, comp: EffortComponent, actual: Long, lo: Long, hi: Long):
    def contains: Boolean = lo <= actual && actual <= hi
    def width: Double = (hi.toDouble + 1) / (lo.toDouble + 1)
    def show: String = f"$label%-40s ${backend.slug}%-9s $comp%-6s actual=$actual%8d in [${Ivl(lo, hi).show}]  ${if contains then "OK" else "OUT"}"

  def rows(label: String, rep: CostReport, ev: Events): Vector[Row] =
    EffortEvent.calibratedComponents.map(c => Row(label, rep.backend, c, ev.component(c), rep.component(c).lo, rep.component(c).hi))

  def check(label: String, prog: Space, inputs: CostSem.Inputs, spaces: Map[SpaceMention, SpaceValue],
            rc: PartialFunction[RoutinePtr, Routine] = noRc, withGraph: Boolean = true): (Vector[Row], Vector[String]) =
    val g = if withGraph then Some(transpile(Routine(RoutinePtr("m"), Vector.empty, spaces.keys.toVector, prog))) else None
    val c = counted(prog, spaces, rc, g)
    val out = Vector.newBuilder[Row]; val bad = Vector.newBuilder[String]
    def one(b: Backend, ev: Events): Unit =
      val rep = if b == Backend.Graph then CostSem.analyzeGraph(g.get, inputs) else CostSem.analyze(prog, inputs, b, rc)
      val rs = rows(label, rep, ev); out ++= rs
      val v = rep.bounds.violations(ev)
      if v.nonEmpty then bad += s"$label/${b.slug}: ${v.mkString("; ")}\n    prog = ${prog.show.replace('\n', ' ').take(200)}\n    counted = ${ev.show}\n    ${rep.derivation.render().linesIterator.take(12).mkString("\n    ")}"
    one(Backend.Reference, c.reference); one(Backend.Trie, c.trie); one(Backend.Zipper, c.zipper)
    for ge <- c.graph do one(Backend.Graph, ge)
    (out.result(), bad.result())

  /** the usefulness report: per (backend, component) the p50 / p95 / worst width, against the tiers */
  def usefulness(title: String, rs: Vector[Row]): Unit =
    println(s"USEFULNESS — $title (${rs.length} rows; reported, not gated at M1)")
    for b <- Backend.values; c <- EffortEvent.calibratedComponents do
      val mine = rs.filter(r => r.backend == b && r.comp == c)
      if mine.nonEmpty then
        val ws = mine.map(_.width).sorted
        val tier = ProductRequirement.tierOf(b.slug, c)
        val worst = ws.last
        val verdict = tier match
          case Some(t) if t.width.isInfinite => "not gated"
          case Some(t) => if worst <= t.width then s"USEFUL (${t.name})" else s"NOT USEFUL for ${t.name} (worst width ${f"$worst%.1f"} > ${t.width})"
          case None => "no tier"
        println(f"USEFULNESS:   ${b.slug}%-9s $c%-6s p50=${ws(ws.length / 2)}%8.2f p95=${ws((ws.length * 95) / 100 min (ws.length - 1))}%8.2f worst=$worst%10.2f  $verdict")

  // ==============================================================================================
  // 1. EXHAUSTIVE SMALL-MODEL CHECK — exact declarations
  // ==============================================================================================

  val binops: Vector[(String, (Space, Space) => Space)] = Vector(
    "union" -> Space.Union.apply, "inter" -> Space.Intersection.apply, "sub" -> Space.Subtraction.apply,
    "restrict" -> Space.Restriction.apply, "raff" -> Space.Raffination.apply, "comp" -> Space.Composition.apply)
  val unops: Vector[(String, Space => Space)] = Vector(
    "tails-union" -> Space.TailsUnion.apply, "tails-inter" -> Space.TailsIntersection.apply,
    "wrap" -> (x => Space.Wrap(x, Path.Constant(p("w")))), "unwrap-a" -> (x => Space.Unwrap(x, Path.Constant(p("a")))),
    "range-first" -> (x => Space.Range(x, 0, 1)), "range-last" -> (x => Space.Range(x, -1, 0)), "range-full" -> (x => Space.Range(x, 0, 0)),
    "iter-heads" -> (x => Space.Iteration(x, PathRef("h").known(1), SpaceMention("r"), Space.Singleton(Path.Deref(PathRef("h").known(1))))),
    "iter-tails" -> (x => Space.Iteration(x, PathRef("h").known(1), SpaceMention("r"), Space.Mention(SpaceMention("r")))),
    "iter-rebuild" -> (x => Space.Iteration(x, PathRef("h").known(1), SpaceMention("r"), Space.Wrap(Space.Mention(SpaceMention("r")), Path.Deref(PathRef("h").known(1))))),
    "fix-suffix" -> (x => Space.Fixpoint(x, SpaceMention("f"), Space.Union(Space.Mention(SpaceMention("f")), Space.TailsUnion(Space.Mention(SpaceMention("f")))))))

  test("EXHAUSTIVE: every binary constructor over every pair of small values, exact declarations, four backends") {
    var all = Vector.empty[Row]; var bad = Vector.empty[String]
    val pairs = for a <- small; b <- small yield (a, b)
    for (name, op) <- binops do
      val prog = op(S0, S1)
      for (a, b) <- pairs do
        val (rs, bs) = check(s"$name", prog, CostSem.Inputs(values = Map(s0 -> a, s1 -> b)), Map(s0 -> a, s1 -> b))
        all ++= rs; bad ++= bs
      // aliased operand: the same input twice
      for a <- small do
        val (rs, bs) = check(s"$name/aliased", op(S0, S0), CostSem.Inputs(values = Map(s0 -> a)), Map(s0 -> a))
        all ++= rs; bad ++= bs
    println(s"COST: exhaustive binary — ${all.length} rows, ${bad.length} containment failures")
    bad.take(6).foreach(b => println("COST: OUT " + b))
    usefulness("exhaustive binary, exact declarations", all)
    assertEquals(bad.length, 0, s"containment failures:\n${bad.take(10).mkString("\n")}")
  }

  test("EXHAUSTIVE: every unary, positional and loop constructor over every small value, exact declarations") {
    var all = Vector.empty[Row]; var bad = Vector.empty[String]
    for (name, op) <- unops; a <- small do
      val (rs, bs) = check(name, op(S0), CostSem.Inputs(values = Map(s0 -> a)), Map(s0 -> a))
      all ++= rs; bad ++= bs
    println(s"COST: exhaustive unary — ${all.length} rows, ${bad.length} containment failures")
    bad.take(6).foreach(b => println("COST: OUT " + b))
    usefulness("exhaustive unary, exact declarations", all)
    assertEquals(bad.length, 0, s"containment failures:\n${bad.take(10).mkString("\n")}")
  }

  // ==============================================================================================
  // 2. THE SUMMARIZED TIER — inputs declared by type, outcomes sampled from γ
  // ==============================================================================================

  test("SUMMARIZED: inputs declared by their spatial type; every sampled member's execution is contained") {
    var all = Vector.empty[Row]; var bad = Vector.empty[String]
    // three declarations of increasing coarseness for the same sample family
    val decls: Vector[(String, SpaceValue => SpatialType)] = Vector(
      "SpatialType.of" -> (v => SpatialType.of(v)),
      "bounded(len≤2, ≤3)" -> (_ => SpatialType(Shape.top, SpaceType.bounded(Lower.LenBounds(0, 2), 3))),
      "closed-heads" -> (v => SpatialType(Shape.of(v).copy(others = Ivl.zero), SpaceType.bounded(Lower.LenBounds(0, 2), 3))))
    val rng = new java.util.Random(7)
    val sample = small.filter(_ => rng.nextInt(3) == 0).take(16)
    for (dn, decl) <- decls; (name, op) <- binops; a <- sample; b <- sample.take(6) do
      val inputs = CostSem.Inputs(summaries = Map(s0 -> decl(a), s1 -> decl(b)))
      val (rs, bs) = check(s"$name/$dn", op(S0, S1), inputs, Map(s0 -> a, s1 -> b))
      all ++= rs; bad ++= bs
    for (dn, decl) <- decls; (name, op) <- unops; a <- sample do
      val (rs, bs) = check(s"$name/$dn", op(S0), CostSem.Inputs(summaries = Map(s0 -> decl(a))), Map(s0 -> a))
      all ++= rs; bad ++= bs
    println(s"COST: summarized — ${all.length} rows, ${bad.length} containment failures")
    bad.take(6).foreach(b => println("COST: OUT " + b))
    usefulness("summarized declarations", all)
    assertEquals(bad.length, 0, s"containment failures:\n${bad.take(10).mkString("\n")}")
  }

  // ==============================================================================================
  // 3. THE RANDOMIZED SOUNDNESS HUNT
  // ==============================================================================================

  test("HUNT: random programs over random inputs, exact and summarized declarations, four backends") {
    val recs = Corpus.load(sys.props.get("cost.progs").map(_.toInt).getOrElse(120))
    val Al = SpaceFuzzer.alphabet
    val rng = new java.util.Random(20260905)
    def randPath() = PathValue(List.fill(1 + rng.nextInt(2))(Al(rng.nextInt(Al.length))))
    def smallTrie() = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 2).map(j => PathRef("p" + j)).toVector
    var all = Vector.empty[Row]; var bad = Vector.empty[String]; var n = 0
    for r <- recs if r.nPath == 0 do
      val svs = sNames.take(r.nSpace).map(_ -> smallTrie()).toMap
      val exact = CostSem.Inputs(values = svs)
      val summ = CostSem.Inputs(summaries = svs.view.mapValues(SpatialType.of).toMap)
      val (rs1, bs1) = check(s"corpus#$n/exact", r.prog, exact, svs)
      val (rs2, bs2) = check(s"corpus#$n/summ", r.prog, summ, svs)
      all ++= rs1 ++ rs2; bad ++= bs1 ++ bs2; n += 1
    println(s"COST: hunt — $n programs, ${all.length} rows, ${bad.length} containment failures")
    bad.take(8).foreach(b => println("COST: OUT " + b))
    usefulness("corpus hunt", all)
    assertEquals(bad.length, 0, s"containment failures:\n${bad.take(10).mkString("\n")}")
  }

  // ==============================================================================================
  // 4. THE TWO KNOWN ZIPPER COUNTEREXAMPLES — permanent regressions
  // ==============================================================================================

  test("REGRESSION: the two corpus programs whose zipper Work escaped the old model are contained") {
    // identified by their rendering in the 2026-09-05 baseline run (build.log, A4): the two programs whose
    // counted `execZ` Work fell outside the old model's interval (27 ∉ [16, 26]; 30 ∉ [22, 29])
    val marks = Vector(
      "Singleton(P\"h686557\" x \"d.c\") <| Range((TailsIntersection(",
      "TailsUnion((S\"s0\" \\/ S\"s0\"))(\"c\").iter(P\"h668698\"")
    val recs = Corpus.load()
    val found = marks.map(m => recs.find(r => r.prog.show.replace('\n', ' ').contains(m)))
    assert(found.forall(_.isDefined), s"the two counterexample programs must still be in the corpus: ${found.map(_.isDefined)}")
    val rng = new java.util.Random(20260807)
    val Al = SpaceFuzzer.alphabet
    def randPath() = PathValue(List.fill(1 + rng.nextInt(2))(Al(rng.nextInt(Al.length))))
    def smallTrie() = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath()).toSet)
    val svs = (0 until 3).map(i => SpaceMention("s" + i) -> smallTrie()).toMap
    var bad = Vector.empty[String]
    for r <- found.flatten do
      val inputs = svs.filter((k, _) => (0 until r.nSpace).map(i => SpaceMention("s" + i)).contains(k))
      for tries <- 0 until 3 do
        val vals = inputs.view.mapValues(_ => smallTrie()).toMap
        val (rs, bs) = check("zipper-counterexample", r.prog, CostSem.Inputs(values = vals), vals, withGraph = false)
        bad ++= bs
        rs.filter(_.backend == Backend.Zipper).foreach(row => println("COST: " + row.show))
    assertEquals(bad, Vector.empty[String])
  }

  // ==============================================================================================
  // 5. FIBRES: the puzzle15 requirement, in the small
  // ==============================================================================================

  test("FIBRES: a 16-cell board's per-cell projections compose to one path, priced from fibres, no Shape.top") {
    val cells = (0 until 16).map(i => s"c$i")
    val board = SpaceValue(cells.zipWithIndex.map((c, i) => PathValue(List(c, s"tile$i"))).toSet)
    val state = SpaceMention("state")
    val product = cells.map(c => Space.Unwrap(Space.Mention(state), Path.Constant(p(c)))).reduce(Space.Composition.apply)
    val inputs = CostSem.Inputs(values = Map(state -> board))
    val (rs, bad) = check("board-collapse", product, inputs, Map(state -> board))
    assertEquals(bad, Vector.empty[String])
    for b <- Backend.values do
      val rep = if b == Backend.Graph then CostSem.analyzeGraph(transpile(Routine(RoutinePtr("m"), Vector.empty, Vector(state), product)), inputs) else CostSem.analyze(product, inputs, b)
      assert(rep.finite, s"${b.slug}: ${rep.show}")
      assert(rep.magnitude < 100000L, s"${b.slug}: a 16-fold composition of one-tile fibres is small: ${rep.bounds.showComponents}")
      assertEquals(rep.value.node match { case t: XTrie => t.children.size; case _ => -1 }, 1, s"${b.slug}: the product is one path, got ${rep.value.show.take(120)}")
      assert(rep.domain.exact, rep.domain.show)
    // the same with the board declared ONLY by its summary: the fibres are no longer one tile each, and
    // the bound is wider — but finite, and it names no Shape.top
    val summ = CostSem.Inputs(summaries = Map(state -> SpatialType.of(board)))
    val rep2 = CostSem.analyze(product, summ, Backend.Trie)
    println(s"COST: board exact  ${CostSem.analyze(product, inputs, Backend.Trie).bounds.showComponents}")
    println(s"COST: board summ   ${rep2.bounds.showComponents}")
    println(CostSem.analyze(product, inputs, Backend.Trie).derivation.render().linesIterator.take(6).mkString("\n"))
  }

  // ==============================================================================================
  // 6. THE DERIVATION DAG is deterministic and names its rules
  // ==============================================================================================

  test("DERIVATION: two analyses render the same certificate; every interval has a rule") {
    val prog = Space.Union(Space.TailsUnion(S0), Space.Composition(S1, Space.Unwrap(S0, Path.Constant(p("a")))))
    val inputs = CostSem.Inputs(values = Map(s0 -> sv(p("a", "x"), p("b", "y")), s1 -> sv(p("k"))))
    for b <- Backend.values.filterNot(_ == Backend.Graph) do
      val r1 = CostSem.analyze(prog, inputs, b); val r2 = CostSem.analyze(prog, inputs, b)
      assertEquals(r1.derivation.render(), r2.derivation.render(), s"${b.slug}: the derivation is not deterministic")
      assertEquals(r1.bounds, r2.bounds)
      assert(r1.derivation.size >= (if b == Backend.Zipper then 1 else 5), s"${b.slug}: ${r1.derivation.size} derivation nodes")
      def allRules(d: Derivation): Vector[String] = d.rule +: d.children.flatMap(allRules)
      assert(allRules(r1.derivation).forall(_.nonEmpty))
    println(CostSem.analyze(prog, inputs, Backend.Trie).derivation.render())
  }

  test("NO EVALUATION: the analysis never runs an executor — a bomb literal is priced, not detonated") {
    val bomb = Space.GroundedSS(S0, _ => throw new AssertionError("the analysis evaluated its subject"))
    val prog = Space.Union(Space.TailsUnion(bomb), S1)
    val inputs = CostSem.Inputs(values = Map(s0 -> sv(p("a")), s1 -> sv(p("b"))))
    for b <- Backend.values.filterNot(_ == Backend.Graph) do
      val rep = CostSem.analyze(prog, inputs, b)
      assert(rep.notes.exists(_.contains("grounded")), rep.notes.toString)
    println("COST: bomb subterm priced on three backends without evaluation")
  }
