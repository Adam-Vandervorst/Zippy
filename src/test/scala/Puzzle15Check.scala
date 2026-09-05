package morkl

import munit.FunSuite
import morkl.Space.*
import morkl.EffortComponent.*

/** PUZZLE15 AS A FIRST-CLASS STRESS THEOREM.
 *
 *  The board invariants are stated and proved independently of the cost model in
 *  proofs/lean/Zippy/Puzzle15.lean (a board is a permutation; <= 4 successors; one expansion <= 4·|frontier|;
 *  16! states; the encoding's fibres).  This suite CHECKS their instantiation on the MORKL encoding — every
 *  board of the first BFS levels is a legal state and every successor a legal move — then prices one
 *  expansion under four declarations (two by value, two symbolic), holds every counted run to its interval,
 *  every result-size bound to the proved maximum, every interval to the committed usefulness thresholds
 *  (proofs/puzzle15/THRESHOLDS.tsv), and selects a backend from the certificate.  Everything it produces
 *  goes through ArtifactSink to proofs/puzzle15/ and is re-derived by scripts/check_puzzle15.py. */
class Puzzle15Check extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  val puzzle = Sliding.puzzle(4, 4)
  val frontier = SpaceMention("frontier")
  val prog: Space = puzzle.expandStep(Mention(frontier))
  val rc = puzzle.defs
  val dir = new java.io.File("proofs/puzzle15")
  val depth = 2

  def evalWith(front: Set[PathValue]): Set[PathValue] =
    eval(prog)(using PathContextMap(Map.empty), SpaceContextMap(Map(frontier -> SpaceValue(front))), rc).paths

  /** the BFS levels 0..depth by the MORKL program itself */
  lazy val levels: Vector[Set[PathValue]] =
    var cur = Set(puzzle.initial); val out = Vector.newBuilder[Set[PathValue]]; out += cur
    for _ <- 1 to depth do { cur = evalWith(cur); out += cur }
    out.result()
  lazy val edges: Vector[(PathValue, PathValue)] =
    (for lvl <- (0 until depth).toVector; b <- levels(lvl).toVector.sortBy(_.show); s <- evalWith(Set(b)).toVector.sortBy(_.show) yield (b, s))

  def cellIndex(item: Any): Option[Int] = item.toString match { case s if s.startsWith("c") => s.drop(1).toIntOption; case _ => None }
  def neighbours(i: Int): Vector[Int] =
    val (r, c) = (i / 4, i % 4)
    Vector((r - 1, c), (r + 1, c), (r, c - 1), (r, c + 1)).filter((rr, cc) => rr >= 0 && rr < 4 && cc >= 0 && cc < 4).map((rr, cc) => rr * 4 + cc)
  /** (blank cell, tile by cell) of a legal board path, None otherwise */
  def board(p: PathValue): Option[(Int, Vector[Option[Int]])] =
    if p.items.length != 16 then None
    else cellIndex(p.items.head).flatMap { b =>
      val tiles = p.items.tail.map(_.toString.toIntOption)
      if tiles.exists(_.isEmpty) || tiles.flatten.sorted != (1 to 15).toVector then None
      else
        val cells = (0 until 16).filterNot(_ == b)
        val arr = Array.fill[Option[Int]](16)(None)
        for (c, t) <- cells.zip(tiles.flatten) do arr(c) = Some(t)
        Some((b, arr.toVector))
    }

  test("INVARIANTS: every board of the first BFS levels is a legal state, every successor a legal move, the counts match the independent oracle") {
    val all = levels.flatten.toSet
    for b <- all do assert(board(b).isDefined, s"illegal board ${b.show}")
    for (parent, ss) <- edges.groupBy(_._1).view.mapValues(_.map(_._2).toSet) do
      val Some((blank, tiles)) = board(parent): @unchecked
      val legal = neighbours(blank).map { j =>
        val nb = tiles.updated(blank, tiles(j)).updated(j, None)
        PathValue(List(s"c$j") ++ (0 until 16).filterNot(_ == j).map(c => nb(c).get.toString))
      }.toSet
      assertEquals(ss, legal, s"${parent.show}: the successors are not exactly the legal moves of the blank")
      assert(ss.size <= 4)
    // the reachable count to `depth` equals the independent reference BFS (Sliding.refReachable)
    val reachable = levels.flatten.toSet.size
    assertEquals(reachable, Sliding.refReachable(4, 4, depth), "reachable states to depth 2")
    println(s"D3 invariants: ${all.size} boards over ${depth + 1} levels legal; ${edges.length} edges legal moves; oracle agrees")
    val sb = new StringBuilder
    sb ++= "# PUZZLE15 EXPANSION — the BFS levels the MORKL program produced; re-derived by scripts/check_puzzle15.py\n"
    sb ++= s"initial\t${puzzle.initial.show}\nlevel\t$depth\n"
    for (a, b) <- edges do sb ++= s"${a.show}\t${b.show}\n"
    ArtifactSink.write(new java.io.File(dir, "EXPANSION.tsv"), sb.result())
  }

  // ---- the declarations ------------------------------------------------------------------------------------
  final case class Decl(name: String, inputs: CostSem.Inputs, frontierSize: Int, values: Option[Map[SpaceMention, SpaceValue]])
  lazy val decls: Vector[Decl] =
    val one = Map(frontier -> SpaceValue(Set(puzzle.initial)))
    val l2 = Map(frontier -> SpaceValue(levels(2)))
    Vector(
      Decl("value:1", CostSem.Inputs(values = one), 1, Some(one)),
      Decl("value:level2", CostSem.Inputs(values = l2), levels(2).size, Some(l2)),
      Decl("symbolic:1", CostSem.Inputs(summaries = Map(frontier -> SpatialType(Shape.top, SpaceType.boundedExact(Lower.LenBounds(16, 16), 1)))), 1, None),
      Decl("symbolic:4", CostSem.Inputs(summaries = Map(frontier -> SpatialType(Shape.top, SpaceType.bounded(Lower.LenBounds(16, 16), 4)))), 4, None))

  final case class Row(decl: Decl, backend: Backend, rep: CostReport, counted: Option[Events])
  lazy val table: Vector[Row] =
    for d <- decls; b <- Backend.values.toVector yield
      val routine = Routine(RoutinePtr("expand"), Vector.empty, Vector(frontier), prog)
      val rep = SpatialPipeline.priceInputs(routine, d.inputs, rc, b)
      val cnt = d.values.flatMap(v => Decisions.counted(Residual(prog, SC.materialize(prog, rc)), b, v))
      Row(d, b, rep, cnt)

  def thresholds: Vector[(String, String, String, String)] =
    scala.io.Source.fromFile("proofs/puzzle15/THRESHOLDS.tsv").getLines().filterNot(l => l.startsWith("#") || l.trim.isEmpty)
      .map(_.split("\t")).filter(_.length >= 4).map(c => (c(0), c(1), c(2), c(3))).toVector
  def width(i: Ivl): Double = if i.hi >= Ivl.INF then Double.PositiveInfinity else (i.hi.toDouble + 1) / (i.lo.toDouble + 1)
  def slug(c: EffortComponent) = c.toString.toLowerCase

  test("SOUNDNESS: every counted run lies in its interval, and no result-size bound exceeds the proved maximum 4·|frontier|") {
    for r <- table do
      for ev <- r.counted do
        val v = r.rep.bounds.violations(ev)
        assert(v.isEmpty, s"${r.decl.name}/${r.backend.slug}: ${v.mkString("; ")}")
      // Zippy.Puzzle15.expand_le: one expansion has at most 4·|F| boards; a FINITE bound above that contradicts
      // the theorem (unsound).  An infinite one exceeds every maximum as a loss of precision: the USEFULNESS test
      if r.rep.valueSize.hi < Ivl.INF then
        assert(r.rep.valueSize.hi <= 4L * r.decl.frontierSize, s"${r.decl.name}/${r.backend.slug}: result size ${r.rep.valueSize.show} exceeds 4·${r.decl.frontierSize}")
      println(f"D3 ${r.decl.name}%-14s ${r.backend.slug}%-9s ${r.rep.bounds.showComponents}  size ${r.rep.valueSize.show}  counted ${r.counted.map(_.showComponents).getOrElse("-")}")
  }

  test("USEFULNESS: every committed threshold holds (a failure here is SOUND-BUT-NOT-USEFUL, not unsound)") {
    val failed = Vector.newBuilder[String]
    for (dn, bn, cn, t) <- thresholds do
      val r = table.find(r => r.decl.name == dn && r.backend.slug == bn).getOrElse(fail(s"threshold names no row: $dn/$bn"))
      val comp = EffortEvent.calibratedComponents.find(c => slug(c) == cn).getOrElse(fail(s"component $cn"))
      val iv = r.rep.component(comp); val w = width(iv)
      val ok = if t == "finite" then iv.hi < Ivl.INF else w <= t.toDouble
      if !ok then failed += f"$dn/$bn/$cn: ${iv.show} width ${if w.isInfinite then "inf" else f"$w%.3f"} vs threshold $t"
    // the proved maximum: every result-size bound must be finite and at most 4·|frontier| (Zippy.Puzzle15.expand_le)
    for r <- table if r.rep.valueSize.hi >= Ivl.INF do failed += s"${r.decl.name}/${r.backend.slug}: result-size bound infinite, the proved maximum is 4·${r.decl.frontierSize}"
    val fs = failed.result()
    for f <- fs do println(s"D3 NOT USEFUL: $f")
    assert(fs.isEmpty, s"${fs.length} threshold(s) not met:\n  ${fs.mkString("\n  ")}")
  }

  test("DECISION: a backend is chosen from the certificate, and the counted runs confirm it") {
    val one = decls.head
    val fr = Alternatives.exploreRoutine(Routine(RoutinePtr("expand"), Vector.empty, Vector(frontier), prog), rc.orElse(Map(RoutinePtr("expand") -> Routine(RoutinePtr("expand"), Vector.empty, Vector(frontier), prog))),
                                        one.inputs, Alternatives.Options(pairs = false, unrolls = Vector.empty))
    val sel = Pareto.select(fr, Pareto.Objective.minimise(Alloc))
    val chosen = sel.selected.getOrElse(fail("nothing selected"))
    val alt = fr(chosen.alt)
    val counted = Backend.values.toVector.flatMap(b => Decisions.counted(alt.residual, b, one.values.get).map(ev => b -> ev.component(Alloc)))
    val best = counted.minBy(_._2)
    println(s"D3 decision: alloc → ${chosen.key}; counted alloc per backend ${counted.map((b, n) => s"${b.slug}=$n").mkString(" ")}")
    assertEquals(chosen.backend, best._1, "the certificate's choice is the backend whose counted alloc is least")
    assert(Pareto.replay(sel.render).isEmpty)
    ArtifactSink.write(new java.io.File(dir, "SELECTION-alloc.tsv"), sel.render)
  }

  test("ARTIFACTS: the certificate and the derivation report") {
    val sb = new StringBuilder
    sb ++= "# PUZZLE15 CERTIFICATE — one expansion priced under four declarations on four backends; re-derived by scripts/check_puzzle15.py\n"
    sb ++= "# C\tdeclaration\tbackend\tfrontier\twork.lo\twork.hi\talloc.lo\talloc.hi\trounds.lo\trounds.hi\ttouch.lo\ttouch.hi\tcounted-work\tcounted-alloc\tcounted-rounds\tcounted-touch\tsize.lo\tsize.hi\tcertified\n"
    def n(x: Long) = if x >= Ivl.INF then "inf" else x.toString
    for r <- table do
      val cs = EffortEvent.calibratedComponents
      sb ++= (Vector("C", r.decl.name, r.backend.slug, r.decl.frontierSize.toString) ++ cs.flatMap(c => Vector(n(r.rep.component(c).lo), n(r.rep.component(c).hi))) ++
              cs.map(c => r.counted.map(_.component(c).toString).getOrElse("-")) ++ Vector(n(r.rep.valueSize.lo), n(r.rep.valueSize.hi), if r.rep.certified then "CERTIFIED" else "UNCERTIFIED")).mkString("\t") ++= "\n"
    ArtifactSink.write(new java.io.File(dir, "CERTIFICATE.tsv"), sb.result())
    // the report
    val md = new StringBuilder
    md ++= "# puzzle15 — the stress theorem's derivation report\n\n<!-- GENERATED by Puzzle15Check; a verify run fails on drift -->\n\n"
    md ++= s"One BFS expansion of the 15-puzzle (`expandStep`), priced by the compositional resource analysis. The state-space facts it is held to are proved in `proofs/lean/Zippy/Puzzle15.lean` (see `proofs/puzzle15/REGISTRY.tsv`): a board is a permutation, a board has at most four successors, one expansion of a frontier `F` has at most `4·|F|` boards, the encoding's first position has 16 possible values and every other one 15.\n\n"
    md ++= s"**Invariants checked on the MORKL encoding.** ${levels.flatten.toSet.size} boards over ${depth + 1} BFS levels are legal states; ${edges.length} successor edges are legal blank moves; the reachable count to depth $depth equals the independent oracle (`Sliding.refReachable`). Committed as `EXPANSION.tsv`, re-derived by `scripts/check_puzzle15.py` with its own BFS.\n\n"
    md ++= "## Certificates\n\n| declaration | backend | work | alloc | rounds | touch | result size | counted (work/alloc/rounds/touch) | certified |\n|---|---|---|---|---|---|---|---|---|\n"
    for r <- table do
      md ++= s"| ${r.decl.name} | ${r.backend.slug} | ${r.rep.component(Work).show} | ${r.rep.component(Alloc).show} | ${r.rep.component(Rounds).show} | ${r.rep.component(Touch).show} | ${r.rep.valueSize.show} (max ${4 * r.decl.frontierSize}) | ${r.counted.map(e => s"${e.work}/${e.alloc}/${e.rounds}/${e.touch}").getOrElse("—")} | ${if r.rep.certified then "yes" else "no"} |\n"
    md ++= "\n## Usefulness against the committed thresholds\n\n| declaration | backend | component | interval | width | threshold | verdict |\n|---|---|---|---|---|---|---|\n"
    for (dn, bn, cn, t) <- thresholds do
      val r = table.find(r => r.decl.name == dn && r.backend.slug == bn).get
      val comp = EffortEvent.calibratedComponents.find(c => slug(c) == cn).get
      val iv = r.rep.component(comp); val w = width(iv)
      val ok = if t == "finite" then iv.hi < Ivl.INF else w <= t.toDouble
      md ++= f"| $dn | $bn | $cn | ${iv.show} | ${if w.isInfinite then "inf" else f"$w%.3f"} | $t | ${if ok then "USEFUL" else "NOT USEFUL"} |\n"
    md ++= "\n## Where the symbolic declarations lose\n\n"
    for r <- table if r.decl.values.isEmpty && r.backend == Backend.Reference do
      val lines = r.rep.derivation.render().linesIterator.toVector
      val inf = lines.filter(l => l.contains("inf]")).map(_.trim).distinct.take(6)
      val wid = lines.filter(_.contains("WIDENED")).map(_.trim).distinct.take(6)
      md ++= s"**${r.decl.name}** (reference): ${r.rep.domain.widenings.length} widening(s); first unbounded rules: " + (if inf.isEmpty then "none" else inf.map(l => s"`${l.take(120)}`").mkString("; ")) + (if wid.isEmpty then "" else "; widenings: " + wid.map(l => s"`${l.take(120)}`").mkString("; ")) + "\n\n"
    md ++= "The value-declared certificates are tight where the executor is deterministic (reference, graph) and finite everywhere; under the symbolic declarations the summarized iteration nest of the 16-deep projection multiplies fibres it cannot correlate, and the bounds are not useful — reported here, not excused. The decision fixture is `proofs/decisions/puzzle15-expand*.tsv`  and `SELECTION-alloc.tsv` here.\n"
    ArtifactSink.write(new java.io.File(dir, "REPORT.md"), md.result())
  }

  test("every committed puzzle15 artifact matches what this suite produces") {
    ArtifactSink.assertClean("morkl.Puzzle15Check")
  }
