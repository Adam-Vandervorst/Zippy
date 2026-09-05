package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions
import morkl.Space.*

/** tasks.md B1 — RESIDUAL ALTERNATIVES ARE EXPLICIT.
 *
 *  Acceptance: a deterministic fixture exposes at least three semantically equivalent residual choices
 *  with pairwise different certified cost, created and merged with NO ground evaluation.  Beyond the
 *  acceptance sentence: every alternative's trace replays; every certificate contains the counted run
 *  of every executor; hash-consing merges alpha-equivalent residuals under equal assumptions and keeps
 *  them apart under different ones; the widening budget records what it dropped; the rendering is
 *  deterministic; the GROUND law set agrees with proofs/laws/REGISTRY.tsv. */
class AlternativesCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)

  // ---- THE FIXTURE: two same-source loops (fusion), a loop with an invariant branch (sharing), a
  //      restriction of a union (prefix restriction) — one program, four law-table normal forms ------
  val s = SpaceMention("s"); val k = SpaceMention("k"); val h = PathRef("h"); val r = SpaceMention("r")
  val body: Space =
    Union(
      Union(Iteration(Mention(s), h, r, Wrap(Intersection(Mention(r), Mention(k)), Path.Deref(h))),
            Iteration(Mention(s), h, r, Wrap(TailsUnion(Mention(r)), Path.Deref(h)))),
      Union(Iteration(Mention(s), h, r, Union(Wrap(Subtraction(Mention(r), Mention(k)), Path.Deref(h)), Mention(k))),
            Restriction(Union(Mention(s), TailsUnion(Mention(k))), Literal(sv(p("a"), p("b"))))))
  val prog = Routine(RoutinePtr("choices"), Vector.empty, Vector(s, k), body)
  val defs: PartialFunction[RoutinePtr, Routine] = Map(prog.name -> prog)

  val sVal = sv(p("a", "x"), p("a", "y", "z"), p("b", "x"), p("c", "q", "r", "t"), p("b"))
  val kVal = sv(p("x"), p("y", "z"), p("q", "r"), p("a", "x"))
  val values = Map(s -> sVal, k -> kVal)
  /** the input ASSUMPTIONS: summaries of the two spaces — nothing is evaluated to build them */
  val inputs = CostSem.Inputs(summaries = Map(s -> SpatialType.of(sVal), k -> SpatialType.of(kVal)))

  lazy val (frontier, eventsDuringExploration) =
    val (f, ev) = EffortSink.count(Alternatives.exploreRoutine(prog, defs, inputs))
    (f, ev)

  /** the counted runs of the executors that can run a residual */
  def counted(res: Residual): Map[Backend, Events] =
    val pc = PathContextMap(Map.empty); val sc = SpaceContextMap(values); val rc = res.env
    val ic = values.view.mapValues(ITrie.fromSpaceValue).toMap
    val re = EffortSink.events(eval(res.top)(using pc, sc, rc))
    val te = EffortSink.events(evalI(res.top)(using pc, ic, rc))
    val ze = EffortSink.events(execZ(res.top)(using pc, ic, rc))
    Map(Backend.Reference -> re, Backend.Trie -> te, Backend.Zipper -> ze)

  test("THE GROUND LAW SET agrees with proofs/laws/REGISTRY.tsv (kind GROUND)") {
    val rows = scala.io.Source.fromFile("proofs/laws/REGISTRY.tsv").getLines().filterNot(l => l.startsWith("#") || l.trim.isEmpty).map(_.split("\t")).toVector
    val ground = rows.filter(c => c.length > 1 && c(1).trim == "GROUND").map(_(0).trim).toSet
    assertEquals(ground, SC.groundLaws, "the registry's GROUND rows are exactly SC.groundLaws")
    assert(SC.groundLaws.forall(g => SC.sourceLaws.exists(_._1 == g)), "every ground law is a source law")
  }

  test("ACCEPTANCE: at least three semantically equivalent residuals with pairwise different certified cost, no ground evaluation") {
    val f = frontier
    println(f.render)
    assertEquals(eventsDuringExploration.total, 0L, s"the exploration evaluated something: ${eventsDuringExploration.nonZero}")
    assert(f.alternatives.length >= 3, s"only ${f.alternatives.length} alternatives")
    // no alternative used a GROUND law, and every trace replays
    for a <- f.alternatives do
      assert(a.laws.forall(l => !SC.groundLaws(l)), s"${a.id}: ground law in trace ${a.laws}")
      val bad = ProofTrace.Checker.check(a.trace, defs, a.nodes)
      assert(bad.isEmpty, s"${a.id}: ${bad.mkString("; ")}")
      assertEquals(a.trace.dst, a.top, s"${a.id}: the trace ends at the residual")
      assert(a.trace.src == Call(prog.name, Vector.empty, Vector(Mention(s), Mention(k))), s"${a.id}: the trace starts at the configuration")
    // semantically equivalent: every residual evaluates to the same value on the concrete inputs
    val vals = f.alternatives.map(a => eval(a.top)(using PathContextMap(Map.empty), SpaceContextMap(values), a.residual.env))
    assert(vals.distinct.length == 1, s"the alternatives disagree: ${vals.map(_.paths.size)}")
    assertEquals(vals.head, eval(body)(using PathContextMap(Map.empty), SpaceContextMap(values), defs), "and agree with the source program")
    // pairwise different certified cost on the trie backend (work or alloc): three such alternatives
    def sig(a: Alternatives.Alternative) = (a.interval(Backend.Trie, EffortComponent.Work), a.interval(Backend.Trie, EffortComponent.Alloc))
    val distinctCosts = f.alternatives.map(sig).distinct
    println(s"B1: ${f.alternatives.length} alternatives, ${distinctCosts.length} distinct (work, alloc) trie intervals: ${distinctCosts.map((w, a) => s"work ${w.show} alloc ${a.show}").mkString(" | ")}")
    assert(distinctCosts.length >= 3, s"fewer than three distinct costs: $distinctCosts")
    // every alternative is a DIFFERENT program (the frontier hash-conses)
    assertEquals(f.alternatives.map(_.canonKey).distinct.length, f.alternatives.length, "no two frontier alternatives are the same canonical residual")
    // the four families are represented: the driver, fusion off, sharing off, prefix restriction off
    for c <- Vector(Alternatives.Choice.Fold, Alternatives.Choice.Fusion, Alternatives.Choice.Sharing, Alternatives.Choice.PrefixRestriction) do
      assert(f.alternatives.exists(_.provenance.exists(_.choice == c)) || f.pruned.exists(_._1.provenance.exists(_.choice == c)),
             s"no alternative (kept or pruned) came from $c")
  }

  test("CERTIFICATES contain the counted run of every executor, for every alternative") {
    for a <- frontier.alternatives do
      val evs = counted(a.residual)
      for (b, ev) <- evs do
        val v = a.certificate(b).bounds.violations(ev)
        assert(v.isEmpty, s"${a.id}/${b.slug}: ${v.mkString("; ")}\n${a.certificate(b).derivation.render().linesIterator.take(15).mkString("\n")}")
        println(f"B1: ${a.id} ${b.slug}%-9s ${a.certificate(b).bounds.showComponents}  counted ${ev.showComponents}")
  }

  test("HASH-CONSING: an alpha-equivalent residual merges under equal assumptions and is kept apart under different ones") {
    val f = frontier
    val a = f.alternatives.head
    val b = new Alternatives.Builder(32)
    assertEquals(b.add(a), Some(a.id))
    // the same residual with its routine names shuffled and its bound names renamed is the SAME alternative
    val renamed = a.copy(id = "other", residual = Residual(Matching.canon(a.top), a.residual.routines))
    assertEquals(b.add(renamed), Some(a.id), "merged into the first")
    // the same residual under DIFFERENT resource assumptions is a second alternative
    val other = a.copy(id = "other2", assumptions = CostSem.Inputs(summaries = Map(s -> SpatialType.of(sVal))))
    assertEquals(b.add(other), Some("other2"))
    val fr = b.result
    assertEquals(fr.alternatives.length, 2)
    assertEquals(fr.pruned.map(_._2.show).count(_.startsWith("MERGED")), 1)
    assert(fr.notes.exists(_.contains("same residual under different assumptions")), fr.notes.mkString)
    // a CONDITIONAL twin of an unconditional alternative is subsumed
    val cond = a.copy(id = "cond", scope = FactScope.Conditional(Map(s -> SpatialType.of(sVal)), Map.empty, Map.empty))
    val b2 = new Alternatives.Builder(32); b2.add(a); assertEquals(b2.add(cond), None)
    assert(b2.result.pruned.exists((x, why) => x.id == "cond" && why.show.startsWith("SUBSUMED")))
  }

  test("WIDENING: past the budget the largest residual is dropped and recorded with the budget") {
    val f = frontier
    assert(f.alternatives.length >= 3)
    val b = new Alternatives.Builder(2)
    for a <- f.alternatives do b.add(a)
    val fr = b.result
    assertEquals(fr.alternatives.length, 2)
    val widened = fr.pruned.filter(_._2.isInstanceOf[Alternatives.Pruned.Widened])
    assertEquals(widened.length, f.alternatives.length - 2)
    assert(widened.forall(_._2.show.contains("budget 2")))
    // what survived is never larger than what was dropped
    assert(fr.alternatives.forall(a => widened.forall(_._1.size >= a.size)), "the widening dropped the largest")
    assertEquals(fr.pruned.length + fr.alternatives.length, f.alternatives.length, "nothing is lost silently")
  }

  test("DETERMINISM: two explorations render identically, traces included") {
    val f1 = Alternatives.exploreRoutine(prog, defs, inputs)
    val f2 = Alternatives.exploreRoutine(prog, defs, inputs)
    assertEquals(f1.render, f2.render)
    assertEquals(f1.renderTraces, f2.renderTraces)
    assertEquals(f1.render, frontier.render)
  }

  test("UNFOLD/FOLD: a recursive fixture yields the fold-first residual AND an unrolled one, both replaying") {
    val m = SpaceMention("m")
    val suf = Routine(RoutinePtr("suf"), Vector.empty, Vector(m), Union(Mention(m), Call(RoutinePtr("suf"), Vector.empty, Vector(TailsUnion(Mention(m))))))
    val d: PartialFunction[RoutinePtr, Routine] = Map(suf.name -> suf)
    val in = CostSem.Inputs(summaries = Map(m -> SpatialType.of(sVal)))
    val f = Alternatives.exploreRoutine(suf, d, in, Alternatives.Options(families = Vector.empty, pairs = false, unrolls = Vector(1, 2)))
    println(f.render)
    val unrolled = f.byProvenance(Alternatives.Choice.Unfold)
    assert(unrolled.nonEmpty, "an unrolled alternative survived")
    assert(f.alternatives.exists(a => a.unrolls == 0), "the fold-first alternative survived")
    assert(unrolled.forall(_.unrolls > 0))
    for a <- f.alternatives do
      val bad = ProofTrace.Checker.check(a.trace, d, a.nodes)
      assert(bad.isEmpty, s"${a.id}: ${bad.mkString("; ")}")
      for (g, dag) <- a.nodeTraces do
        val nb = ProofTrace.Checker.check(dag, d, a.nodes)
        assert(nb.isEmpty, s"${a.id}/${g.s}: ${nb.mkString("; ")}")
        assertEquals(dag.dst, a.residual.routines(g).body, s"${a.id}/${g.s}: the node trace ends at the body")
      assert(a.kinds.contains("Unfold"), s"${a.id}: kinds ${a.kinds}")
    // the unrolled residual is a different program with a different residual size
    assert(f.alternatives.map(_.canonKey).distinct.length == f.alternatives.length)
    assert(f.alternatives.map(_.size).distinct.length >= 2, s"sizes ${f.alternatives.map(_.size)}")
  }
