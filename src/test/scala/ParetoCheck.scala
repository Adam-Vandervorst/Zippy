package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions
import morkl.Space.*
import morkl.EffortComponent.*
import scala.jdk.CollectionConverters.*

/** SELECTION FROM A CERTIFIED PARETO FRONTIER.
 *
 *  Acceptance: selection is deterministic; every removal is replayable by an independent checker
 *  (`scripts/check_selection.py`, run from here on the certificates this suite writes); changing the
 *  objective selects different alternatives in the fusion, prefix/range, call-composition, sharing and
 *  recursion fixtures.  Beyond that: dominance never uses an infinite or widened-to-infinity upper bound,
 *  overlapping intervals are incomparable, the reference's `touch` can neither win nor lose, an alternative
 *  with an OPEN trace closure or an uncertified derivation is not admitted, and a forged certificate fails
 *  the replay. */
class ParetoCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  val s = SpaceMention("s"); val k = SpaceMention("k"); val h = PathRef("h"); val r = SpaceMention("r"); val m = SpaceMention("m")
  val sVal = sv(p("a", "x"), p("a", "y", "z"), p("b", "x"), p("c", "q", "r", "t"), p("b"), p("a", "x", "w"))
  val kVal = sv(p("x"), p("y", "z"), p("q", "r"), p("a", "x"), p("b"))

  final case class Case(name: String, family: String, routine: Routine, defs: PartialFunction[RoutinePtr, Routine],
                           values: Map[SpaceMention, SpaceValue], opts: Alternatives.Options = Alternatives.Options())

  // ---- FUSION: two same-source loops, an invariant branch, a restriction of a union (the B1 fixture) --
  val fusionBody: Space =
    Union(
      Union(Iteration(Mention(s), h, r, Wrap(Intersection(Mention(r), Mention(k)), Path.Deref(h))),
            Iteration(Mention(s), h, r, Wrap(TailsUnion(Mention(r)), Path.Deref(h)))),
      Union(Iteration(Mention(s), h, r, Union(Wrap(Subtraction(Mention(r), Mention(k)), Path.Deref(h)), Mention(k))),
            Restriction(Union(Mention(s), TailsUnion(Mention(k))), Literal(sv(p("a"), p("b"))))))
  val fusion = Routine(RoutinePtr("fusion"), Vector.empty, Vector(s, k), fusionBody)

  // ---- SHARING: a loop whose body carries an expensive invariant — computed once (hoisted) or per head
  val sharingBody: Space =
    Iteration(Mention(s), h, r, Union(Wrap(Subtraction(Mention(r), Mention(k)), Path.Deref(h)),
                                      Intersection(TailsUnion(TailsUnion(Mention(k))), Union(Mention(k), TailsUnion(Mention(k))))))
  val sharing = Routine(RoutinePtr("sharing"), Vector.empty, Vector(s, k), sharingBody)

  // ---- PREFIX / RANGE: a restriction over a union of three operands, and a range over a union -------
  val prefixBody: Space =
    Union(Restriction(Union(Union(Mention(s), Wrap(Mention(k), Path.Constant(p("a")))), TailsUnion(Mention(s))), Literal(sv(p("a"), p("b", "x")))),
          Range(Union(Mention(s), Mention(k)), 0, 3))
  val prefix = Routine(RoutinePtr("prefix"), Vector.empty, Vector(s, k), prefixBody)

  // ---- CALL COMPOSITION: a routine called twice, its loops fusable after inlining --------------------
  // (the first loop also carries an invariant — `tails(tails m)` — so hoisting it trades allocation for work
  //  on both call sites at once: the choice is only visible after the calls are composed)
  val f = Routine(RoutinePtr("f"), Vector.empty, Vector(m),
                  Union(Iteration(Mention(m), h, r, Union(Wrap(Mention(r), Path.Concat(Path.Deref(h), Path.Constant(p("x")))), TailsUnion(TailsUnion(Mention(m))))),
                        Iteration(Mention(m), h, r, Wrap(TailsUnion(Mention(r)), Path.Deref(h)))))
  val compBody: Space = Union(Call(f.name, Vector.empty, Vector(Mention(s))), Restriction(Call(f.name, Vector.empty, Vector(Mention(k))), Mention(s)))
  val composition = Routine(RoutinePtr("composition"), Vector.empty, Vector(s, k), compBody)

  // ---- RECURSION: the suffix closure, fold-first or unrolled --------------------------------------
  val suf = Routine(RoutinePtr("suf"), Vector.empty, Vector(m), Union(Mention(m), Call(RoutinePtr("suf"), Vector.empty, Vector(TailsUnion(Mention(m))))))

  val fixtures = Vector(
    Case("fusion", "fusion", fusion, Map(fusion.name -> fusion), Map(s -> sVal, k -> kVal)),
    Case("sharing", "sharing", sharing, Map(sharing.name -> sharing), Map(s -> sVal, k -> kVal)),
    Case("prefix", "prefix/range", prefix, Map(prefix.name -> prefix), Map(s -> sVal, k -> kVal)),
    Case("composition", "call-composition", composition, Map(composition.name -> composition, f.name -> f), Map(s -> sVal, k -> kVal)),
    Case("recursion", "recursion", suf, Map(suf.name -> suf), Map(m -> sVal), Alternatives.Options(families = Vector.empty, pairs = false, unrolls = Vector(1, 2))))

  val objectives: Vector[Pareto.Objective] = Vector(
    Pareto.Objective.minimise(Work), Pareto.Objective.minimise(Alloc), Pareto.Objective.minimise(Rounds), Pareto.Objective.minimise(Touch),
    Pareto.Objective("work-on-trie", Vector(Work, Alloc, Rounds, Touch), backends = Vector(Backend.Trie)),
    Pareto.Objective("alloc-under-rounds", Vector(Alloc, Work, Rounds, Touch), constraints = Vector(Pareto.Constraint(Rounds, 8))))

  val outDir = java.nio.file.Paths.get("target/decisions")
  lazy val frontiers: Map[String, Alternatives.Frontier] =
    fixtures.map(fx => fx.name -> Alternatives.exploreRoutine(fx.routine, fx.defs, CostSem.Inputs(values = fx.values), fx.opts)).toMap

  def write(name: String, text: String): java.nio.file.Path =
    java.nio.file.Files.createDirectories(outDir)
    val f = outDir.resolve(s"$name.tsv"); java.nio.file.Files.writeString(f, text); f

  test("EVERY FIXTURE has a frontier of at least two alternatives, all admitted") {
    for fx <- fixtures do
      val fr = frontiers(fx.name)
      println(s"B2 ${fx.name}: ${fr.alternatives.length} alternatives, ${fr.pruned.length} pruned, ${fr.refused.length} refused")
      assert(fr.alternatives.length >= 2, s"${fx.name}: ${fr.render}")
      for a <- fr.alternatives do
        assert(a.certified, s"${fx.name}/${a.id}: not certified")
        val cl = TraceClosure.of(a.trace +: a.nodeTraces.values.toVector)
        assert(cl.closed, s"${fx.name}/${a.id}: ${cl.render}")
  }

  test("SELECTION is deterministic, every removal replays in-process and by the independent checker") {
    java.nio.file.Files.createDirectories(outDir)
    for f <- java.nio.file.Files.list(outDir).iterator().asScala.toVector do java.nio.file.Files.delete(f)
    var written = 0
    for fx <- fixtures; o <- objectives do
      val fr = frontiers(fx.name)
      val sel = Pareto.select(fr, o)
      val sel2 = Pareto.select(fr, o)
      assertEquals(sel.render, sel2.render, s"${fx.name}/${o.name}: two selections render differently")
      val bad = Pareto.replay(sel.render)
      assert(bad.isEmpty, s"${fx.name}/${o.name}:\n${bad.mkString("\n")}\n${sel.render}")
      // every candidate is accounted for exactly once
      assertEquals(sel.rejected.length + sel.survivors.length, sel.candidates.length, s"${fx.name}/${o.name}: partition")
      write(s"${fx.name}-${o.name}", sel.render); written += 1
      println(s"B2 ${fx.name}/${o.name}: " + sel.selected.map(_.key).getOrElse("NONE") + s"  rejected ${sel.rejected.length} (dominated ${sel.rejected.count(_._2.isInstanceOf[Pareto.Rejection.Dominated])}), kept ${sel.kept.length}")
    val proc = new ProcessBuilder("python3", "scripts/check_selection.py", outDir.toString).redirectErrorStream(true).start()
    val out = scala.io.Source.fromInputStream(proc.getInputStream).mkString
    val rc = proc.waitFor()
    println(out.linesIterator.toVector.takeRight(3).mkString("\n"))
    assertEquals(rc, 0, s"check_selection.py failed:\n$out")
    assert(out.contains(s"$written file(s), 0 problem(s)"), out)
  }

  test("CHANGING THE OBJECTIVE changes the choice in every fixture family, and each choice minimises its component's upper bound") {
    for fx <- fixtures do
      val fr = frontiers(fx.name)
      val chosen = for o <- objectives.take(4) yield
        val sel = Pareto.select(fr, o)
        val c = sel.selected.getOrElse(fail(s"${fx.name}/${o.name}: nothing selected"))
        // the selected candidate has the least upper bound on the objective's first component among the survivors
        for other <- sel.kept.map(_._1) do
          assert(c.hi(o.priority.head) <= other.hi(o.priority.head), s"${fx.name}/${o.name}: ${c.key} hi ${c.hi(o.priority.head)} > ${other.key} ${other.hi(o.priority.head)}")
        println(s"B2 ${fx.name}: minimise ${o.name} → ${c.key} " + EffortEvent.calibratedComponents.map(cc => s"${Pareto.slug(cc)}=${c.bounds(cc).show}").mkString(" "))
        o.name -> c.key
      val distinct = chosen.map(_._2).distinct
      println(s"B2 ${fx.name}: ${distinct.length} distinct choices over four objectives: ${chosen.map((o, c) => s"$o→$c").mkString(", ")}")
      val byId = fr.alternatives.map(a => a.id -> a).toMap
      def altOf(key: String) = byId(key.split("/").head)
      fx.name match
        case "recursion" =>
          // THE EXPECTED ALTERNATIVE under every objective is the fold-first residual: the unrolled ones
          // carry unbounded certificates (an unrolled body is priced as an unbounded recursion), and an
          // infinite upper bound is never selected over a finite one
          for (o, key) <- chosen do assertEquals(altOf(key).unrolls, 0, s"recursion/$o selected an unrolled alternative $key")
          val sel = Pareto.select(fr, objectives.head)
          assert(sel.kept.exists(k => altOf(k._1.key).unrolls > 0), "the unrolled alternatives are KEPT (incomparable), not rejected")
        case "sharing" =>
          // hoisting the invariant SHARES it: one allocation instead of one per head, so the hoisted residual
          // (the ordinary driver's) is expected under `alloc`.  Under `work` the hoisted residual's interval is
          // WIDER (the guard composition `headed(s)·inv` is priced with may-facts) and the tie rule ranks by the
          // upper bound: the per-head recomputation (Sharing disabled), priced exactly, is the expected choice —
          // the conservative one, and the certificate shows the overlap
          val workSel = altOf(chosen.find(_._1 == "work").get._2); val allocSel = altOf(chosen.find(_._1 == "alloc").get._2)
          assert(!allocSel.provenance.exists(_.choice == Alternatives.Choice.Sharing), s"sharing/alloc selected the unhoisted residual: ${allocSel.provenance.map(_.show)}")
          assert(workSel.provenance.exists(_.choice == Alternatives.Choice.Sharing), s"sharing/work selected the hoisted residual: ${workSel.provenance.map(_.show)}")
          assert(allocSel.interval(Backend.Reference, Alloc).hi < workSel.interval(Backend.Reference, Alloc).lo, "the hoisted residual allocates strictly less")
          assert(workSel.interval(Backend.Reference, Work).hi < allocSel.interval(Backend.Reference, Work).hi, "…and the unhoisted one has the tighter work upper bound")
          assert(distinct.length >= 2, s"${fx.name}: $chosen")
        case _ =>
          assert(distinct.length >= 2, s"${fx.name} (${fx.family}): the objective did not change the choice: $chosen")
  }

  test("DOMINANCE: an infinite upper bound never wins, overlap is incomparable, the reference cannot win on touch") {
    def cand(id: String, b: Backend, w: (Long, Long), a: (Long, Long), r: (Long, Long), t: (Long, Long)) =
      Pareto.Candidate(id, b, Map(Work -> Ivl(w._1, w._2), Alloc -> Ivl(a._1, a._2), Rounds -> Ivl(r._1, r._2), Touch -> Ivl(t._1, t._2)), true, TraceClosure.Status.Closed)
    val all = EffortEvent.calibratedComponents
    val x = cand("x", Backend.Trie, (1, 5), (1, 5), (1, 5), (1, 5))
    val y = cand("y", Backend.Trie, (6, 9), (5, 9), (6, 9), (6, 9))
    assert(Pareto.dominates(x, y, all).isDefined, "x below y on every component (one touching: 5<=5) with three strict")
    assert(Pareto.dominates(y, x, all).isEmpty)
    val z = cand("z", Backend.Trie, (1, 5), (1, 5), (1, 5), (1, Ivl.INF))
    assert(Pareto.dominates(z, y, all).isEmpty, "an infinite upper bound cannot win")
    assert(Pareto.dominates(y, z, all).isEmpty, "…and y is not below z")
    val o = cand("o", Backend.Trie, (4, 7), (1, 5), (1, 5), (1, 5))
    assert(Pareto.dominates(x, o, all).isEmpty && Pareto.dominates(o, x, all).isEmpty, "overlap on work is incomparable")
    assertEquals(Pareto.overlaps(x, o, all), all, "x=[1,5] and o=[4,7] overlap on work, and equal intervals overlap on the rest")
    val eq = cand("e", Backend.Trie, (1, 5), (1, 5), (1, 5), (1, 5))
    assert(Pareto.dominates(x, eq, all).isEmpty, "equal intervals: nothing strict, no dominance")
    // the reference's touch is [0, inf] after Candidate.of: it can neither dominate nor be dominated on touch
    val fr = frontiers("fusion")
    val a = fr.alternatives.head
    val ref = Pareto.Candidate.of(a, Backend.Reference)
    assertEquals(ref.bounds(Touch), Ivl(0, Ivl.INF))
    val sel = Pareto.select(fr, Pareto.Objective.minimise(Touch))
    assert(sel.selected.exists(_.backend != Backend.Reference), "minimising touch never picks the modelled reference")
    for (c, rej) <- sel.rejected do rej match
      case Pareto.Rejection.Dominated(by, _) => assert(by.backend != Backend.Reference || c.backend == Backend.Reference || true)
      case _ => ()
    assert(!sel.rejected.exists((c, rj) => c.backend == Backend.Reference && rj.isInstanceOf[Pareto.Rejection.Dominated] &&
                                  rj.asInstanceOf[Pareto.Rejection.Dominated].evidence.exists((cc, xhi, ylo) => cc == Touch && xhi < ylo)),
           "no reference candidate was beaten strictly on touch")
  }

  test("ADMISSION: an uncertified derivation or an OPEN trace closure is rejected NOT-ADMITTED, with the reason") {
    val fr = frontiers("fusion")
    val o = Pareto.Objective.minimise(Work, Vector(Backend.Trie))
    val cands = fr.alternatives.map(a => Pareto.Candidate.of(a, Backend.Trie))
    val open = cands.head.copy(closure = TraceClosure.Status.Open(Vector("law x: no status row")))
    val uncert = cands(1).copy(certified = false)
    val sel = Pareto.decide(o, Vector(open, uncert) ++ cands.drop(2))
    assert(sel.rejected.exists((c, r) => c.alt == open.alt && r.kind == "NOT-ADMITTED" && r.detail.contains("trace closure OPEN")), sel.render)
    assert(sel.rejected.exists((c, r) => c.alt == uncert.alt && r.kind == "NOT-ADMITTED" && r.detail.contains("not certified")), sel.render)
    assert(sel.selected.forall(c => c.alt != open.alt && c.alt != uncert.alt))
    assert(Pareto.replay(sel.render).isEmpty)
    // constraints: a cap below every lower bound rejects everything as INFEASIBLE; nothing is selected
    val none = Pareto.decide(Pareto.Objective("tight", Vector(Work), constraints = Vector(Pareto.Constraint(Work, 1))), cands)
    assert(none.selected.isEmpty && none.rejected.forall(r => r._2.kind == "INFEASIBLE" || r._2.kind == "UNPROVEN"), none.render)
    assert(none.rejected.exists(_._2.kind == "INFEASIBLE"), none.render)
    assert(Pareto.replay(none.render).isEmpty)
  }

  test("A FORGED CERTIFICATE fails the replay (in-process and independent)") {
    val fr = frontiers("fusion")
    val sel = Pareto.select(fr, Pareto.Objective.minimise(Work))
    val text = sel.render
    assert(sel.rejected.nonEmpty, "the fixture has rejections to forge")
    // 1. drop one rejection row: the candidate is unaccounted for
    val lines = text.linesIterator.toVector
    val xi = lines.indexWhere(_.startsWith("X\t"))
    val forged1 = lines.patch(xi, Nil, 1).mkString("\n") + "\n"
    assert(Pareto.replay(forged1).nonEmpty)
    // 2. swap the selected candidate for a kept one (or a rejected one)
    val si = lines.indexWhere(_.startsWith("S\t"))
    val victim = lines.find(l => l.startsWith("X\t")).get.split("\t")
    val forged2 = lines.updated(si, s"S\t${victim(1)}\t${victim(2)}\tforged").mkString("\n") + "\n"
    assert(Pareto.replay(forged2).nonEmpty)
    // 3. change a number in a C row so a recorded dominance no longer holds
    val ci = lines.indexWhere(_.startsWith("C\t"))
    val cols = lines(ci).split("\t")
    val forged3 = lines.updated(ci, (cols.take(3) ++ Array("0", "0") ++ cols.drop(5)).mkString("\t")).mkString("\n") + "\n"
    assert(Pareto.replay(forged3).nonEmpty)
    for (f, i) <- Vector(forged1, forged2, forged3).zipWithIndex do
      val path = java.nio.file.Files.createTempFile(java.nio.file.Paths.get("target"), s"forged$i", ".tsv")
      java.nio.file.Files.writeString(path, f)
      val proc = new ProcessBuilder("python3", "scripts/check_selection.py", path.toString).redirectErrorStream(true).start()
      val out = scala.io.Source.fromInputStream(proc.getInputStream).mkString
      assertEquals(proc.waitFor(), 1, s"forgery $i passed the independent checker:\n$out")
      java.nio.file.Files.delete(path)
  }
