package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions
import morkl.Space.*

/** tasks.md A5 — CALLS AND RECURSIVE COMPONENTS ARE COMPOSITIONAL IN THE RESOURCE DOMAIN.
 *
 *  Every bound here is produced by `CostSem` WITHOUT inlining as an analysis step: a `Call` is answered by
 *  the callee's PARAMETRIC SUMMARY at the caller's abstract arguments (computed once per canonical routine
 *  and abstract input, reused afterwards), and a positive passthrough recursive component is answered by
 *  the IR's SIMULTANEOUS SYSTEM (`DeltaIR`).  The oracle is the counted execution: the four executors for
 *  acyclic calls, the IR solver (`DeltaIR.Exec`) for a mutually recursive component, which no executor's
 *  own Call rule can run. */
class CrossFunctionCostCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  val emptyPc: PathContext = PathContextMap(Map.empty)

  /** the counted runs of the executors that can run a program */
  def counted(prog: Space, spaces: Map[SpaceMention, SpaceValue], paths: Map[PathRef, PathValue],
              rc: PartialFunction[RoutinePtr, Routine]): Map[Backend, Events] =
    val pc = PathContextMap(paths); val sc = SpaceContextMap(spaces)
    val ic = spaces.view.mapValues(ITrie.fromSpaceValue).toMap
    eval(prog)(using pc, sc, rc); val re = EffortSink.events(eval(prog)(using pc, sc, rc))
    evalI(prog)(using pc, ic, rc); val te = EffortSink.events(evalI(prog)(using pc, ic, rc))
    execZ(prog)(using pc, ic, rc); val ze = EffortSink.events(execZ(prog)(using pc, ic, rc))
    Map(Backend.Reference -> re, Backend.Trie -> te, Backend.Zipper -> ze)

  def check(label: String, prog: Space, spaces: Map[SpaceMention, SpaceValue], paths: Map[PathRef, PathValue],
            rc: PartialFunction[RoutinePtr, Routine]): Map[Backend, CostReport] =
    val inputs = CostSem.Inputs(values = spaces, paths = paths)
    val evs = counted(prog, spaces, paths, rc)
    val reps = evs.map((b, _) => b -> CostSem.analyze(prog, inputs, b, rc))
    for (b, ev) <- evs do
      val rep = reps(b)
      val v = rep.bounds.violations(ev)
      assert(v.isEmpty, s"$label/${b.slug}: ${v.mkString("; ")}\n  ${rep.derivation.render().linesIterator.take(20).mkString("\n  ")}")
      assert(rep.finite, s"$label/${b.slug}: not finite ${rep.bounds.showComponents}")
      println(f"A5: $label%-36s ${b.slug}%-9s ${rep.bounds.showComponents}  counted ${ev.showComponents}  summaries reused/computed=${rep.summaries}")
    reps

  /** the zipper prices a call through its evalI fallback, once per cursor pass (two passes): the same
   *  summaries are COMPUTED (the cache is shared) and every second lookup is a hit */
  def zipperConsistent(z: (Int, Int), trie: (Int, Int), why: String): Unit =
    assert(z._2 == trie._2 && z._1 + z._2 == 2 * (trie._1 + trie._2),
           s"zipper: $why — got $z against the trie's $trie (expected the same misses and twice the lookups)")

  def expect(reps: Map[Backend, CostReport], hits: Int, misses: Int, why: String): Unit =
    for (b, rep) <- reps do
      if b == Backend.Zipper then zipperConsistent(rep.summaries, (hits, misses), why)
      else assertEquals(rep.summaries, (hits, misses), s"${b.slug}: $why")

  // ---- the routines ---------------------------------------------------------------------------------
  val s0 = SpaceMention("s0"); val s1 = SpaceMention("s1")
  val q1 = PathRef("q1"); val q2 = PathRef("q2")
  /** wr(p; m) = p · m */
  val wr = Routine(RoutinePtr("wr"), Vector(PathRef("p")), Vector(SpaceMention("m")),
                   Wrap(Mention(SpaceMention("m")), Path.Deref(PathRef("p"))))
  /** tw(; m) = m ∪ tails(m) */
  val tw = Routine(RoutinePtr("tw"), Vector.empty, Vector(SpaceMention("m")),
                   Union(Mention(SpaceMention("m")), TailsUnion(Mention(SpaceMention("m")))))
  /** cf(; a, b) = (a ∩ b) ∪ (a ∖ b): two space parameters, correlated result */
  val cf = Routine(RoutinePtr("cf"), Vector.empty, Vector(SpaceMention("a"), SpaceMention("b")),
                   Union(Intersection(Mention(SpaceMention("a")), Mention(SpaceMention("b"))),
                         Subtraction(Mention(SpaceMention("a")), Mention(SpaceMention("b")))))
  val rc: PartialFunction[RoutinePtr, Routine] = Map(wr.name -> wr, tw.name -> tw, cf.name -> cf)

  val in0 = sv(p("a"), p("a", "b"), p("b", "c", "d"), p("c"))
  val in1 = sv(p("a", "b"), p("d"))

  test("CHANGING PATH ARGUMENTS: the same routine at two path arguments is two summaries, both contained") {
    val prog = Union(Call(wr.name, Vector(Path.Deref(q1)), Vector(Mention(s0))),
                     Call(wr.name, Vector(Path.Deref(q2)), Vector(Mention(s0))))
    val reps = check("wr(q1; s0) ∪ wr(q2; s0)", prog, Map(s0 -> in0), Map(q1 -> p("x"), q2 -> p("y", "z")), rc)
    expect(reps, 0, 2, "two different path arguments are two summaries")
    // and the SAME path argument twice is one summary, reused once
    val same = Union(Call(wr.name, Vector(Path.Deref(q1)), Vector(Mention(s0))),
                     Call(wr.name, Vector(Path.Deref(q1)), Vector(Mention(s0))))
    val reps2 = check("wr(q1; s0) ∪ wr(q1; s0)", same, Map(s0 -> in0), Map(q1 -> p("x")), rc)
    expect(reps2, 1, 1, "the second call must reuse the first summary")
  }

  test("SUMMARY REUSE: four calls at one abstract input compute one summary; a different input computes another") {
    val c = Call(wr.name, Vector(Path.Deref(q1)), Vector(Mention(s0)))
    val prog = Union(Union(c, c), Union(c, Call(wr.name, Vector(Path.Deref(q1)), Vector(Mention(s1)))))
    val reps = check("4× wr, two inputs", prog, Map(s0 -> in0, s1 -> in1), Map(q1 -> p("x")), rc)
    expect(reps, 2, 2, "3 calls on s0 share one summary, s1 has its own")
    // the reuse is visible in the certificate: the reused node points at the computed derivation
    val d = reps(Backend.Trie).derivation.render()
    assert(d.contains("summary REUSED"), "the derivation must say where a summary was reused")
    assert(d.contains("summary COMPUTED"), "and where it was computed")
  }

  test("CORRELATED RESULT: (a ∩ b) ∪ (a ∖ b) through a call is priced from the arguments' correlation, and contained") {
    // the same object twice: a ∩ a = a and a ∖ a = ∅ by pointer identity — the summary at the alias
    // class (0, 0) sees that; the summary at (0, 1) does not
    val same = Call(cf.name, Vector.empty, Vector(Mention(s0), Mention(s0)))
    val diff = Call(cf.name, Vector.empty, Vector(Mention(s0), Mention(s1)))
    val r1 = check("cf(s0, s0)", same, Map(s0 -> in0, s1 -> in1), Map.empty, rc)
    val r2 = check("cf(s0, s1)", diff, Map(s0 -> in0, s1 -> in1), Map.empty, rc)
    assert(r1(Backend.Trie).touch.hi < r2(Backend.Trie).touch.hi,
           s"the aliased call must be cheaper in touch: ${r1(Backend.Trie).touch.show} vs ${r2(Backend.Trie).touch.show}")
    // both are one abstract input each: no reuse across the two programs' separate analyses, one summary each
    for r <- Vector(r1, r2) do expect(r, 0, 1, "one abstract input, one summary")
  }

  test("RANGE OF A CALL RESULT: Range(tw(s0), 0, 1) and Range(tw(s0), -1, 0) are contained and finite") {
    for (lo, hi) <- Vector((0, 1), (-1, 0), (1, 3)) do
      val prog = Range(Call(tw.name, Vector.empty, Vector(Mention(s0))), lo, hi)
      check(s"Range(tw(s0), $lo, $hi)", prog, Map(s0 -> in0), Map.empty, rc)
  }

  test("CALLS BELOW BINDERS: a call in a loop body, its path argument the loop head, contained on every backend") {
    val h = PathRef("h").known(1); val t = SpaceMention("t")
    val prog = Iteration(Mention(s0), h, t, Call(wr.name, Vector(Path.Deref(h)), Vector(Mention(t))))
    val reps = check("s0.iter(h, t, wr(h; t))", prog, Map(s0 -> in0), Map.empty, rc)
    // one summary per distinct head (the path argument differs), none reused
    expect(reps, 0, 3, "distinct heads are distinct abstract inputs")
    // and below a Fixpoint binder
    val f = SpaceMention("f")
    val fix = Fixpoint(Mention(s0), f, Call(tw.name, Vector.empty, Vector(Mention(f))))
    check("fix f = s0 ∪ tw(f)", fix, Map(s0 -> in0), Map.empty, rc)
  }

  test("MUTUAL RECURSION: a positive passthrough component is priced as the IR's simultaneous system, against the solver's counted rounds") {
    // even(m) = m ∪ odd(m);  odd(m) = tails(m) ∪ even(m)  — the suffix closure, as two routines calling
    // each other with the same parameter.  `eval`'s own Call rule DIVERGES on it (the stabilised-argument
    // shortcut needs the callee to be the caller), so the only execution is the IR's.
    val m = SpaceMention("m")
    val even = Routine(RoutinePtr("even"), Vector.empty, Vector(m), Union(Mention(m), Call(RoutinePtr("odd"), Vector.empty, Vector(Mention(m)))))
    val odd = Routine(RoutinePtr("odd"), Vector.empty, Vector(m), Union(TailsUnion(Mention(m)), Call(RoutinePtr("even"), Vector.empty, Vector(Mention(m)))))
    val rc2: PartialFunction[RoutinePtr, Routine] = Map(even.name -> even, odd.name -> odd)
    val prog = Call(even.name, Vector.empty, Vector(Mention(s0)))
    val inputs = CostSem.Inputs(values = Map(s0 -> in0))
    val rep = CostSem.analyze(prog, inputs, Backend.Reference, rc2)
    assert(rep.finite, s"the component must be finite: ${rep.bounds.showComponents}")
    println(s"A5: even/odd system  reference ${rep.bounds.showComponents}")
    println(rep.derivation.render().linesIterator.take(12).mkString("  ", "\n  ", ""))
    // the oracle: the IR solver's counted rounds
    val lowered = DeltaIR.lower(prog, rc2) match
      case Verdict.Accepted(pr) => pr
      case other => fail(s"the component must lower: ${other.show}")
    val (value, solves) = Exec.run(lowered, Schedule.Naive, SpaceContextMap(Map(s0 -> in0)), emptyPc, verify = true, countEvents = true)
    assertEquals(solves.length, 1, "one system solve for one call")
    val sysEvents = solves.head.rounds.map(_.events).reduce(_ + _)
    // the System node of the certificate bounds exactly the solver's rounds
    def find(d: Derivation): Option[Derivation] = if d.rule == "System" then Some(d) else d.children.iterator.map(find).collectFirst { case Some(x) => x }
    val sysNode = find(rep.derivation).getOrElse(fail("no System node in the derivation"))
    val v = sysNode.result.violations(sysEvents)
    assert(v.isEmpty, s"the system's rounds escape the System node: ${v.mkString("; ")}\n  solver ${sysEvents.show}\n  node ${sysNode.result.show}")
    println(s"A5: even/odd system node ${sysNode.result.showComponents}  solver rounds ${sysEvents.showComponents} over ${solves.head.rounds.length} rounds")
    // the value: PASSTHROUGH means `tails` is applied to the parameter once — even(m) = m ∪ tails(m)
    // (the suffix CLOSURE would need `tails(even)`, an argument-changing call) — and the abstract result admits it
    val expected = SpaceValue(in0.paths ++ in0.paths.collect { case PathValue(_ :: t) => PathValue(t) })
    assertEquals(value, expected, "the solver's value is m ∪ tails(m)")
    val d = new Domain(DomainBudget())
    assert(SpatialType.accepts(d.summary(rep.value.node), value), s"the abstract result must admit the solver's value: ${rep.value.show}")
    // the rounds are exact on the exact tier: point intervals
    assertEquals(sysNode.result.component(EffortComponent.Work).lo, sysNode.result.component(EffortComponent.Work).hi, "exact rounds: a point interval on Work")
    // summarized input: still finite, with the first round certain and the rest bounded by growth
    val summ = CostSem.analyze(prog, CostSem.Inputs(summaries = Map(s0 -> SpatialType.of(in0))), Backend.Reference, rc2)
    assert(summ.finite, s"summarized: ${summ.bounds.showComponents}")
    val summSys = find(summ.derivation).getOrElse(fail("no System node in the summarized derivation"))
    val v2 = summSys.result.violations(sysEvents)
    assert(v2.isEmpty, s"summarized: the solver's rounds escape the System node: ${v2.mkString("; ")}")
    println(s"A5: even/odd summarized ${summ.bounds.showComponents}; system node ${summSys.result.showComponents}")
  }

  test("CORNERSTONE CALL CHAINS: gol (nextStep → neigh), aunt (aunt_query → child) and puzzle15 are finite and far below ⊤") {
    val live = Set((1, 0), (1, 1), (1, 2))
    val golRules = GoL.rulesFor(live)
    val puz = Sliding.puzzle(4, 4)
    val cases = Vector[(String, Space, Map[SpaceMention, SpaceValue], PartialFunction[RoutinePtr, Routine])](
      ("gol", Call(RoutinePtr("nextStep"), Vector.empty, Vector(Mention(SpaceMention("field")))), Map(SpaceMention("field") -> GoL.field(live)), golRules.defs),
      ("aunt", Routines.aunt_query_routine.body, AuntQuery.context.asInstanceOf[SpaceContextMap].m, Syntax.mod(Routines.child_routine)),
      ("puzzle15", puz.expandStep(Mention(SpaceMention("frontier"))), Map(SpaceMention("frontier") -> SpaceValue(Set(puz.initial))), puz.defs))
    for (name, body, spaces, rcc) <- cases do
      // the DEFINITIONAL body, calls preserved (no `Routine.optimized` inlining): the summaries do the work
      val reps = check(name, body, spaces, Map.empty, rcc)
      for (b, rep) <- reps do
        assert(rep.magnitude < ProductRequirement.Astronomical.toLong, s"$name/${b.slug}: astronomical ${rep.bounds.showComponents}")
        val widths = EffortEvent.calibratedComponents.map(c => (rep.component(c).hi + 1).toDouble / (rep.component(c).lo + 1))
        println(f"A5: $name%-10s ${b.slug}%-9s widths ${widths.map(w => f"$w%.2f").mkString(" ")}  summaries reused/computed=${rep.summaries}")
        assert(widths.forall(_ < 1000.0), s"$name/${b.slug}: a call-chain bound wider than 1000x is not materially tighter than ⊤: ${rep.bounds.showComponents}")
      // the calls are PRESERVED: the certificate names them (a summary, a stationary recursion or a system), never an inlined body
      val rendered = reps(Backend.Trie).derivation.render()
      if callees(body).nonEmpty then
        assert(rendered.linesIterator.exists(_.trim.startsWith("Call ")), s"$name: the derivation names no Call rule — calls must be preserved, not inlined")
      println(s"A5: $name call rules: ${rendered.linesIterator.map(_.trim).filter(_.startsWith("Call ")).map(_.takeWhile(_ != '[').trim).toVector.distinct.take(6).mkString(" | ")}")
  }
end CrossFunctionCostCheck
