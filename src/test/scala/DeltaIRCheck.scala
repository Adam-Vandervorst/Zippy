package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==============================================================================================
 *  A2 — THE STRATIFIED DELTA-FIXPOINT IR, AGAINST ITS ACCEPTANCE SENTENCE.
 *
 *  tasks.md A2: "positive mutual recursion and negative dependencies on lower strata are accepted;
 *  cycles containing a negative or unknown edge are rejected; naive and delta execution produce the
 *  same accumulator at every round boundary and the same stationary result; recursive `Call` SCCs
 *  and explicit `Fixpoint` lower to the same IR when extensionally equivalent; every accepted IR
 *  instance carries replayable Lean-backed stratification and delta premises."
 *  ============================================================================================== */
class DeltaIRCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  val s0 = SpaceMention("s0"); val s1 = SpaceMention("s1")
  val S0 = Space.Mention(s0); val S1 = Space.Mention(s1)
  val r = SpaceMention("r"); val q = SpaceMention("q")
  val R = Space.Mention(r); val Q = Space.Mention(q)
  val edges = sv(p("e", "0", "1"), p("e", "1", "2"), p("e", "2", "3"), p("e", "3", "0"), p("e", "3", "4"))
  val words = sv(p("a", "b", "c", "d"), p("x", "y"), p("z"))

  /** one transitive-closure hop over `x` (edges under head `e`) — the datalog body */
  def hop(x: Space): Space =
    Space.Iteration(Space.Unwrap(x, Path.Constant(p("e"))), PathRef("a").known(1), SpaceMention("as"),
      Space.Iteration(Space.Mention(SpaceMention("as")), PathRef("b").known(1), SpaceMention("_"),
        Space.Iteration(Space.Unwrap(Space.Unwrap(S0, Path.Constant(p("e"))), Path.Deref(PathRef("b").known(1))), PathRef("c").known(1), SpaceMention("_2"),
          Space.Wrap(Space.Singleton(Path.Concat(Path.Deref(PathRef("a").known(1)), Path.Deref(PathRef("c").known(1)))), Path.Constant(p("e"))))))

  def accepted(v: Verdict): Lowered = v match
    case Verdict.Accepted(l) => l
    case other => fail(s"expected ACCEPTED, got\n${other.show}")

  def env(kv: (SpaceMention, SpaceValue)*): SpaceContext = SpaceContextMap(kv.toMap)

  // ---- 1. variance ----------------------------------------------------------------------------------

  test("variance: the constructor table, and it agrees with monotoneInMention on the fuzzer corpus") {
    import Variance.*
    assertEquals(Variance.of(Space.Union(R, S0), r), Pos)
    assertEquals(Variance.of(Space.Subtraction(S0, R), r), Neg)
    assertEquals(Variance.of(Space.Subtraction(R, R), r), Zero, "both sides of a difference: unknown")
    assertEquals(Variance.of(Space.Subtraction(S0, Space.Subtraction(S1, R)), r), Pos, "- ∘ - = +")
    assertEquals(Variance.of(Space.TailsIntersection(R), r), Zero, "TailsIntersection is not monotone (O3d-X1)")
    assertEquals(Variance.of(Space.Range(R, 0, 1), r), Zero)
    assertEquals(Variance.of(S0, r), Absent)
    // iteration: the source is a positive position only when the body is monotone in the tails it binds
    val it1 = Space.Iteration(R, PathRef("h").known(1), SpaceMention("t"), Space.Mention(SpaceMention("t")))
    assertEquals(Variance.of(it1, r), Pos)
    val it2 = Space.Iteration(R, PathRef("h").known(1), SpaceMention("t"), Space.Subtraction(S0, Space.Mention(SpaceMention("t"))))
    assertEquals(Variance.of(it2, r), Zero, "a rest-antitone body makes the source position unknown (O3d-X2)")
    // fixpoint: antitone in an outer variable when init/body are antitone in it and the body is positive in rec
    val fx = Space.Fixpoint(Space.Subtraction(S0, R), q, Space.Union(Q, Space.TailsUnion(Q)))
    assertEquals(Variance.of(fx, r), Neg)
    assertEquals(Variance.of(fx, q), Absent, "the binder shadows")
    // routine parameter variances through a table: f(m) = s0 \ m is antitone in m; g(m) = f(f(m)) positive
    val f = Routine(RoutinePtr("f"), Vector.empty, Vector(r), Space.Subtraction(S0, R))
    val g = Routine(RoutinePtr("g"), Vector.empty, Vector(r), Space.Call(RoutinePtr("f"), Vector.empty, Vector(Space.Call(RoutinePtr("f"), Vector.empty, Vector(R)))))
    val table = Variance.routineTable(Syntax.mod(f, g), Seq(RoutinePtr("g")))
    assertEquals(table(RoutinePtr("f")), Vector(Neg))
    assertEquals(table(RoutinePtr("g")), Vector(Pos))
    // recursive: h(m) = m ∪ h(m) is positive; k(m) = s0 \ k(m) is unknown (it would need - ∘ -, over a cycle)
    val h = Routine(RoutinePtr("h"), Vector.empty, Vector(r), Space.Union(R, Space.Call(RoutinePtr("h"), Vector.empty, Vector(R))))
    val k = Routine(RoutinePtr("k"), Vector.empty, Vector(r), Space.Subtraction(S0, Space.Call(RoutinePtr("k"), Vector.empty, Vector(R))))
    val t2 = Variance.routineTable(Syntax.mod(h, k), Seq(RoutinePtr("h"), RoutinePtr("k")))
    assertEquals(t2(RoutinePtr("h")), Vector(Pos))
    assertEquals(t2(RoutinePtr("k")), Vector(Absent), "k never reads its parameter directly: absent")
    // THE OLD DECISION PROCEDURE IS SOUND FOR THE NEW ONE: monotoneInMention ⇒ monotone variance, corpus-wide
    var checked = 0
    for rec <- Corpus.load(200); m <- Matching.freeMentions(rec.prog) do
      checked += 1
      if AgnosticPipeline.monotoneInMention(rec.prog, m) then
        assert(Variance.of(rec.prog, m).monotone,
               s"monotoneInMention accepts but variance says ${Variance.of(rec.prog, m).show}: ${rec.prog.show.take(200)}")
    println(s"DELTA: variance agrees with monotoneInMention on $checked (program, mention) pairs")
  }

  // ---- 2. acceptance, rejection, unsupported ---------------------------------------------------------

  test("ACCEPTED: positive mutual recursion, as a passthrough Call SCC, lowers to one two-equation system") {
    val ev = RoutinePtr("ev"); val od = RoutinePtr("od"); val g = SpaceMention("g"); val acc = SpaceMention("acc")
    val evR = Routine(ev, Vector.empty, Vector(g, acc),
      Space.Union(Space.Restriction(Space.Mention(acc), Space.Mention(g)), Space.Call(od, Vector.empty, Vector(Space.Mention(g), Space.Mention(acc)))))
    val odR = Routine(od, Vector.empty, Vector(g, acc),
      Space.Union(Space.TailsUnion(Space.Mention(acc)), Space.Call(ev, Vector.empty, Vector(Space.Mention(g), Space.Mention(acc)))))
    val term = Space.Call(ev, Vector.empty, Vector(S0, S1))
    val low = accepted(DeltaIR.lower(term, Syntax.mod(evR, odR)))
    assertEquals(low.systems.length, 1)
    assertEquals(low.systems.head.eqs.length, 2)
    assert(low.systems.head.routines.keySet == Set(ev, od))
    assert(low.graph.sccs.exists(s => s.recursive && s.certified && s.nodes.length == 2))
    println(DeltaIRRender.render(Verdict.Accepted(low)))
    // and it RUNS, both schedules, agreeing with the reference `lowerCalls` semantics
    val (top, residual) = lowerCalls(Routine(RoutinePtr("m"), Vector.empty, Vector(s0, s1), term), Syntax.mod(evR, odR))
    assert(residual.isEmpty)
    val ref = eval(top)(using PathContextMap(Map.empty), env(s0 -> words, s1 -> sv(p("a", "b", "c", "d"), p("q"))), PartialFunction.empty)
    val (vN, _) = Exec.run(low, Schedule.Naive, env(s0 -> words, s1 -> sv(p("a", "b", "c", "d"), p("q"))))
    val (vD, sols) = Exec.run(low, Schedule.Delta, env(s0 -> words, s1 -> sv(p("a", "b", "c", "d"), p("q"))), verify = true)
    assertEquals(vN, ref); assertEquals(vD, ref)
    println(s"DELTA: mutual SCC solved — ${sols.map(_.show).mkString(" | ")}")
  }

  test("ACCEPTED: a negative dependency on a LOWER stratum is a frozen input, not a rejection") {
    // the outer closure subtracts the value of an inner, independent closure: `-` edge across strata
    val inner = Space.Fixpoint(S1, q, Space.Union(Q, Space.TailsUnion(Q)))
    val outer = Space.Fixpoint(S0, r, Space.Subtraction(Space.Union(R, Space.TailsUnion(R)), inner))
    val low = accepted(DeltaIR.lower(outer))
    assertEquals(low.systems.length, 2)
    val strata = low.systems.map(_.stratum)
    assert(strata(0) < strata(1), s"the inner system must be the lower stratum: $strata")
    val neg = low.graph.edges.filter(_.variance == Variance.Neg)
    assert(neg.nonEmpty && neg.forall(e => low.graph.stratumOf(e.from) > low.graph.stratumOf(e.to)),
           s"every `-` edge points down a stratum: ${neg.map(_.show)}")
    val ctx = env(s0 -> words, s1 -> sv(p("a", "b", "c", "d")))
    val ref = eval(outer)(using PathContextMap(Map.empty), ctx, PartialFunction.empty)
    val (vD, _) = Exec.run(low, Schedule.Delta, ctx, verify = true)
    assertEquals(vD, ref)
    println(DeltaIRRender.render(Verdict.Accepted(low)))
  }

  test("REJECTED: a cycle through a `-` or a `0` edge is outside the certified language") {
    val negSelf = Space.Fixpoint(S0, r, Space.Subtraction(S1, R))
    DeltaIR.lower(negSelf) match
      case Verdict.Rejected(_, off) => assert(off.exists(_.variance == Variance.Neg), off.map(_.show).toString)
      case other => fail(s"expected REJECTED: ${other.show}")
    // both a positive and a negative occurrence: unknown, still a rejection
    val mixedSelf = Space.Fixpoint(S0, r, Space.Union(R, Space.Subtraction(S1, R)))
    DeltaIR.lower(mixedSelf) match
      case Verdict.Rejected(_, off) => assert(off.exists(_.variance == Variance.Zero), off.map(_.show).toString)
      case other => fail(s"expected REJECTED: ${other.show}")
    val unkSelf = Space.Fixpoint(S0, r, Space.Union(R, Space.Range(R, 0, 1)))
    DeltaIR.lower(unkSelf) match
      case Verdict.Rejected(_, off) => assert(off.exists(_.variance == Variance.Zero))
      case other => fail(s"expected REJECTED: ${other.show}")
    val tiSelf = Space.Fixpoint(S0, r, Space.Union(R, Space.TailsIntersection(R)))
    assert(DeltaIR.lower(tiSelf).isInstanceOf[Verdict.Rejected], "TailsIntersection of the recursion variable")
    // a negative MUTUAL cycle
    val ev = RoutinePtr("ev"); val od = RoutinePtr("od"); val g = SpaceMention("g"); val acc = SpaceMention("acc")
    val evR = Routine(ev, Vector.empty, Vector(g, acc), Space.Union(Space.Mention(acc), Space.Call(od, Vector.empty, Vector(Space.Mention(g), Space.Mention(acc)))))
    val odR = Routine(od, Vector.empty, Vector(g, acc), Space.Subtraction(Space.Mention(g), Space.Call(ev, Vector.empty, Vector(Space.Mention(g), Space.Mention(acc)))))
    DeltaIR.lower(Space.Call(ev, Vector.empty, Vector(S0, S1)), Syntax.mod(evR, odR)) match
      case Verdict.Rejected(gph, off) =>
        assert(off.exists(e => e.variance == Variance.Neg && e.from == DepNode.Rout(od)), off.map(_.show).toString)
        println(gph.show)
      case other => fail(s"expected REJECTED: ${other.show}")
    // a `-` edge in a NON-recursive position is fine: s0 \ fixpoint is not a cycle
    accepted(DeltaIR.lower(Space.Subtraction(S0, Space.Fixpoint(S1, r, Space.Union(R, Space.TailsUnion(R))))))
  }

  test("UNSUPPORTED (not rejected): an argument-changing recursive Call component is not a finite system") {
    // datalog's semi-naive routine: `all` and `delta` change across the call
    def join(rr: Space, s: Space): Space = rr.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
    val snTC = Routine(RoutinePtr("sn_tc"), Vector.empty, Vector(SpaceMention("e"), SpaceMention("all"), SpaceMention("delta")),
                       S"all" \/ Space.Call(RoutinePtr("sn_tc"), Vector.empty,
                         Vector(S"e", S"all" \/ (join(S"delta", S"e") \ S"all"), join(S"delta", S"e") \ S"all")))
    DeltaIR.lower(Space.Call(RoutinePtr("sn_tc"), Vector.empty, Vector(S0, S0, S0)), Syntax.mod(snTC)) match
      case Verdict.Unsupported(_, why) => assert(why.contains("passthrough"), why); println(s"DELTA: $why")
      case other => fail(s"expected UNSUPPORTED: ${other.show}")
  }

  // ---- 3. naive vs delta, round for round --------------------------------------------------------------

  test("naive and delta execution agree at EVERY round boundary and on the stationary result") {
    val fixtures: Vector[(String, Space, SpaceContext)] = Vector(
      ("transitive closure", Space.Fixpoint(S0, r, hop(R)), env(s0 -> edges)),
      ("suffix closure", Space.Fixpoint(S0, r, Space.Union(R, Space.TailsUnion(R))), env(s0 -> words)),
      ("nonlinear: r ∩ (tails r · r)", Space.Fixpoint(S0, r, Space.Intersection(Space.Union(R, Space.TailsUnion(R)), Space.Composition(Space.TailsUnion(R), Space.Union(R, S1)))),
        env(s0 -> words, s1 -> sv(p("d"), p("c", "d")))),
      ("restriction both sides", Space.Fixpoint(S0, r, Space.Restriction(Space.Union(R, Space.TailsUnion(R)), Space.Union(R, Space.TailsUnion(R)))), env(s0 -> words)),
      ("new heads per round", Space.Fixpoint(S0, r,
        Space.Iteration(R, PathRef("h").known(1), SpaceMention("t"), Space.Union(Space.Mention(SpaceMention("t")), Space.Wrap(Space.Mention(SpaceMention("t")), Path.Deref(PathRef("h").known(1)))))),
        env(s0 -> sv(p("a", "b"), p("c")))),
      ("frozen subtrahend", Space.Fixpoint(S0, r, Space.Subtraction(Space.Union(R, Space.TailsUnion(R)), S1)), env(s0 -> words, s1 -> sv(p("b", "c", "d")))),
      ("stationary at once", Space.Fixpoint(S0, r, R), env(s0 -> words)),
      ("empty init", Space.Fixpoint(Space.Empty, r, Space.Union(R, S0)), env(s0 -> words)))
    for (name, fx, ctx) <- fixtures do
      val low = accepted(DeltaIR.lower(fx))
      val ref = eval(fx)(using PathContextMap(Map.empty), ctx, PartialFunction.empty)
      val (vN, sN) = Exec.run(low, Schedule.Naive, ctx)
      val (vD, sD) = Exec.run(low, Schedule.Delta, ctx, verify = true)     // verify: step equation at every round + per-round equality
      assertEquals(vN, ref, name); assertEquals(vD, ref, name)
      assertEquals(sN.map(_.rounds.map(_.acc)), sD.map(_.rounds.map(_.acc)), s"$name: accumulators differ at a round boundary")
      // the delta schedule's per-round deltas are exactly the naive `new` sets
      assertEquals(sN.map(_.rounds.map(_.delta)), sD.map(_.rounds.map(_.delta)), s"$name: deltas differ")
      // provenance: the round that introduced each element is the first round it appears in
      for sol <- sD; (v, intro) <- sol.introducedAt; (e, n) <- intro do
        assert(sol.rounds(n).acc(v).paths.contains(e) && (n == 0 || !sol.rounds(n - 1).acc(v).paths.contains(e)), s"$name: provenance of ${e.show}")
      println(f"DELTA: $name%-30s ${sD.head.rounds.length} rounds, |result|=${ref.paths.size}; ${sD.head.show.take(120)}")
  }

  test("the step equation is checked at run time, and a wrong differential would be caught") {
    // a body whose differential the transfer handles incrementally: the run-time check passes …
    val fx = Space.Fixpoint(S0, r, Space.Union(R, Space.Composition(Space.TailsUnion(R), S1)))
    val ctx = env(s0 -> sv(p("a", "b")), s1 -> sv(p("k")))
    val low = accepted(DeltaIR.lower(fx))
    Exec.run(low, Schedule.Delta, ctx, verify = true)
    // … and a deliberately WRONG differential (dropping the mixed term) violates it: modelled by feeding
    // the delta of only ONE operand of a composition where both change
    val bothChange = Space.Composition(Space.TailsUnion(R), R)
    val old = env(r -> sv(p("a", "b")))
    val nw = env(r -> sv(p("a", "b"), p("c", "d")))
    val full = eval(bothChange)(using PathContextMap(Map.empty), nw, PartialFunction.empty).paths
    val oldV = eval(bothChange)(using PathContextMap(Map.empty), old, PartialFunction.empty).paths
    val d = Delta.dden(bothChange, Set(r), old, nw, PathContextMap(Map.empty), PartialFunction.empty)
    assert(full.subsetOf(oldV union d), "D1: new ⊆ old ∪ dden")
    assert(d.subsetOf(full), "D2: dden ⊆ new")
    // the naive "substitute the delta everywhere" is NOT sound here: tails(Δ) · Δ misses tails(Δ) · old
    val deltaOnly = eval(bothChange)(using PathContextMap(Map.empty), env(r -> sv(p("c", "d"))), PartialFunction.empty).paths
    assert(!full.subsetOf(oldV union deltaOnly), "replacing every occurrence by the delta drops the mixed terms")
    println(s"DELTA: composition both-change — full ${full.size}, old ${oldV.size}, dden ${d.size}, delta-only ${deltaOnly.size}")
  }

  // ---- 4. Call SCC vs explicit Fixpoint: the same IR -------------------------------------------------------

  test("a recursive Call written as `r(m) = m ∪ r(next m)` and the explicit Fixpoint lower to the SAME equations") {
    val next = Space.Union(R, Space.TailsUnion(R))
    val asRoutine = Routine(RoutinePtr("suf"), Vector.empty, Vector(r), Space.Union(R, Space.Call(RoutinePtr("suf"), Vector.empty, Vector(Space.TailsUnion(R)))))
    val viaCall = accepted(DeltaIR.lower(Space.Call(RoutinePtr("suf"), Vector.empty, Vector(S0)), Syntax.mod(asRoutine)))
    val viaFix = accepted(DeltaIR.lower(Space.Fixpoint(S0, r, Space.TailsUnion(R))))
    assertEquals(viaCall.systems.length, 1); assertEquals(viaFix.systems.length, 1)
    println(s"DELTA: via call     ${viaCall.systems.head.show}\nDELTA: via fixpoint ${viaFix.systems.head.show}")
    assertEquals(viaCall.canonical, viaFix.canonical, "the same IR: alpha-equal term and equations under one renaming")
    val ctx = env(s0 -> words)
    val ref = eval(Space.Call(RoutinePtr("suf"), Vector.empty, Vector(S0)))(using PathContextMap(Map.empty), ctx, Syntax.mod(asRoutine))
    assertEquals(Exec.run(viaCall, Schedule.Delta, ctx, verify = true)._1, ref)
    assertEquals(Exec.run(viaFix, Schedule.Delta, ctx, verify = true)._1, ref)
    println(DeltaIRRender.render(Verdict.Accepted(viaCall)))
  }

  // ---- 5. premises ---------------------------------------------------------------------------------------------

  test("every accepted instance carries replayable, Lean-backed premises") {
    val fx = Space.Fixpoint(S0, r, Space.Subtraction(hop(R), Space.Fixpoint(S1, q, Space.Union(Q, Space.TailsUnion(Q)))))
    val low = accepted(DeltaIR.lower(fx))
    assert(low.premises.theorems.nonEmpty)
    for t <- low.premises.theorems do
      val Array(file, thm) = t.split("#", 2)
      assert(new java.io.File(Loaders.repoRoot, file).exists, s"the cited Lean file must exist: $file")
      val text = scala.io.Source.fromFile(new java.io.File(Loaders.repoRoot, file)).mkString
      val short = thm.split('.').last
      val declared = ("(theorem|lemma)\\s+([A-Za-z_][A-Za-z0-9_']*\\.)*" + java.util.regex.Pattern.quote(short) + "\\b").r
      assert(declared.findFirstIn(text).isDefined, s"$file must state $short")
    // replay: the labels are recomputed from the term, not remembered
    assert(low.premises.replay(accepted(DeltaIR.lower(fx)).graph.edges), "replaying the variance labels reproduces them")
    assert(!low.premises.replay(low.graph.edges.map(e => e.copy(variance = Variance.Zero))), "a tampered label set does not replay")
    println(low.premises.show)
  }

  test("the six cornerstones through the IR: what lowers, what is unsupported, and the schedules agree") {
    val puz = Sliding.puzzle(3, 3)
    val queens = NQueens.board(4)
    val live = Set((1, 0), (1, 1), (1, 2)); val golRules = GoL.rulesFor(live)
    def join(rr: Space, s: Space): Space = rr.iter(P"n", S"nbs", P"n" x \/(s <| S"nbs"))
    val snTC = Routine(RoutinePtr("sn_tc"), Vector.empty, Vector(SpaceMention("e"), SpaceMention("all"), SpaceMention("delta")),
                       S"all" \/ Space.Call(RoutinePtr("sn_tc"), Vector.empty,
                         Vector(S"e", S"all" \/ (join(S"delta", S"e") \ S"all"), join(S"delta", S"e") \ S"all")))
    val cases: Vector[(String, Space, PartialFunction[RoutinePtr, Routine], SpaceContext)] = Vector(
      ("aunt", Routines.aunt_query_routine.body, Syntax.mod(Routines.child_routine), AuntQuery.context),
      ("gol", Space.Call(RoutinePtr("nextStep"), Vector.empty, Vector(Space.Mention(SpaceMention("field")))), golRules.defs, env(SpaceMention("field") -> GoL.field(live))),
      ("puzzle3x3-step", puz.expandStep(Space.Mention(SpaceMention("frontier"))), puz.defs, env(SpaceMention("frontier") -> sv(puz.initial))),
      ("nqueens4", queens.program, queens.defs, env()),
      ("datalog-sn", Space.Call(RoutinePtr("sn_tc"), Vector.empty, Vector(S"edges", S"edges", S"edges")), Syntax.mod(snTC), env(SpaceMention("edges") -> sv(p("0", "1"), p("1", "2"), p("2", "3")))),
      ("puzzle2x2-reachable", {
        val p2 = Sliding.puzzle(2, 2)
        val rec = SpaceMention("reach")
        Space.Fixpoint(Space.Singleton(Path.Constant(p2.initial)), rec, Space.Union(Space.Mention(rec), p2.expandStep(Space.Mention(rec))))
      }, Sliding.puzzle(2, 2).defs, env()))
    for (name, term, rc, ctx) <- cases do
      DeltaIR.lower(term, rc) match
        case Verdict.Accepted(low) =>
          val ref = eval(term)(using PathContextMap(Map.empty), ctx, rc)
          val t0 = java.lang.System.nanoTime()
          val (vD, sols) = Exec.run(low, Schedule.Delta, ctx, verify = true)
          val (vN, _) = Exec.run(low, Schedule.Naive, ctx)
          assertEquals(vD, ref, name); assertEquals(vN, ref, name)
          println(f"DELTA: $name%-22s ACCEPTED ${low.systems.length} system(s), ${sols.map(_.rounds.length).sum} rounds, ${(java.lang.System.nanoTime() - t0) / 1e6}%.0f ms")
        case Verdict.Unsupported(_, why) => println(f"DELTA: $name%-22s UNSUPPORTED — ${why.take(100)}")
        case Verdict.Rejected(_, off) => fail(s"$name rejected: ${off.map(_.show)}")
  }
