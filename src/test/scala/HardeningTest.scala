import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Tests for the soundness/robustness hardening called for in critique_on_b.md. */
class SCHardening extends FunSuite:
  import Space.*
  import Matching.*

  // B1 — capture-avoiding substitution: a substituted term whose free var collides with a
  // binder must NOT be captured; the binder is alpha-renamed instead.
  test("subst is capture-avoiding (alpha-renames a colliding binder)") {
    val it: Space = Space.Iteration(Mention(SpaceMention("src")), PathRef("p"), SpaceMention("r"),
      Union(Mention(SpaceMention("x")), Mention(SpaceMention("r"))))
    assertEquals(freeMentions(it), Set(SpaceMention("src"), SpaceMention("x")))
    // substitute x := S"r"; the inserted r must remain FREE (not captured by the binder)
    val out = subst(it, sm = Map(SpaceMention("x") -> Mention(SpaceMention("r"))))
    assertEquals(freeMentions(out), Set(SpaceMention("src"), SpaceMention("r")),
      s"inserted S\"r\" was captured: ${out.show}")
  }

  // B2 — reserved name prefixes are rejected at the entry point.
  test("reserved name prefixes are rejected") {
    val bad: Space = R"f"(Mention(SpaceMention("#g0")))
    val ex = intercept[RuntimeException](SC.supercompile(bad, PartialFunction.empty))
    assert(ex.getMessage.contains("reserved"), ex.getMessage)
  }

  // B3 — Fold is treated structurally by alpha-equality, instance matching, and msg.
  test("Fold is matching/msg aware") {
    def fold(src: String, init: String): Space =
      Space.Fold(Mention(SpaceMention(src)), Path.Constant(init), PathRef("a"), PathRef("h"),
        SpaceMention("t"), Union(sP"a", Mention(SpaceMention("t"))), P"a" x P"h")
    assert(alphaEqual(fold("s", "0"), fold("s", "0")))
    assert(instanceOf(fold("s", "0"), fold("s", "0")).isDefined)
    val g = msg(fold("s1", "0"), fold("s2", "0"))
    assert(!g.isTrivial && g.skeleton.isInstanceOf[Space.Fold], s"${g.skeleton.show}")
  }

  // B4 — grounded nodes couple/match only when they are the SAME host operation.
  test("grounded nodes are keyed by operation identity") {
    val f: SpaceValue => SpaceValue = sv => sv
    val h: SpaceValue => SpaceValue = sv => SpaceValue(sv.paths)
    val af: Space = GroundedSS(Mention(SpaceMention("x")), f)
    val af2: Space = GroundedSS(Mention(SpaceMention("y")), f) // same op f, different arg
    val ah: Space = GroundedSS(Mention(SpaceMention("x")), h) // different op
    assert(embeds(af, af2), "same op should couple")
    assert(!embeds(af, ah), "different op must not couple")
    assert(instanceOf(af, af2).isDefined, "same op, arg is a renaming/instance")
    assert(instanceOf(af, ah).isEmpty, "different op is not an instance")
  }

  // B5 — the embedding heuristic is a documented choice; both modes behave as specified.
  test("literalsAreAtoms heuristic toggles literal coupling") {
    val a: Space = R"f"(s("a"))
    val b: Space = R"f"(s("a", "b"))
    assert(embeds(a, b, litAtoms = true), "atoms: growing literal embeds")
    assert(!embeds(a, b, litAtoms = false), "structural: distinct literals do not embed")
    assert(!msg(a, b, litAtoms = true).isTrivial, "atoms: msg abstracts the literal")
  }

  // B6 — instanceOf binds a parameter to a term containing that parameter (the recurrence),
  // applied exactly once; folding such a configuration stays sound.
  test("instanceOf self-occurrence (the recurrence) is exact") {
    val pat: Space = R"f"(S"acc")
    val term: Space = R"f"(S"acc" \/ S"delta")
    val Some((sm, _)) = instanceOf(pat, term): @unchecked
    assertEquals(sm(SpaceMention("acc")), (S"acc" \/ S"delta"): Space)
  }

  // B8 — generalization is deterministic: alpha-renamed inputs give the same residual shape.
  test("supercompilation is stable under input renaming") {
    val r1 = R"reach"(S"edges", S"frontier") :=
      S"frontier" \/ R"reach"(S"edges", S"edges" <| S"frontier")
    val r2 = R"reach"(S"E", S"F") :=
      S"F" \/ R"reach"(S"E", S"E" <| S"F")
    val n1 = SC.supercompile(r1, Syntax.mod(r1)).routines.size
    val n2 = SC.supercompile(r2, Syntax.mod(r2)).routines.size
    assertEquals(n1, n2)
  }

/** Tests for the report-bearing facade and operation-graph lowering of residuals. */
class SCFacade extends FunSuite:
  import Space.*

  test("compileRoutine yields a report and an eval-sound residual") {
    val defs = Syntax.mod(Routines.transitive_routine)
    val prog = Supercompiler.compileRoutine(Routines.transitive_routine, defs)
    assert(prog.report.summary.nonEmpty)
    assert(prog.report.unfoldings >= 1, prog.report.summary)
    val edges = eval(Space.Mention(SpaceMention("g1")).apply(Path.Constant("edge")))(using sc = Graphs.scc_context)
    val ctx = SpaceContextMap(Map(SpaceMention("edges") -> edges))
    val got = eval(prog.top)(using PathContextMap(Map.empty), ctx, prog.env)
    val orig = eval(Space.Call(RoutinePtr("transitive"), Vector(), Vector(Space.Literal(edges))))(using rc = defs)
    assertEquals(got, orig)
  }

  test("compileCall flags compile-time evaluation on fully static input") {
    // a closed relational computation reduces to its answer at supercompile time
    val call = Space.Restriction(Space.Literal(SpaceValue("Foo.a", "Foo.b", "Bar.c")), ss"Foo")
    val prog = Supercompiler.compileCall(call)
    assert(prog.report.compileTimeEvaluated, prog.report.summary)
    assertEquals(prog.evaluate, eval(call))
  }

  test("specialize bakes static data away and stays sound") {
    val defs = Syntax.mod(Routines.aunt_query_routine)
    val prog = Supercompiler.specialize(Routines.aunt_query_routine,
      spaceArgs = Map(SpaceMention("family") -> Space.Literal(AuntQuery.context.resolve(SpaceMention("family")))), defs = defs)
    val entry = prog.routines(prog.top.asInstanceOf[Space.Call].r)
    assert(!entry.mentions.exists(_.s == "family"), s"family not specialized away: ${entry.mentions}")
    val sc = SpaceContextMap(Map(SpaceMention("people") -> AuntQuery.context.resolve(SpaceMention("people"))))
    assertEquals(eval(prog.top)(using PathContextMap(Map.empty), sc, prog.env),
                 SpaceValue("Aunt.Ann.Liz", "Aunt.Jim.Ann", "Aunt.Pat.Liz"))
  }

  // property-based: on many random small graphs, the supercompiled transitive-closure residual
  // agrees with an independent reference closure (eval-agreement under varied data).
  test("property: SC residual of TC matches reference on random graphs") {
    val rnd = new scala.util.Random(1234)
    val defs = Syntax.mod(Routines.transitive_routine)
    def refTC(es: Set[(Int, Int)]): Set[(Int, Int)] =
      var s = es; var grew = true
      while grew do { val a = for (x, y) <- s; (c, d) <- s if y == c yield (x, d); val n = s ++ a; grew = n.size != s.size; s = n }
      s
    for _ <- 0 until 25 do
      val n = 2 + rnd.nextInt(4)
      val es = (0 until (n + rnd.nextInt(n * 2))).map(_ => (rnd.nextInt(n), rnd.nextInt(n))).toSet
      val edges = SpaceValue(es.map((a, b) => PathValue(List(PathItem.Symbol(a.toString), PathItem.Symbol(b.toString)))))
      val res = SC.supercompile(Space.Call(RoutinePtr("transitive"), Vector(), Vector(Space.Literal(edges))), defs)
      val got = eval(res.top)(using PathContextMap(Map.empty), SpaceContextMap(Map.empty), res.env).paths
        .map(p => (p.items(0), p.items(1)) match { case (PathItem.Symbol(a), PathItem.Symbol(b)) => (a.toInt, b.toInt) })
      assertEquals(got, refTC(es), s"mismatch on edges=$es")
  }

  // L3 — a backend-supported residual lowers to an operation graph and `exec` agrees with eval.
  test("residual lowers to an operation graph and exec agrees with eval") {
    val prog = Supercompiler.compileRoutine(Routines.union_iter_routine, Syntax.mod(Routines.union_iter_routine))
    assert(prog.report.backendUnsupported.isEmpty, s"unexpected unsupported: ${prog.report.backendUnsupported}")
    assert(prog.graphs.nonEmpty, "expected operation-graph lowerings")
    // exec the entry residual graph and compare to eval on a concrete input
    val entryRp = prog.top.asInstanceOf[Space.Call].r
    val code = prog.graphs(entryRp)
    val xs = SpaceValue("a.1", "b.foo"); val ys = SpaceValue("a.2", "c.bar")
    val stack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](code.nodes.length))
    stack.top(0) = xs; stack.top(1) = ys
    exec(code, stack)
    val viaGraph = stack.top.last.asInstanceOf[SpaceValue]
    val viaEval = eval(prog.top)(using PathContextMap(Map.empty),
      SpaceContextMap(Map(SpaceMention("xs") -> xs, SpaceMention("ys") -> ys)), prog.env)
    assertEquals(viaGraph, viaEval)
  }

  // compile time must be bounded and ACCOUNTED separately from runtime.
  test("compile is time-bounded: a tiny budget falls back gracefully and stays sound") {
    val defs = Syntax.mod(Routines.transitive_routine)
    val edges = SpaceValue("a.b", "b.c", "c.d", "d.e", "e.f")
    val call = Space.Call(RoutinePtr("transitive"), Vector(), Vector(Space.Literal(edges)))
    // a sub-microsecond budget expires on the first driven Call -> graceful fallback, not a hang/crash
    val prog = Supercompiler.compileCall(call, defs, SC.Config(compileBudgetMs = 1e-5))
    assert(!prog.report.converged, s"expected budget fallback, got: ${prog.report.summary}")
    assertEquals(prog.evaluate, eval(call)(using rc = defs), "budget fallback must still evaluate correctly")
    // and the unbounded compile DOES converge on the same input
    val full = Supercompiler.compileCall(call, defs)
    assert(full.report.converged)
    assertEquals(full.evaluate, eval(call)(using rc = defs))
  }

  test("optimization passes report both timing AND improvement") {
    val prog = Supercompiler.compileRoutine(Routines.union_iter_routine, Syntax.mod(Routines.union_iter_routine))
    val ph = prog.report.phaseMillis
    assert(prog.report.compileMillis > 0.0, "compile time not measured")
    assert(ph.contains("supercompile") && ph.contains("transpile"), s"missing phase times: ${ph.keys}")
    // the optimizer ran on this backend-supported residual, so its passes are individually accounted
    assert(ph.contains("push_out") && ph.contains("optimize_sharing"), s"optimizer passes not timed: ${ph.keys}")
    // and IMPROVEMENT is recorded: union_iter hoists loop-invariant constants out of its iterations
    assert(prog.report.phaseImprovement.getOrElse("push_out", 0L) > 0, s"push_out improvement not recorded: ${prog.report.phaseImprovement}")
    Loaders.note(s"[sc/timing] ${prog.report.timing}")
  }
end SCFacade
