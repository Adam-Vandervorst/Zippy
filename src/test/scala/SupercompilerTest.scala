package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

class SCMatching extends FunSuite:
  import Space.*
  import Matching.*

  test("freeMentions / freeRefs respect binders") {
    val s: Space = S"a" \/ (S"b" x S"a")
    assertEquals(freeMentions(s), Set(SpaceMention("a"), SpaceMention("b")))
    // Iteration binds symbol p and rest r
    val it = S"xs".iter(P"p", S"r", P"p" x S"r" x S"extern")
    assertEquals(freeMentions(it), Set(SpaceMention("xs"), SpaceMention("extern")))
    assert(!freeRefs(it).exists(_.s == "p"), s"p should be bound, got ${freeRefs(it)}")
  }

  test("subst substitutes free, shadows bound") {
    val s: Space = S"a" \/ S"b"
    val r = subst(s, sm = Map(SpaceMention("a") -> ss"X"))
    assertEquals(eval(r)(using sc = SpaceContextMap(Map(SpaceMention("b") -> SpaceValue("Y")))),
                 SpaceValue("X", "Y"))
    // binder shadows: substituting r inside iteration body must not touch bound r
    val it = S"xs".iter(P"p", S"r", S"r")
    assertEquals(subst(it, sm = Map(SpaceMention("r") -> ss"BOOM")).show, it.show)
  }

  test("canon makes alpha-equivalent iterations equal") {
    val a = S"xs".iter(P"p", S"r", P"p" x S"r")
    val b = S"xs".iter(P"q", S"t", P"q" x S"t")
    assert(alphaEqual(a, b), s"\n${canon(a).show}\n${canon(b).show}")
    val c = S"xs".iter(P"q", S"t", P"q" x S"t" x ss"extra")
    assert(!alphaEqual(a, c))
  }

  test("renaming detects bijective free-var renamings") {
    val a: Space = (S"x" /\ S"y") \ S"z"
    val b: Space = (S"p" /\ S"q") \ S"r"
    val Some((sm, _)) = renaming(a, b): @unchecked
    assertEquals(sm(SpaceMention("x")), SpaceMention("p"))
    assertEquals(sm(SpaceMention("z")), SpaceMention("r"))
    // not a renaming: 'x' would have to map to both p and q
    assertEquals(renaming((S"x" /\ S"x"): Space, (S"p" /\ S"q"): Space), None)
  }

  test("instanceOf finds folding substitution") {
    val pattern: Space = R"reach"(S"e", S"frontier")
    val term: Space = R"reach"(S"e", S"frontier" \/ S"delta")
    val Some((sm, _)) = instanceOf(pattern, term): @unchecked
    assertEquals(sm(SpaceMention("frontier")), (S"frontier" \/ S"delta"): Space)
    assert(sm.get(SpaceMention("e")).forall(_ == (S"e": Space)) || !sm.contains(SpaceMention("e")))
    // a more specific term is NOT an instance of a constant-bearing pattern
    assertEquals(instanceOf(ss"foo": Space, ss"bar": Space), None)
  }

  test("homeomorphic embedding: the whistle") {
    // accumulator growth should be flagged
    val small: Space = R"f"(S"acc")
    val grown: Space = R"f"(S"acc" \/ S"more")
    assert(embeds(small, grown), "f(acc) should embed in f(acc \\/ more)")
    // unrelated shapes do not embed
    assert(!embeds((S"a" /\ S"b"): Space, (S"a" \/ S"b"): Space))
    // a term embeds in itself
    assert(embeds(grown, grown))
  }

  test("msg generalizes growing argument") {
    val a: Space = R"f"(S"acc")
    val b: Space = R"f"(S"acc" \/ S"delta")
    val g = msg(a, b)
    assert(!g.isTrivial, "should not be a trivial generalization")
    // skeleton instantiated by left subst recovers a; by right subst recovers b
    assertEquals(Matching.subst(g.skeleton, g.lsm, g.lpm).show, canon(a).show)
    assertEquals(Matching.subst(g.skeleton, g.rsm, g.rpm).show, canon(b).show)
  }
end SCMatching

/** Driver: termination + soundness (residual eval-agrees with the original program). */
class SCDriver extends FunSuite:
  import Space.*

  def agree(routine: Routine, defs: PartialFunction[RoutinePtr, Routine],
            binds: Map[SpaceMention, SpaceValue], pbinds: Map[PathRef, PathValue] = Map.empty): Residual =
    val res = SC.supercompile(routine, defs)
    val sc = SpaceContextMap(binds)
    val pc = PathContextMap(pbinds)
    val orig = eval(Space.Call(routine.name, routine.refs.map(Path.Deref(_)), routine.mentions.map(Space.Mention(_))))(using pc, sc, defs)
    val got = eval(res.top)(using pc, sc, res.env)
    assertEquals(got, orig, s"\n--- residual ---\n${res.show}")
    res

  test("transitive closure: terminates + sound") {
    val defs = Syntax.mod(Routines.transitive_routine)
    val edges = eval(Space.Mention(SpaceMention("g1")).apply(Path.Constant("edge")))(using sc = Graphs.scc_context)
    val res = agree(Routines.transitive_routine, defs, Map(SpaceMention("edges") -> edges))
    assert(res.routines.nonEmpty, "should produce residual routines")
  }

  test("reachable (3-mention recursion): terminates + sound") {
    val defs = Syntax.mod(Routines.reachable_routine)
    val graph = eval(Space.Mention(SpaceMention("g2")).apply(Path.Constant("edge")))(using sc = Graphs.scc_context)
    import morkl.Syntax.*
    val transpose = eval(Space.Literal(graph).iter(P"x", S"r", S"r".iter(P"y", S"_", Singleton(P"y" x P"x"))))
    val nodes = eval(Space.Literal(graph).iter(P"fwd", S"_1", sP"fwd") \/ Space.Literal(transpose).iter(P"bwd", S"_2", sP"bwd"))
    agree(Routines.reachable_routine, defs,
      Map(SpaceMention("edges") -> graph, SpaceMention("nodemask") -> nodes, SpaceMention("reach") -> SpaceValue("t")))
  }

  test("aunt query (non-recursive pipeline): sound + fully driven") {
    val defs = Syntax.mod(Routines.aunt_query_routine)
    val res = agree(Routines.aunt_query_routine, defs,
      Map(SpaceMention("family") -> AuntQuery.context.resolve(SpaceMention("family")),
          SpaceMention("people") -> AuntQuery.context.resolve(SpaceMention("people"))))
    // sanity: the known aunt answer
    val got = eval(res.top)(using PathContextMap(Map.empty),
      SpaceContextMap(Map(SpaceMention("family") -> AuntQuery.context.resolve(SpaceMention("family")),
                          SpaceMention("people") -> AuntQuery.context.resolve(SpaceMention("people")))), res.env)
    assertEquals(got, SpaceValue("Aunt.Ann.Liz", "Aunt.Jim.Ann", "Aunt.Pat.Liz"))
  }

  test("predecessors (recursive helper): terminates + sound") {
    import morkl.Syntax.*
    val pred = R"predecessor_helper"(S"family", S"oldest", S"people") :=
      S"people" \/ R"predecessor_helper"(S"family",
        \/(S"family"("child") <| S"oldest"),
        S"people" \/ \/(S"family"("child") <| S"oldest"))
    val defs = Syntax.mod(pred)
    agree(pred, defs,
      Map(SpaceMention("family") -> AuntQuery.context.resolve(SpaceMention("family")),
          SpaceMention("oldest") -> SpaceValue("Ann"),
          SpaceMention("people") -> SpaceValue()))
  }

/** Generalization / whistle: prove the homeomorphic-embedding whistle is exercised,
 *  is necessary for termination on growing configurations, and yields a recursive loop. */
class SCGeneralization extends FunSuite:
  import Space.*

  // reachable with a concrete seed but symbolic graph: driving grows the frontier without
  // bound, so termination REQUIRES generalization of the accumulating argument.
  def reachEntry: Space =
    Space.Call(RoutinePtr("reachable"), Vector(), Vector(
      Space.Mention(SpaceMention("edges")), Space.Mention(SpaceMention("nodemask")),
      Space.Literal(SpaceValue("t"))))
  val defs = Syntax.mod(Routines.reachable_routine)

  test("whistle is NECESSARY: without generalization, driving diverges (hits the cap)") {
    // the symbolic frontier doubles each unfold, so driving never folds without the whistle
    val ex = intercept[RuntimeException] {
      SC.supercompile(reachEntry, defs, SC.Config(maxNodes = 12, maxDepth = 12, generalize = false))
    }
    assert(ex.getMessage.contains("cap"), s"expected a cap error, got: ${ex.getMessage}")
  }

  test("with generalization: terminates, yields a recursive loop, stays sound") {
    val res = SC.supercompile(reachEntry, defs, SC.Config(generalize = true))
    // a residual routine must call itself (the generalized loop)
    def selfRec(r: Routine): Boolean =
      val (calls, _) = collect(r.body)({ case Space.Call(rp, _, _) if rp == r.name => () })
      calls.nonEmpty
    assert(res.routines.values.exists(selfRec), s"expected a self-recursive residual:\n${res.show}")
    // and a residual routine must carry a generalized (variable) accumulator parameter
    assert(res.routines.values.exists(_.mentions.nonEmpty), "expected a generalized mention parameter")
    // soundness on a concrete graph (g2 from the SCC fixture)
    val graph = eval(Space.Mention(SpaceMention("g2")).apply(Path.Constant("edge")))(using sc = Graphs.scc_context)
    val sc = SpaceContextMap(Map(SpaceMention("edges") -> graph, SpaceMention("nodemask") -> graph))
    val got  = eval(res.top)(using PathContextMap(Map.empty), sc, res.env)
    val orig = eval(reachEntry)(using PathContextMap(Map.empty), sc, defs)
    assertEquals(got, orig)
  }

  test("generalization makes residual size independent of the data") {
    // the semi-naive TC residual has the same shape whether the graph has 3 or 17 edges
    val sn = R"sn_tc"(S"edges", S"all", S"delta") :=
      S"all" \/ R"sn_tc"(S"edges",
        S"all" \/ (S"delta".iter(P"n", S"nbs", P"n" x \/(S"edges" <| S"nbs")) \ S"all"),
        S"delta".iter(P"n", S"nbs", P"n" x \/(S"edges" <| S"nbs")) \ S"all")
    val snDefs = Syntax.mod(sn)
    def edges(es: Vector[(String, String)]) =
      SpaceValue(es.map((a, b) => PathValue(List(a, b))).toSet)
    def nodes(es: SpaceValue) = SC.supercompile(
      Space.Call(RoutinePtr("sn_tc"), Vector(), Vector(Space.Literal(es), Space.Literal(es), Space.Literal(es))),
      snDefs).routines.size
    val small = nodes(edges(Vector("a" -> "b", "b" -> "c")))
    val big   = nodes(edges(Vector.tabulate(30)(i => i.toString -> (i + 1).toString)))
    assertEquals(small, big, "residual node count should not grow with the data")
  }
