package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

class MatchingProcessTest extends FunSuite:
  import Space.*
  import Matching.*

  test("free variables respect Iteration and Fold binders") {
    val iter = S"xs".iter(P"h", S"tail", P"h" x S"tail" x S"outside")
    assertEquals(freeMentions(iter).map(_.s), Set("xs", "outside"))
    assert(!freeRefs(iter).exists(_.s == "h"))

    val fold = S"xs".fold("z", "acc", "h", "tail", P"acc" x P"h" x S"tail" x S"outside", P"acc" x P"h")
    assertEquals(freeMentions(fold).map(_.s), Set("xs", "outside"))
    assert(!freeRefs(fold).exists(pr => pr.s == "acc" || pr.s == "h"))
  }

  test("substitution avoids capture by iteration binders") {
    val term = Space.Iteration(
      Space.Literal(SpaceValue("a.tail")),
      PathRef("h").known(1),
      SpaceMention("r"),
      S"x" x S"r"
    )
    val substituted = Matching.subst(term, sm = Map(SpaceMention("x") -> S"r"))
    val got = eval(substituted)(using sc = SpaceContextMap(Map(SpaceMention("r") -> SpaceValue("EXT"))))
    assertEquals(got, SpaceValue("EXT.tail"))
  }

  test("canonicalization makes alpha-equivalent Fold terms equal") {
    val left = S"xs".fold("z", "acc", "h", "tail", P"acc" x P"h" x S"tail", P"acc" x P"h")
    val right = S"xs".fold("z", "a2", "x2", "rest2", P"a2" x P"x2" x S"rest2", P"a2" x P"x2")
    assert(alphaEqual(left, right), s"\n${canon(left).show}\n${canon(right).show}")
  }

  test("instance matching folds simple renamings but refuses cyclic growth") {
    val simple = instanceOf(R"f"(S"x"), R"f"(S"y"))
    assert(simple.nonEmpty)
    assertEquals(simple.get._1(SpaceMention("x")), S"y")

    val growing = instanceOf(R"f"(S"x"), R"f"(S"x" \/ S"delta"))
    assertEquals(growing, None)
  }

  test("MSG skeleton reinstantiates both sides") {
    val small: Space = R"f"(S"acc")
    val grown: Space = R"f"(S"acc" \/ S"delta")
    assert(embeds(small, grown))
    val g = msg(small, grown)
    assertEquals(Matching.subst(g.skeleton, g.lsm, g.lpm).show, canon(small).show)
    assertEquals(Matching.subst(g.skeleton, g.rsm, g.rpm).show, canon(grown).show)
  }

  test("grounded nodes match only by stable function identity") {
    val same: SpaceValue => SpaceValue = identity
    val other: SpaceValue => SpaceValue = identity
    val pattern = Space.GroundedSS(S"x", same)
    assert(instanceOf(pattern, Space.GroundedSS(S"y", same)).nonEmpty)
    assertEquals(instanceOf(pattern, Space.GroundedSS(S"y", other)), None)
  }

class SupercompilerProcessTest extends FunSuite:
  import Space.*
  import Unification.MQT

  private def evalResidual(res: Residual, sc: SpaceContext = SpaceContextMap(Map.empty)): SpaceValue =
    eval(res.top)(using PathContext.emptyMap, sc, res.env)

  private val edges = SpaceValue("edge.a.b", "edge.b.c", "edge.c.d")

  private val semiNaive = DatalogExample.semiNaiveTransitive
  private val semiNaiveDefs: PartialFunction[RoutinePtr, Routine] = { case semiNaive.name => semiNaive }

  test("positive SC terminates and stays sound on semi-naive transitive closure") {
    val initial = DatalogExample.semiNaiveInitial(Literal(edges))
    val call = semiNaive.name(initial)
    val res = SC.supercompile(call, semiNaiveDefs, SC.Config(maxNodes = 100, maxDepth = 80))
    val got = evalResidual(res)
    val original = eval(call)(using rc = semiNaiveDefs)
    assertEquals(got, original)
    assert(res.routines.nonEmpty)
    assert(res.report.unfolds > 0)
  }

  test("whistle/generalization is necessary for symbolic growing reachability") {
    val reach = R"reach"(S"edges", S"all", S"delta") :=
      S"all" \/ R"reach"(S"edges",
        S"all" \/ (S"delta".iter(P"n", S"nbs", P"n" x \/(S"edges" <| S"nbs")) \ S"all"),
        S"delta".iter(P"n", S"nbs", P"n" x \/(S"edges" <| S"nbs")) \ S"all")
    val defs = mod(reach)
    val entry = R"reach"(S"edges", Space.Literal(SpaceValue("a.b")), Space.Literal(SpaceValue("a.b")))

    val noWhistle = intercept[RuntimeException] {
      SC.supercompile(entry, defs, SC.Config(maxNodes = 8, maxDepth = 8, generalize = false))
    }
    assert(noWhistle.getMessage.contains("cap"))

    val res = SC.supercompile(entry, defs, SC.Config(maxNodes = 100, maxDepth = 80, generalize = true))
    assert(res.report.whistles > 0)
    assert(res.report.generalizations > 0)
    assert(res.routines.values.exists(r => collect(r.body)({ case Space.Call(rp, _, _) if rp == r.name => () })._1.nonEmpty))

    given SpaceContext = SpaceContextMap(Map(SpaceMention("edges") -> SpaceValue("a.b", "b.c", "c.d")))
    val got = evalResidual(res, summon[SpaceContext])
    val original = eval(entry)(using PathContext.emptyMap, summon[SpaceContext], defs)
    assertEquals(got, original)
  }

  test("generalization keeps residual control size independent of static graph size") {
    val small = SpaceValue("edge.a.b", "edge.b.c")
    val big = SpaceValue((0 until 30).map(i => Syntax.parse(s"edge.$i.${i + 1}")).toSet)

    case class ControlShape(routines: Int, nodes: Int, calls: Int, iterations: Int, literals: Int)

    def residualControlShape(es: SpaceValue): ControlShape =
      val initial = DatalogExample.semiNaiveInitial(Literal(es))
      val res = SC.supercompile(semiNaive.name(initial), semiNaiveDefs, SC.Config(maxNodes = 100, maxDepth = 80))
      val stats = res.routines.values.map(r => Supercompiler.stats(r.body)).foldLeft(Supercompiler.stats(res.top))(_ + _)
      ControlShape(res.routines.size, stats.totalNodes, stats.calls, stats.iterations, stats.literals)

    assertEquals(residualControlShape(small), residualControlShape(big))
  }
