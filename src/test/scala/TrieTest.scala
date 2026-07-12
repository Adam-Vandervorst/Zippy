package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** The trie must be an exact, faster implementation of the reference Set[List[PathItem]]
 *  semantics. These tests pin trie ops against `eval`, and `evalT` against `eval`. */
class TrieOps extends FunSuite:
  import Space.*

  val rnd = new scala.util.Random(7)
  val alphabet = Vector("a", "b", "c", "0", "1", "x")
  def randPath(): PathValue = PathValue(List.fill(rnd.nextInt(4))(alphabet(rnd.nextInt(alphabet.size))))
  def randSV(): SpaceValue = SpaceValue((0 until rnd.nextInt(7)).map(_ => randPath()).toSet)
  def t(sv: SpaceValue): Trie = Trie.fromSpaceValue(sv)

  test("round-trip SpaceValue <-> Trie is identity") {
    for _ <- 0 until 200 do
      val sv = randSV()
      assertEquals(Trie.fromSpaceValue(sv).toSpaceValue, sv)
  }

  test("binary ops agree with the reference evaluator") {
    for _ <- 0 until 300 do
      val a = randSV(); val b = randSV()
      def ref(op: Space) = eval(op)
      assertEquals(Trie.union(t(a), t(b)).toSpaceValue, ref(Union(Literal(a), Literal(b))), "union")
      assertEquals(Trie.intersection(t(a), t(b)).toSpaceValue, ref(Intersection(Literal(a), Literal(b))), "intersection")
      assertEquals(Trie.subtraction(t(a), t(b)).toSpaceValue, ref(Subtraction(Literal(a), Literal(b))), "subtraction")
      assertEquals(Trie.composition(t(a), t(b)).toSpaceValue, ref(Composition(Literal(a), Literal(b))), "composition")
      assertEquals(Trie.restriction(t(a), t(b)).toSpaceValue, ref(Restriction(Literal(a), Literal(b))), "restriction")
      assertEquals(Trie.raffination(t(a), t(b)).toSpaceValue, ref(Raffination(Literal(a), Literal(b))), "raffination")
  }

  test("unary / prefix / tails ops agree with the reference") {
    for _ <- 0 until 300 do
      val a = randSV(); val p = randPath()
      assertEquals(Trie.wrap(p.items, t(a)).toSpaceValue, eval(Wrap(Literal(a), Path.Constant(p))), "wrap")
      assertEquals(Trie.unwrap(t(a), p.items).toSpaceValue, eval(Unwrap(Literal(a), Path.Constant(p))), "unwrap")
      assertEquals(Trie.tailsUnion(t(a)).toSpaceValue, eval(TailsUnion(Literal(a))), "tailsUnion")
      assertEquals(Trie.tailsIntersection(t(a)).toSpaceValue, eval(TailsIntersection(Literal(a))), "tailsIntersection")
  }

  test("join-all / meet-all agree with pairwise reduce") {
    for _ <- 0 until 200 do
      val ss = (0 to rnd.nextInt(5)).map(_ => randSV()).toVector
      val ts = ss.map(t)
      val joinRef = if ss.isEmpty then SpaceValue() else ss.reduce((x, y) => eval(Union(Literal(x), Literal(y))))
      assertEquals(Trie.joinAll(ts).toSpaceValue, joinRef, "join-all")
      if ts.nonEmpty then
        val meetRef = ss.reduce((x, y) => eval(Intersection(Literal(x), Literal(y))))
        assertEquals(Trie.meetAll(ts).toSpaceValue, meetRef, "meet-all")
  }

  test("zipper descend/ascend round-trips to the same trie") {
    for _ <- 0 until 100 do
      val tr = t(randSV())
      if tr.children.nonEmpty then
        val k = tr.children.keys.toVector(rnd.nextInt(tr.children.size))
        val z = Zipper(tr).descend(k).get
        assertEquals(z.ascend.get.root, tr)
        assertEquals(z.path, List(k))
  }

/** evalT (the direct trie evaluator) must agree with eval on the real example programs. */
class TrieEval extends FunSuite:
  import Space.*

  def agree(s: Space, tc: Map[SpaceMention, Trie] = Map.empty,
            rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
            pc: PathContext = PathContextMap(Map.empty)): Unit =
    val sc = SpaceContextMap(tc.map((k, v) => k -> v.toSpaceValue))
    assertEquals(evalT(s)(using pc, tc, rc).toSpaceValue, eval(s)(using pc, sc, rc))

  test("evalT == eval: aunt query over the fixture") {
    val fam = AuntQuery.context.resolve(SpaceMention("family"))
    val ppl = AuntQuery.context.resolve(SpaceMention("people"))
    agree(Space.Call(RoutinePtr("aunts"), Vector(), Vector(S"family", S"people")),
      tc = Map(SpaceMention("family") -> Trie.fromSpaceValue(fam), SpaceMention("people") -> Trie.fromSpaceValue(ppl)),
      rc = Syntax.mod(Routines.aunt_query_routine))
  }

  test("evalT == eval: semi-naive datalog TC (static graph)") {
    val sn = R"sn_tc"(S"edges", S"all", S"delta") :=
      S"all" \/ R"sn_tc"(S"edges",
        S"all" \/ (S"delta".iter(P"n", S"nbs", P"n" x \/(S"edges" <| S"nbs")) \ S"all"),
        S"delta".iter(P"n", S"nbs", P"n" x \/(S"edges" <| S"nbs")) \ S"all")
    val edges = SpaceValue("a.b", "b.c", "c.d", "d.e")
    agree(Space.Call(RoutinePtr("sn_tc"), Vector(), Vector(Literal(edges), Literal(edges), Literal(edges))),
      rc = Syntax.mod(sn))
  }

  test("evalT == eval: transitive closure (recursive routine)") {
    val edges = eval(Space.Mention(SpaceMention("g3")).apply(Path.Constant("edge")))(using sc = Graphs.scc_context)
    agree(Space.Call(RoutinePtr("transitive"), Vector(), Vector(Literal(edges))),
      rc = Syntax.mod(Routines.transitive_routine))
  }

  test("evalT == eval: Game of Life step (pure, precomputed number relations)") {
    val live = Set((1, 0), (1, 1), (1, 2), (2, 2), (0, 2))
    agree(Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Literal(GoL.field(live)))), rc = GoL.rulesFor(live ++ GoL.step(live)).defs)
  }

  test("evalT == eval: n-queens n=6 (pure)") {
    val b = NQueens.board(6)
    agree(b.program, rc = b.defs)
  }

  test("evalT == eval: sliding puzzle expansion (pure)") {
    val p = Sliding.puzzle(3, 3)
    // two pure BFS expansions from the initial state
    agree(Union(p.expandStep(Singleton(Path.Constant(p.initial))),
                p.expandStep(p.expandStep(Singleton(Path.Constant(p.initial))))), rc = p.defs)
  }
end TrieEval

/** The interned IntMap-trie must be an exact, faster implementation too. */
class ITrieOps extends FunSuite:
  import Space.*
  val rnd = new scala.util.Random(11)
  val alphabet = Vector("a", "b", "c", "0", "1", "x")
  def randPath(): PathValue = PathValue(List.fill(rnd.nextInt(4))(alphabet(rnd.nextInt(alphabet.size))))
  def randSV(): SpaceValue = SpaceValue((0 until rnd.nextInt(7)).map(_ => randPath()).toSet)
  def t(sv: SpaceValue): ITrie = ITrie.fromSpaceValue(sv)

  test("ITrie round-trip + ops agree with the reference evaluator") {
    for _ <- 0 until 300 do
      val a = randSV(); val b = randSV()
      assertEquals(t(a).toSpaceValue, a)
      def ref(op: Space) = eval(op)
      assertEquals(ITrie.union(t(a), t(b)).toSpaceValue, ref(Union(Literal(a), Literal(b))), "union")
      assertEquals(ITrie.intersection(t(a), t(b)).toSpaceValue, ref(Intersection(Literal(a), Literal(b))), "intersection")
      assertEquals(ITrie.subtraction(t(a), t(b)).toSpaceValue, ref(Subtraction(Literal(a), Literal(b))), "subtraction")
      assertEquals(ITrie.composition(t(a), t(b)).toSpaceValue, ref(Composition(Literal(a), Literal(b))), "composition")
      assertEquals(ITrie.restriction(t(a), t(b)).toSpaceValue, ref(Restriction(Literal(a), Literal(b))), "restriction")
      assertEquals(ITrie.tailsUnion(t(a)).toSpaceValue, ref(TailsUnion(Literal(a))), "tailsUnion")
      assertEquals(ITrie.tailsIntersection(t(a)).toSpaceValue, ref(TailsIntersection(Literal(a))), "tailsIntersection")
  }
  test("ITrie join-all / meet-all agree with pairwise reduce") {
    for _ <- 0 until 200 do
      val ss = (0 to rnd.nextInt(5)).map(_ => randSV()).toVector; val ts = ss.map(t)
      val joinRef = if ss.isEmpty then SpaceValue() else ss.reduce((x, y) => eval(Union(Literal(x), Literal(y))))
      assertEquals(ITrie.joinAll(ts).toSpaceValue, joinRef, "join-all")
      if ts.nonEmpty then assertEquals(ITrie.meetAll(ts).toSpaceValue, ss.reduce((x, y) => eval(Intersection(Literal(x), Literal(y)))), "meet-all")
  }

class ITrieEval extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(10, "min")
  def agree(s: Space, ic: Map[SpaceMention, ITrie] = Map.empty,
            rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Unit =
    val sc = SpaceContextMap(ic.map((k, v) => k -> v.toSpaceValue))
    assertEquals(evalI(s)(using PathContextMap(Map.empty), ic, rc).toSpaceValue, eval(s)(using PathContextMap(Map.empty), sc, rc))

  test("evalI == eval: aunt") {
    val fam = AuntQuery.context.resolve(SpaceMention("family")); val ppl = AuntQuery.context.resolve(SpaceMention("people"))
    agree(Space.Call(RoutinePtr("aunts"), Vector(), Vector(S"family", S"people")),
      ic = Map(SpaceMention("family") -> ITrie.fromSpaceValue(fam), SpaceMention("people") -> ITrie.fromSpaceValue(ppl)),
      rc = Syntax.mod(Routines.aunt_query_routine))
  }
  test("evalI == eval: transitive closure") {
    val edges = eval(Space.Mention(SpaceMention("g3")).apply(Path.Constant("edge")))(using sc = Graphs.scc_context)
    agree(Space.Call(RoutinePtr("transitive"), Vector(), Vector(Literal(edges))), rc = Syntax.mod(Routines.transitive_routine))
  }
  test("evalI == eval: Game of Life (pure, precomputed number relations)") {
    val live = Set((1,0),(1,1),(1,2),(2,2),(0,2))
    agree(Space.Call(RoutinePtr("nextStep"), Vector(), Vector(Literal(GoL.field(live)))), rc = GoL.rulesFor(live ++ GoL.step(live)).defs)
  }
  test("evalI == eval: pure n-queens n=6") {
    val b = NQueens.board(6); agree(b.program, rc = b.defs)
  }
  test("evalI == eval: pure sliding 2x2 full") {
    val p = Sliding.puzzle(2, 2); agree(p.entry, rc = p.defs)
  }
end ITrieEval
