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

/** The AlgebraicResult case analysis must be EXACT: a set Identity bit always means set-equality
 *  with that argument; Empty means the empty set; Bespoke means the result differs from both
 *  arguments — with the single documented exception (restriction's ε-prefix short-circuit may
 *  under-report the RIGHT bit).  Identity must also be an OBJECT: `pick` returns the argument
 *  node itself, so sharing survives across op applications (the fixpoint absorption pattern). */
class TrieAlgebra extends FunSuite:
  import Trie.AlgebraicResult
  import Trie.AlgebraicResult.{LEFT, RIGHT}

  val rnd = new scala.util.Random(19)
  val alphabet = Vector("a", "b", "c", "0", "1", "x")
  def randPath(maxLen: Int = 4): PathValue = PathValue(List.fill(rnd.nextInt(maxLen + 1))(alphabet(rnd.nextInt(alphabet.size))))
  def randSV(n: Int = 8): SpaceValue = SpaceValue((0 until rnd.nextInt(n)).map(_ => randPath()).toSet)
  def t(sv: SpaceValue): Trie = Trie.fromSpaceValue(sv)

  // reference set semantics
  def refUnion(a: SpaceValue, b: SpaceValue): Set[PathValue] = a.paths union b.paths
  def refInter(a: SpaceValue, b: SpaceValue): Set[PathValue] = a.paths intersect b.paths
  def refSub(a: SpaceValue, b: SpaceValue): Set[PathValue] = a.paths removedAll b.paths
  def refRestr(a: SpaceValue, b: SpaceValue): Set[PathValue] = a.paths.filter(p => b.paths.exists(q => p.items.startsWith(q.items)))
  def refRaff(a: SpaceValue, b: SpaceValue): Set[PathValue] = a.paths removedAll refRestr(a, b)
  def refComp(a: SpaceValue, b: SpaceValue): Set[PathValue] = for p <- a.paths; q <- b.paths yield PathValue(p.items ++ q.items)

  /** soundness of every case + completeness of the flagged bits */
  def check(op: String, r: AlgebraicResult, a: SpaceValue, b: SpaceValue, ref: Set[PathValue],
            leftComplete: Boolean = true, rightComplete: Boolean = true): Unit =
    r match
      case AlgebraicResult.Empty => assertEquals(ref, Set.empty[PathValue], s"$op: Empty must mean the empty set ($a, $b)")
      case AlgebraicResult.Identity(m) =>
        assert(m != 0, s"$op: zero identity mask")
        if (m & LEFT) != 0 then assertEquals(a.paths, ref, s"$op: LEFT bit unsound ($a, $b)")
        if (m & RIGHT) != 0 then assertEquals(b.paths, ref, s"$op: RIGHT bit unsound ($a, $b)")
        assert(ref.nonEmpty, s"$op: empty identity should be Empty (precedence) ($a, $b)")
      case AlgebraicResult.Bespoke(res) => assertEquals(res.toSpaceValue.paths, ref, s"$op: Bespoke wrong ($a, $b)")
    val flaggedL = r match { case AlgebraicResult.Identity(m) => (m & LEFT) != 0; case _ => false }
    val flaggedR = r match { case AlgebraicResult.Identity(m) => (m & RIGHT) != 0; case _ => false }
    val emptyCase = r == AlgebraicResult.Empty
    if leftComplete && ref == a.paths && ref.nonEmpty then assert(flaggedL, s"$op: result == left not flagged ($a, $b)")
    if rightComplete && ref == b.paths && ref.nonEmpty then assert(flaggedR, s"$op: result == right not flagged ($a, $b)")
    if ref.isEmpty then assert(emptyCase, s"$op: empty result not reported Empty ($a, $b)")

  test("case analysis is exact on random spaces") {
    for _ <- 0 until 2000 do
      val a = randSV(); val b = randSV()
      val (ta, tb) = (t(a), t(b))
      check("union", Trie.unionR(ta, tb), a, b, refUnion(a, b))
      check("intersection", Trie.intersectionR(ta, tb), a, b, refInter(a, b))
      check("subtraction", Trie.subtractionR(ta, tb), a, b, refSub(a, b), rightComplete = false)
      check("restriction", Trie.restrictionR(ta, tb), a, b, refRestr(a, b), rightComplete = false)
      check("raffination", Trie.raffinationR(ta, tb), a, b, refRaff(a, b), rightComplete = false)
      check("composition", Trie.compositionR(ta, tb), a, b, refComp(a, b))
  }

  test("case analysis is exact on correlated spaces (subsets, prefixes, self)") {
    for _ <- 0 until 2000 do
      val a = randSV()
      val ta = t(a)
      val sub = SpaceValue(a.paths.filter(_ => rnd.nextBoolean()))
      val tsub = t(sub)
      val pre = SpaceValue(a.paths.map(p => PathValue(p.items.take(rnd.nextInt(p.items.length + 1)))).filter(_ => rnd.nextBoolean()))
      val tpre = t(pre)
      // structurally distinct copy of the same set: identity must be detected by VALUE, not eq
      val copy = t(SpaceValue(a.paths))
      check("union(a,sub)", Trie.unionR(ta, tsub), a, sub, refUnion(a, sub))
      check("union(sub,a)", Trie.unionR(tsub, ta), sub, a, refUnion(sub, a))
      check("union(a,copy)", Trie.unionR(ta, copy), a, a, refUnion(a, a))
      check("inter(a,sub)", Trie.intersectionR(ta, tsub), a, sub, refInter(a, sub))
      check("inter(a,copy)", Trie.intersectionR(ta, copy), a, a, refInter(a, a))
      check("sub(a,sub)", Trie.subtractionR(ta, tsub), a, sub, refSub(a, sub), rightComplete = false)
      check("sub(a,copy)", Trie.subtractionR(ta, copy), a, a, refSub(a, a), rightComplete = false)
      check("restr(a,pre)", Trie.restrictionR(ta, tpre), a, pre, refRestr(a, pre), rightComplete = false)
      check("restr(a,copy)", Trie.restrictionR(ta, copy), a, a, refRestr(a, a), rightComplete = false)
      check("raff(a,pre)", Trie.raffinationR(ta, tpre), a, pre, refRaff(a, pre), rightComplete = false)
      check("comp(a,sub)", Trie.compositionR(ta, tsub), a, sub, refComp(a, sub))
  }

  test("identity results ARE the argument object (structural sharing)") {
    for _ <- 0 until 500 do
      val a = randSV(6)
      if a.paths.nonEmpty then
        val ta = t(a)
        val sub = t(SpaceValue(a.paths.filter(_ => rnd.nextBoolean())))
        assert(Trie.union(ta, sub) eq ta, "union with a subset must return the left object")
        val up = Trie.union(sub, ta)   // when sub == a as a set either object is a valid identity
        assert((up eq ta) || ((up eq sub) && sub == ta), "union into a superset must return an argument object")
        assert(Trie.intersection(ta, Trie.union(ta, t(randSV()))) eq ta, "intersection with a superset must return the smaller object")
        assert(Trie.subtraction(ta, t(SpaceValue(randSV().paths.map(p => PathValue("z" :: p.items))))) eq ta, "subtraction of a disjoint set must return the left object")
        assert(Trie.restriction(ta, Trie.epsilon) eq ta, "restriction by {ε} must return the left object")
        assert(Trie.raffination(ta, t(SpaceValue(Set(PathValue(List("z")))))) eq ta, "raffination by a non-prefix must return the left object")
        assert(Trie.composition(ta, Trie.epsilon) eq ta, "composition with {ε} must return the left object")
        assert(Trie.composition(Trie.epsilon, ta) eq ta, "composition of {ε} must return the right object")
        // fixpoint absorption: re-unioning an already-absorbed iterate allocates nothing
        val grown = Trie.union(ta, t(randSV()))
        assert(Trie.union(grown, sub) eq grown, "absorbed iterate must not rebuild the accumulator")
  }

  test("subtraction never reports the right-identity; empty covers a\\b == b") {
    // a\b == b as sets forces b ⊆ a\b, hence b == ∅, hence a == ∅: exactly the Empty case.
    assertEquals(Trie.subtractionR(Trie.empty, Trie.empty), Trie.AlgebraicResult.Empty)
    for _ <- 0 until 500 do
      val a = randSV(); val b = randSV()
      Trie.subtractionR(t(a), t(b)) match
        case Trie.AlgebraicResult.Identity(m) => assertEquals(m, LEFT, s"subtraction set a counter-identity bit for ($a, $b)")
        case _ => ()
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
