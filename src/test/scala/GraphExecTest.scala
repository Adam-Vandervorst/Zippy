package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** The op-graph backend: execT (trie-native) must match eval/evalI, and graph OPTIMIZATION
 *  (push_out + optimize_sharing) must be SEMANTICS-PRESERVING — checked by execT-agreement,
 *  not by brittle expected-string snapshots (the optimizer is not to be trusted blindly). */
class GraphExecT extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(10, "min")

  def iT(sv: SpaceValue): ITrie = ITrie.fromSpaceValue(sv)

  def callNodes(g: RecursiveOpGraph): Int =
    g.nodes.iterator.map { case Left(n) => if n.operation == "Call" then 1 else 0; case Right(sg) => callNodes(sg) }.sum
  def hasFixpoint(g: RecursiveOpGraph): Boolean =
    g.nodes.iterator.exists { case Right(sg) => sg.root.operation == "Fixpoint" || hasFixpoint(sg); case _ => false }
  // first malformed input coordinate, for diagnostics
  def firstBad(g: RecursiveOpGraph): Option[String] =
    def chk(node: RecursiveOpGraph, chain: Vector[RecursiveOpGraph], path: Vector[Int]): Option[String] =
      val ch = chain :+ node
      def ok(l: Int, x: Int) = l >= 0 && l < ch.length && x >= 0 && x < ch(l).nodes.length
      node.nodes.zipWithIndex.foreach {
        case (Left(n), i) => n.inputs.find(c => !ok(c._1, c._2)).foreach(c => return Some(s"path=$path #$i ${n.operation} bad $c sizes=${ch.map(_.nodes.length)}"))
        case (Right(sg), i) =>
          sg.root.inputs.find(c => !ok(c._1, c._2)).foreach(c => return Some(s"path=$path sub#$i ${sg.root.operation} bad root $c"))
          chk(sg, ch, path :+ i).foreach(s => return Some(s))
      }
      None
    chk(g, Vector.empty, Vector.empty)

  // ---- example programs that the op-graph backend supports (no recursion / grounded) -------

  /** aunt query: pure iter pipeline; mentions family, people */
  def auntCase: (RecursiveOpGraph, Map[String, ITrie], PartialFunction[String, RecursiveOpGraph], SpaceValue) =
    val fam = AuntQuery.context.resolve(SpaceMention("family")); val ppl = AuntQuery.context.resolve(SpaceMention("people"))
    val g = transpile(Routines.aunt_query_routine)
    val ref = eval(Space.Call(RoutinePtr("aunts"), Vector(), Vector(Literal(fam), Literal(ppl))))(using rc = Syntax.mod(Routines.aunt_query_routine))
    (g, Map("family" -> iT(fam), "people" -> iT(ppl)), PartialFunction.empty, ref)

  /** n-queens place(k,n): nested iterk + Call(aoe) (aoe non-recursive) */
  def queensCase(n: Int): (RecursiveOpGraph, PartialFunction[String, RecursiveOpGraph], SpaceValue) =
    val b = NQueens.board(n)
    val main = R"main"() := b.program
    val g = transpile(main)
    val idx: PartialFunction[String, RecursiveOpGraph] = { case "aoe" => transpile(b.aoe_routine) }
    val ref = eval(b.program)(using rc = b.defs)
    (g, idx, ref)

  /** temperature: restriction over literals (relational fragment) */
  def tempCase: (RecursiveOpGraph, SpaceValue) =
    val cells = NOAA.worldTemp(NOAA.load(NOAA.file.get.getPath))
    val q = Space.Unwrap(Space.Restriction(Literal(cells), ss"VW"), Path.Constant("VW"))
    (transpile(R"main"() := q), eval(q))

  test("execT(transpile) == eval : aunt query") {
    val (g, ms, idx, ref) = auntCase
    assertEquals(runGraphT(g, mentions = ms, index = idx).toSpaceValue, ref)
  }

  test("graph OPTIMIZE is semantics-preserving : aunt query") {
    val (g, ms, idx, ref) = auntCase
    val go = optimize(g)
    assertEquals(runGraphT(go, mentions = ms, index = idx).toSpaceValue, ref, s"optimize changed semantics!\n${go.show}")
  }

  test("execT(transpile) == eval : n-queens place (n=6)") {
    val (g, idx, ref) = queensCase(6)
    assertEquals(runGraphT(g, index = idx).toSpaceValue, ref)
  }

  test("graph OPTIMIZE is semantics-preserving : n-queens place (n=6)") {
    val (g, idx, ref) = queensCase(6)
    assertEquals(runGraphT(optimize(g), index = idx).toSpaceValue, ref)
  }

  test("execT(transpile) == eval and OPTIMIZE preserves : temperature restriction") {
    val (g, ref) = tempCase
    assertEquals(runGraphT(g).toSpaceValue, ref)
    assertEquals(runGraphT(optimize(g)).toSpaceValue, ref)
  }

  // union_iter is the canonical push-out case: the Left/Right Constants are loop-invariant and
  // should be hoisted OUT of the iteration subgraphs. Verify the optimizer (a) changes the graph
  // and (b) preserves semantics.
  test("OPTIMIZE hoists loop-invariants and preserves semantics : union_iter") {
    val g = transpile(Routines.union_iter_routine)
    val go = optimize(g)
    assert(g.show != go.show, "optimize should transform union_iter (hoist constants)")
    val xs = ITrie.fromSpaceValue(SpaceValue("a.1", "b.foo")); val ys = ITrie.fromSpaceValue(SpaceValue("a.2", "c.bar"))
    val ref = eval(Space.Call(RoutinePtr("union_iter"), Vector(), Vector(
      Literal(xs.toSpaceValue), Literal(ys.toSpaceValue))))(using rc = Syntax.mod(Routines.union_iter_routine))
    assertEquals(runGraphT(g, mentions = Map("xs" -> xs, "ys" -> ys)).toSpaceValue, ref)
    assertEquals(runGraphT(go, mentions = Map("xs" -> xs, "ys" -> ys)).toSpaceValue, ref, s"optimize changed semantics\n${go.show}")
  }

  // sliding expandStep: Calls (superpose/collapse) + deeply nested iterations + a loop-invariant
  // `all_moves` subexpression — a strong optimizer stress test.
  test("execT(transpile) == eval and OPTIMIZE preserves : sliding expandStep") {
    val p = Sliding.puzzle(3, 3)
    val step = R"step"(S"frontier") := p.expandStep(S"frontier")
    val g = transpile(step)
    val idx: PartialFunction[String, RecursiveOpGraph] =
      { case "superpose" => transpile(p.superpose); case "collapse" => transpile(p.collapse) }
    val frontier = SpaceValue(Set(Path.Constant(p.initial)).map { case Path.Constant(pv) => pv })
    val ref = eval(Space.Call(RoutinePtr("step"), Vector(), Vector(Literal(frontier))))(using rc = Syntax.mod(step, p.superpose, p.collapse))
    val fr = Map("frontier" -> ITrie.fromSpaceValue(frontier))
    assertEquals(runGraphT(g, mentions = fr, index = idx).toSpaceValue, ref)
    assertEquals(runGraphT(optimize(g), mentions = fr, index = idx).toSpaceValue, ref, "optimize changed semantics on sliding")
  }

  // ---- push_out (LICM) is well-formed + semantics-preserving at any nesting depth ----------
  // Regression for the deep-nesting bug: push_out used to emit a downward coordinate into the wrong
  // graph; the rewrite is coordinate-free until linearization, so it is well-formed by construction.
  def nestedIter(depth: Int): Routine =
    def hd(nm: String): Path = Path.Deref(PathRef(nm))
    def it(sym: String, rest: String, tmpl: Space): Space = Space.Iteration(S"src", PathRef(sym), SpaceMention(rest), tmpl)
    var body: Space = it("x0", "r0", Space.Composition(Space.Singleton(hd("x0")), S"r0"))
    for d <- 1 until depth do body = it(s"x$d", s"r$d", Space.Composition(Space.Singleton(hd(s"x$d")), body))
    R"nest"(S"src") := body

  for d <- 1 to 4 do
    test(s"push_out well-formed + correct at iteration-nesting depth $d") {
      val r = nestedIter(d); val g = transpile(r); val po = push_out(g)
      assert(wellFormed(po), s"push_out not well-formed at depth $d: ${firstBad(po)}")
      val src = ITrie.fromSpaceValue(SpaceValue("a.1", "a.2", "b.3", "c.4"))
      val ref = eval(Space.Call(RoutinePtr("nest"), Vector(), Vector(Literal(src.toSpaceValue))))(using rc = Syntax.mod(r))
      assertEquals(runGraphT(po, mentions = Map("src" -> src)).toSpaceValue, ref, s"push_out exec wrong at depth $d")
    }

  test("push_out well-formed + correct : sliding 3x3 (the deep-nesting regression)") {
    val p = Sliding.puzzle(3, 3)
    val step = R"step"(S"frontier") := p.expandStep(S"frontier")
    val po = push_out(transpile(step))
    assert(wellFormed(po), s"push_out not well-formed on sliding: ${firstBad(po)}")
    val idx: PartialFunction[String, RecursiveOpGraph] = { case "superpose" => transpile(p.superpose); case "collapse" => transpile(p.collapse) }
    val frontier = SpaceValue(Set(p.initial))
    val ref = eval(Space.Call(RoutinePtr("step"), Vector(), Vector(Literal(frontier))))(using rc = Syntax.mod(step, p.superpose, p.collapse))
    assertEquals(runGraphT(po, mentions = Map("frontier" -> ITrie.fromSpaceValue(frontier)), index = idx).toSpaceValue, ref)
  }

  // ---- push_out is a real LICM driver: it measurably hoists loop-invariant nodes out of loops --
  test("push_out hoists loop-invariant nodes out of loops (improvement is real)") {
    // union_iter's Left/Right constants are loop-invariant inside the two iterations
    val g = transpile(Routines.union_iter_routine)
    val po = push_out(g)
    assert(wellFormed(po), s"push_out ill-formed: ${firstBad(po)}")
    assert(loopNodes(po) < loopNodes(g), s"push_out should shrink in-loop node count: ${loopNodes(g)} -> ${loopNodes(po)}")
  }

  // ---- push_out hoists a whole LOOP-INVARIANT SUBGRAPH out of an enclosing loop ------------
  def rootSubgraphs(x: RecursiveOpGraph): Int = x.nodes.count(_.isRight)

  test("push_out hoists a loop-invariant inner iteration out to the root (semantics preserved)") {
    def hd(n: String): Path = Path.Deref(PathRef(n))
    // inner iterates a fixed literal using only its own vars => invariant w.r.t. the outer loop var
    val inner: Space = Space.Iteration(Literal(SpaceValue("m.1", "m.2", "n.3")), PathRef("y"), SpaceMention("s"),
      Space.Composition(Space.Singleton(hd("y")), S"s"))
    val outer = R"o"(S"src") := Space.Iteration(S"src", PathRef("x"), SpaceMention("r"),
      Space.Composition(inner, Space.Singleton(hd("x"))))
    val g = transpile(outer)
    val poNo = push_out(g, hoistSubgraphs = false)   // node-only LICM (inner stays nested)
    val poYes = push_out(g, hoistSubgraphs = true)    // subgraph hoisting (inner lifts to root)
    assert(wellFormed(poYes), s"hoist ill-formed: ${firstBad(poYes)}")
    assert(rootSubgraphs(poYes) > rootSubgraphs(poNo),
      s"the invariant inner loop should lift to the root: rootSubgraphs ${rootSubgraphs(poNo)} -> ${rootSubgraphs(poYes)}")
    val src = ITrie.fromSpaceValue(SpaceValue("a.1", "b.2", "c.3"))
    val ref = eval(Space.Call(RoutinePtr("o"), Vector(), Vector(Literal(src.toSpaceValue))))(using rc = Syntax.mod(outer))
    assertEquals(runGraphT(poNo, mentions = Map("src" -> src)).toSpaceValue, ref, "no-hoist semantics")
    assertEquals(runGraphT(poYes, mentions = Map("src" -> src)).toSpaceValue, ref, "hoist semantics")
  }

  // ---- CSE shares structurally-identical subgraphs (not just flat nodes) -------------------
  def subgraphCount(x: RecursiveOpGraph): Int =
    x.nodes.iterator.map { case Right(sg) => 1 + subgraphCount(sg); case _ => 0 }.sum

  test("optimize_sharing deduplicates two structurally-identical iteration subgraphs") {
    val it: Space = Space.Iteration(S"xs", PathRef("x"), SpaceMention("r"),
      Space.Composition(Space.Singleton(Path.Deref(PathRef("x"))), S"r"))
    val prog = Space.Union(it, it)                       // two identical iterations over xs
    val g = transpile(R"main"(S"xs") := prog)
    assertEquals(subgraphCount(g), 2, "expected two subgraphs before CSE")
    val sh = optimize_sharing(g)
    assert(wellFormed(sh), s"CSE produced ill-formed graph: ${firstBad(sh)}")
    assertEquals(subgraphCount(sh), 1, s"CSE should merge the identical iterations:\n${sh.show}")
    val xs = ITrie.fromSpaceValue(SpaceValue("a.1", "a.2", "b.3"))
    val ref = eval(prog)(using sc = SpaceContextMap(Map(SpaceMention("xs") -> xs.toSpaceValue)))
    assertEquals(runGraphT(sh, mentions = Map("xs" -> xs)).toSpaceValue, ref, "CSE changed semantics")
  }

  // ---- inlining: non-recursive Calls expand into the graph (no Call dispatch left) ---------
  test("inline: n-queens place(6) transpiles Call-free and execT(inline+opt) == eval") {
    val b = NQueens.board(6)
    val ref = eval(b.program)(using rc = b.defs)
    val g = transpile(R"main"() := inlineCalls(b.program, b.defs))
    assertEquals(callNodes(g), 0, "inlining left Call nodes")
    val go = optimize(g); assert(wellFormed(go), s"inline+opt not wf: ${firstBad(go)}")
    assertEquals(runGraphT(go).toSpaceValue, ref)
  }

  // ---- Space.Fixpoint is first-class: eval/evalT/evalI/execT all agree -----------------------
  test("Space.Fixpoint: transitive closure agrees across eval, evalT, evalI, and execT") {
    // reuse transitive_routine's `next` expression (edges \/ step(edges)) as the fixpoint body
    val next = Routines.transitive_routine.body match
      case Space.Union(_, Space.Call(_, _, Vector(n))) => n
      case other => fail(s"unexpected transitive body: ${other.show}")
    val tc = R"tc"(S"edges") := Space.Fixpoint(S"edges", SpaceMention("edges"), next)
    val edges = SpaceValue("a.b", "b.c", "c.d", "d.e")
    val call = Space.Call(RoutinePtr("tc"), Vector(), Vector(Literal(edges)))
    val defs = Syntax.mod(tc)
    val ref = eval(call)(using rc = defs)
    // the Space.Fixpoint must equal the recursive-routine closure
    val refRoutine = eval(Space.Call(RoutinePtr("transitive"), Vector(), Vector(Literal(edges))))(using rc = Syntax.mod(Routines.transitive_routine))
    assertEquals(ref, refRoutine, "Space.Fixpoint disagrees with the recursive routine")
    assertEquals(evalT(call)(using rc = defs).toSpaceValue, ref, "evalT")
    assertEquals(evalI(call)(using rc = defs).toSpaceValue, ref, "evalI")
    // transpile the Space.Fixpoint and run it on the trie executor (Call-free, no index)
    val g = transpile(tc)
    assert(hasFixpoint(g), s"Space.Fixpoint did not transpile to a Fixpoint subgraph:\n${g.show}")
    assertEquals(runGraphT(g, mentions = Map("edges" -> ITrie.fromSpaceValue(edges))).toSpaceValue, ref, "execT")
    assertEquals(runGraphT(optimize(g), mentions = Map("edges" -> ITrie.fromSpaceValue(edges))).toSpaceValue, ref, "execT(opt)")
  }

  // ---- lowering: union-saturating self-recursion becomes a Fixpoint subgraph ---------------
  test("lower: transitive closure (datalog) lowers to Fixpoint and execT == eval") {
    val g = transpile(Routines.transitive_routine)
    assert(hasFixpoint(g), s"transitive did not lower to Fixpoint:\n${g.show}")
    val edges = SpaceValue("a.b", "b.c", "c.d", "d.e")
    val ref = eval(Space.Call(RoutinePtr("transitive"), Vector(), Vector(Literal(edges))))(using rc = Syntax.mod(Routines.transitive_routine))
    val et = Map("edges" -> ITrie.fromSpaceValue(edges))
    assertEquals(runGraphT(g, mentions = et).toSpaceValue, ref, "execT(Fixpoint) != eval")
    assertEquals(runGraph(g, mentions = Map("edges" -> edges)), ref, "exec(Fixpoint) != eval")
    assertEquals(runGraphT(optimize(g), mentions = et).toSpaceValue, ref, "execT(opt Fixpoint) != eval")
  }

  // ---- SCC-aware inliner/lowerer (`lower`) -------------------------------------------------
  def fixpointCount(s: Space): Int = collect(s)({ case f: Space.Fixpoint => f })._1.size

  test("lower: transitive (single-mention recursion) -> Fixpoint, no residual, eval == closure") {
    val (top, residual) = lowerCalls(Routines.transitive_routine, Syntax.mod(Routines.transitive_routine))
    assert(residual.isEmpty, s"expected no honest residual, got ${residual.keys}")
    assertEquals(fixpointCount(top), 1, s"expected one Fixpoint in the lowered body:\n${top.show}")
    assert(callees(top).isEmpty, "lowered transitive should be Call-free")
    val edges = SpaceValue("a.b", "b.c", "c.d", "d.e")
    val sc = SpaceContextMap(Map(SpaceMention("edges") -> edges))
    val ref = eval(Space.Call(RoutinePtr("transitive"), Vector(), Vector(Literal(edges))))(using rc = Syntax.mod(Routines.transitive_routine))
    assertEquals(eval(top)(using PathContextMap(Map.empty), sc, PartialFunction.empty), ref)
  }

  test("lower: reachable (multi-parameter recursion) -> Fixpoint over the changing mention") {
    val (top, residual) = lowerCalls(Routines.reachable_routine, Syntax.mod(Routines.reachable_routine))
    assert(residual.isEmpty, s"reachable should fully lower; residual ${residual.keys}")
    assertEquals(fixpointCount(top), 1, s"reachable should lower to one Fixpoint:\n${top.show}")
    // edges/nodemask pass through as free mentions; only `reach` saturates
    assert(Matching.freeMentions(top).map(_.s) == Set("edges", "nodemask", "reach"), s"free: ${Matching.freeMentions(top).map(_.s)}")
  }

  test("lower: mutual recursion lowers to a single tagged Fixpoint (eval-sound, no residual)") {
    // degenerate case: f(x)=x ∪ g(x), g(x)=x ∪ f(x) ⇒ least fixpoint f=g=x
    val f = R"f"(S"x") := S"x" \/ R"g"(S"x")
    val g = R"g"(S"x") := S"x" \/ R"f"(S"x")
    val (top, residual) = lowerCalls(f, Syntax.mod(f, g))
    assert(fixpointCount(top) >= 1, s"mutual recursion should lower to a Fixpoint:\n${top.show}")
    assert(residual.isEmpty, s"no residual recursion should remain: ${residual.keys.map(_.s)}")
    assert(callees(top).isEmpty, s"no surviving calls into the cycle: ${callees(top).map(_.s)}")
    val v = SpaceValue("a", "b.c", "d")
    val main = Routine(RoutinePtr("main"), Vector.empty, Vector(SpaceMention("x")), top)
    assertEquals(eval(top)(using sc = SpaceContextMap(Map(SpaceMention("x") -> v))), v, s"eval(lowered f) must be x:\n${top.show}")
    assertEquals(evalI(top)(using ic = Map(SpaceMention("x") -> iT(v))).toSpaceValue, v)
    assertEquals(runGraphT(optimize(transpile(main)), mentions = Map("x" -> iT(v))).toSpaceValue, v)
  }

  test("lower: non-degenerate mutual recursion (intersection-bounded) lowers and is eval-sound") {
    // A(u) = {a} ∪ (B(u) ∩ u),  B(u) = {b} ∪ (A(u) ∩ u);  over u={a,b,c} ⇒ A=B={a,b}
    val a = R"A"(S"u") := s("a") \/ (R"B"(S"u") /\ S"u")
    val b = R"B"(S"u") := s("b") \/ (R"A"(S"u") /\ S"u")
    val (top, residual) = lowerCalls(a, Syntax.mod(a, b))
    assert(fixpointCount(top) >= 1 && residual.isEmpty && callees(top).isEmpty, s"should fully lower:\n${top.show}")
    val u = SpaceValue("a", "b", "c"); val expected = SpaceValue("a", "b")
    val main = Routine(RoutinePtr("main"), Vector.empty, Vector(SpaceMention("u")), top)
    assertEquals(eval(top)(using sc = SpaceContextMap(Map(SpaceMention("u") -> u))), expected, s"eval(lowered A):\n${top.show}")
    assertEquals(evalI(top)(using ic = Map(SpaceMention("u") -> iT(u))).toSpaceValue, expected)
    assertEquals(runGraphT(optimize(transpile(main)), mentions = Map("u" -> iT(u))).toSpaceValue, expected)
  }

  test("lower: arg-changing mutual recursion lowers via Gaussian elimination (eval-sound)") {
    // f(x)=x ∪ g(x("h")), g(x)=x ∪ f(x).  Unfold g into f ⇒ f(x)=x ∪ x("h") ∪ f(x("h")) ⇒ f(x)=⋃ₖ x("h"ᵏ).
    val f = R"f"(S"x") := S"x" \/ R"g"(S"x"("h"))
    val g = R"g"(S"x") := S"x" \/ R"f"(S"x")
    val (top, residual) = lowerCalls(f, Syntax.mod(f, g))
    assert(fixpointCount(top) >= 1, s"arg-changing mutual recursion should lower:\n${top.show}")
    assert(residual.isEmpty && callees(top).isEmpty, s"no residual/calls: ${residual.keys.map(_.s)} / ${callees(top).map(_.s)}")
    val x = SpaceValue("h.h.a"); val expected = SpaceValue("h.h.a", "h.a", "a")  // ⋃ₖ x("h"ᵏ): strip "h" 0,1,2 times
    // NB: naive eval of the ORIGINAL mutual recursion diverges (f(∅)↔g(∅) loops); the lowered Fixpoint
    // *converges* to the least fixpoint — exactly the point of fixpoint lowering. Verify against the lfp.
    val main = Routine(RoutinePtr("main"), Vector.empty, Vector(SpaceMention("x")), top)
    assertEquals(eval(top)(using sc = SpaceContextMap(Map(SpaceMention("x") -> x))), expected, s"eval(lowered f):\n${top.show}")
    assertEquals(evalI(top)(using ic = Map(SpaceMention("x") -> iT(x))).toSpaceValue, expected)
    assertEquals(runGraphT(optimize(transpile(main)), mentions = Map("x" -> iT(x))).toSpaceValue, expected)
  }

  test("lower: non-monotone mutual recursion stays an honest residual (recursive call under subtraction)") {
    // f(x) = a \ g(x), g(x) = b \ f(x): the recursive calls are in a subtractive (anti-monotone)
    // position, so there is no least fixpoint to lower to — must stay residual, not be falsely lowered.
    val f = R"f"(S"x") := s("a") \ R"g"(S"x")
    val g = R"g"(S"x") := s("b") \ R"f"(S"x")
    val (top, residual) = lowerCalls(f, Syntax.mod(f, g))
    assert(fixpointCount(top) == 0, s"non-monotone mutual recursion must NOT be lowered:\n${top.show}")
    assert(residual.keySet.map(_.s) == Set("f", "g"), s"both must stay residual: ${residual.keys.map(_.s)}")
  }

  test("lower: n-queens place(6) inlines all acyclic calls -> Call-free, execT == eval") {
    val b = NQueens.board(6)
    val (top, residual) = lowerCalls(R"main"() := b.program, b.defs)
    assert(residual.isEmpty && callees(top).isEmpty, s"place should fully inline; residual ${residual.keys}, calls ${callees(top)}")
    val ref = eval(b.program)(using rc = b.defs)
    assertEquals(runGraphT(optimize(transpile(R"main"() := top))).toSpaceValue, ref)
  }
end GraphExecT
