package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** Can the CURRENT optimizers rewrite the low-level product-into-union example
 *
 *    s("foo").iter(x, x_, s("bar").iter(y, y_, {cux.x} ∪ {cux.y}))
 *
 *  toward   "cux" x (Head(s("foo")) ∪ Head(s("bar")))  ?
 *
 *  Two layers are checked:
 *   - the static Space-level `Lower` rules (`Routine.optimized`): IterUnion_Indep is exactly the
 *     "push out (loop)" step, but it is GUARDED by `provablyHeaded(src)` — the hoisted form is NOT
 *     equal to the original when either source is empty (the outer loop then runs zero times and
 *     the whole product is ∅, while the hoisted union still emits the other side).
 *   - the op-graph optimizer (`transpile` + `optimize` = push_out LICM + optimize_sharing CSE),
 *     which performs the loop-invariant motion SOUNDLY for symbolic sources (computation is
 *     hoisted, the union accumulation stays inside the loop, so ∅-sources still yield ∅).
 */
class ProductUnionCheck extends FunSuite:
  import Space.*

  def product(src1: Space, src2: Space): Space =
    src1.iter(P"x", S"x_",
      src2.iter(P"y", S"y_",
        Singleton("cux" x P"x") \/ Singleton("cux" x P"y")))

  /** the target shape from the derivation: "cux" x (Head(a) ∪ Head(b)) */
  def target(src1: Space, src2: Space): Space = "cux" x (head(src1) \/ head(src2))

  val bindings = Seq(
    "both nonempty"   -> SpaceValue("foo.a", "foo.b", "bar.c", "bar.d"),
    "only foo"        -> SpaceValue("foo.a", "foo.b"),
    "only bar"        -> SpaceValue("bar.c"),
    "empty"           -> SpaceValue(),
    "foo is {ε}"      -> SpaceValue("foo", "bar.c"),   // s("foo") = {ε}: nonempty but HEADLESS
    "bar is {ε}"      -> SpaceValue("foo.a", "bar"),
  )
  def ctx(sv: SpaceValue) = SpaceContextMap(Map(SpaceMention("s") -> sv))

  test("the bare target form is NOT equivalent — the hoist needs both sources headed") {
    val prog = product(S"s"("foo"), S"s"("bar"))
    val tgt  = target(S"s"("foo"), S"s"("bar"))
    assertEquals(eval(prog)(using sc = ctx(bindings(0)._2)), eval(tgt)(using sc = ctx(bindings(0)._2)))
    // one-sided sources: the product is ∅ (a loop ran zero times) but the target still emits
    assertEquals(eval(prog)(using sc = ctx(bindings(1)._2)), SpaceValue())
    assertNotEquals(eval(tgt)(using sc = ctx(bindings(1)._2)), SpaceValue())
    assertEquals(eval(prog)(using sc = ctx(bindings(2)._2)), SpaceValue())
    assertNotEquals(eval(tgt)(using sc = ctx(bindings(2)._2)), SpaceValue())
  }

  test("guard laws: headedGuard/nonEmptyGuard are the constant-time {ε}/∅ factors") {
    val rnd = new scala.util.Random(23)
    val alphabet = Vector("a", "b", "")
    for _ <- 0 until 300 do
      val sv = SpaceValue((0 until rnd.nextInt(5)).map(_ =>
        PathValue(List.fill(rnd.nextInt(3))(alphabet(rnd.nextInt(alphabet.size))))).toSet)
      val x = Space.Literal(sv)
      val eps = SpaceValue(PathValue(Nil))
      assertEquals(eval(Lower.nonEmptyGuard(x)), if sv.paths.nonEmpty then eps else SpaceValue(), s"nonEmpty($sv)")
      assertEquals(eval(Lower.headedGuard(x)), if sv.paths.exists(_.items.nonEmpty) then eps else SpaceValue(), s"headed($sv)")
  }

  test("a nonEmpty-guarded target still leaks on an ε-only source; the headed guard does not") {
    // s("bar") = {ε}: non-empty, but the inner loop runs ZERO times, so the product is ∅.
    val sv = bindings(5)._2
    val prog = product(S"s"("foo"), S"s"("bar"))
    val neTgt = "cux" x ((Lower.nonEmptyGuard(S"s"("bar")) x head(S"s"("foo"))) \/ (Lower.nonEmptyGuard(S"s"("foo")) x head(S"s"("bar"))))
    val hdTgt = "cux" x ((Lower.headedGuard(S"s"("bar")) x head(S"s"("foo"))) \/ (Lower.headedGuard(S"s"("foo")) x head(S"s"("bar"))))
    assertEquals(eval(prog)(using sc = ctx(sv)), SpaceValue())
    assertNotEquals(eval(neTgt)(using sc = ctx(sv)), SpaceValue(), "nonEmpty guard leaks on {ε} source")
    assertEquals(eval(hdTgt)(using sc = ctx(sv)), SpaceValue(), "headed guard must not leak")
    // and the headed-guarded target is equivalent on every binding
    for (name, b) <- bindings do
      assertEquals(eval(hdTgt)(using sc = ctx(b)), eval(prog)(using sc = ctx(b)), s"binding: $name")
  }

  test("literal (provably headed) sources: Lower reaches the fully hoisted/folded form") {
    val prog = product(s("a1", "a2"), s("b1", "b2"))
    val opt = (R"q"() := prog).optimized(using PartialFunction.empty)
    println(s"[lit] before: ${prog.show}")
    println(s"[lit] after : ${opt.body.show}")
    assertEquals(eval(opt.body), eval(prog), "literal-source optimization changed semantics")
    // the product must be gone: no nested iteration left
    def hasIter(sp: Space): Boolean =
      val (found, _) = collect(sp)({ case i: Space.Iteration => i }, PartialFunction.empty)
      found.nonEmpty
    def anyNested(sp: Space): Boolean =
      val (iters, _) = collect(sp)({ case i: Space.Iteration => i }, PartialFunction.empty)
      iters.exists((_, i) => i match { case Space.Iteration(_, _, _, b) => hasIter(b) })
    assert(!anyNested(opt.body), s"nested product iteration survived: ${opt.body.show}")
  }

  test("symbolic sources: Lower reaches the guarded factored form (product eliminated)") {
    val prog = product(S"s"("foo"), S"s"("bar"))
    val opt = (R"q"(S"s") := prog).optimized(using PartialFunction.empty)
    println(s"[sym] before: ${prog.show}")
    println(s"[sym] after : ${opt.body.show}")
    for (name, sv) <- bindings do
      assertEquals(eval(opt.body)(using sc = ctx(sv)), eval(prog)(using sc = ctx(sv)), s"binding: $name")
    // the nested product is gone: no iteration remains inside another iteration's body
    def hasIter(sp: Space): Boolean =
      val (found, _) = collect(sp)({ case i: Space.Iteration => i }, PartialFunction.empty)
      found.nonEmpty
    def anyNested(sp: Space): Boolean =
      val (iters, _) = collect(sp)({ case i: Space.Iteration => i }, PartialFunction.empty)
      iters.exists((_, i) => i match { case Space.Iteration(_, _, _, b) => hasIter(b) })
    assert(!anyNested(opt.body), s"nested product iteration survived: ${opt.body.show}")
    // and the common prefix was factored: exactly one Wrap of "cux" at the top
    opt.body match
      case Space.Wrap(_, Path.Constant(PathValue(List("cux")))) => ()
      case other => fail(s"expected the factored cux-Wrap at the top, got: ${other.show}")
  }

  test("symbolic sources: op-graph optimize (union/composition splits) eliminates the product") {
    val r = R"q"(S"s") := product(S"s"("foo"), S"s"("bar"))
    val g = transpile(r)
    val og = optimize(g)
    def loopDepth(gg: RecursiveOpGraph): Int =
      (gg.nodes.collect { case Right(sg) => 1 + loopDepth(sg) } ++ Seq(0)).max
    println(s"[graph] loop depth: ${loopDepth(g)} -> ${loopDepth(og)}; loop-resident ${loopNodes(g)} -> ${loopNodes(og)}; total ${nodeCount(g)} -> ${nodeCount(og)}")
    println("[graph] before:\n" + g.show)
    println("[graph] after:\n" + og.show)
    assertEquals(loopDepth(g), 2, "sanity: the source program is a nested product")
    assertEquals(loopDepth(og), 1, "the product must be split apart: no loop remains inside a loop")
    for (name, sv) <- bindings do
      val ref = eval(r.body)(using sc = ctx(sv))
      assertEquals(runGraphT(og, mentions = Map("s" -> ITrie.fromSpaceValue(sv))).toSpaceValue, ref, s"binding: $name")
      assertEquals(runGraph(og, mentions = Map("s" -> sv)), ref, s"binding: $name (SpaceValue exec)")
  }

  test("same-source product: α-invariant sharing merges the two head-loops and guards") {
    // x and y range over the SAME source; after the splits the two head-loops differ only in
    // binder names (iter x {cux.x} vs iter y {cux.y}) — α-invariant sharing must merge them,
    // and the two headed-guards of the same source must collapse to one.
    val r = R"q"(S"s") := product(S"s"("foo"), S"s"("foo"))
    val og = optimize(transpile(r))
    def subgraphs(gg: RecursiveOpGraph): Vector[RecursiveOpGraph] =
      gg.nodes.collect { case Right(sg) => sg }.toVector
    println("[share] after:\n" + og.show)
    assertEquals(subgraphs(og).length, 2, s"expected ONE merged head-loop + ONE merged guard, got:\n${og.show}")
    for sv <- Seq(SpaceValue("foo.a", "foo.b"), SpaceValue("foo"), SpaceValue()) do
      val ref = eval(r.body)(using sc = SpaceContextMap(Map(SpaceMention("s") -> sv)))
      assertEquals(runGraphT(og, mentions = Map("s" -> ITrie.fromSpaceValue(sv))).toSpaceValue, ref, s"sv=$sv")
  }
