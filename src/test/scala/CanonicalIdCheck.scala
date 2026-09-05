package morkl

import munit.FunSuite

/** THE RESIDUAL IDENTITY: injective, total, stable — and refusing where it cannot be.
 *
 *  `AgnosticPipeline.ResidualCut.symbol` names the fresh free input that `unrollControl` puts in
 *  place of a recursive call past depth `k`, and that name is written into COMMITTED `.egg`/`.smt2`
 *  artifacts. The obligation those artifacts state is "the two k-unrollings agree for all values of
 *  that input", which is sound only if both sides cut the same thing — so the name has to be a
 *  function of the cut, and of nothing else.
 *
 *  IT WAS A 32-BIT PREFIX OF SHA-256 OVER `Space.show`, and each of those three choices was wrong
 *  in its own way. This file pins the replacement in the four directions that matter, one test
 *  each, because they fail independently:
 *
 *    TOTALITY   `Space.show` has no `Fold` arm, so the old digest THREW on a `Fold` argument.
 *    INJECTIVITY `show` renders `Wrap(src, p)` as `(p x src)` and `Composition(x, y)` as `(x x y)`.
 *    STABILITY  grounded nodes rendered as `f.hashCode()`, a per-JVM identity hash — so the same
 *               term digested differently in a fresh JVM, and the artifact would differ with it.
 *    REFUSAL    and because no stable identity for an arbitrary Scala function exists at all
 *               (`docs/TRUSTED.md` T6), the encoder must decline rather than invent one.
 */
class CanonicalIdCheck extends FunSuite:
  import Space.*
  import AgnosticPipeline.{CanonicalId, ResidualCut}

  private def sv(xs: String*): SpaceValue =
    SpaceValue(xs.map(s => PathValue(s.split('.').toList)).toSet)
  private val a: Space = Mention(SpaceMention("a"))
  private val b: Space = Mention(SpaceMention("b"))
  private val h = PathRef("h").known(1)
  private val pk = Path.Constant(PathValue(List("k")))
  private val dh: Path = Path.Deref(h)

  /** every constructor of `Space`, with a grounded-free body wherever one is possible */
  private val allSpaces: Vector[(String, Space)] = Vector(
    "Empty" -> Empty,
    "Mention" -> a,
    "Singleton" -> Singleton(dh),
    "Literal" -> Literal(sv("x.y", "z")),
    "Union" -> Union(a, b),
    "Intersection" -> Intersection(a, b),
    "Subtraction" -> Subtraction(a, b),
    "Restriction" -> Restriction(a, b),
    "Raffination" -> Raffination(a, b),
    "Composition" -> Composition(a, b),
    "Wrap" -> Wrap(a, pk),
    "Unwrap" -> Unwrap(a, pk),
    "TailsUnion" -> TailsUnion(a),
    "TailsIntersection" -> TailsIntersection(a),
    "Range" -> Range(a, 0, 1),
    "Iteration" -> Iteration(a, h, SpaceMention("t"), Wrap(Mention(SpaceMention("t")), dh)),
    "Fixpoint" -> Fixpoint(a, SpaceMention("r"), Union(Mention(SpaceMention("r")), b)),
    "Fold" -> Fold(a, pk, PathRef("acc"), h, SpaceMention("t"), Mention(SpaceMention("t")), pk),
    "Call" -> Call(RoutinePtr("f"), Vector(dh), Vector(a, b)),
  )

  // ---- TOTALITY -------------------------------------------------------------------------------
  test("TOTAL over every non-grounded constructor — including the `Fold` arm `show` does not have") {
    val missing = allSpaces.filter((_, s) => CanonicalId.of(s).isEmpty).map(_._1)
    assertEquals(missing, Vector.empty[String],
      s"CanonicalId.of returned None for: ${missing.mkString(", ")} — None means 'contains a " +
      "grounded node', and none of these do")
    // AND `Space.show` IS NOW TOTAL TOO, which this test used to assert the opposite of.
    // `intercept[MatchError]` stood here, pinning the fact that `show` had no `Fold` arm -- and
    // pinning it was a mistake: `ResidualCut.canonical` renders through `show`, and `canonical` is
    // what the collision guard compares, what `alignCuts` uses in production, and what the emitters
    // print into COMMITTED artifacts.  So the `MatchError` the digest no longer throws was still
    // reachable one call away, and a test asserting its presence made that look intended.
    val f = Fold(a, pk, PathRef("acc"), h, SpaceMention("t"), Mention(SpaceMention("t")), pk)
    val shown = f.show
    assert(shown.contains("fold"), s"a Fold must render as a fold: $shown")
    assert(shown.contains("acc"), s"the accumulator binder must appear: $shown")
    // and the whole cut descriptor, which is the path that actually mattered
    val cut = ResidualCut("tc", 1, Vector.empty, Vector(f))
    assert(cut.canonical.contains("fold"), s"canonical must render a Fold argument: ${cut.canonical}")
    assert(cut.symbol.startsWith("residual_tc_1_"), cut.symbol)
    // every Path constructor too
    for p <- Vector(dh, pk, Path.Concat(pk, dh)) do
      assert(CanonicalId.ofPath(p).isDefined, s"CanonicalId.ofPath returned None for ${p.show}")
  }

  // ---- INJECTIVITY ----------------------------------------------------------------------------
  test("INJECTIVE across all constructors — no two distinct terms share a key") {
    val keys = allSpaces.map((n, s) => n -> CanonicalId.of(s).get)
    val dupes = keys.groupBy(_._2).filter(_._2.size > 1)
    assertEquals(dupes, Map.empty[String, Vector[(String, String)]],
      s"distinct terms share a canonical key: $dupes")
  }

  test("INJECTIVE on the pair `show` conflates: Wrap(src, p) vs Composition") {
    // `show` renders `Wrap(a, p)` as `(p x a)` and `Composition(x, y)` as `(x x y)` — one syntax
    val w = Wrap(a, pk)
    val c = Composition(Singleton(pk), a)
    assertNotEquals(CanonicalId.of(w).get, CanonicalId.of(c).get,
      "Wrap and Composition share a canonical key")
    // operand ORDER must matter where the operator is not commutative
    assertNotEquals(CanonicalId.of(Subtraction(a, b)).get, CanonicalId.of(Subtraction(b, a)).get)
    assertNotEquals(CanonicalId.of(Restriction(a, b)).get, CanonicalId.of(Restriction(b, a)).get)
    // and the length prefixes must stop a concatenation from being ambiguous: `S"ab" u S"c"`
    // against `S"a" u S"bc"` is the classic way an unprefixed encoder collides
    def m(x: String): Space = Mention(SpaceMention(x))
    assertNotEquals(CanonicalId.of(Union(m("ab"), m("c"))).get,
                    CanonicalId.of(Union(m("a"), m("bc"))).get,
                    "an unprefixed encoding would make these two the same string")
    // Range's bounds are part of the identity
    assertNotEquals(CanonicalId.of(Range(a, 0, 1)).get, CanonicalId.of(Range(a, -1, 0)).get)
    assertNotEquals(CanonicalId.of(Range(a, 0, 12)).get, CanonicalId.of(Range(a, 1, 2)).get)
    // a Fold differing in ONE field only
    def fold(initial: Path = pk, upd: Path = pk, acc: String = "acc"): Space =
      Fold(a, initial, PathRef(acc), h, SpaceMention("t"), Mention(SpaceMention("t")), upd)
    assertNotEquals(CanonicalId.of(fold()).get,
                    CanonicalId.of(fold(upd = Path.Concat(pk, pk))).get, "Fold.update")
    assertNotEquals(CanonicalId.of(fold()).get,
                    CanonicalId.of(fold(initial = Path.Concat(pk, pk))).get, "Fold.initial")
    assertNotEquals(CanonicalId.of(fold()).get,
                    CanonicalId.of(fold(acc = "other")).get, "Fold.acc binder")
    // Literal identity is the VALUE, and different values differ
    assertNotEquals(CanonicalId.of(Literal(sv("x"))).get, CanonicalId.of(Literal(sv("y"))).get)
    assertEquals(CanonicalId.of(Literal(sv("x", "y"))).get, CanonicalId.of(Literal(sv("y", "x"))).get,
                 "a Literal is a SET: element order must NOT change the key")
  }

  test("INJECTIVE ON PATH ITEMS — the collision a single-letter alphabet cannot show") {
    // THE DEFECT THIS PINS.  The encoder wrote a path as `items.mkString(" ")` inside ONE
    // length-prefixed string, so any item containing the separator collapsed two distinct terms
    // onto one key: `PathValue(List("a b"))` and `PathValue(List("a", "b"))` both became `"a b"`.
    // Every fixture in this file and in the law suites uses single-letter items, which is exactly
    // why the constructor-by-constructor injectivity checks above could not see it -- a duplicate
    // scan over hand-built terms tests the terms you thought of.
    def pv(xs: String*) = PathValue(xs.toList)
    val pairs = Vector(
      "one item with a space vs two items" -> (pv("a b"), pv("a", "b")),
      "leading separator"                  -> (pv(" a"), pv("", "a")),
      "trailing separator"                 -> (pv("a "), pv("a", "")),
      "two spaces vs three items"          -> (pv("a b c"), pv("a", "b", "c")),
      "empty item vs no item"              -> (pv(""), pv()),
    )
    var collided = Vector.empty[String]
    for (why, (p1, p2)) <- pairs do
      assertNotEquals(p1, p2, s"$why: the fixture must be two DISTINCT PathValues")
      // through a Literal, a Path.Constant, and a whole cut descriptor
      val asLit = (CanonicalId.of(Literal(SpaceValue(Set(p1)))), CanonicalId.of(Literal(SpaceValue(Set(p2)))))
      val asPath = (CanonicalId.ofPath(Path.Constant(p1)), CanonicalId.ofPath(Path.Constant(p2)))
      val asCut = (ResidualCut("r", 0, Vector(Path.Constant(p1)), Vector.empty).symbol,
                   ResidualCut("r", 0, Vector(Path.Constant(p2)), Vector.empty).symbol)
      if asLit._1 == asLit._2 then collided = collided :+ s"$why (Literal)"
      if asPath._1 == asPath._2 then collided = collided :+ s"$why (Path.Constant)"
      if asCut._1 == asCut._2 then collided = collided :+ s"$why (residual symbol)"
    assertEquals(collided, Vector.empty[String],
      s"the encoding COLLIDES on: ${collided.mkString(", ")} — two distinct terms share a residual " +
      "identity, which is the whole defect the collision-safe identity exists to prevent")
    // a Literal is a SET, so element ORDER still must not matter even with multi-item paths
    assertEquals(CanonicalId.of(Literal(SpaceValue(Set(pv("a b"), pv("c"))))).get,
                 CanonicalId.of(Literal(SpaceValue(Set(pv("c"), pv("a b"))))).get,
                 "a Literal's key must be a function of the SET")
  }

  // ---- STABILITY ------------------------------------------------------------------------------
  test("STABLE: the key and the digest depend on the term alone, not on object identity") {
    // structurally equal but distinct objects must key alike (the old grounded `hashCode` did not)
    def build(): Space = Union(Mention(SpaceMention("a")), Literal(sv("x.y")))
    val (s1, s2) = (build(), build())
    assert(!(s1 eq s2), "the fixture must build two distinct objects")
    assertEquals(CanonicalId.of(s1).get, CanonicalId.of(s2).get)
    val c1 = ResidualCut("tc", 2, Vector(dh), Vector(s1))
    val c2 = ResidualCut("tc", 2, Vector(dh), Vector(s2))
    assertEquals(c1.digest, c2.digest)
    assertEquals(c1.symbol, c2.symbol)
    // 256 bits, not 32: the whole hash is kept
    assertEquals(c1.digest.length, 64, s"digest is ${c1.digest.length} hex chars, expected 64")
    assert(c1.digest.forall(ch => ch.isDigit || ('a' to 'f').contains(ch)), c1.digest)
  }

  test("the CUT descriptor's own fields are all in the identity") {
    val base = ResidualCut("tc", 2, Vector(dh), Vector(a))
    val vary = Vector(
      "routine" -> base.copy(routine = "sn"),
      "depth" -> base.copy(depth = 3),
      "path arg" -> base.copy(refs = Vector(pk)),
      "space arg" -> base.copy(mentions = Vector(b)),
      "arity (paths)" -> base.copy(refs = Vector(dh, dh)),
      "arity (spaces)" -> base.copy(mentions = Vector(a, a)),
    )
    for (what, c) <- vary do
      assertNotEquals(base.symbol, c.symbol, s"$what is not part of the residual identity")
  }

  // ---- REFUSAL --------------------------------------------------------------------------------
  test("REFUSES a grounded node rather than inventing an identity for it") {
    val gs: Space = GroundedSS(a, identity)
    val gp: Space = GroundedPS(dh, _ => SpaceValue(Set.empty))
    for g <- Vector(gs, gp, Union(a, gs), Iteration(a, h, SpaceMention("t"), gs)) do
      assertEquals(CanonicalId.of(g), None, s"a grounded node was given an identity: ${g.show}")
    for p <- Vector[Path](Path.GroundedPP(pk, x => x), Path.GroundedSP(a, _ => PathValue(Nil))) do
      assertEquals(CanonicalId.ofPath(p), None, "a grounded PATH was given an identity")
    // ...and the cut fails LOUDLY rather than emitting an unstable symbol into an artifact
    val cut = ResidualCut("tc", 1, Vector.empty, Vector(gs))
    assertEquals(cut.identity, None)
    val ex = intercept[IllegalStateException](cut.symbol)
    assert(ex.getMessage.contains("GROUNDED"), ex.getMessage)
    assert(ex.getMessage.contains("COMMITTED artifact"), ex.getMessage)
  }
end CanonicalIdCheck
