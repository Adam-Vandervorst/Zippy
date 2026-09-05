package morkl

import munit.FunSuite

/** ==================================================================================================
 *  THE RANK ABSTRACTION, CHECKED AGAINST EVERY EXECUTOR.
 *
 *  `Range` is the one operator whose result is not a function of membership: which paths survive
 *  depends on their RANK in the canonical order, which is why `docs/TRUSTED.md` T5 records `Range` as
 *  being outside the certified pointwise algebra.  The analysis used to know only the WINDOW WIDTH —
 *  `Shape.range` kept every head and capped the count, so `Range(x, 0, 1)` over a four-head literal
 *  reported "one path, any of four heads".
 *
 *  `Shape.orderMin` / `orderMax` and `Shape.rangeAt` are the rank abstraction, and this suite is
 *  what makes them a claim rather than an idea:
 *
 *   A. THE RANK ITSELF, against `pathValueOrdering`.  `orderMin`/`orderMax` are checked against the
 *      actual minimum and maximum of the concrete path set, on shapes built from literals — so the
 *      abstraction is compared with the ORDER IT CLAIMS TO ABSTRACT, not with another abstraction.
 *   B. `None` IS CHECKED TOO, and this is the half that matters.  An abstraction that answered
 *      `Some` whenever it felt like it would pass A on every determined case; what makes it sound is
 *      that it says `None` exactly where the shape does not determine the rank — an untracked head
 *      (no known position) or a may-present ε.  Those two are exercised directly.
 *   C. SOUNDNESS OF THE TRANSFER, differentially against ALL SEVEN EXECUTORS.  For each case the
 *      inferred type must ACCEPT the value every executor computes.  Seven, not one, because
 *      `execZ`'s `Range` is a fused cursor slice rather than a call into `ITrie.range` and is the
 *      backend most able to disagree about order — the same reason `RangeOrderCheck` exists.
 *   D. IT ACTUALLY TIGHTENS, measured.  A transfer that fell back to the width-only reading
 *      everywhere would pass A, B and C; the point of the task is that `Range(x, 0, 1)` becomes a
 *      NAMED singleton, so the suite asserts the `Fact.SelectedPath` appears and that the head set
 *      narrows on the wider slices.
 *  ================================================================================================== */
class RangeRankCheck extends FunSuite:
  import Space.*

  private def pv(s: String): PathValue = PathValue(s.split('.').toList)
  private def sv(xs: String*): SpaceValue = SpaceValue(xs.map(pv).toSet)
  private def lit(xs: String*): Space = Literal(sv(xs*))

  private def shapeOf(v: SpaceValue): Shape = Shape.of(v)

  // ------------------------------------------------------------------------------------------------
  // A. THE RANK, against the order it abstracts
  // ------------------------------------------------------------------------------------------------

  private val litCases: Vector[Vector[String]] = Vector(
    Vector("a"),
    Vector("a", "b"),
    Vector("b", "a"),
    Vector("a.1", "a.2", "b.3", "c.4"),
    Vector("a", "a.1"),                       // shorter-is-less on a shared prefix
    Vector("a.1", "a", "a.0"),
    Vector("z", "a.b.c", "a.b"),
    Vector("m.1", "m.2", "m.3", "n.1", "n.2"),
  )

  test("A. orderMin/orderMax agree with pathValueOrdering on every literal shape") {
    for xs <- litCases do
      val v = sv(xs*)
      val sorted = v.paths.toVector.sorted(using pathValueOrdering)
      val sh = shapeOf(v)
      assertEquals(sh.orderMin, Some(sorted.head),
        s"orderMin disagrees with the canonical order on {${xs.mkString(", ")}}: the least path is " +
        s"${sorted.head.show}")
      assertEquals(sh.orderMax, Some(sorted.last),
        s"orderMax disagrees with the canonical order on {${xs.mkString(", ")}}: the greatest path " +
        s"is ${sorted.last.show}")
  }

  test("A'. the empty shape determines no rank, and a lone ε is both endpoints") {
    assertEquals(Shape.empty.orderMin, None, "the empty shape has no least element to name")
    assertEquals(Shape.empty.orderMax, None, "…nor a greatest")
    val justEps = shapeOf(SpaceValue(Set(PathValue(Nil))))
    assertEquals(justEps.orderMin, Some(PathValue(Nil)),
      "ε has length 0 and is a prefix of everything, so it is the minimum whenever it is present")
    assertEquals(justEps.orderMax, Some(PathValue(Nil)),
      "and it is also the maximum when the space has nothing else")
  }

  // ------------------------------------------------------------------------------------------------
  // B. `None` WHERE THE SHAPE DOES NOT DETERMINE THE RANK — the soundness half
  // ------------------------------------------------------------------------------------------------

  test("B. an UNTRACKED head defeats both endpoints: it has no known position") {
    // `Shape.top` has `others = [0, INF]`: an untracked head's item could sort before every tracked
    // head, after all of them, or between any two, so no rank claim survives it in either
    // direction.  This is the case an abstraction that guessed would get wrong.
    assertEquals(Shape.top.orderMin, None,
      "⊤ named a least path.  An untracked head has no known position, so there is nothing to name.")
    assertEquals(Shape.top.orderMax, None, "⊤ named a greatest path")
    // and the same for a shape that tracks SOME heads and has untracked ones as well
    val partial = Shape.union(shapeOf(sv("a", "b")), Shape.top)
    assertEquals(partial.orderMin, None,
      s"a shape with untracked heads named a least path: ${partial.show}")
    assertEquals(partial.orderMax, None, s"…and a greatest: ${partial.show}")
  }

  test("B'. a MAY-present ε defeats orderMin but not orderMax") {
    // ε is the SMALLEST element, so a may-present ε makes the minimum undetermined (it is ε when
    // present and the least head otherwise) while leaving the maximum alone.  This asymmetry is why
    // the two endpoints are separate functions rather than one `Option[(min, max)]`.
    val certain = shapeOf(sv("a", "b"))
    // the LUB of "{ε,a,b}" and "{a,b}": ε is MUST on one side and NO on the other, so the join's ε
    // is MAY — which is the shape the test needs and the only honest way to build it (a `Literal`
    // always gives a MUST or a NO).
    val mayEps = Shape.lub(shapeOf(SpaceValue(Set(PathValue(Nil), pv("a"), pv("b")))), certain)
    assert(mayEps.eps == Presence.May,
      s"the probe shape does not have a MAY-present ε (${mayEps.eps}); the test measures nothing")
    assertEquals(mayEps.orderMin, None,
      s"a may-present ε named a least path: it is ε when present and `a` otherwise, so the least " +
      s"element is not determined.  ${mayEps.show}")
    assertEquals(mayEps.orderMax, Some(pv("b")),
      s"a may-present ε should not disturb the GREATEST element, which is `b` either way.  " +
      s"${mayEps.show}")
  }

  // ------------------------------------------------------------------------------------------------
  // C. SOUNDNESS, differentially against all seven executors
  // ------------------------------------------------------------------------------------------------

  /** every executor's answer for a closed term.  The same seven `RangeOrderCheck` uses, and for the
   *  same reason: `execZ`'s `Range` is a fused cursor slice, not a call into `ITrie.range`. */
  private def allBackends(prog: Space): Vector[(String, SpaceValue)] =
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
    val g = transpile(Routine(RoutinePtr("r"), Vector.empty, Vector.empty, prog))
    Vector(
      "eval"            -> eval(prog),
      "evalT"           -> evalT(prog).toSpaceValue,
      "evalI"           -> evalI(prog).toSpaceValue,
      "execZ"           -> execZ(prog).toSpaceValue,
      "exec"            -> runGraph(g),
      "execT"           -> runGraphT(g).toSpaceValue,
      "execT/optimized" -> runGraphT(optimize(g)).toSpaceValue,
    )

  /** the windows worth checking: the two the plan names, plus wider and boundary slices */
  private val windows: Vector[(Int, Int)] =
    Vector((0, 1), (-1, 0), (0, 2), (0, 3), (2, 3), (1, 2), (-2, 0), (0, 0), (0, 99), (5, 6))

  test("C. the inferred type ACCEPTS every executor's answer, on every window") {
    var checked = 0
    for xs <- litCases; (lo, hi) <- windows do
      val prog = Range(lit(xs*), lo, hi)
      val answers = allBackends(prog)
      // the executors must agree with each other first, or "the type accepts the answer" is
      // ambiguous about which answer
      val distinct = answers.map(_._2).distinct
      assertEquals(distinct.length, 1,
        s"the executors disagree on Range({${xs.mkString(",")}}, $lo, $hi): " +
        answers.map((n, v) => s"$n=${v.show}").mkString("  "))
      val got = distinct.head
      val t = SpatialTyping.infer(prog, SpatialTyping.Env())
      assert(SpatialType.accepts(t, got),
        s"the inferred type REJECTS the value every executor computed.\n" +
        s"  term    Range({${xs.mkString(",")}}, $lo, $hi)\n" +
        s"  value   ${got.show}\n" +
        s"  type    ${t.show}\n" +
        "That is an UNSOUND transfer: `Shape.rangeAt` dropped a head the window actually selects, " +
        "or pinned the wrong rank.")
      checked += 1
    println(s"RANGE-RANK: $checked (literal, window) pairs accepted by the inferred type, " +
            s"7 executors agreeing on each")
  }

  test("C'. soundness holds under a binder and over a non-literal source") {
    // `Range` under an `Iteration` and over a `TailsUnion`: the source's shape is then built by a
    // transfer rather than read off a literal, which is where a rank claim could be made on a
    // shape whose head order does not match the value's.
    val cases: Vector[Space] = Vector(
      Range(TailsUnion(lit("a.1", "a.2", "b.3")), 0, 1),
      Range(TailsUnion(lit("a.1", "a.2", "b.3")), -1, 0),
      Range(Union(lit("a", "c"), lit("b")), 0, 1),
      Range(Union(lit("a", "c"), lit("b")), 0, 2),
      Range(Intersection(lit("a", "b", "c"), lit("b", "c", "d")), 0, 1),
      Range(Wrap(lit("1", "2"), Path.Constant(pv("p"))), 0, 1),
      Iteration(lit("h.1", "h.2", "g.3"), PathRef("y"), SpaceMention("rest"),
                Range(Mention(SpaceMention("rest")), 0, 1)),
      Range(Range(lit("a", "b", "c", "d"), 0, 3), -1, 0),
    )
    for prog <- cases do
      val answers = allBackends(prog)
      val distinct = answers.map(_._2).distinct
      assertEquals(distinct.length, 1,
        s"the executors disagree on ${prog.show.replace('\n', ' ')}: " +
        answers.map((n, v) => s"$n=${v.show}").mkString("  "))
      val t = SpatialTyping.infer(prog, SpatialTyping.Env())
      assert(SpatialType.accepts(t, distinct.head),
        s"the inferred type REJECTS the computed value.\n  term  ${prog.show.replace('\n', ' ')}\n" +
        s"  value ${distinct.head.show}\n  type  ${t.show}")
  }

  test("C''. THE WITNESS: a MIXED-SIGN window, where the width is not monotone in the size") {
    // `SpatialSoundnessHunt` HUNT 2 found this on the first run of the rank transfer, and it is the
    // one case a hand-written window list would not have covered.  The first `rangeAt` fell back to
    // a width it computed itself from `sz.hi`, and THE WINDOW WIDTH IS NOT MONOTONE IN THE SIZE once
    // a bound counts from the end:
    //
    //     RangeBounds.normalize(1, -2, 2) = (0, 1)   width 1
    //     RangeBounds.normalize(3, -2, 2) = (0, 0)   width 0
    //
    // so the width at the size's UPPER endpoint bounds nothing, and the transfer reported
    // `DefinitelyEmpty` for a term evaluating to `{b.c}`.  `SpatialTypeSystem.windowCard` does the
    // breakpoint analysis this needs; `rangeAt` is now `Option`-valued and computes no width at all.
    //
    // Pinned here as well as in the hunt because a 100 000-case search is the wrong place to learn
    // that one arithmetic identity is false: this runs in milliseconds and names the reason.
    assertEquals(RangeBounds.normalize(1, -2, 2), (0, 1),
      "the premise of this regression has changed: at size 1 the mixed-sign window is non-empty")
    assertEquals(RangeBounds.normalize(3, -2, 2), (0, 0),
      "…and at size 3 it collapses, which is what makes the width non-monotone")
    // the shape of the witness: a source whose size the analysis does NOT pin, under a mixed-sign
    // window.  `Fixpoint` over an opaque body is the hunt's generator; `Mention` of an untyped input
    // is the same situation in one node.
    val opaque = Mention(SpaceMention("s1"))
    for (lo, hi) <- Vector((-2, 2), (-1, 2), (-3, 3), (2, -1), (-2, -1), (1, -1)) do
      val prog = Range(opaque, lo, hi)
      val env = SpatialTyping.Env(spaces = Map(SpaceMention("s1") ->
        SpatialType.of(sv("b.c"))))
      val t = SpatialTyping.infer(prog, env)
      given PathContext = PathContextMap(Map.empty)
      given SpaceContext = SpaceContextMap(Map(SpaceMention("s1") -> sv("b.c")))
      given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
      val got = eval(prog)
      assert(SpatialType.accepts(t, got),
        s"the inferred type REJECTS the computed value on the mixed-sign window ($lo, $hi).\n" +
        s"  value ${got.show}\n  type  ${t.show}\n" +
        "This is the HUNT 2 witness's shape: the window width is not monotone in the size, so a " +
        "width read off the size's upper endpoint bounds nothing.")
  }

  // ------------------------------------------------------------------------------------------------
  // D. IT TIGHTENS — otherwise the task delivered nothing
  // ------------------------------------------------------------------------------------------------

  test("D. `Range(x, 0, 1)` yields a NAMED singleton, not `one path, any head`") {
    for xs <- litCases do
      val v = sv(xs*)
      val least = v.paths.toVector.sorted(using pathValueOrdering).head
      val t = SpatialTyping.infer(Range(lit(xs*), 0, 1), SpatialTyping.Env())
      assertEquals(t.shape.orderMin, Some(least),
        s"Range({${xs.mkString(",")}}, 0, 1) did not pin the least path ${least.show}")
      assert(Fact.from(t).contains(Fact.SelectedPath(least)),
        s"no `SelectedPath` fact for Range({${xs.mkString(",")}}, 0, 1): the type is a singleton " +
        s"but does not NAME its member, which is what an optimiser needs.  facts=${Fact.from(t).map(_.show)}")
      // and the head set is a SINGLETON, not the source's whole head set
      if least.items.nonEmpty then
        assertEquals(t.shape.heads.keySet.filter(h => t.shape.heads(h).possiblyNonEmpty),
                     Set(least.items.head),
                     s"the head set did not narrow to the selected path's head on {${xs.mkString(",")}}")
  }

  test("D'. `Range(x, -1, 0)` yields the greatest path at an exact size") {
    for xs <- litCases do
      val v = sv(xs*)
      val greatest = v.paths.toVector.sorted(using pathValueOrdering).last
      val t = SpatialTyping.infer(Range(lit(xs*), -1, 0), SpatialTyping.Env())
      assertEquals(t.shape.orderMax, Some(greatest),
        s"Range({${xs.mkString(",")}}, -1, 0) did not pin the greatest path ${greatest.show}")
  }

  test("D''. a WIDER window narrows the head set where a bound follows") {
    // `{m.1,m.2,m.3,n.1,n.2}`: the first three paths are all under `m`, so `Range(x, 0, 3)`'s head
    // set is `{m}` and not `{m, n}`.  This is the "extended to wider slices where a bound follows"
    // half of the task — the window's BLOCK arithmetic, not just the singleton case.
    val xs = Vector("m.1", "m.2", "m.3", "n.1", "n.2")
    def headsOf(lo: Int, hi: Int): Set[PathItem] =
      val t = SpatialTyping.infer(Range(lit(xs*), lo, hi), SpatialTyping.Env())
      t.shape.heads.keySet.filter(h => t.shape.heads(h).possiblyNonEmpty)
    assertEquals(headsOf(0, 3), Set[PathItem]("m"),
      "the three least paths are all under `m`, so the window cannot reach `n`")
    assertEquals(headsOf(0, 4), Set[PathItem]("m", "n"),
      "the fourth path is under `n`, so both heads are reachable")
    assertEquals(headsOf(4, 5), Set[PathItem]("n"),
      "positions 4..5 are entirely inside `n`'s block, so `m` is not selected")
    assertEquals(headsOf(0, 5), Set[PathItem]("m", "n"), "the whole slice keeps both")
    // and the soundness of each of those, against the executors
    for (lo, hi) <- Vector((0, 3), (0, 4), (4, 5), (0, 5)) do
      val prog = Range(lit(xs*), lo, hi)
      val got = allBackends(prog).map(_._2).distinct
      assertEquals(got.length, 1, s"executors disagree on Range(_, $lo, $hi)")
      assert(SpatialType.accepts(SpatialTyping.infer(prog, SpatialTyping.Env()), got.head),
        s"the narrowed type rejects the computed value for Range(_, $lo, $hi): ${got.head.show}")
  }
end RangeRankCheck
