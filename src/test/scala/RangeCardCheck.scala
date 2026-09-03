package morkl

import munit.FunSuite

/** `RangeBounds.normalize` LIFTED OVER AN INPUT-SIZE INTERVAL, checked against the function itself.
 *
 *  `Range` is the one operator whose result is not a function of MEMBERSHIP: whether a path survives
 *  depends on its RANK in the canonical order (`docs/TRUSTED.md` T5). The analysis therefore cannot
 *  say which paths a window keeps, but it can say HOW MANY — and the review requires both endpoints,
 *  "for every bound form".
 *
 *  `SpatialTyping.windowWidth` used to give an upper bound only, by a case split on the signs of
 *  `start` and `end` with `INF` for three of the forms. Two things were wrong with that beyond the
 *  missing lower endpoint: it was a SECOND IMPLEMENTATION of `normalize`'s arithmetic and could
 *  disagree with it (its `start == 0 && end > 0` arm returns `end` where `normalize` clamps to
 *  `size`), and the width is NOT MONOTONE in the source size, so no case split on signs alone gets
 *  the extrema right.
 *
 *  This file is the ground-truth check: for every bound pair in a range that covers all nine sign
 *  combinations, and every size interval up to a bound, EXHAUST the sizes in the interval, take the
 *  true min and max of `normalize`'s own width, and require `windowCard` to contain them — and to be
 *  exactly them, because an interval lift of a piecewise-linear function has no reason to be loose.
 */
class RangeCardCheck extends FunSuite:

  private def trueWidth(size: Int, start: Int, end: Int): Long =
    val (lo, hi) = RangeBounds.normalize(size, start, end)
    (hi - lo).toLong

  private val bounds = (-6 to 6).toVector

  test("EXACT against normalize itself, exhaustively, over every bound form and size interval") {
    var checked = 0
    var loose = Vector.empty[String]
    var unsound = Vector.empty[String]
    for start <- bounds; end <- bounds; sLo <- 0 to 12; sHi <- sLo to 12 do
      val truth = (sLo to sHi).map(s => trueWidth(s, start, end))
      val got = SpatialTyping.windowCard(Ivl(sLo.toLong, sHi.toLong), start, end)
      checked += 1
      if got.lo > truth.min || got.hi < truth.max then
        unsound = unsound :+ s"Range(_,$start,$end) size[$sLo,$sHi]: true [${truth.min}, ${truth.max}] " +
                             s"but predicted ${got.show} — DOES NOT CONTAIN"
      else if got.lo != truth.min || got.hi != truth.max then
        loose = loose :+ s"Range(_,$start,$end) size[$sLo,$sHi]: true [${truth.min}, ${truth.max}] " +
                         s"predicted ${got.show}"
    assertEquals(unsound, Vector.empty[String],
      s"${unsound.length} of $checked lifts are UNSOUND:\n  " + unsound.take(12).mkString("\n  "))
    assertEquals(loose, Vector.empty[String],
      s"${loose.length} of $checked lifts are sound but LOOSE:\n  " + loose.take(12).mkString("\n  "))
    println(s"RANGE-CARD: $checked (bound-pair, size-interval) lifts, all EXACT " +
            s"(${bounds.length}x${bounds.length} bound pairs x 91 intervals)")
  }

  test("EXACT at a different MAGNITUDE too — the breakpoint set has to scale with the bounds") {
    // the sweep above has |bound| <= 6 and size <= 12, so every breakpoint it needs is small.  This
    // one moves both an order of magnitude out, which is where a breakpoint set that happened to be
    // right by coincidence would come apart.
    var bad = Vector.empty[String]
    var n = 0
    for start <- (-42 to -36) ++ (36 to 42); end <- (-42 to -36) ++ (36 to 42)
        sLo <- 30 to 46; sHi <- sLo to 46 do
      val truth = (sLo to sHi).map(s => trueWidth(s, start, end))
      val got = SpatialTyping.windowCard(Ivl(sLo.toLong, sHi.toLong), start, end)
      n += 1
      if got.lo != truth.min || got.hi != truth.max then
        bad = bad :+ s"Range(_,$start,$end) size[$sLo,$sHi]: true [${truth.min}, ${truth.max}] " +
                     s"predicted ${got.show}" + (if got.lo > truth.min || got.hi < truth.max then " UNSOUND" else "")
    assertEquals(bad, Vector.empty[String],
      s"${bad.length} of $n lifts are not exact:\n  " + bad.take(12).mkString("\n  "))
    println(s"RANGE-CARD: $n more lifts at |bound| in 36..42, size in 30..46, all EXACT")
  }

  test("the NON-MONOTONICITY that makes endpoint-only evaluation unsound is real") {
    // `Range(x, -3, 5)`: lo = size-3, hi = 4, so the width SHRINKS as the source grows
    val ws = (0 to 10).map(s => trueWidth(s, -3, 5))
    assert(ws.zip(ws.tail).exists((a, b) => b < a),
           s"the fixture is meant to be non-monotone in size, got $ws")
    // and the maximum is attained strictly INSIDE [0, 10], which is what an endpoint-only lift misses
    val interior = ws.slice(1, ws.length - 1)
    assert(interior.max > math.max(ws.head, ws.last),
           s"the maximum should be interior; got $ws")
    val got = SpatialTyping.windowCard(Ivl(0, 10), -3, 5)
    assertEquals(got, Ivl(ws.min, ws.max), "the lift must find the interior maximum")
  }

  // ---- the two endpoint slices the review names by hand ----------------------------------------
  test("Range(x, 0, 1) is the FIRST path: exactly one where the source is non-empty, else empty") {
    for n <- 0 to 8 do
      assertEquals(trueWidth(n, 0, 1), if n == 0 then 0L else 1L, s"|x| = $n")
    // empty source: provably empty window
    assertEquals(SpatialTyping.windowCard(Ivl(0, 0), 0, 1), Ivl(0, 0))
    // provably non-empty source: provably a SINGLETON — both endpoints 1, which is the fact the
    // predecessor could not state at all (its lower endpoint was always 0)
    assertEquals(SpatialTyping.windowCard(Ivl(1, 1), 0, 1), Ivl(1, 1))
    assertEquals(SpatialTyping.windowCard(Ivl(1, 100), 0, 1), Ivl(1, 1))
    assertEquals(SpatialTyping.windowCard(Ivl(1, Ivl.INF), 0, 1), Ivl(1, 1))
    // size not known non-empty: [0, 1]
    assertEquals(SpatialTyping.windowCard(Ivl(0, 5), 0, 1), Ivl(0, 1))
  }

  test("Range(x, -1, 0) is the LAST path: the same, from the other end") {
    for n <- 0 to 8 do
      assertEquals(trueWidth(n, -1, 0), if n == 0 then 0L else 1L, s"|x| = $n")
    assertEquals(SpatialTyping.windowCard(Ivl(0, 0), -1, 0), Ivl(0, 0))
    assertEquals(SpatialTyping.windowCard(Ivl(1, 1), -1, 0), Ivl(1, 1))
    assertEquals(SpatialTyping.windowCard(Ivl(1, Ivl.INF), -1, 0), Ivl(1, 1))
    assertEquals(SpatialTyping.windowCard(Ivl(0, 5), -1, 0), Ivl(0, 1))
  }

  test("a FULL window is the identity, and its cardinality says so on both endpoints") {
    for n <- 0 to 8 do assertEquals(trueWidth(n, 0, 0), n.toLong, s"|x| = $n")
    assertEquals(SpatialTyping.windowCard(Ivl(3, 3), 0, 0), Ivl(3, 3))
    assertEquals(SpatialTyping.windowCard(Ivl(2, 7), 0, 0), Ivl(2, 7))
    assertEquals(SpatialTyping.windowCard(Ivl(0, Ivl.INF), 0, 0), Ivl(0, Ivl.INF))
    assertEquals(SpatialTyping.windowCard(Ivl(4, Ivl.INF), 0, 0), Ivl(4, Ivl.INF))
  }

  test("CLAMPING, NEGATIVE and MIXED-SIGN bounds, stated as the values they take") {
    // clamping: a window past the end keeps what there is
    assertEquals(SpatialTyping.windowCard(Ivl(3, 3), 0, 10), Ivl(3, 3))
    assertEquals(SpatialTyping.windowCard(Ivl(0, 3), 0, 10), Ivl(0, 3))
    // both negative: a fixed-width tail window, clamped by the source
    assertEquals(SpatialTyping.windowCard(Ivl(9, 9), -4, -1), Ivl(3, 3))
    assertEquals(SpatialTyping.windowCard(Ivl(2, 2), -4, -1), Ivl(1, 1))
    // mixed sign, start > 0 && end < 0: width GROWS with the source
    assertEquals(SpatialTyping.windowCard(Ivl(10, 10), 3, -2), Ivl(trueWidth(10, 3, -2), trueWidth(10, 3, -2)))
    assert(SpatialTyping.windowCard(Ivl(0, Ivl.INF), 3, -2).hi == Ivl.INF,
           "start > 0 && end < 0 grows without bound")
    // mixed sign, start < 0 && end > 0: width SHRINKS with the source and collapses to 0
    assertEquals(SpatialTyping.windowCard(Ivl(20, 20), -3, 5), Ivl(0, 0))
    assert(SpatialTyping.windowCard(Ivl(0, Ivl.INF), -3, 5).hi != Ivl.INF,
           "start < 0 && end > 0 does NOT grow without bound")
  }

  test("the lift agrees with the EXECUTOR, not only with normalize") {
    // `sliceRange` is what `eval` runs; the cardinality claim has to bound IT
    def sv(n: Int): Set[PathValue] = (0 until n).map(i => PathValue(List("p" + ('a' + i).toChar))).toSet
    for n <- 0 to 8; start <- -4 to 4; end <- -4 to 4 do
      val got = sliceRange(sv(n), start, end).size.toLong
      val pred = SpatialTyping.windowCard(Ivl(n.toLong, n.toLong), start, end)
      assert(pred.lo <= got && got <= pred.hi,
             s"|x|=$n Range(_,$start,$end): sliceRange kept $got, predicted ${pred.show}")
  }
end RangeCardCheck
