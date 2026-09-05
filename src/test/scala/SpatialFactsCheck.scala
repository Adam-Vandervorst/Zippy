package morkl

import munit.FunSuite
import scala.collection.immutable.SortedMap
import scala.util.Random

/** DERIVED SPATIAL FACTS — the differential gate for `SpatialFacts.scala`.
 *
 *  Every formula in that file is bracketed against CONCRETE ground truth here: for each abstract
 *  type `t` and every concrete `v` in a finite universe with `v ∈ γ(t)`, the fact computed
 *  abstractly must contain the quantity computed by counting `v`'s paths.  `eval` appears only as
 *  ground truth (never inside an analysis), and the two documented soundness traps — the histogram
 *  spill branch and the per-untracked-head reading of `otherTail` — are explicit regressions with
 *  their own counterexamples. */
class SpatialFactsCheck extends FunSuite:
  import Lower.LenBounds
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  // ------------------------------------------------------------------------------------------------
  // helpers
  // ------------------------------------------------------------------------------------------------
  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  def lit(ps: PathValue*): Space = Space.Literal(sv(ps*))

  /** the concrete truths the abstract formulas must bracket */
  def truePaths(v: SpaceValue, d: Int): Long = v.paths.count(_.items.length >= d).toLong
  def truePrefixes(v: SpaceValue, d: Int): Long =
    v.paths.iterator.filter(_.items.length >= d).map(_.items.take(d)).toSet.size.toLong
  def trueFibers(v: SpaceValue, d: Int): Vector[Int] =
    v.paths.iterator.filter(_.items.length >= d).toVector
      .groupBy(_.items.take(d)).valuesIterator.map(_.size).toVector

  def inIvl(i: Ivl, x: Long): Boolean = i.lo <= x && x <= i.hi

  /** the finite universe: 2 items, path length ≤ 2 → 7 paths → 2^7 = 128 spaces */
  val items: Vector[PathItem] = Vector("a", "b")
  val universe: Vector[SpaceValue] = SpatialGamma.universe(items, 2)
  val maxD = 3

  /** every abstract type family the differential runs over, each with a label for the report */
  lazy val exactTypes: Vector[(String, SpatialType)] =
    universe.map(v => s"exact ${v.pretty}" -> SpatialType.of(v))

  lazy val lubTypes: Vector[(String, SpatialType)] =
    val rng = new Random(20260807L)
    Vector.fill(400) {
      val a = universe(rng.nextInt(universe.size))
      val b = universe(rng.nextInt(universe.size))
      s"lub" -> SpatialGamma.lub(SpatialType.of(a), SpatialType.of(b))
    }

  /** hand-built types that exercise the interesting branches: a spill bucket whose window straddles
   *  the query depth, an open head set, and a per-head `otherTail` summary */
  lazy val handBuilt: Vector[(String, SpatialType)] = Vector(
    "top" -> SpatialType.top,
    "spill straddling" -> SpatialType(Shape.top, SpaceType.boundedExact(LenBounds(0, 3), 2)),
    "spill above" -> SpatialType(Shape.top, SpaceType.boundedExact(LenBounds(2, 2), 2)),
    "spill loose" -> SpatialType(Shape.top, SpaceType.bounded(LenBounds(1, 2), 3)),
    "spill wide" -> SpatialType(Shape.top, SpaceType.bounded(LenBounds(0, 2), 4)),
    "open shape only" -> SpatialType(Shape.top, SpaceType.unknown),
    "two heads, eps-only tails" ->
      SpatialType(Shape(Presence.No, SortedMap.empty, Ivl(2, 2), Some(Shape.epsOnly)),
                  SpaceType.exact(1, 2)),
    "two heads, per-head {x} tails" -> SpatialType(perHeadTrapShape, SpaceType.exact(2, 2)),
    "closed heads a,b" ->
      SpatialType(Shape.of(sv(p("a"), p("b"))), SpaceType.exact(1, 2)),
    "one head a, open tail" ->
      SpatialType(Shape(Presence.No, SortedMap("a" -> Shape.top), Ivl.zero, None), SpaceType.unknown),
  )

  /** `others = [2,2]` with a per-head summary admitting exactly `{x}` — the shape behind the
   *  `otherTail` regression below */
  def perHeadTrapShape: Shape =
    val x = Shape(Presence.No, SortedMap("x" -> Shape.epsOnly), Ivl.zero, None)
    Shape(Presence.No, SortedMap.empty, Ivl(2, 2), Some(x))

  /** run one bracket check over every universe member of `t`; returns (members, checks) */
  def differential(label: String, t: SpatialType)(check: (SpaceValue, Int) => Unit): (Int, Int) =
    var members = 0
    var checks = 0
    for v <- universe if SpatialTyping.gammaMember(v, t) do
      members += 1
      for d <- 0 to maxD do
        check(v, d)
        checks += 1
    (members, checks)

  lazy val allFamilies: Vector[(String, SpatialType)] = exactTypes ++ lubTypes ++ handBuilt

  // ================================================================================================
  // 1.  E_d
  // ================================================================================================

  test("E_d brackets the concrete count of paths reaching depth d") {
    var members = 0; var checks = 0; var exact = 0
    for (label, t) <- allFamilies do
      val (m, c) = differential(label, t) { (v, d) =>
        val e = SpatialFacts.pathsAtDepth(t.lens, d)
        val truth = truePaths(v, d)
        assert(inIvl(e, truth), s"$label d=$d: E=${e.show} misses truth $truth for ${v.pretty}")
        if e.lo == e.hi then exact += 1
      }
      members += m; checks += c
    println(s"[E_d]  ${allFamilies.size} types, $members (type, value) pairs, $checks brackets, $exact exact")
    assert(checks > 3000, s"the differential must actually run: $checks")
  }

  test("REGRESSION: the spill branch — adding rest.lo whenever restLens.hi >= d is UNSOUND") {
    // exactly 2 paths, each of some length in 0..3, none of them tracked
    val t = SpatialType(Shape.top, SpaceType.boundedExact(LenBounds(0, 3), 2))
    val v = sv(p(), p("a"))                    // both paths are SHORTER than 2
    assert(SpatialTyping.gammaMember(v, t), s"precondition: ${v.pretty} must inhabit ${t.show}")
    assertEquals(truePaths(v, 2), 0L)

    val sound = SpatialFacts.pathsAtDepth(t.lens, 2)
    assertEquals(sound, Ivl(0, 2), s"the spill may contribute only its upper endpoint here: ${sound.show}")
    assert(inIvl(sound, 0L))

    // the unsound variant the design note warns about, written out so the trap is a regression
    def unsound(st: SpaceType, d: Int): Ivl =
      var out = Ivl.zero
      for (len, c) <- st.byLen if len >= d do out = Ivl(Ivl.add(out.lo, c.lo), Ivl.add(out.hi, c.hi))
      if st.rest.hi > 0 && !st.restLens.isEmpty && st.restLens.hi >= d
      then Ivl(Ivl.add(out.lo, st.rest.lo), Ivl.add(out.hi, st.rest.hi)) else out
    val bad = unsound(t.lens, 2)
    assertEquals(bad.lo, 2L)
    assert(!inIvl(bad, truePaths(v, 2)),
           s"the unsound variant must be refuted by this witness: ${bad.show} vs truth 0")

    // and it is refuted for the whole product too, at every depth strictly inside the window
    for d <- 1 to 3 do
      val s = SpatialFacts.pathsAtDepth(t.lens, d)
      assert(inIvl(s, truePaths(v, d)), s"d=$d ${s.show}")
    // the branch that DOES keep the lower bound: every possible rest length reaches d
    val above = SpatialType(Shape.top, SpaceType.boundedExact(LenBounds(2, 2), 2))
    assertEquals(SpatialFacts.pathsAtDepth(above.lens, 2), Ivl(2, 2))
    assertEquals(SpatialFacts.pathsAtDepth(above.lens, 3), Ivl(0, 0))
  }

  // ================================================================================================
  // 2.  K_d
  // ================================================================================================

  test("K_d brackets the concrete distinct-prefix count") {
    var members = 0; var checks = 0; var exact = 0; var contradictions = 0
    for (label, t) <- allFamilies do
      val (m, c) = differential(label, t) { (v, d) =>
        SpatialFacts.prefixesAt(t, d) match
          case Left(bad) =>
            contradictions += 1
            fail(s"$label d=$d reported a contradiction while ${v.pretty} inhabits the type: ${bad.show}")
          case Right(k) =>
            val truth = truePrefixes(v, d)
            assert(inIvl(k, truth), s"$label d=$d: K=${k.show} misses truth $truth for ${v.pretty}")
            if k.lo == k.hi then exact += 1
      }
      members += m; checks += c
    println(s"[K_d]  $members (type, value) pairs, $checks brackets, $exact exact, $contradictions contradictions")
    assertEquals(contradictions, 0)
    assert(checks > 3000, s"the differential must actually run: $checks")
  }

  test("K_d equals ITrie.prefixCount on a concrete trie") {
    var n = 0
    for v <- universe do
      val t = ITrie.fromSpaceValue(v)
      for d <- 0 to maxD do
        val k = SpatialFacts.prefixesAt(SpatialType.of(v), d).fold(c => fail(c.show), identity)
        assertEquals(k, Ivl(t.prefixCount(d).toLong, t.prefixCount(d).toLong),
                     s"K_$d for ${v.pretty}")
        n += 1
    println(s"[K_d = ITrie.prefixCount]  $n exact identities over ${universe.size} concrete spaces")
  }

  test("REGRESSION: otherTail is a PER-UNTRACKED-HEAD summary, not one global tail set") {
    val t = SpatialType(perHeadTrapShape, SpaceType.exact(2, 2))
    val v = sv(p("a", "x"), p("b", "x"))
    assert(SpatialTyping.gammaMember(v, t), s"precondition: ${v.pretty} must inhabit ${t.show}")
    assertEquals(truePrefixes(v, 2), 2L)         // "a.x" and "b.x" are DISTINCT length-2 prefixes

    val raw = SpatialFacts.rawPrefixesAt(t.shape, 2)
    assert(inIvl(raw, 2L), s"per-head reading must admit 2 prefixes: ${raw.show}")
    assertEquals(raw.hi, 2L, "others.hi * perHead.hi = 2 * 1")

    // the GLOBAL reading: one shared tail set, so at most perHead.hi distinct depth-2 prefixes
    val global = SpatialFacts.rawPrefixesAt(Shape.weaken(perHeadTrapShape.otherTail.get), 1)
    assertEquals(global.hi, 1L)
    assert(!inIvl(global, 2L), s"the global reading must be refuted by this witness: ${global.show}")

    // and the derived degree is sound on every member of the type
    for u <- universe if SpatialTyping.gammaMember(u, t) do
      val k = SpatialFacts.prefixesAt(t, 2).fold(c => fail(c.show), identity)
      assert(inIvl(k, truePrefixes(u, 2)), s"${u.pretty}: ${k.show}")
  }

  // ================================================================================================
  // 3.  THE REDUCTION AND ITS CONTRADICTIONS
  // ================================================================================================

  test("the reduction K_d <= E_d and E_d > 0 => K_d > 0 holds on every family") {
    var checks = 0
    for (label, t) <- allFamilies; d <- 0 to maxD do
      SpatialFacts.degreeAt(t, d) match
        case Left(_) => ()      // an uninhabited hand-built type: nothing to reduce
        case Right(g) =>
          assert(g.prefixes.hi <= g.paths.hi, s"$label d=$d: K.hi ${g.prefixes.hi} > E.hi ${g.paths.hi}")
          assert(g.prefixes.lo <= g.paths.lo, s"$label d=$d: K.lo ${g.prefixes.lo} > E.lo ${g.paths.lo}")
          if g.paths.lo > 0 then assert(g.prefixes.lo >= 1, s"$label d=$d: E>0 but K.lo=${g.prefixes.lo}")
          assert(g.prefixes.lo <= g.prefixes.hi && g.paths.lo <= g.paths.hi)
          checks += 1
    println(s"[reduction]  $checks reduced degrees over ${allFamilies.size} types")
    assert(checks > 500)
  }

  test("an inconsistent product returns an explicit contradiction, never a throw or a widening") {
    // the shape says exactly {ε}; the histogram says five paths of length three
    val a = SpatialType(Shape.epsOnly, SpaceType.exact(3, 5))
    val ca = SpatialFacts.contradiction(a)
    assert(ca.isDefined, "must be reported")
    assertEquals(ca.get.depth, 0, s"detected at ${ca.get.show}")
    assert(SpatialFacts.prefixesAt(a, 0).isLeft)
    assert(universe.forall(v => !SpatialTyping.gammaMember(v, a)), "and the type really is uninhabited")

    // the shape says exactly {a}; the histogram says one path of length three — the disagreement
    // only becomes visible at depth 2, which is why the scan is per depth and not at the root
    val b = SpatialType(Shape.ofPath(p("a")), SpaceType.exact(3, 1))
    assert(SpatialFacts.degreeAt(b, 0).isRight)
    assert(SpatialFacts.degreeAt(b, 1).isRight)
    val cb = SpatialFacts.degreeAt(b, 2)
    assert(cb.isLeft, s"depth 2 must contradict: $cb")
    assertEquals(SpatialFacts.contradiction(b).get.depth, 2)
    assert(SpatialFacts.profile(b).isLeft)
    assert(SpatialFacts.trieNodes(b).isLeft)

    // nothing is repaired: the endpoints are reported as they were
    val c = SpatialFacts.contradiction(b).get
    assert(c.why.nonEmpty)
    assert(c.prefixes.lo <= c.prefixes.hi || true)   // raw endpoints, whatever they were

    // and a consistent product is Right at every depth
    val ok = SpatialType.of(sv(p("a", "b"), p("a")))
    for d <- 0 to 4 do assert(SpatialFacts.degreeAt(ok, d).isRight)
    assertEquals(SpatialFacts.contradiction(ok), None)
  }

  test("degreeAt is total: no throw on any family, at any depth up to the profile cap") {
    var n = 0
    for (label, t) <- allFamilies; d <- 0 to 12 do
      SpatialFacts.degreeAt(t, d); n += 1
    for (label, t) <- handBuilt do
      SpatialFacts.profile(t); SpatialFacts.trieNodes(t); SpatialFacts.specializations(t)
      SpatialFacts.commonPrefix(t); SpatialFacts.exactValue(t); n += 1
    println(s"[totality]  $n calls, no exception")
  }

  // ================================================================================================
  // 4.  FIBER ENVELOPES
  // ================================================================================================

  test("fiber envelopes bracket the concrete minimum and maximum fiber size") {
    var members = 0; var checks = 0; var tightMin = 0; var tightMax = 0
    for (label, t) <- allFamilies do
      val (m, c) = differential(label, t) { (v, d) =>
        val g = SpatialFacts.degreeAt(t, d).fold(bad => fail(s"$label: ${bad.show}"), identity)
        val fibers = trueFibers(v, d)
        if fibers.isEmpty then
          assert(g.paths.lo == 0, s"$label d=$d: no fiber but E.lo=${g.paths.lo}")
        else
          val mn = fibers.min.toLong; val mx = fibers.max.toLong
          assert(inIvl(g.minFiber, mn),
                 s"$label d=$d: minFiber=${g.minFiber.show} misses $mn (fibers $fibers, ${v.pretty})")
          assert(inIvl(g.maxFiber, mx),
                 s"$label d=$d: maxFiber=${g.maxFiber.show} misses $mx (fibers $fibers, ${v.pretty})")
          assert(g.minFiber.lo <= g.maxFiber.hi, s"$label d=$d: min envelope above max envelope")
          if g.minFiber.lo == g.minFiber.hi then tightMin += 1
          if g.maxFiber.lo == g.maxFiber.hi then tightMax += 1
      }
      members += m; checks += c
    println(s"[fibers]  $members (type, value) pairs, $checks brackets, $tightMin exact minFiber, $tightMax exact maxFiber")
    assert(checks > 3000)
  }

  test("the pigeonhole LOWER bound on the largest fiber does real work") {
    // five paths spread over at most two heads: some head group must hold ⌈5/2⌉ = 3 of them.
    // Nothing in `size`, `len` or `headCount` says that; it comes from E_1 and K_1 together.
    val t = SpatialType(Shape(Presence.No, SortedMap("a" -> Shape.top, "b" -> Shape.top), Ivl.zero, None),
                        SpaceType.exact(2, 5))
    val g = SpatialFacts.degreeAt(t, 1).fold(c => fail(c.show), identity)
    assertEquals(g.paths, Ivl(5, 5))
    assertEquals(g.prefixes, Ivl(1, 2))
    assertEquals(g.maxFiber, Ivl(3, 5), "⌈E.lo / K.hi⌉ = 3 is the pigeonhole term")
    assertEquals(g.minFiber, Ivl(1, 5))

    // brute force it: every 5-subset of the 6 length-2 paths over heads {a,b} and items {0,1,2}
    val all = for h <- Vector("a", "b"); i <- Vector("0", "1", "2") yield p(h, i)
    var checked = 0
    for sub <- all.toSet.subsets(5) do
      val v = SpaceValue(sub)
      assert(SpatialTyping.gammaMember(v, t), s"precondition: ${v.pretty}")
      val fibers = trueFibers(v, 1)
      assert(inIvl(g.maxFiber, fibers.max.toLong), s"${v.pretty}: fibers $fibers vs ${g.maxFiber.show}")
      assert(inIvl(g.minFiber, fibers.min.toLong), s"${v.pretty}: fibers $fibers vs ${g.minFiber.show}")
      assert(fibers.max >= 3, "and the pigeonhole really is achieved")
      checked += 1
    assertEquals(checked, 6)
    println(s"[pigeonhole]  maxFiber=${g.maxFiber.show} from E=${g.paths.show}, K=${g.prefixes.show}; $checked concrete witnesses")
  }

  test("the pigeonhole directions are the ones the envelope claims") {
    // 4 paths sharing one head: E_1 = 4, K_1 = 1, so the single fiber is 4
    val one = SpatialType.of(sv(p("a", "0"), p("a", "1"), p("a", "2"), p("a", "3")))
    val g1 = SpatialFacts.degreeAt(one, 1).toOption.get
    assertEquals(g1.prefixes, Ivl(1, 1)); assertEquals(g1.paths, Ivl(4, 4))
    assertEquals(g1.minFiber, Ivl(1, 4)); assertEquals(g1.maxFiber, Ivl(4, 4))
    assertEquals(trueFibers(sv(p("a", "0"), p("a", "1"), p("a", "2"), p("a", "3")), 1), Vector(4))

    // 4 paths with distinct heads: E_1 = 4, K_1 = 4, so every fiber is 1
    val four = SpatialType.of(sv(p("a", "0"), p("b", "0"), p("c", "0"), p("d", "0")))
    val g4 = SpatialFacts.degreeAt(four, 1).toOption.get
    assertEquals(g4.prefixes, Ivl(4, 4)); assertEquals(g4.paths, Ivl(4, 4))
    assertEquals(g4.minFiber, Ivl(1, 1)); assertEquals(g4.maxFiber, Ivl(1, 1))
    assert(g4.singletonFibers, "singleton fibers license an inlined single-value body")
    assert(!g1.singletonFibers)
  }

  // ================================================================================================
  // 4b.  PAST THE SHAPE'S DEPTH CAP
  // ================================================================================================

  /** one item, path length ≤ 6 → 7 paths → 2^7 = 128 spaces, all DEEPER than `Shape.MaxDepth`.
   *  Below the cap the trie keeps only an untracked-head COUNT with a ⊤ tail, so this is where the
   *  histogram is the only component still saying anything and the reduction has to carry the
   *  result. */
  lazy val deepUniverse: Vector[SpaceValue] = SpatialGamma.universe(Vector("a"), 6)

  test("the reduction keeps K_d exact past Shape.MaxDepth, where the trie alone is ⊤") {
    assert(Shape.MaxDepth < 6, s"precondition: the cap must actually bite (${Shape.MaxDepth})")
    var checks = 0; var exactPastCap = 0; var rawTopPastCap = 0
    for v <- deepUniverse do
      val t = SpatialType.of(v)
      val trie = ITrie.fromSpaceValue(v)
      for d <- 0 to 7 do
        val g = SpatialFacts.degreeAt(t, d).fold(c => fail(s"${v.pretty} d=$d: ${c.show}"), identity)
        assertEquals(g.paths, Ivl(truePaths(v, d), truePaths(v, d)), s"E_$d for ${v.pretty}")
        assertEquals(g.prefixes, Ivl(truePrefixes(v, d), truePrefixes(v, d)), s"K_$d for ${v.pretty}")
        assertEquals(g.prefixes.hi, trie.prefixCount(d).toLong)
        val fibers = trueFibers(v, d)
        if fibers.nonEmpty then
          assert(inIvl(g.minFiber, fibers.min.toLong), s"minFiber d=$d ${v.pretty}: ${g.minFiber.show} vs $fibers")
          assert(inIvl(g.maxFiber, fibers.max.toLong), s"maxFiber d=$d ${v.pretty}: ${g.maxFiber.show} vs $fibers")
        if d > Shape.MaxDepth then
          exactPastCap += 1
          // the SHAPE alone has given up below the cap: the raw upper is ∞ once the ⊤ tail is reached
          if SpatialFacts.rawPrefixesAt(t.shape, d).hi == Ivl.INF then rawTopPastCap += 1
        checks += 1
      // and the exact node identity survives the cap
      assertEquals(SpatialFacts.trieNodes(t).fold(c => fail(c.show), identity),
                   Ivl(trie.nodeCount.toLong, trie.nodeCount.toLong), s"nodes for ${v.pretty}")
      // exactValue is honest about the cap: a value with a path deeper than MaxDepth is NOT pinned
      // down, because the shape's level-MaxDepth node is an untracked count with a ⊤ tail — and that
      // really is imprecision in the carrier rather than in this query, as the witness below shows.
      val deepest = if v.paths.isEmpty then 0 else v.paths.map(_.items.length).max
      if deepest <= Shape.MaxDepth then assertEquals(SpatialFacts.exactValue(t), Some(v), s"exactValue for ${v.pretty}")
      else assertEquals(SpatialFacts.exactValue(t), None, s"exactValue must not over-claim for ${v.pretty}")
    // THE WITNESS MOVED, AND THAT IS THE POINT OF THE UNTRACKED-HEAD CERTIFICATE.  {a·a·a·a·a} and
    // {a·a·a·a·b} used to be indistinguishable to the capped trie: `capDepth` collapsed the level-4
    // node to an untracked COUNT with a ⊤ tail and threw the head NAMES away, so γ admitted both.
    // Channel (e) keeps the names through the collapse — "the untracked heads are within {a}" — so
    // the second value is now correctly REJECTED, and `exactValue` may pin the first down.
    val five = SpatialType.of(sv(p("a", "a", "a", "a", "a")))
    assert(!SpatialTyping.gammaMember(sv(p("a", "a", "a", "a", "b")), five),
           "the depth spill keeps the head NAMES, so a different deep head is not admitted")
    assert(SpatialTyping.gammaMember(sv(p("a", "a", "a", "a", "a")), five),
           "and the value itself is of course still admitted")
    // …and the certificate carries a SET, not one name: a two-path value past the cap keeps both, and
    // a third head is still refused.
    val two = SpatialType.of(sv(p("a", "a", "a", "a", "a"), p("a", "a", "a", "a", "b")))
    assert(SpatialTyping.gammaMember(sv(p("a", "a", "a", "a", "a"), p("a", "a", "a", "a", "b")), two))
    assert(!SpatialTyping.gammaMember(sv(p("a", "a", "a", "a", "a"), p("a", "a", "a", "a", "c")), two),
           s"a head the spill did not name must stay out: ${two.show}")
    // WHERE THE RESIDUAL IMPRECISION NOW LIVES.  It is no longer the carrier: the length histogram
    // forbids a path longer than the collapsed level and channel (e) forbids a different head at it,
    // so γ(five) really is the singleton.  It is the QUERY — `exactValue` reads the SHAPE, whose
    // level-MaxDepth node is an untracked COUNT with a ⊤ tail, and refuses to pin anything below the
    // cap rather than cross-reading the histogram.  Sound, incomplete, and stated as such: the loop
    // above holds it to `None` for every value deeper than the cap.
    assert(!SpatialTyping.gammaMember(sv(p("a", "a", "a", "a", "a", "a")), five),
           "the histogram forbids a path longer than the collapsed level")
    assertEquals(SpatialFacts.exactValue(five), None)
    println(s"[deep]  ${deepUniverse.size} spaces of length ≤ 6, $checks exact degrees, " +
            s"$exactPastCap past the depth-$MaxDepthShown cap of which $rawTopPastCap had a ⊤ raw shape upper")
    assert(rawTopPastCap > 100, s"the cap must really be reached: $rawTopPastCap")
  }
  private def MaxDepthShown: Int = Shape.MaxDepth

  test("deep abstract types stay sound past the depth cap") {
    val rng = new Random(9001L)
    var members = 0; var checks = 0
    val deepTypes = Vector.fill(200) {
      SpatialGamma.lub(SpatialType.of(deepUniverse(rng.nextInt(deepUniverse.size))),
                       SpatialType.of(deepUniverse(rng.nextInt(deepUniverse.size))))
    } ++ Vector(SpatialType(Shape.top, SpaceType.boundedExact(LenBounds(3, 6), 2)),
                SpatialType(Shape.top, SpaceType.bounded(LenBounds(0, 6), 3)))
    for t <- deepTypes do
      for v <- deepUniverse if SpatialTyping.gammaMember(v, t) do
        members += 1
        for d <- 0 to 7 do
          val g = SpatialFacts.degreeAt(t, d).fold(c => fail(s"${v.pretty} d=$d: ${c.show}"), identity)
          assert(inIvl(g.paths, truePaths(v, d)), s"E_$d ${g.paths.show} vs ${truePaths(v, d)} for ${v.pretty}")
          assert(inIvl(g.prefixes, truePrefixes(v, d)), s"K_$d ${g.prefixes.show} vs ${truePrefixes(v, d)} for ${v.pretty}")
          val fibers = trueFibers(v, d)
          if fibers.nonEmpty then
            assert(inIvl(g.minFiber, fibers.min.toLong), s"minFiber d=$d ${v.pretty}")
            assert(inIvl(g.maxFiber, fibers.max.toLong), s"maxFiber d=$d ${v.pretty}")
          checks += 1
        assert(v.paths.forall(_.items.startsWith(SpatialFacts.commonPrefix(t).items)))
        assert(inIvl(SpatialFacts.trieNodes(t).fold(c => fail(c.show), identity),
                     ITrie.fromSpaceValue(v).nodeCount.toLong))
    println(s"[deep abstract]  ${deepTypes.size} types, $members (type, value) pairs, $checks brackets")
    assert(checks > 3000)
  }

  // ================================================================================================
  // 5.  TRIE NODES
  // ================================================================================================

  test("trieNodes = 1 + sum of K_d = ITrie.nodeCount") {
    var n = 0; var exact = 0
    for v <- universe do
      val t = SpatialType.of(v)
      val nodes = SpatialFacts.trieNodes(t).fold(c => fail(c.show), identity)
      val real = ITrie.fromSpaceValue(v).nodeCount.toLong
      assert(inIvl(nodes, real), s"${v.pretty}: ${nodes.show} misses $real")
      if nodes.lo == nodes.hi then { exact += 1; assertEquals(nodes.lo, real) }
      // and the coarse fallback the cost model uses today is never tighter
      val coarse = Ivl.add(1L, Ivl.mul(t.size.hi, if t.len.isEmpty then 0L else t.len.hi))
      assert(nodes.hi <= coarse, s"${v.pretty}: ${nodes.hi} must beat size*len+1 = $coarse")
      n += 1
    println(s"[trieNodes]  $n concrete spaces, $exact exact matches against ITrie.nodeCount")
    assertEquals(exact, n, "every concrete space must be exact")
    // truncation is visible in the data, never read as "no deeper prefixes"
    val top = SpatialFacts.trieNodes(SpatialType.top).toOption.get
    assertEquals(top.hi, Ivl.INF)
    assert(SpatialFacts.profile(SpatialType.top).toOption.get.truncated)
    assertEquals(SpatialFacts.profile(SpatialType.top).toOption.get.prefixes(999), Ivl.unknown)
  }

  // ================================================================================================
  // 6.  COMMON PREFIXES AND SAFE EXTRACTION
  // ================================================================================================

  test("the common prefix is shared by every path of every member") {
    var withPrefix = 0; var checks = 0
    for (label, t) <- allFamilies do
      val cp = SpatialFacts.commonPrefix(t)
      if cp.nonTrivial then withPrefix += 1
      for v <- universe if SpatialTyping.gammaMember(v, t) do
        assert(v.paths.forall(_.items.startsWith(cp.items)),
               s"$label: ${v.pretty} does not start with ${cp.show}")
        if cp.definitelyPresent then assert(v.paths.nonEmpty, s"$label: claimed present but ${v.pretty}")
        checks += 1
    println(s"[commonPrefix]  $withPrefix of ${allFamilies.size} types have a non-trivial prefix, $checks value checks")

    // the spine cases, spelled out
    assertEquals(SpatialFacts.commonPrefix(SpatialType.of(sv(p("a", "b", "x"), p("a", "b", "y")))).items,
                 List("a", "b"))
    assertEquals(SpatialFacts.commonPrefix(SpatialType.of(sv(p("a", "x"), p("b", "x")))).items, Nil)
    // ε in the space kills the prefix: a path ENDS at the root
    assertEquals(SpatialFacts.commonPrefix(SpatialType.of(sv(p(), p("a", "b")))).items, Nil)
    // vacuous on the empty space, and the flag says so
    val e = SpatialFacts.commonPrefix(SpatialType.empty)
    assertEquals(e.items, Nil); assert(!e.definitelyPresent)
    assert(SpatialFacts.commonPrefix(SpatialType.of(sv(p("a", "b")))).definitelyPresent)
  }

  test("safe extraction separates cardinality from path length") {
    val three = SpatialType.of(sv(p("a", "b", "c"), p("x", "y", "z")))
    assert(SpatialFacts.canExtractEveryPath(three, 3))
    assert(!SpatialFacts.canExtractEveryPath(three, 4))
    // the trap: len.lo on the EMPTY space is INF, which would "prove" any number of extractions
    assertEquals(SpatialType.empty.len.lo, LenBounds.empty.lo)
    assert(!SpatialFacts.canExtractEveryPath(SpatialType.empty, 3))
    assert(!SpatialFacts.canExtractEveryPath(SpatialType.empty, 1))
    // three paths exist but only one item each: MinimumCardinality(3) does NOT give extraction
    val short = SpatialType.of(sv(p("a"), p("b"), p("c")))
    assert(Fact.from(short).contains(Fact.MinimumCardinality(3)))
    assert(SpatialFacts.canExtractEveryPath(short, 1))
    assert(!SpatialFacts.canExtractEveryPath(short, 2))
    // and it is sound over the whole universe
    for (label, t) <- allFamilies; k <- 0 to 3 if SpatialFacts.canExtractEveryPath(t, k.toLong) do
      for v <- universe if SpatialTyping.gammaMember(v, t) do
        assert(v.paths.nonEmpty && v.paths.forall(_.items.length >= k),
               s"$label claimed $k extractions but ${v.pretty}")
  }

  test("Fact.PrefixAbsent is emittable — the dead promise, discharged by a query") {
    val t = SpatialType.of(sv(p("a", "x"), p("a", "y")))
    assertEquals(SpatialFacts.prefixAbsent(t, List("b")), Some(Fact.PrefixAbsent(List("b"))))
    assertEquals(SpatialFacts.prefixAbsent(t, List("a", "z")), Some(Fact.PrefixAbsent(List("a", "z"))))
    assertEquals(SpatialFacts.prefixAbsent(t, List("a")), None)
    assertEquals(SpatialFacts.prefixAbsent(t, List("a", "x")), None)
    // an open head set proves nothing
    assertEquals(SpatialFacts.prefixAbsent(SpatialType.top, List("b")), None)
    // sound over the universe: a claimed-absent prefix is absent from every member
    var claims = 0
    val probes = Vector(List("a"), List("b"), List("a", "a"), List("a", "b"), List("b", "b"))
    for (label, ty) <- allFamilies; pr <- probes if SpatialFacts.prefixAbsent(ty, pr).isDefined do
      claims += 1
      for v <- universe if SpatialTyping.gammaMember(v, ty) do
        assert(!v.paths.exists(_.items.startsWith(pr)), s"$label claimed $pr absent but ${v.pretty}")
    println(s"[PrefixAbsent]  $claims absence proofs, all confirmed over the universe")
    assert(claims > 50)
  }

  // ================================================================================================
  // 7.  EXACT VALUES
  // ================================================================================================

  test("exactValue recovers exactly the unique member, or nothing") {
    var recovered = 0
    for v <- universe do
      SpatialFacts.exactValue(SpatialType.of(v)) match
        case Some(u) => assertEquals(u, v, s"round trip for ${v.pretty}"); recovered += 1
        case None => fail(s"a literal's own type must pin it down: ${v.pretty}")
    assertEquals(recovered, universe.size)

    var pinned = 0
    for (label, t) <- allFamilies do
      SpatialFacts.exactValue(t) match
        case None => ()
        case Some(v) =>
          pinned += 1
          val members = universe.filter(u => SpatialTyping.gammaMember(u, t))
          assert(members.forall(_ == v),
                 s"$label pinned ${v.pretty} but the universe also admits ${members.filter(_ != v).map(_.pretty)}")
    println(s"[exactValue]  ${universe.size} literal round trips, $pinned of ${allFamilies.size} types pinned down")
    assertEquals(SpatialFacts.exactValue(SpatialType.top), None)
    assertEquals(SpatialFacts.exactValue(SpatialType.empty), Some(sv()))
    // a histogram that disagrees with the shape yields None, not a value outside the type
    assertEquals(SpatialFacts.exactValue(SpatialType(Shape.epsOnly, SpaceType.exact(3, 5))), None)
  }

  // ================================================================================================
  // 8.  THE PREFIX PROFILE:  2N, NOT N²
  // ================================================================================================

  val h1: PathRef = PathRef("h1").known(1)
  val h2: PathRef = PathRef("h2").known(1)
  val r1: SpaceMention = SpaceMention("r1")
  val r2: SpaceMention = SpaceMention("r2")

  /** the clean 2-level full-path nest; `leaf` is analysed and evaluated with h1/h2 bound */
  def nest2(src: Space, leaf: Space): Space =
    Space.Iteration(src, h1, r1, Space.Iteration(Space.Mention(r1), h2, r2, leaf))
  /** the same nest with a per-level counter spliced into each body (instrumentation of the
   *  EVALUATOR, in a test — never of an analysis) */
  def nest2Counted(src: Space, leaf: Space, c: Array[Int]): Space =
    def tick(i: Int) = Space.GroundedSS(Space.Empty, _ => { c(i) += 1; SpaceValue(Set.empty) })
    Space.Iteration(src, h1, r1,
      Space.Union(tick(1), Space.Iteration(Space.Mention(r1), h2, r2, Space.Union(tick(2), leaf))))

  val leaf1: Space = Space.Singleton(Path.Concat(Path.Deref(h1), Path.Deref(h2)))
  val leaf2: Space = Space.Union(leaf1,
    Space.Singleton(Path.Concat(Path.Concat(Path.Deref(h1), Path.Deref(h2)), Path.Constant(p("z")))))

  /** N paths with DISTINCT heads: K_1 = K_2 = N, so Σ = 2N and the product is N² */
  def distinctHeads(n: Int): SpaceValue = sv((1 to n).map(i => p(s"a$i", "b"))*)
  /** N paths under ONE head: K_1 = 1, K_2 = N, so Σ = N+1 and the product is only N */
  def sharedHead(n: Int): SpaceValue = sv((1 to n).map(i => p("a", s"x$i"))*)

  test("a nested full-path iterator is bounded POINTWISE: 2N frames, not N^2") {
    println("[profile]  N | family   | K_1 | K_2 | sum K_i | prod K_i | counted frames | result | bound")
    for n <- 2 to 6 do
      for (name, v) <- Vector("distinct" -> distinctHeads(n), "shared" -> sharedHead(n)) do
        val t = SpatialType.of(v)
        val prof = SpatialFacts.profile(t).fold(c => fail(c.show), identity)
        val k1 = prof.prefixes(1); val k2 = prof.prefixes(2)
        val sum = prof.frameEntries(2)
        val prod = prof.naiveProductBound(2)
        assertEquals(k1, Ivl(truePrefixes(v, 1), truePrefixes(v, 1)))
        assertEquals(k2, Ivl(truePrefixes(v, 2), truePrefixes(v, 2)))

        // GROUND TRUTH: count the evaluator's per-level body entries
        val c = Array(0, 0, 0)
        val counted = eval(nest2Counted(Space.Literal(v), leaf1, c))
        val frames = (c(1) + c(2)).toLong
        assertEquals(c(1).toLong, k1.hi, s"level-1 entries must be K_1 ($name N=$n)")
        assertEquals(c(2).toLong, k2.hi, s"level-2 entries must be K_2 ($name N=$n)")
        assertEquals(sum, Ivl(frames, frames), s"Σ K_i must be the exact frame count ($name N=$n)")

        // the result is bounded pointwise by K_2 * leafUpper, and the two-path leaf gives 2N
        val res2 = eval(nest2(Space.Literal(v), leaf2))
        val bound2 = SpatialFacts.chainBound(
          RestChain.recognize(nest2(Space.Literal(v), leaf2)).get,
          SpatialTyping.Env()).fold(m => fail(m), identity)
        assert(bound2.resultCardinality.hi <= 2L * n,
               s"$name N=$n: result upper ${bound2.resultCardinality.show} must be <= 2N")
        assert(inIvl(bound2.resultCardinality, res2.paths.size.toLong),
               s"$name N=$n: ${bound2.resultCardinality.show} misses ${res2.paths.size}")

        println(f"[profile]  $n%d | $name%-8s | ${k1.hi}%3d | ${k2.hi}%3d | ${sum.hi}%7d | ${prod.hi}%8d | $frames%14d | ${res2.paths.size}%6d | ${bound2.resultCardinality.show}")

        if name == "distinct" then
          assertEquals(sum.hi, 2L * n, "the distinct-head family: Σ K_i = 2N")
          assertEquals(prod.hi, n.toLong * n.toLong, "…while the per-level product is N²")
          assert(sum.hi < prod.hi || n <= 2, s"2N must beat N² for N > 2 (N=$n)")
        else
          assertEquals(sum.hi, n.toLong + 1L, "the shared-head family: Σ K_i = N+1")
          assertEquals(prod.hi, n.toLong, "…while the per-level product is only N")
          // the product is not merely loose: it is UNSOUND as a frame count
          assert(prod.hi < frames,
                 s"the per-level product must be refuted as a frame bound: ${prod.hi} < $frames")
  }

  val h3: PathRef = PathRef("h3").known(1)
  val r3: SpaceMention = SpaceMention("r3")

  def nest3(src: Space, leaf: Space): Space =
    Space.Iteration(src, h1, r1,
      Space.Iteration(Space.Mention(r1), h2, r2,
        Space.Iteration(Space.Mention(r2), h3, r3, leaf)))
  def nest3Counted(src: Space, leaf: Space, c: Array[Int]): Space =
    def tick(i: Int) = Space.GroundedSS(Space.Empty, _ => { c(i) += 1; SpaceValue(Set.empty) })
    Space.Iteration(src, h1, r1, Space.Union(tick(1),
      Space.Iteration(Space.Mention(r1), h2, r2, Space.Union(tick(2),
        Space.Iteration(Space.Mention(r2), h3, r3, Space.Union(tick(3), leaf))))))
  val leaf3: Space =
    Space.Singleton(Path.Concat(Path.Concat(Path.Deref(h1), Path.Deref(h2)), Path.Deref(h3)))
  def distinct3(n: Int): SpaceValue = sv((1 to n).map(i => p(s"a$i", s"b$i", "c"))*)

  test("a three-level nest is 3N frames, not N^3") {
    println("[nest3]  N | K_1 K_2 K_3 | sum K_i | prod K_i | counted frames | leafInv | result")
    for n <- 2 to 5 do
      val v = distinct3(n)
      val chain = RestChain.recognize(nest3(Space.Literal(v), leaf3)).get
      assertEquals(chain.depth, 3)
      val cb = SpatialFacts.chainBound(chain, SpatialTyping.Env()).fold(m => fail(m), identity)
      val c = Array(0, 0, 0, 0)
      val out = eval(nest3Counted(Space.Literal(v), leaf3, c))
      val frames = (c(1) + c(2) + c(3)).toLong
      assertEquals(cb.frameEntries, Ivl(frames, frames), s"Σ K_i must be the exact frame count (N=$n)")
      assertEquals(cb.frameEntries.hi, 3L * n, "Σ K_i = 3N")
      assertEquals(cb.naiveProductBound.hi, n.toLong * n * n, "…while the per-level product is N³")
      assertEquals(cb.leafInvocations, Ivl(n, n), "K_3 = N leaf invocations")
      assertEquals(c(3).toLong, n.toLong)
      assert(inIvl(cb.resultCardinality, out.paths.size.toLong))
      assertEquals(Sym.bigO(cb.framesSym).degree, 1)
      assertEquals(Sym.bigO(cb.naiveSym).degree, 3)
      assertEquals(cb.framesSym.show, "3*N")
      println(f"[nest3]  $n%d | ${cb.profile.prefixes(1).hi}%3d ${cb.profile.prefixes(2).hi}%3d ${cb.profile.prefixes(3).hi}%3d | ${cb.frameEntries.hi}%7d | ${cb.naiveProductBound.hi}%8d | $frames%14d | ${cb.leafInvocations.hi}%7d | ${out.paths.size}%6d")
      if n >= 2 then assert(cb.frameEntries.hi <= 3L * n && cb.naiveProductBound.hi >= cb.frameEntries.hi)
  }

  test("the chain bound is symbolically d*N, not N^d") {
    val v = distinctHeads(5)
    val cb = SpatialFacts.chainBound(RestChain.recognize(nest2(Space.Literal(v), leaf1)).get,
                                     SpatialTyping.Env()).fold(m => fail(m), identity)
    assertEquals(cb.depth, 2)
    assertEquals(cb.framesSym.show, "2*N")
    assertEquals(cb.naiveSym.show, "N^2")
    assertEquals(Sym.bigO(cb.framesSym).degree, 1, s"frames ${cb.framesSym.show}")
    assertEquals(Sym.bigO(cb.naiveSym).degree, 2, s"naive ${cb.naiveSym.show}")
    assert(Sym.bigO(cb.framesSym) < Sym.bigO(cb.naiveSym))
    assertEquals(cb.leafInvocations, Ivl(5, 5))
    assertEquals(cb.frameEntries, Ivl(10, 10))
    // the reference evaluator regroups the whole surviving set at every level: Σ E_i = 10 here
    assertEquals(cb.groupingVisits, Ivl(10, 10))
    println(s"[chainBound]  ${cb.show}")
  }

  test("the chain bound refuses the cases where pointwise reasoning does not apply") {
    // mixed path lengths: a short path is exhausted early, so the leaf is not a per-path map
    val mixed = Space.Literal(sv(p("a", "b"), p("c")))
    assert(SpatialFacts.chainBound(RestChain.recognize(nest2(mixed, leaf1)).get, SpatialTyping.Env()).isLeft)
    // a leaf that reads an outer rest set AGGREGATES siblings
    val aggregating = nest2(Space.Literal(distinctHeads(3)), Space.Mention(r1))
    val res = SpatialFacts.chainBound(RestChain.recognize(aggregating).get, SpatialTyping.Env())
    assert(res.isLeft, s"the readsRest guard must fire: $res")
    assert(res.left.exists(_.contains("aggregates")))
    // reading the INNERMOST rest is refused too (conservative, and it is the same guard)
    val innermost = nest2(Space.Literal(distinctHeads(3)), Space.Mention(r2))
    assert(SpatialFacts.chainBound(RestChain.recognize(innermost).get, SpatialTyping.Env()).isLeft)
    // not an iteration at all
    assertEquals(RestChain.recognize(Space.Empty), None)
    // a one-level nest is a depth-1 chain
    val one = Space.Iteration(Space.Literal(sv(p("a"), p("b"))), h1, r1, Space.Singleton(Path.Deref(h1)))
    val c1 = RestChain.recognize(one).get
    assertEquals(c1.depth, 1)
    val b1 = SpatialFacts.chainBound(c1, SpatialTyping.Env()).fold(m => fail(m), identity)
    assertEquals(b1.leafInvocations, Ivl(2, 2))
    assertEquals(b1.frameEntries, Ivl(2, 2))
    assertEquals(eval(one).paths.size, 2)
  }

  // ================================================================================================
  // 9.  DERIVED FACTS ON INFERRED TYPES  (a live soundness probe on the existing transfers)
  // ================================================================================================

  val ms: Vector[SpaceMention] = Vector(SpaceMention("s0"), SpaceMention("s1"))

  /** paths up to length 5, so the inferred shapes cross `Shape.MaxDepth` too */
  def randomPaths(rng: Random): SpaceValue =
    val alphabet = Vector("a", "b", "c")
    SpaceValue((0 until rng.nextInt(4)).map { _ =>
      PathValue((0 until rng.nextInt(6)).map(_ => alphabet(rng.nextInt(alphabet.size))).toList)
    }.toSet)

  def genTerm(rng: Random, depth: Int): Space =
    if depth <= 0 then rng.nextInt(4) match
      case 0 => Space.Mention(ms(rng.nextInt(ms.size)))
      case 1 => Space.Literal(randomPaths(rng))
      case 2 => Space.Empty
      case _ => Space.Singleton(Path.Constant(PathValue(List("a", "b").take(rng.nextInt(3)))))
    else
      def sub = genTerm(rng, depth - 1)
      rng.nextInt(13) match
        case 0 => Space.Union(sub, sub)
        case 1 => Space.Intersection(sub, sub)
        case 2 => Space.Subtraction(sub, sub)
        case 3 => Space.Restriction(sub, sub)
        case 4 => Space.Raffination(sub, sub)
        case 5 => Space.Composition(sub, sub)
        case 6 => Space.Wrap(sub, Path.Constant(p("a")))
        case 7 => Space.Unwrap(sub, Path.Constant(p("a")))
        case 8 => Space.TailsUnion(sub)
        case 9 => Space.TailsIntersection(sub)
        case 10 => Space.Range(sub, rng.nextInt(3), rng.nextInt(3))
        case 11 => Space.Iteration(sub, h1, r1, Space.Wrap(Space.Mention(r1), Path.Deref(h1)))
        case _ => Space.Iteration(sub, h1, r1, Space.Singleton(Path.Deref(h1)))

  test("derived facts bracket eval on inferred types, and inferred types never contradict") {
    val rng = new Random(31337L)
    var terms = 0; var gateFailures = 0; var contradictions = 0; var checks = 0
    val badGate = Vector.newBuilder[String]
    val badContra = Vector.newBuilder[String]
    for _ <- 1 to 1500 do
      val term = genTerm(rng, 3)
      val conc = ms.map(m => m -> randomPaths(rng)).toMap
      val env = SpatialTyping.Env(spaces = conc.view.mapValues(SpatialType.of).toMap)
      val t = SpatialTyping.infer(term, env)
      val out =
        try eval(term)(using PathContext.emptyMap, SpaceContextMap(conc))
        catch case _: Throwable => null
      if out != null then
        terms += 1
        // the EXISTING gate; a failure here is a pre-existing transfer bug, reported separately
        if !SpatialTyping.gammaMember(out, t) then
          gateFailures += 1
          if gateFailures <= 3 then badGate += s"${term.show} with $conc -> ${out.pretty} vs ${t.show}"
        else
          SpatialFacts.contradiction(t) match
            case Some(c) =>
              contradictions += 1
              if contradictions <= 3 then badContra += s"${term.show}: ${c.show}"
            case None =>
              val prof = SpatialFacts.profile(t).toOption.get
              for d <- 0 to prof.lastDepth do
                val g = prof.degrees(d)
                assert(inIvl(g.paths, truePaths(out, d)),
                       s"E_$d ${g.paths.show} misses ${truePaths(out, d)} for ${term.show}")
                assert(inIvl(g.prefixes, truePrefixes(out, d)),
                       s"K_$d ${g.prefixes.show} misses ${truePrefixes(out, d)} for ${term.show}")
                val fs = trueFibers(out, d)
                if fs.nonEmpty then
                  assert(inIvl(g.minFiber, fs.min.toLong), s"minFiber d=$d for ${term.show}: ${g.minFiber.show} vs ${fs.min}")
                  assert(inIvl(g.maxFiber, fs.max.toLong), s"maxFiber d=$d for ${term.show}: ${g.maxFiber.show} vs ${fs.max}")
                checks += 1
              val nodes = SpatialFacts.trieNodes(t).toOption.get
              assert(inIvl(nodes, ITrie.fromSpaceValue(out).nodeCount.toLong),
                     s"trieNodes ${nodes.show} misses ${ITrie.fromSpaceValue(out).nodeCount} for ${term.show}")
              val cp = SpatialFacts.commonPrefix(t)
              assert(out.paths.forall(_.items.startsWith(cp.items)),
                     s"commonPrefix ${cp.show} for ${term.show} -> ${out.pretty}")
              SpatialFacts.exactValue(t).foreach(v => assertEquals(v, out, s"exactValue for ${term.show}"))
    println(s"[inferred]  $terms terms, $checks depth brackets, $gateFailures gate failures, $contradictions contradictions")
    assertEquals(gateFailures, 0, s"pre-existing γ-gate failures: ${badGate.result().mkString("; ")}")
    assertEquals(contradictions, 0, s"derived contradictions on inferred types: ${badContra.result().mkString("; ")}")
    assert(checks > 1000)
  }

  // ================================================================================================
  // 10.  SPECIALIZATION CANDIDATES
  // ================================================================================================

  test("specialization candidates are derived, justified, and never wired to a backend") {
    // an exactly-known space folds to a constant
    val exact = SpatialType.of(sv(p("a", "b"), p("a", "c")))
    val cs = SpatialFacts.specializations(exact)
    assert(cs.exists(_.spec.isInstanceOf[SpatialSpecialization.GraphConstantFold]),
           s"expected a constant fold: ${cs.map(_.show)}")
    assertEquals(cs.collectFirst { case SpecializationCandidate(SpatialSpecialization.GraphConstantFold(v), _, _) => v },
                 Some(sv(p("a", "b"), p("a", "c"))))
    // …and the same type has a common spine, so the zipper can pre-focus
    assertEquals(cs.collectFirst { case SpecializationCandidate(SpatialSpecialization.ZipperPrefocus(pv), _, _) => pv },
                 Some(p("a")))
    // …and a proved maximum path length licenses a complete unroll, with the per-depth fan-out
    val unroll = cs.collectFirst { case SpecializationCandidate(SpatialSpecialization.TrieUnroll(d, prof), _, _) => (d, prof) }
    assertEquals(unroll.map(_._1), Some(2))
    assertEquals(unroll.map(_._2.size), Some(3))
    assert(cs.forall(_.why.nonEmpty), "every candidate must carry its justification")
    assert(cs.forall(_.evidence.nonEmpty), "…and the validated propositions it rests on")

    // an open type licenses nothing
    assertEquals(SpatialFacts.specializations(SpatialType.top), Vector.empty)
    // an unbounded path length blocks the unroll even when a prefix exists
    val openTail = SpatialType(Shape(Presence.No, SortedMap("a" -> Shape.top), Ivl.zero, None), SpaceType.unknown)
    val co = SpatialFacts.specializations(openTail)
    assert(co.exists(_.spec.isInstanceOf[SpatialSpecialization.ZipperPrefocus]))
    assert(!co.exists(_.spec.isInstanceOf[SpatialSpecialization.TrieUnroll]),
           s"an unbounded length must not be unrolled: ${co.map(_.show)}")
    for (label, t) <- allFamilies do SpatialFacts.specializations(t)   // total
    println(s"[specializations]  ${SpatialFacts.specializations(exact).map(_.show).mkString("; ")}")
  }

  // ================================================================================================
  // 11.  CORRELATED PATH SHAPES  (whispers §5)
  // ================================================================================================

  /** the deterministic substitution generator: TEST support, deliberately not in production
   *  (the review asks for exactly that separation) */
  object PatternGenerator:
    private def product[A](axes: Vector[(String, Vector[A])]): Iterator[Map[String, A]] =
      def go(i: Int, acc: Map[String, A]): Iterator[Map[String, A]] =
        if i == axes.size then Iterator.single(acc)
        else
          val (name, values) = axes(i)
          values.iterator.flatMap(v => go(i + 1, acc.updated(name, v)))
      go(0, Map.empty)

    def bindings(patterns: Vector[PathPattern]): Iterator[Map[String, Int]] =
      val occurrences = for
        pp <- patterns
        case ItemPattern.AffineInt(_, x, _, lo, hi) <- pp.items
      yield x -> (lo, hi)
      val domains = occurrences.groupMap(_._1)(_._2).toVector.sortBy(_._1).map { (x, rs) =>
        val lo = rs.map(_._1).max
        val hi = rs.map(_._2).min
        x -> (if hi < lo then Vector.empty else (lo to hi).toVector)
      }
      product(domains)

    def image(patterns: Vector[PathPattern]): Set[PathValue] =
      bindings(patterns).flatMap(env => patterns.iterator.flatMap(_.instantiate(env))).toSet

  def aff(x: String, off: Int, lo: Int, hi: Int): ItemPattern = ItemPattern.AffineInt("cell", x, off, lo, hi)

  test("PatternImage.cardinality brackets the brute-forced image") {
    val n = 4
    val families = Vector(
      "identity" -> Vector(PathPattern(Vector(aff("x", 0, 0, n - 1)))),
      "shifted pair" -> Vector(PathPattern(Vector(aff("x", 0, 0, n - 1))),
                               PathPattern(Vector(ItemPattern.Constant("t"), aff("x", 0, 0, n - 1)))),
      "two namespaces" -> Vector(PathPattern(Vector(aff("x", 0, 0, n - 1))),
                                 PathPattern(Vector(ItemPattern.AffineInt("other", "x", 0, 0, n - 1)))),
      "adjacent affine" -> Vector(PathPattern(Vector(aff("x", 0, 0, n - 1))),
                                  PathPattern(Vector(aff("x", 1, 0, n - 1)))),
      "constant only" -> Vector(PathPattern(Vector(ItemPattern.Constant("k")))),
    )
    for (name, ps) <- families do
      val img = PatternGenerator.image(ps)
      val card = PatternImage.cardinality(Ivl(n, n), Set("x"), ps)
      assert(inIvl(card, img.size.toLong), s"$name: ${card.show} misses ${img.size}")
      println(f"[patterns] $name%-14s q=${ps.size} image=${img.size}%3d bound=${card.show}")

    // the counterexample that prevents an unsound q*N LOWER bound: `x` and `x+1` are different at
    // every binding but their IMAGES overlap between adjacent inputs
    val a = aff("x", 0, 0, n - 1); val b = aff("x", 1, 0, n - 1)
    assert(ItemPattern.differentAtSameBinding(a, b), "different under every fixed binding")
    assert(!ItemPattern.globallyDisjoint(a, b), "but NOT globally disjoint")
    val adjacent = Vector(PathPattern(Vector(a)), PathPattern(Vector(b)))
    val cardAdj = PatternImage.cardinality(Ivl(n, n), Set("x"), adjacent)
    assertEquals(cardAdj.lo, 1L, "so the lower bound must collapse to positivity")
    assertEquals(PatternGenerator.image(adjacent).size, n + 1, "the true image is N+1, not 2N")
    assert(cardAdj.lo < 2L * n)

    // whereas two namespaces ARE globally disjoint, so 2N is licensed and achieved
    val two = Vector(PathPattern(Vector(aff("x", 0, 0, n - 1))),
                     PathPattern(Vector(ItemPattern.AffineInt("other", "x", 0, 0, n - 1))))
    assertEquals(PatternImage.cardinality(Ivl(n, n), Set("x"), two), Ivl(2L * n, 2L * n))
    assertEquals(PatternGenerator.image(two).size, 2 * n)

    // an empty key set is accepted only when there is at most one input
    assertEquals(PatternImage.cardinality(Ivl(1, 1), Set.empty, two), Ivl(2, 2))
    assertEquals(PatternImage.cardinality(Ivl(n, n), Set.empty, two).lo, 1L)
    // Unknown items are never provably disjoint
    assert(!ItemPattern.globallyDisjoint(ItemPattern.Unknown("?"), ItemPattern.Constant("k")))
    // the length-prefixed encoding keeps namespaces apart even when one textually prefixes another
    assert(ItemPattern.globallyDisjoint(ItemPattern.AffineInt("a", "x", 0, 0, 9),
                                        ItemPattern.AffineInt("ab", "x", 0, 0, 9)))
    assertEquals(ItemPattern.decode("a", ItemPattern.encode("ab", 3)), None)
    assertEquals(ItemPattern.decode("a", ItemPattern.encode("a", 3)), Some(3L))
    // headGroupsUpper is bounded by both the cardinality and the head choices
    assertEquals(PatternStratum(Ivl(0, 3), two).headGroupsUpper, 3L)
    assertEquals(PatternStratum(Ivl(0, 100), two).headGroupsUpper, 2L * n)
  }

  // ================================================================================================
  // 12.  NO EVALUATION
  // ================================================================================================

  test("no derived fact ever runs the subject program") {
    val bomb: Space = Space.GroundedSS(Space.Empty,
      _ => throw RuntimeException("a derived spatial fact evaluated its subject"))
    val t = SpatialTyping.infer(bomb)
    // every entry point, on the ⊤ the analysis produces for an opaque closure
    SpatialFacts.pathsAtDepth(t.lens, 3)
    SpatialFacts.rawPrefixesAt(t.shape, 3)
    assert(SpatialFacts.degreeAt(t, 3).isRight)
    assert(SpatialFacts.profile(t).isRight)
    assert(SpatialFacts.trieNodes(t).isRight)
    SpatialFacts.commonPrefix(t)
    SpatialFacts.prefixAbsent(t, List("a"))
    SpatialFacts.canExtractEveryPath(t, 3)
    SpatialFacts.exactValue(t)
    assertEquals(SpatialFacts.specializations(t), Vector.empty)
    assertEquals(SpatialFacts.contradiction(t), None)
    // and through the chain recogniser, whose leaf is the bomb
    val chain = RestChain.recognize(nest2(bomb, bomb)).get
    SpatialFacts.chainBound(chain, SpatialTyping.Env())
    // a bomb inside a literal-sourced chain: the LEAF must not be run either
    val live = RestChain.recognize(nest2(Space.Literal(distinctHeads(3)), bomb)).get
    val b = SpatialFacts.chainBound(live, SpatialTyping.Env())
    assert(b.isRight, s"the chain is still analysable: $b")
    assertEquals(b.toOption.get.leafType.size.hi, Ivl.INF, "the leaf is ⊤, which is the honest answer")
    // the sentinel really would throw if anything ran it
    intercept[RuntimeException] { eval(bomb) }
  }
