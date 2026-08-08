package morkl

import munit.FunSuite
import scala.collection.immutable.IntMap

/** ================================================================================================
 *  THE OPTIMAL TRIE ALGEBRA: CASE SOUNDNESS, ITS EVENT ORACLE, AND ASYMPTOTIC GATES
 *  (review.md items 1 and 4)
 *
 *  `Backend.Trie` means `evalI` over `ITrie`.  That algebra is now the CASE-RETURNING one: its ring
 *  operations return `ITrie.AlgebraicResult` (`Empty | Identity(mask) | Bespoke`), decided at EVERY
 *  node, so containment, disjointness and prefix coverage let it accept or reject a whole subtrie BY
 *  POINTER.  This suite is the check that (a) those cases are sound and, where claimed, complete,
 *  (b) the event vocabulary really counts them, and (c) the operations whose asymptotics the cases
 *  exist to deliver actually deliver them.
 *
 *  ==WHY THE GATES ARE ON SLOPES, NOT CEILINGS==
 *
 *  A bound that is linear where the algorithm is O(1) or O(depth) is a FAILURE even if it "contains"
 *  the measurement.  So each gate runs a geometric ladder of operand sizes `n, 2n, 4n, ...` and
 *  asserts the measured slope
 *
 *      slope = log2((C(2n) + 1) / (C(n) + 1))
 *
 *  is flat (`<= 0.35`), where a count linear in `n` would show `slope ~ 1.0`.  The tolerance is set by
 *  the arithmetic, not by the measurement: over the ladder used here a DEPTH-linear count `c·d` shows
 *  slopes `log2(10/9) = 0.15` down to `log2(13/12) = 0.12`, so `0.35` admits O(1) and O(depth) and
 *  excludes anything linear.  A second assertion pins the end-to-end ratio at `<= 3x` over four
 *  doublings, where linear would be `16x`.
 *
 *  ==WHAT "BEFORE" MEANS IN THE BEFORE/AFTER TABLE==
 *
 *  The `legacy*` functions below are the algorithms this change replaced, re-implemented here and
 *  instrumented with the SAME events, run over the SAME operands.  They call the CURRENT `ITrie`
 *  primitives, so they already benefit from the new identity propagation inside `union`/
 *  `intersection`/`subtraction`.  The before/after gap is therefore an UNDER-estimate of the change:
 *  it isolates the control structure (full size walk vs order statistics, pairwise fold vs n-ary
 *  pass, two walks vs one, structural equality vs frontier equality) and nothing else.
 *
 *  ==NO EVALUATION INSIDE AN ANALYSIS==
 *
 *  Nothing here is an analysis.  This is measurement of RUNS plus a set-level reference built from
 *  `toSpaceValue` (not from an executor), which is what a test is allowed to do.
 *  ============================================================================================== */
class OptimalTrieCheck extends FunSuite:
  import ITrie.AlgebraicResult
  import AlgebraicResult.{LEFT, RIGHT}

  override val munitTimeout = scala.concurrent.duration.Duration(10, "min")

  // ==============================================================================================
  // GENERATORS
  // ==============================================================================================

  def ids(items: String*): List[Int] = Interner.internPath(items.toList)
  def sing(items: String*): ITrie = ITrie.singleton(ids(items*))
  def ps(t: ITrie): Set[PathValue] = t.toSpaceValue.paths

  /** A COMPLETE BINARY TRIE of depth `d`: `2^d` paths, `2^(d+1) - 1` nodes.  Keys depend only on the
   *  LEVEL, so two tries built with the same `tag` have identical content — and, because the two
   *  recursive calls are separate, they are DISTINCT OBJECTS at every node.  That matters: a
   *  generator that accidentally shared subtries would make every measurement below trivially
   *  constant through `eq` short circuits, which is exactly the mistake a sharing-aware gate must
   *  not make. */
  def binTrie(d: Int, tag: String): ITrie =
    if d == 0 then ITrie.epsilon
    else
      val ka = Interner.intern(s"$tag.L$d.a")
      val kb = Interner.intern(s"$tag.L$d.b")
      ITrie(false, IntMap(ka -> binTrie(d - 1, tag), kb -> binTrie(d - 1, tag)))

  /** the leftmost path of [[binTrie]]`(d, tag)` — one present prefix of length `d` */
  def leftSpine(d: Int, tag: String): ITrie =
    ITrie.singleton((d to 1 by -1).toList.map(i => Interner.intern(s"$tag.L$i.a")))

  /** a fresh single path of length `len`, sharing nothing with anything else */
  def deepPath(len: Int, tag: String): ITrie = ITrie.singleton((0 until len).toList.map(i => Interner.intern(s"$tag.d$i")))

  /** `k` distinct one-item paths */
  def fanout(k: Int, tag: String): Vector[ITrie] = (0 until k).toVector.map(i => sing(s"$tag.h$i"))

  val rnd = new scala.util.Random(20260808)
  val alphabet = Vector("a", "b", "c", "0", "1")
  def randPath(maxLen: Int = 3): PathValue = PathValue(List.fill(rnd.nextInt(maxLen + 1))(alphabet(rnd.nextInt(alphabet.size))))
  def randTrie(maxPaths: Int = 6): ITrie = ITrie.fromPaths((0 until rnd.nextInt(maxPaths + 1)).map(_ => randPath()))

  // ==============================================================================================
  // SET-LEVEL REFERENCE (no executor involved)
  // ==============================================================================================

  def refUnion(a: ITrie, b: ITrie): Set[PathValue] = ps(a) | ps(b)
  def refInter(a: ITrie, b: ITrie): Set[PathValue] = ps(a) & ps(b)
  def refDiff(a: ITrie, b: ITrie): Set[PathValue] = ps(a) -- ps(b)
  def extendsSome(x: PathValue, b: Set[PathValue]): Boolean = b.exists(p => x.items.startsWith(p.items))
  def refRestrict(a: ITrie, b: ITrie): Set[PathValue] = { val pb = ps(b); ps(a).filter(extendsSome(_, pb)) }
  def refRaff(a: ITrie, b: ITrie): Set[PathValue] = { val pb = ps(b); ps(a).filterNot(extendsSome(_, pb)) }
  def refComp(a: ITrie, b: ITrie): Set[PathValue] =
    for x <- ps(a); y <- ps(b) yield PathValue(x.items ++ y.items)

  // ==============================================================================================
  // 1. CASE SOUNDNESS AND LEFT-BIT COMPLETENESS
  // ==============================================================================================

  /** Check one algebraic decision: the materialised result is the reference set, `Empty` really means
   *  empty, and each SET identity bit really names an argument — as the OBJECT, not merely as an
   *  equal value, because reusing the object is the entire asymptotic point. */
  def checkCase(op: String, a: ITrie, b: ITrie, r: AlgebraicResult, ref: Set[PathValue]): Unit =
    val got = ITrie.pick(r, a, b)
    assertEquals(ps(got), ref, s"$op: materialised result differs from the set reference")
    r match
      case AlgebraicResult.Empty =>
        assert(ref.isEmpty, s"$op reported Empty but the reference is ${ref.size} paths")
      case AlgebraicResult.Identity(m) =>
        if (m & LEFT) != 0 then
          assertEquals(ref, ps(a), s"$op reported Identity(LEFT) but the result is not the left argument")
          assert(got eq a, s"$op reported Identity(LEFT) but did not hand back the left OBJECT")
        if (m & RIGHT) != 0 then
          assertEquals(ref, ps(b), s"$op reported Identity(RIGHT) but the result is not the right argument")
      case AlgebraicResult.Bespoke(_) => ()

  def allCases(a: ITrie, b: ITrie): Unit =
    checkCase("union", a, b, ITrie.unionR(a, b), refUnion(a, b))
    checkCase("intersection", a, b, ITrie.intersectionR(a, b), refInter(a, b))
    checkCase("subtraction", a, b, ITrie.subtractionR(a, b), refDiff(a, b))
    checkCase("restriction", a, b, ITrie.restrictionR(a, b), refRestrict(a, b))
    checkCase("raffination", a, b, ITrie.raffinationR(a, b), refRaff(a, b))
    checkCase("composition", a, b, ITrie.compositionR(a, b), refComp(a, b))

  test("the algebraic case is SOUND at every node on random operands") {
    for _ <- 0 until 400 do allCases(randTrie(), randTrie())
  }

  test("the algebraic case is SOUND on the correlated shapes a random corpus never generates") {
    // subsets, supersets, shared and unshared equal representation, prefix cylinders, epsilon/empty,
    // self — review.md item 2's generator list, which is where these backends actually win.
    val big = binTrie(4, "c")
    val bigTwin = binTrie(4, "c")                        // equal content, DISTINCT objects
    val sub = ITrie(false, IntMap.from(big.children.take(1)))   // a shared sub-branch of `big`
    val pre = ITrie.wrap(ids("c.L4.a"), ITrie.epsilon)          // a prefix cylinder of `big`
    val pool = Vector(ITrie.empty, ITrie.epsilon, big, bigTwin, sub, pre,
                      leftSpine(4, "c"), deepPath(5, "z"), sing("q"),
                      ITrie.union(big, sing("q")), ITrie.subtraction(big, sub))
    for a <- pool; b <- pool do allCases(a, b)
  }

  test("the LEFT identity bit is COMPLETE on its characterizing cases") {
    val a = binTrie(4, "l")
    val sub = ITrie(false, IntMap.from(a.children.take(1)))     // sub ⊆ a, shared representation
    val disjoint = sing("l.other")
    def isLeft(r: AlgebraicResult): Boolean = r match
      case AlgebraicResult.Identity(m) => (m & LEFT) != 0
      case _ => false
    assert(isLeft(ITrie.unionR(a, sub)), "b ⊆ a must give union Identity(LEFT)")
    assert(isLeft(ITrie.unionR(a, a)), "a ∪ a must give Identity(LEFT) (BOTH)")
    assert(isLeft(ITrie.intersectionR(sub, a)), "a ⊆ b must give intersection Identity(LEFT)")
    assert(isLeft(ITrie.subtractionR(a, disjoint)), "disjoint subtraction must give Identity(LEFT)")
    assert(isLeft(ITrie.restrictionR(a, ITrie.epsilon)), "restriction by {ε} must give Identity(LEFT)")
    assert(isLeft(ITrie.restrictionR(a, ITrie.head(a))), "restriction by a covering head set must give Identity(LEFT)")
    assert(isLeft(ITrie.raffinationR(a, disjoint)), "raffination by an unrelated prefix must give Identity(LEFT)")
    assert(isLeft(ITrie.compositionR(a, ITrie.epsilon)), "a·{ε} must give Identity(LEFT)")
    // and the RIGHT bit where it is claimed
    assertEquals(ITrie.compositionR(ITrie.epsilon, a), AlgebraicResult.Identity(RIGHT), "{ε}·b == b")
    assert(ITrie.intersectionR(a, sub) match { case AlgebraicResult.Identity(m) => (m & RIGHT) != 0; case _ => false },
           "b ⊆ a must give intersection Identity(RIGHT)")
    // THE ONE DOCUMENTED UNDER-REPORT: equal sets through distinct objects report LEFT, not BOTH.
    val twin = binTrie(4, "l")
    assertEquals(ps(twin), ps(a), "the twin must be content-equal")
    assertEquals(ITrie.unionR(a, twin), AlgebraicResult.Identity(LEFT),
                 "pinned under-report: unshared equal operands give LEFT, not BOTH (see ITrie.AlgebraicResult)")
  }

  // ==============================================================================================
  // 2. THE EVENT ORACLE — exact hand-computed counts for the whole-subtree cases
  // ==============================================================================================

  def ev(body: => Any): Events = EffortSink.count(body)._2

  test("the case oracle counts exactly one case per decision, and names the accepted subtries") {
    val big = binTrie(8, "o")                            // 256 paths, 511 nodes
    val sub = ITrie(false, IntMap.from(big.children.take(1)))

    // restriction by {ε}: ONE decision, Identity(LEFT), one subtrie accepted, nothing allocated
    val r1 = ev(ITrie.restriction(big, ITrie.epsilon))
    assertEquals(r1(EffortEvent.AlgebraIdentityLeft), 1L, r1.show)
    assertEquals(r1(EffortEvent.AlgebraBespoke), 0L, r1.show)
    assertEquals(r1(EffortEvent.SubtrieAcceptedByPointer), 1L, r1.show)
    assertEquals(r1.alloc, 0L, s"restriction by {ε} must allocate nothing: ${r1.show}")
    assertEquals(r1.touch, 1L, s"restriction by {ε} must be ONE node visit: ${r1.show}")

    // self-subtraction: one Empty decision, no allocation, and the pointer short circuit is counted
    val r2 = ev(ITrie.subtraction(big, big))
    assertEquals(r2(EffortEvent.AlgebraEmpty), 1L, r2.show)
    assertEquals(r2(EffortEvent.ReusedSubtrie), 1L, r2.show)
    assertEquals(r2.alloc, 0L, r2.show)

    // {ε}·B is CONSTANT TIME and returns B itself
    val r3 = EffortSink.count(ITrie.composition(ITrie.epsilon, big))
    assert(r3._1 eq big, "{ε}·B must return the B object")
    assertEquals(r3._2(EffortEvent.AlgebraIdentityRight), 1L, r3._2.show)
    assertEquals(r3._2.alloc, 0L, r3._2.show)
    assertEquals(r3._2.touch, 1L, r3._2.show)

    // a contained operand comes back by pointer, with work only down the shared frontier
    val r4 = EffortSink.count(ITrie.intersection(big, sub))
    assert(r4._1 eq sub, "A ∩ B with B ⊆ A (shared) must return the B object")
    assertEquals(r4._2.alloc, 0L, r4._2.show)
    assert(r4._2(EffortEvent.AlgebraIdentityRight) >= 1L, r4._2.show)

    // a FULL range is O(1) once the terminal count is cached, and allocates nothing
    big.count
    val r5 = EffortSink.count(ITrie.range(big, 0, 0))
    assert(r5._1 eq big, "a full-window Range must return its operand")
    assertEquals(r5._2.alloc, 0L, r5._2.show)
    assertEquals(r5._2.touch, 1L, s"a warm full Range must be ONE visit: ${r5._2.show}")
    assertEquals(r5._2(EffortEvent.SubtrieAcceptedByPointer), 1L, r5._2.show)

    // a union of two tries with disjoint heads attaches both branches unchanged: ONE fresh node.
    // The operands are built OUTSIDE the counted region — `wrap` allocates its own spine, and that
    // is operand construction, not the cost of the union.
    val ux = ITrie.wrap(ids("o.x"), big)
    val uy = ITrie.wrap(ids("o.y"), binTrie(8, "o2"))
    val u = ev(ITrie.union(ux, uy))
    assertEquals(u(EffortEvent.FreshTrieNode), 1L, s"disjoint union allocates ONE node: ${u.show}")
    assert(u(EffortEvent.SubtrieAcceptedByPointer) >= 2L, s"both branches accepted whole: ${u.show}")

    println(s"EVENTS: restriction-by-epsilon ${r1.show}")
    println(s"EVENTS: self-subtraction       ${r2.show}")
    println(s"EVENTS: epsilon-composition    ${r3._2.show}")
    println(s"EVENTS: subset-intersection    ${r4._2.show}")
    println(s"EVENTS: full-range (warm)      ${r5._2.show}")
    println(s"EVENTS: disjoint union         ${u.show}")
  }

  // ==============================================================================================
  // 3. THE LADDERS
  // ==============================================================================================

  final case class Rung(n: Int, ev: Events):
    def touch: Long = ev.touch
    def alloc: Long = ev.alloc
    def accepted: Long = ev(EffortEvent.SubtrieAcceptedByPointer)
    def rejected: Long = ev(EffortEvent.SubtrieRejectedByPointer)
    def equality: Long = ev(EffortEvent.EqualityFrontierVisit)

  /** ONE measured slope of a geometric ladder: `log2((C(2n)+1)/(C(n)+1))`. */
  def slope(cn: Long, c2n: Long): Double = math.log((c2n + 1).toDouble / (cn + 1).toDouble) / math.log(2.0)
  def slopes(xs: Vector[Long]): Vector[Double] =
    if xs.length < 2 then Vector(0.0) else xs.sliding(2).map(w => slope(w(0), w(1))).toVector
  def maxSlope(xs: Vector[Long]): Double = slopes(xs).max

  /** Run one operation over a geometric ladder.  `build(n)` constructs the operands (OUTSIDE the
   *  counted region — operand construction is not the thing being measured) and returns the thunk
   *  that performs the operation. */
  def ladder(sizes: Seq[Int], build: Int => () => Any): Vector[Rung] =
    sizes.toVector.map { n =>
      val run = build(n)
      Rung(n, ev(run()))
    }

  val flatTol = 0.35
  val flatRatio = 3.0

  def show(name: String, rs: Vector[Rung]): Unit =
    def row(label: String, f: Rung => Long): String =
      val xs = rs.map(f)
      f"    $label%-9s ${xs.mkString(",")}%-46s maxslope=${maxSlope(xs)}%5.2f"
    println(f"SLOPE $name%-46s sizes=${rs.map(_.n).mkString(",")}")
    println(row("touch", _.touch))
    println(row("steps", steps))
    println(row("alloc", _.alloc))
    println(row("accepted", _.accepted))
    if rs.exists(_.rejected > 0) then println(row("rejected", _.rejected))
    if rs.exists(_.equality > 0) then println(row("equality", _.equality))

  /** THE GATE: the count must be constant-or-depth, not merely under some linear ceiling. */
  def assertFlat(name: String, rs: Vector[Rung], what: String, f: Rung => Long): Unit =
    val xs = rs.map(f)
    val ms = maxSlope(xs)
    assert(ms <= flatTol,
      s"$name: $what is NOT constant-or-depth — measured slopes ${slopes(xs).map(d => f"$d%.2f").mkString(",")} " +
      s"over counts ${xs.mkString(",")} (a linear count shows ~1.00)")
    val ratio = (xs.last + 1).toDouble / (xs.head + 1).toDouble
    assert(ratio <= flatRatio,
      f"$name: $what grew $ratio%.1fx over ${xs.length - 1} doublings (counts ${xs.mkString(",")}); linear would be ${math.pow(2, xs.length - 1)}%.0fx")

  val depths = Vector(9, 10, 11, 12, 13)                 // 512 .. 8192 paths, 1023 .. 16383 nodes
  def sizeOf(d: Int): Int = 1 << d

  test("ASYMPTOTIC GATE: restriction by {ε} is O(1) in the size of the restricted space") {
    val rs = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val x = binTrie(d, s"r1.$d")
      () => ITrie.restriction(x, ITrie.epsilon))
    show("restriction by {ε}", rs)
    assertFlat("restriction by {ε}", rs, "touch", _.touch)
    assertFlat("restriction by {ε}", rs, "alloc", _.alloc)
  }

  test("ASYMPTOTIC GATE: restriction by ONE present prefix is O(depth of the prefix), not O(selected subtree)") {
    // the prefix has FIXED length 8; the selected subtree below it doubles at every rung
    val pre = ids("r2.p0", "r2.p1", "r2.p2", "r2.p3", "r2.p4", "r2.p5", "r2.p6", "r2.p7")
    val rs = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val x = ITrie.union(ITrie.wrap(pre, binTrie(d, s"r2.$d")), sing("r2.sibling"))
      val p = ITrie.singleton(pre)
      () => ITrie.restriction(x, p))
    show("restriction by one present prefix", rs)
    assertFlat("restriction by one present prefix", rs, "touch", _.touch)
    assertFlat("restriction by one present prefix", rs, "alloc", _.alloc)
  }

  test("ASYMPTOTIC GATE: union of two disjoint deep tries allocates ONE node") {
    val rs = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val a = ITrie.wrap(ids("r3.x"), binTrie(d, s"r3a.$d"))
      val b = ITrie.wrap(ids("r3.y"), binTrie(d, s"r3b.$d"))
      () => ITrie.union(a, b))
    show("disjoint union", rs)
    assertFlat("disjoint union", rs, "touch", _.touch)
    assertFlat("disjoint union", rs, "alloc", _.alloc)
  }

  test("ASYMPTOTIC GATE: intersection with a shared subset returns it by pointer") {
    val rs = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val a = binTrie(d, s"r4.$d")
      val sub = ITrie(false, IntMap.from(a.children.take(1)))   // shared sub-branch: B ⊆ A
      () => ITrie.intersection(a, sub))
    show("subset intersection (shared)", rs)
    assertFlat("subset intersection (shared)", rs, "touch", _.touch)
    assertFlat("subset intersection (shared)", rs, "alloc", _.alloc)
  }

  test("ASYMPTOTIC GATE: disjoint intersection is rejected without descent") {
    val rs = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val a = ITrie.wrap(ids("r5.x"), binTrie(d, s"r5a.$d"))
      val b = ITrie.wrap(ids("r5.y"), binTrie(d, s"r5b.$d"))
      () => ITrie.intersection(a, b))
    show("disjoint intersection", rs)
    assertFlat("disjoint intersection", rs, "touch", _.touch)
    assertFlat("disjoint intersection", rs, "alloc", _.alloc)
  }

  test("ASYMPTOTIC GATE: self-subtraction and disjoint subtraction are O(1)") {
    val self = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val a = binTrie(d, s"r6.$d")
      () => ITrie.subtraction(a, a))
    show("self-subtraction", self)
    assertFlat("self-subtraction", self, "touch", _.touch)
    assertFlat("self-subtraction", self, "alloc", _.alloc)

    val dis = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val a = ITrie.wrap(ids("r7.x"), binTrie(d, s"r7a.$d"))
      val b = ITrie.wrap(ids("r7.y"), binTrie(d, s"r7b.$d"))
      () => ITrie.subtraction(a, b))
    show("disjoint subtraction", dis)
    assertFlat("disjoint subtraction", dis, "touch", _.touch)
    assertFlat("disjoint subtraction", dis, "alloc", _.alloc)
  }

  test("ASYMPTOTIC GATE: {ε}·B is constant time") {
    val rs = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val b = binTrie(d, s"r8.$d")
      () => ITrie.composition(ITrie.epsilon, b))
    show("{ε}·B", rs)
    assertFlat("{ε}·B", rs, "touch", _.touch)
    assertFlat("{ε}·B", rs, "alloc", _.alloc)

    val rs2 = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val a = binTrie(d, s"r9.$d")
      () => ITrie.composition(a, ITrie.epsilon))
    show("A·{ε}", rs2)
    assertFlat("A·{ε}", rs2, "touch", _.touch)
    assertFlat("A·{ε}", rs2, "alloc", _.alloc)
  }

  test("ASYMPTOTIC GATE: a full Range is O(1), a one-element Range is O(depth) — before/after") {
    val full = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val t = binTrie(d, s"rA.$d")
      t.count                                            // warm the cached terminal count
      () => ITrie.range(t, 0, 0))
    show("full Range (warm)", full)
    assertFlat("full Range", full, "touch", _.touch)
    assertFlat("full Range", full, "alloc", _.alloc)

    val fullCold = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val t = binTrie(d, s"rB.$d")
      () => ITrie.range(t, 0, 0))
    show("full Range (COLD: first count walk)", fullCold)

    val fullLegacy = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val t = binTrie(d, s"rC.$d")
      () => legacyRange(t, 0, 0))
    show("full Range BEFORE (size walk per query)", fullLegacy)
    assert(maxSlope(fullLegacy.map(_.touch)) > 0.7,
           s"the BEFORE full Range should be linear; measured ${fullLegacy.map(_.touch).mkString(",")}")

    val one = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val t = binTrie(d, s"rD.$d")
      t.count
      () => ITrie.range(t, 1, 2))
    show("one-element Range (warm)", one)
    assertFlat("one-element Range", one, "touch", _.touch)
    assertFlat("one-element Range", one, "alloc", _.alloc)

    val oneLegacy = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val t = binTrie(d, s"rE.$d")
      () => legacyRange(t, 1, 2))
    show("one-element Range BEFORE", oneLegacy)
    assert(maxSlope(oneLegacy.map(_.touch)) > 0.7,
           s"the BEFORE one-element Range should be linear; measured ${oneLegacy.map(_.touch).mkString(",")}")
  }

  test("ASYMPTOTIC GATE: n-ary joinAll of disjoint operands allocates ONE node — before/after") {
    val ks = Vector(64, 128, 256, 512, 1024)
    val now = ladder(ks, k =>
      val parts = fanout(k, s"rF.$k")
      () => ITrie.joinAll(parts))
    show("joinAll of k disjoint tries", now)
    assertFlat("joinAll of k disjoint tries", now, "alloc", _.alloc)
    // touch is LINEAR in k here and must be: every operand has to be looked at once.  That is the
    // optimum, not a degeneracy, so it is reported rather than gated flat.
    println(f"SLOPE   joinAll touch slope (linear in k IS optimal) = ${maxSlope(now.map(_.touch))}%.2f")

    val before = ladder(ks, k =>
      val parts = fanout(k, s"rG.$k")
      () => legacyJoinAll(parts))
    show("joinAll BEFORE (balanced pairwise)", before)
    assert(maxSlope(before.map(_.alloc)) > 0.7,
           s"the BEFORE joinAll should allocate linearly in k; measured ${before.map(_.alloc).mkString(",")}")
    assert(now.last.alloc < before.last.alloc,
           s"n-ary joinAll must allocate strictly less than the pairwise fold: ${now.last.alloc} vs ${before.last.alloc}")
  }

  test("ASYMPTOTIC GATE: meetAll follows the smallest frontier at EVERY level — before/after") {
    // A and B are equal-content, distinct-object complete binary tries; C has the same root fanout
    // (so a one-shot sort by fanout cannot help) but only two paths.  The meet is C.
    def operands(d: Int, tag: String): Vector[ITrie] =
      val a = binTrie(d, "m")
      val b = binTrie(d, "m")
      val spine = leftSpine(d - 1, "m")
      val c = ITrie(false, IntMap(Interner.intern(s"m.L$d.a") -> spine, Interner.intern(s"m.L$d.b") -> spine))
      Vector(a, b, c)
    val now = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val os = operands(d, s"rH.$d")
      () => ITrie.meetAll(os))
    show("meetAll (smallest frontier)", now)
    assertFlat("meetAll", now, "touch", _.touch)

    val before = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val os = operands(d, s"rI.$d")
      () => legacyMeetAll(os))
    show("meetAll BEFORE (sorted pairwise left fold)", before)
    assert(maxSlope(before.map(_.touch)) > 0.7,
           s"the BEFORE meetAll should be linear in the LARGEST operand; measured ${before.map(_.touch).mkString(",")}")
    // and both must compute the same set
    val os = operands(11, "rJ")
    assertEquals(ps(ITrie.meetAll(os)), ps(legacyMeetAll(os)), "meetAll must agree with the pairwise fold")
  }

  // ----------------------------------------------------------------------------------------------
  // FEW WIDE OPERANDS — the case an n-ary pass over the operands' KEYS gets asymptotically wrong.
  //
  // The n-ary steps used to be a pass over every child of every operand: group them by key, then
  // rebuild the result key by key (`joinAll`), or iterate the smallest node's keys and probe the other
  // k-1 maps (`meetAll`).  Both are `Θ(Σᵢ fan(mᵢ))` UNCONDITIONALLY, while a Patricia descent separates
  // non-interleaving key ranges structurally.  With k small and the operands wide — a `TailsUnion` over
  // a few large head-groups, an `Iteration` accumulating wide group results — the n-ary pass was
  // therefore WORSE than the pairwise merge it was introduced to beat.
  //
  // The pools below are interned consecutively, so the three key ranges are ADJACENT rather than
  // separated by a high bit: the honest cost is `O(log n)` levels of descent, not `O(1)`.  That is what
  // is gated — a growth-class separation from the linear predecessor, not a flat count.
  // ----------------------------------------------------------------------------------------------

  /** `k` one-level tries of `n` distinct heads each, from `k` non-overlapping symbol pools */
  def wideOperands(k: Int, n: Int, tag: String): Vector[ITrie] =
    (0 until k).toVector.map(j => ITrie.fromPaths((0 until n).map(i => PathValue(List(s"$tag.p$j.i$i")))))

  val wideSizes = Vector(64, 128, 256, 512, 1024)

  /** THE STATISTIC FOR THIS COMPARISON: per-node descents PLUS per-key entry operations.
   *
   *  `touch` alone cannot see the defect.  The replaced loops did their work one KEY at a time, and a
   *  single-key entry is counted as `PatriciaEntry`, which belongs to the `Explain` component — so a
   *  gate on `touch` reads the probe loop as flat at 1.  The sum below is what both implementations
   *  actually perform, and it is the number the growth class is about. */
  def steps(r: Rung): Long = r.touch + r.ev(EffortEvent.PatriciaEntry)

  def assertSubLinear(name: String, now: Vector[Rung], before: Vector[Rung], f: Rung => Long): Unit =
    val ns = now.map(f)
    val bs = before.map(f)
    assert(maxSlope(bs) > 0.7,
           s"$name: the BEFORE pass should be LINEAR in the operands' keys; measured ${bs.mkString(",")}")
    assert(maxSlope(ns) < 0.7,
           s"$name: the n-ary descent should be sub-linear; measured slopes " +
           s"${slopes(ns).map(d => f"$d%.2f").mkString(",")} over ${ns.mkString(",")}")
    assert(ns.last * 4 < bs.last,
           s"$name: the n-ary descent must beat the linear pass by more than a constant at the top rung; " +
           s"measured ${ns.last} against ${bs.last}")

  test("ASYMPTOTIC GATE: n-ary joinAll over FEW WIDE operands descends, it does not scan the keys") {
    val now = ladder(wideSizes, n =>
      val os = wideOperands(3, n, s"rW.$n")
      () => ITrie.joinAll(os))
    show("joinAll of 3 wide operands", now)
    val before = ladder(wideSizes, n =>
      val os = wideOperands(3, n, s"rX.$n")
      () => legacyGroupJoinAll(os))
    show("joinAll BEFORE (group-by-key pass)", before)
    assertSubLinear("joinAll of 3 wide operands", now, before, steps)
    val os = wideOperands(3, 256, "rY")
    assertEquals(ps(ITrie.joinAll(os)), os.map(ps).reduce(_ ++ _),
                 "the n-ary join must equal the union of the operands")
  }

  test("ASYMPTOTIC GATE: n-ary meetAll over FEW WIDE operands descends, it does not probe the keys") {
    val now = ladder(wideSizes, n =>
      val os = wideOperands(3, n, s"rZ.$n")
      () => ITrie.meetAll(os))
    show("meetAll of 3 wide operands", now)
    val before = ladder(wideSizes, n =>
      val os = wideOperands(3, n, s"sA.$n")
      () => legacyProbeMeetAll(os))
    show("meetAll BEFORE (per-key probe loop)", before)
    assertSubLinear("meetAll of 3 wide operands", now, before, steps)
    val os = wideOperands(3, 256, "sB")
    assertEquals(ps(ITrie.meetAll(os)), os.map(ps).reduce(_ intersect _),
                 "the n-ary meet must equal the intersection of the operands")
  }

  // ----------------------------------------------------------------------------------------------
  // THE DISTRIBUTION SWEEP.
  //
  // A merge has no single asymptotic class: it has one PER DATA DISTRIBUTION.  A union of two n-key
  // nodes is constant when the key ranges are separable, `O(log n)` when they are adjacent, and
  // `Θ(n)` when they are interleaved or equal — and each of those is the OPTIMUM for its
  // distribution, not a degeneracy.  So the gate is not "flat": it is that the measured cost tracks
  // the distribution's own parameter, with no over-approximation anywhere on the sweep.
  //
  // The parameter is the PAIRED-KEY COUNT (keys present in both operands, each forcing a recursive
  // merge below it) plus the DESCENT the key layout forces before one side can be attached whole.
  // Five distributions over the same n span the whole range:
  //
  //   separated  A = [0,n), B = [4n,5n)     — one high bit apart:      0 paired, O(1) expected
  //   adjacent   A = [0,n), B = [n,2n)      — contiguous ranges:       0 paired, O(log n) expected
  //   striped    A = evens, B = odds        — maximal interleave:      0 paired, Θ(n) expected
  //   half       A = [0,n), B = [n/2,3n/2)  — half the keys pair:      n/2 paired, Θ(n) expected
  //   equal      A = B (distinct objects)   — every key pairs:         n paired, Θ(n) expected
  //
  // Reported per rung, asserted two ways: the class at each end of the sweep, and — for the paired
  // distributions — that the cost per paired key stays inside a constant band, so the implementation
  // is proportional to the distribution's parameter rather than to n.
  // ----------------------------------------------------------------------------------------------

  /** THE KEY POOL.  The distributions below must control the INTERNED IDS, which are what the trie is
   *  keyed by — not the symbol names.  `Interner` assigns ids in first-use order, so striping the names
   *  produced two ADJACENT id blocks and the sweep measured the same layout twice (caught by this
   *  suite: "striped" read flat, which is impossible for a fully interleaved merge).  One pool interned
   *  in one pass gives consecutive ids, and every distribution is an index set into it. */
  val poolSize = 12288
  val pool: Array[Int] = (0 until poolSize).toArray.map(i => Interner.intern(f"sw.k$i%06d"))
  assert(pool(1) - pool(0) == 1 && pool(poolSize - 1) - pool(0) == poolSize - 1,
         "the key pool must be a consecutive id range for the distributions to mean what they say")

  /** a one-level-plus-leaf trie over the pool ids at `idx`; `leaf` distinguishes the two sides so a
   *  PAIRED key forces a real recursive merge rather than an `eq` short circuit on a shared `epsilon` */
  def fromIdx(idx: Seq[Int], leaf: String): ITrie =
    val child = sing(leaf)
    ITrie(false, IntMap.from(idx.map(i => pool(i) -> child)))

  final case class Dist(name: String, paired: Int => Int, expect: String,
                        build: (Int, String) => (ITrie, ITrie))

  val dists: Vector[Dist] = Vector(
    // one high id block apart: the Patricia join separates them above every key bit
    Dist("separated", _ => 0, "constant",
         (n, t) => (fromIdx(0 until n, s"$t.a"), fromIdx(4 * n until 5 * n, s"$t.b"))),
    // contiguous, POWER-OF-TWO ALIGNED blocks: one bit separates them, so this is constant too — the
    // "log n" label an earlier revision of this sweep carried was an over-approximation, and the
    // measurement (2 steps at every rung) refuted it
    Dist("adjacent", _ => 0, "constant",
         (n, t) => (fromIdx(0 until n, s"$t.a"), fromIdx(n until 2 * n, s"$t.b"))),
    // the same blocks MISALIGNED by one id.  This was the candidate for the in-between class and it is
    // NOT one: measured 3 steps at every rung.  Two contiguous ranges occupy O(1) aligned Patricia
    // subtrees whichever way they are offset, and the merge attaches those whole — so the honest
    // statement is that NON-INTERLEAVING key sets merge in constant time, and the linear cases below
    // are exactly the interleaving and the pairing ones.  Labelled by what it measures, not by what a
    // safe guess would have said.
    Dist("offset-block", _ => 0, "constant",
         (n, t) => (fromIdx(0 until n, s"$t.a"), fromIdx(n + 1 until 2 * n + 1, s"$t.b"))),
    // maximal interleave: no key pairs, yet every Patricia level of both trees is shared
    Dist("striped", _ => 0, "linear",
         (n, t) => (fromIdx(0 until 2 * n by 2, s"$t.a"), fromIdx(1 until 2 * n by 2, s"$t.b"))),
    Dist("half-paired", n => n / 2, "linear",
         (n, t) => (fromIdx(0 until n, s"$t.a"), fromIdx(n / 2 until 3 * n / 2, s"$t.b"))),
    Dist("equal", n => n, "linear",
         (n, t) => (fromIdx(0 until n, s"$t.a"), fromIdx(0 until n, s"$t.b"))))

  /** the sweep for one binary operation: the measured class per distribution, and the cost per unit of
   *  the distribution's own parameter */
  def sweep(op: String, f: (ITrie, ITrie) => ITrie, ref: (ITrie, ITrie) => Set[PathValue]): Unit =
    println(s"SWEEP $op — cost per DATA DISTRIBUTION (steps = descents + per-key entries)")
    for d <- dists do
      val rs = ladder(wideSizes, n =>
        val (a, b) = d.build(n, s"sw.$op.${d.name}.$n")
        () => f(a, b))
      val xs = rs.map(steps)
      val ms = maxSlope(xs)
      val perPaired = xs.zip(wideSizes).map { (c, n) =>
        val p = d.paired(n); if p == 0 then Double.NaN else c.toDouble / p }
      println(f"  ${d.name}%-12s expect ${d.expect}%-9s steps ${xs.mkString(",")}%-34s maxslope=$ms%5.2f" +
              (if perPaired.head.isNaN then "" else f"  per-paired ${perPaired.map(r => f"$r%.2f").mkString(",")}"))
      // the class, at both ends of the sweep
      d.expect match
        case "constant" =>
          assert(ms <= flatTol, s"$op/${d.name}: separable ranges must be constant; steps ${xs.mkString(",")}")
        case "log n" =>
          assert(ms <= 0.7 && (xs.last + 1).toDouble / (xs.head + 1) <= 4.0,
                 s"$op/${d.name}: adjacent ranges must be sub-linear; steps ${xs.mkString(",")}")
        case _ =>
          assert(ms <= 1.15, s"$op/${d.name}: must be at most linear; steps ${xs.mkString(",")}")
      // NO OVER-APPROXIMATION on the paired distributions: a bounded number of steps per paired key
      if d.paired(wideSizes.last) > 0 then
        val worst = perPaired.max
        assert(worst <= 12.0,
               f"$op/${d.name}: $worst%.1f steps per paired key — the cost is not proportional to the " +
               f"distribution's parameter (steps ${xs.mkString(",")}, paired " +
               f"${wideSizes.map(d.paired).mkString(",")})")
      // and the answer is right at every rung
      for n <- wideSizes do
        val (a, b) = d.build(n, s"swc.$op.${d.name}.$n")
        assertEquals(ps(f(a, b)), ref(a, b), s"$op/${d.name} at n=$n")

  test("DISTRIBUTION SWEEP: union cost tracks the data distribution, not a single class") {
    sweep("union", ITrie.union, refUnion)
  }

  test("DISTRIBUTION SWEEP: intersection cost tracks the data distribution") {
    sweep("intersection", ITrie.intersection, refInter)
  }

  test("DISTRIBUTION SWEEP: subtraction cost tracks the data distribution") {
    sweep("subtraction", ITrie.subtraction, refDiff)
  }

  test("DISTRIBUTION SWEEP: the n-ary join over three operands tracks the distribution") {
    println("SWEEP joinAll/3 — cost per DATA DISTRIBUTION")
    val cases = Vector(
      ("separated", "constant", (n: Int, t: String) =>
        Vector(fromIdx(0 until n, s"$t.a"), fromIdx(4 * n until 5 * n, s"$t.b"),
               fromIdx(8 * n until 9 * n, s"$t.c"))),
      ("adjacent", "log n", (n: Int, t: String) =>
        Vector(fromIdx(0 until n, s"$t.a"), fromIdx(n until 2 * n, s"$t.b"),
               fromIdx(2 * n until 3 * n, s"$t.c"))),
      ("striped", "linear", (n: Int, t: String) =>
        Vector(fromIdx(0 until 3 * n by 3, s"$t.a"), fromIdx(1 until 3 * n by 3, s"$t.b"),
               fromIdx(2 until 3 * n by 3, s"$t.c"))),
      ("equal", "linear", (n: Int, t: String) =>
        Vector(fromIdx(0 until n, s"$t.a"), fromIdx(0 until n, s"$t.b"), fromIdx(0 until n, s"$t.c"))))
    for (name, expect, build) <- cases do
      val rs = ladder(wideSizes, n => { val os = build(n, s"nj.$name.$n"); () => ITrie.joinAll(os) })
      val xs = rs.map(steps)
      println(f"  $name%-12s expect $expect%-9s steps ${xs.mkString(",")}%-34s maxslope=${maxSlope(xs)}%5.2f")
      expect match
        case "constant" => assert(maxSlope(xs) <= flatTol, s"joinAll/$name: steps ${xs.mkString(",")}")
        case "log n" => assert(maxSlope(xs) <= 0.7, s"joinAll/$name: steps ${xs.mkString(",")}")
        case _ => assert(maxSlope(xs) <= 1.15, s"joinAll/$name: steps ${xs.mkString(",")}")
      for n <- wideSizes do
        val os = build(n, s"njc.$name.$n")
        assertEquals(ps(ITrie.joinAll(os)), os.map(ps).reduce(_ ++ _), s"joinAll/$name at n=$n")
  }

  test("the n-ary operations return an OPERAND BY POINTER when the answer is one") {
    // b absorbs a; a is contained in b.  Both n-ary steps used to end in an unconditional fresh node,
    // so a whole-subspace accept was impossible in them however cheap the merge was.
    val a = ITrie.fromPaths((0 until 512).map(i => PathValue(List(s"sC.i$i"))))
    val b = ITrie.union(a, sing("sC.extra"))
    val (j, jev) = EffortSink.count(ITrie.joinAll(Vector(a, b, a, b, a)))
    assert(j eq b, "the join of operands absorbed by b IS b, by pointer")
    assertEquals(jev.alloc, 0L, s"an absorbed join allocates nothing; measured ${jev.alloc}")
    val (m, mev) = EffortSink.count(ITrie.meetAll(Vector(b, a, b, a)))
    assert(m eq a, "the meet of operands all containing a IS a, by pointer")
    assertEquals(mev.alloc, 0L, s"a contained meet allocates nothing; measured ${mev.alloc}")
    assertEquals(ps(j), ps(b))
    assertEquals(ps(m), ps(a))
  }

  test("ASYMPTOTIC GATE: tails-intersection of a one-head space is O(1)") {
    val rs = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val inner = binTrie(d, s"rK.$d")
      val s = ITrie.wrap(ids("rK.h"), inner)
      () => ITrie.tailsIntersection(s))
    show("tailsIntersection, one head", rs)
    assertFlat("tailsIntersection, one head", rs, "touch", _.touch)
    assertFlat("tailsIntersection, one head", rs, "alloc", _.alloc)
  }

  test("ASYMPTOTIC GATE: fused raffination never costs more than restriction-then-subtraction") {
    val pre = ids("rL.p0", "rL.p1", "rL.p2", "rL.p3")
    def build(d: Int, tag: String): (ITrie, ITrie) =
      val x = ITrie.union(ITrie.wrap(pre, binTrie(d, s"$tag.$d")), sing("rL.sibling"))
      (x, ITrie.singleton(pre))
    val now = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val (x, y) = build(d, "rL")
      () => ITrie.raffination(x, y))
    show("raffination (fused, one pass)", now)
    assertFlat("raffination", now, "touch", _.touch)
    assertFlat("raffination", now, "alloc", _.alloc)

    val before = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val (x, y) = build(d, "rM")
      () => legacyRaffination(x, y))
    show("raffination BEFORE (restriction then subtraction)", before)
    assert(now.last.touch <= before.last.touch && now.last.alloc <= before.last.alloc,
           s"the fused pass must not cost more: fused ${now.last.ev.showComponents} vs two-pass ${before.last.ev.showComponents}")
    val (x, y) = build(11, "rN")
    assertEquals(ps(ITrie.raffination(x, y)), ps(legacyRaffination(x, y)), "fused raffination must agree with x ∖ (x <| y)")
    // and the identity case allocates nothing at all (operands built outside the counted region)
    val ix = binTrie(9, "rO")
    val iy = sing("rO.unrelated")
    val idn = ev(ITrie.raffination(ix, iy))
    assertEquals(idn.alloc, 0L, s"raffination with nothing to drop must allocate nothing: ${idn.show}")
    assertEquals(idn(EffortEvent.AlgebraIdentityLeft), 1L, idn.show)
  }

  test("ASYMPTOTIC GATE: fixpoint convergence walks only the equality frontier — before/after") {
    // THE ROUND THAT MATTERS is the one that DECIDES TERMINATION: the body produced a value equal to
    // the previous iterate.  With every operation propagating identity, that value shares its
    // structure with the iterate, so the two are equal through a shared children map.  Pointer
    // rejection settles it in O(1); a structural `==` walk visits every node of the fixpoint.
    def converged(d: Int, tag: String): (ITrie, ITrie) =
      val base = binTrie(d, "q")
      (base, ITrie(base.terminal, base.children))        // distinct root object, SAME children
    val now = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val (a, b) = converged(d, s"rP.$d")
      () => ITrie.equalT(a, b))
    show("equalT on the converging round", now)
    assertFlat("equalT (converging round)", now, "equality frontier", _.equality)

    val before = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val (a, b) = converged(d, s"rQ.$d")
      () => legacyEqual(a, b))
    show("structural == BEFORE (converging round)", before)
    assert(maxSlope(before.map(_.equality)) > 0.7,
           s"the BEFORE equality should be linear; measured ${before.map(_.equality).mkString(",")}")

    // a NON-converging round: one branch changed deep down, every other branch shared by pointer.
    // `equalT` walks the changed spine and rejects each shared sibling by pointer.
    def delta(d: Int, tag: String): (ITrie, ITrie) =
      val base = binTrie(d, "q")
      def deepen(t: ITrie): ITrie =
        if t.children.isEmpty then ITrie(true, IntMap(Interner.intern(s"$tag.delta") -> ITrie.epsilon))
        else
          val k = t.children.keysIterator.next()
          ITrie(t.terminal, t.children.updated(k, deepen(t.children(k))))
      (base, deepen(base))
    val dl = ladder(depths.map(sizeOf), n =>
      val d = 31 - Integer.numberOfLeadingZeros(n)
      val (a, b) = delta(d, s"rR.$d")
      () => ITrie.equalT(a, b))
    show("equalT on a one-branch delta", dl)
    assertFlat("equalT (delta round)", dl, "equality frontier", _.equality)

    // agreement
    val (a, b) = delta(10, "rS")
    assertEquals(ITrie.equalT(a, b), false)
    assertEquals(ITrie.equalT(a, b), legacyEqual(a, b))
    val (c, e) = converged(10, "rT")
    assertEquals(ITrie.equalT(c, e), true)
    assertEquals(ITrie.equalT(c, c), true)
    assertEquals(ITrie.equalT(binTrie(6, "rU"), binTrie(6, "rU")), true, "equal content through distinct objects")
    assertEquals(ITrie.equalT(binTrie(6, "rU"), binTrie(5, "rU")), false)
  }

  // ==============================================================================================
  // 4. THE "BEFORE" IMPLEMENTATIONS
  // ==============================================================================================
  // Each is the algorithm this change replaced, instrumented with the same events and run over the
  // same operands.  They call the CURRENT primitives, so they already enjoy the new identity
  // propagation — the gap they show is the control structure alone, and therefore a LOWER bound on
  // the improvement.

  /** BEFORE `ITrie.range`: a full recursive size walk before the identity check, a child-key sort at
   *  every visited node, and the window rebuilt path-by-path through `singleton` + `union`. */
  def legacyRange(t: ITrie, start: Int, end: Int): ITrie =
    def walkSize(n: ITrie): Int =
      effort(EffortEvent.TrieNodeVisit)
      (if n.terminal then 1 else 0) + n.children.valuesIterator.map(walkSize).sum
    val size = walkSize(t)
    val (lo, hi) = RangeBounds.normalize(size, start, end)
    if hi <= lo then ITrie.empty
    else if lo == 0 && hi == size then t
    else
      var idx = 0
      var out = ITrie.empty
      def go(n: ITrie, acc: List[Int]): Unit =
        effort(EffortEvent.TrieNodeVisit)
        if idx < hi then
          if n.terminal then { if idx >= lo then out = ITrie.union(out, ITrie.singleton(acc.reverse)); idx += 1 }
          if idx < hi && n.children.nonEmpty then
            val keys = n.children.keysIterator.toArray.sortBy(Interner.unintern)
            var i = 0
            while i < keys.length && idx < hi do { go(n.children(keys(i)), keys(i) :: acc); i += 1 }
      go(t, Nil)
      out

  /** BEFORE `ITrie.joinAll`: a balanced pairwise merge — `log k` levels, each allocating. */
  def legacyJoinAll(ts: Seq[ITrie]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    val live = ts.filter(_.nonEmpty).toArray
    if live.isEmpty then ITrie.empty
    else if live.length == 1 then live(0)
    else
      def merge(lo: Int, hi: Int): ITrie =
        if hi - lo == 1 then live(lo) else { val mid = (lo + hi) >>> 1; ITrie.union(merge(lo, mid), merge(mid, hi)) }
      merge(0, live.length)

  /** BEFORE `ITrie.joinAll`'s children step: group every child of every operand by key, then rebuild
   *  the result map key by key.  `Θ(Σᵢ fan(mᵢ))` whatever the operands look like. */
  def legacyGroupJoinAll(ts: Seq[ITrie]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    val live = ts.filter(_.nonEmpty).toArray
    if live.isEmpty then ITrie.empty
    else if live.length == 1 then live(0)
    else
      var term = false
      val groups = scala.collection.mutable.LongMap.empty[scala.collection.mutable.ArrayBuffer[ITrie]]
      var i = 0
      while i < live.length do
        val t = live(i)
        if t.terminal then term = true
        t.children.foreach { case (k, c) =>
          effort(EffortEvent.PatriciaEntry)
          groups.getOrElseUpdate(k.toLong, scala.collection.mutable.ArrayBuffer.empty) += c }
        i += 1
      var ch = IntMap.empty[ITrie]
      groups.foreach { case (k, cs) => ch = ch.updated(k.toInt, legacyGroupJoinAll(cs.toSeq)) }
      ITrie(term, ch)

  /** BEFORE `ITrie.meetAll`'s children step: iterate the smallest node's keys and probe the other
   *  `k-1` maps for each.  Follows the smallest branch at every level — at `Θ(fan)` probes to do it. */
  def legacyProbeMeetAll(ts: Seq[ITrie]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if ts.isEmpty then ITrie.empty
    else if ts.exists(_.isEmpty) then { effort(EffortEvent.SubtrieRejectedByPointer); ITrie.empty }
    else
      val live = ts.distinct.toArray
      if live.length == 1 then live(0)
      else
        val term = live.forall(_.terminal)
        var si = 0
        var i = 1
        while i < live.length do { if live(i).children.size < live(si).children.size then si = i; i += 1 }
        val smallest = live(si)
        if smallest.children.isEmpty then (if term then ITrie.epsilon else ITrie.empty)
        else
          var ch = IntMap.empty[ITrie]
          smallest.children.foreach { case (k, sc) =>
            val cs = scala.collection.mutable.ArrayBuffer.empty[ITrie]
            cs += sc
            var j = 0
            var ok = true
            while ok && j < live.length do
              if j != si then
                effort(EffortEvent.PatriciaEntry)
                live(j).children.get(k) match
                  case Some(c) => cs += c
                  case None => ok = false; effort(EffortEvent.SubtrieRejectedByPointer)
              j += 1
            if ok then
              val r = legacyProbeMeetAll(cs.toSeq)
              if r.nonEmpty then ch = ch.updated(k, r) }
          if ch.isEmpty && !term then ITrie.empty else ITrie(term, ch)

  /** BEFORE `ITrie.meetAll`: one sort by root fanout, then a pairwise left fold. */
  def legacyMeetAll(ts: Seq[ITrie]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if ts.isEmpty then ITrie.empty
    else if ts.length == 1 then ts.head
    else if ts.exists(_.isEmpty) then ITrie.empty
    else ts.sortBy(_.children.size).reduceLeft(ITrie.intersection)

  /** BEFORE `ITrie.raffination`: the definitional two-pass `x ∖ (x <| y)`. */
  def legacyRaffination(x: ITrie, y: ITrie): ITrie = ITrie.subtraction(x, ITrie.restriction(x, y))

  /** BEFORE the fixpoint convergence test: a structural walk with no pointer rejection. */
  def legacyEqual(a: ITrie, b: ITrie): Boolean =
    effort(EffortEvent.EqualityFrontierVisit)
    a.terminal == b.terminal && a.children.size == b.children.size &&
      a.children.forall { case (k, ac) => b.children.get(k) match
        case Some(bc) => legacyEqual(ac, bc)
        case None => false }
end OptimalTrieCheck
