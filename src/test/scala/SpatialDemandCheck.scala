package morkl

import munit.FunSuite
import scala.util.Random

/** THE FOUR COUNTEREXAMPLES OF review.md ITEM 3, predicted and measured.
 *
 *  Each test states the LAW ("this forces one node, not `N(A) + N(B)`"), predicts it with
 *  [[SpatialDemand]], measures it with the [[ZipperDemandSink]] + [[EffortSink]] oracle on a real
 *  `execZ` run, and asserts the two agree — plus that the quantity the current `ZipperCost` formula
 *  uses is orders of magnitude larger.  Then the same cases are grown geometrically and the SLOPE
 *  `log2((C(2n)+1)/(C(n)+1))` is checked: containing a measurement under a linear ceiling is not the
 *  same as predicting a constant, and only the second is a pass here.
 *
 *  EVERYTHING IS MEASURED ON THE OPTIMIZED PROGRAM.  Every case is wrapped in a `Routine` and put
 *  through `Routine.optimized` before it is analysed OR run, and the test asserts the operator survived
 *  that pass — a cost claim about a definitional form the backend never runs is the wrong question.
 *  The operands are `Mention`s bound through `ic` for the same reason `ZipperScaleBench` uses them: an
 *  optimizer that can see the operand values folds the whole term away and there is nothing left to
 *  measure.
 *
 *  The `leaf`/`rel` fact oracles live HERE, in the test, and are structural walks over the concrete
 *  operands.  `SpatialDemand` itself never sees a trie: it is a combinator over the facts it is handed. */
class SpatialDemandCheck extends FunSuite:
  import Space.*

  // ----------------------------------------------------------------------------------------------
  // fixtures: uniform tries, so a per-depth max arity IS every node's arity and the prediction is
  // exact rather than merely an upper bound (these are also the geometric-scale generators review.md
  // item 2 asks for: one knob, exponentially growing node counts)
  // ----------------------------------------------------------------------------------------------

  /** every path of length `depth` over the alphabet `alpha`, under `prefix` */
  private def uniform(prefix: List[String], depth: Int, alpha: Seq[String]): Set[PathValue] =
    var acc: Vector[List[String]] = Vector(Nil)
    for _ <- 0 until depth do acc = acc.flatMap(p => alpha.map(a => p :+ a))
    acc.map(p => PathValue(prefix ++ p)).toSet
  private def trie(ps: Set[PathValue]): ITrie = ITrie.fromSpaceValue(SpaceValue(ps))
  private def m(s: String) = SpaceMention(s)
  private def cpath(items: String*) = Path.Constant(PathValue(items.toList))

  // ---- the fact oracles the analysis is handed (structural; no algebra, no evaluation) ----------

  private def isLeaf(s: Space): Boolean = s match
    case Empty | Mention(_) | Literal(_) => true
    case Singleton(Path.Constant(_)) => true
    case _ => false
  private def concrete(ic: Map[SpaceMention, ITrie])(s: Space): ITrie = s match
    case Empty => ITrie.empty
    case Mention(v) => ic.getOrElse(v, ITrie.empty)
    case Literal(sv) => ITrie.fromSpaceValue(sv)
    case Singleton(Path.Constant(pv)) => ITrie.singletonP(pv)
    case _ => ITrie.empty
  private def facts(ic: Map[SpaceMention, ITrie]): (Space => Layers, (Space, Space) => Pairing) =
    (s => if isLeaf(s) then Layers.ofTrie(concrete(ic)(s)) else Layers(Vector.empty, Vector.empty, Vector.empty, false),
     (a, b) => if isLeaf(a) && isLeaf(b) then Pairing.ofTries(concrete(ic)(a), concrete(ic)(b))
               else Pairing.unknown)

  private def predict(s: Space, ic: Map[SpaceMention, ITrie]): DemandSummary =
    val (leaf, rel) = facts(ic)
    SpatialDemand.analyze(SpatialDemand.fromSpace(s, leaf, rel))

  // ---- the measurement -------------------------------------------------------------------------

  private final case class Measured(forcedVirtual: Long, freshNodes: Long, cursorReads: Long,
                                    cursorMapEntries: Long, materializeEntries: Long,
                                    acceptedLit: Long, virtualAlloc: Long,
                                    result: ITrie, events: ZipperCounts):
    def show: String = s"forcedVirtual=$forcedVirtual acceptedLit=$acceptedLit cursorReads=$cursorReads " +
      s"cursorMapEntries=$cursorMapEntries materializeEntries=$materializeEntries virtualAlloc=$virtualAlloc"

  private def measure(s: Space, ic: Map[SpaceMention, ITrie]): Measured =
    val ((r, ev), zc) = ZipperDemandSink.count(EffortSink.count(execZ(s)(using ic = ic)))
    Measured(ev(EffortEvent.ZipperMaterializeNode), ev(EffortEvent.FreshNode),
             ev(EffortEvent.ZipperCursorRead), zc.cursorMapEntries, zc.materializeEntries,
             zc.acceptedLit, zc.virtualAlloc, r, zc)

  /** THE OPTIMIZED PROGRAM — steer 3.  Returns the body `Routine.optimized` produces. */
  private def opt(s: Space, ms: Vector[SpaceMention]): Space =
    Routine(RoutinePtr("q"), Vector.empty, ms, s).optimized.body

  /** assert the four required quantities agree EXACTLY, and report the rest */
  private def agree(label: String, p: DemandSummary, mm: Measured): Unit =
    println(f"  $label%-22s PREDICTED ${p.show}")
    println(f"  ${""}%-22s MEASURED  ${mm.show}")
    println(f"  ${""}%-22s profile   ${p.showProfile}")
    assertEquals(p.forcedVirtual, mm.forcedVirtual, s"$label: forced non-Lit cursor nodes")
    assertEquals(p.freshNodes, mm.freshNodes, s"$label: fresh materialised nodes")
    assertEquals(p.acceptedLit, mm.acceptedLit, s"$label: accepted Lit subtries")
    assertEquals(p.cursorMapEntries + p.materializeEntries,
                 mm.cursorMapEntries + mm.materializeEntries, s"$label: cursor-map visits")
    assertEquals(p.virtualAlloc, mm.virtualAlloc, s"$label: virtual cursor allocations")
    assertEquals(p.cursorReads, mm.cursorReads, s"$label: cursor reads")

  private def slope(cLo: Long, cHi: Long): Double =
    math.log((cHi + 1.0) / (cLo + 1.0)) / math.log(2.0)

  // ==============================================================================================
  // COUNTEREXAMPLE 1 — a union of two deep tries with DISJOINT ROOT BRANCHES
  // ==============================================================================================

  /** `A` on root keys `a0..a3`, `B` on `b0..b3`, each key carrying a complete binary trie of depth
   *  `d - 1`.  `IntMap.unionWith` finds NO shared key, so every child cursor it produces is the
   *  operand's own `Lit` and `materialize` stops there. */
  private def disjointUnion(d: Int): (Space, Map[SpaceMention, ITrie], ITrie, ITrie) =
    val alpha = Seq("x", "y")
    val a = trie((0 until 4).flatMap(i => uniform(List("a" + i), d - 1, alpha)).toSet)
    val b = trie((0 until 4).flatMap(i => uniform(List("b" + i), d - 1, alpha)).toSet)
    (Union(Mention(m("A")), Mention(m("B"))), Map(m("A") -> a, m("B") -> b), a, b)

  test("CE1: a union with disjoint root branches forces ONE node and reuses both child tries") {
    println("\n=== CE1  (A ∪ B), root branches disjoint — the fresh-node count is 1, not N(A)+N(B) ===")
    val (raw, ic, a, b) = disjointUnion(9)
    val prog = opt(raw, Vector(m("A"), m("B")))
    assert(prog.isInstanceOf[Space.Union], s"the optimizer must leave the union in place: ${prog.show}")
    val p = predict(prog, ic); val mm = measure(prog, ic)
    assertEquals(mm.result, ITrie.union(a, b), "execZ must still compute A ∪ B")
    val nA = a.nodeCount.toLong; val nB = b.nodeCount.toLong
    println(f"  N(A)=$nA N(B)=$nB  |A ∪ B| nodes=${mm.result.nodeCount}")
    agree("CE1 disjoint union", p, mm)
    assertEquals(p.forcedVirtual, 1L, "ONE fresh materialised root")
    assertEquals(p.acceptedLit, 8L, "both operands' four root branches accepted by pointer")
    assert(p.exact, s"the prediction must be exact, not a bound: ${p.show}")
    println(f"  the summed-local-worst-case parameter N(A)+N(B) = ${nA + nB} is ${(nA + nB) / 1}x the truth")
    assert(nA + nB > 1000L, "the operands must be big enough for the point to be visible")
  }

  // ==============================================================================================
  // COUNTEREXAMPLE 2 — `Prefix(p, X)`
  // ==============================================================================================

  test("CE2: Prefix(p, X) forces |p|+1 nodes and then reuses X's children") {
    println("\n=== CE2  Wrap(X, p) — |p|+1 fresh nodes, not |p|+1+N(X) ===")
    val alpha = Seq("0", "1", "2")
    val x = trie(uniform(Nil, 7, alpha))
    val ic = Map(m("X") -> x)
    val prog = opt(Wrap(Mention(m("X")), cpath("p1", "p2", "p3")), Vector(m("X")))
    assert(prog.isInstanceOf[Space.Wrap], s"the optimizer must leave the wrap in place: ${prog.show}")
    val p = predict(prog, ic); val mm = measure(prog, ic)
    val nX = x.nodeCount.toLong
    println(f"  N(X)=$nX  root arity of X=${x.children.size}")
    agree("CE2 prefix", p, mm)
    assertEquals(p.forcedVirtual, 4L, "|p| spine nodes plus ONE copied focus node")
    assertEquals(p.acceptedLit, x.children.size.toLong, "X's root children reused unchanged")
    assert(p.exact, s"the prediction must be exact: ${p.show}")
    println(f"  ZipperCost.wrap charges alloc = |p|+1+N(X) = ${3 + 1 + nX}, i.e. ${(3 + 1 + nX) / 4.0}%.0fx the truth")
  }

  // ==============================================================================================
  // COUNTEREXAMPLE 3 — restriction by a length-`d` prefix
  // ==============================================================================================

  test("CE3: restriction by a length-d prefix forces the d-node frontier and accepts the subtree") {
    println("\n=== CE3  X <| {one length-3 prefix} — 3 fresh nodes and ONE accepted subtree ===")
    val k = 3
    val alpha = (0 until k).map(_.toString)
    val x = trie(uniform(Nil, 7, alpha))
    val pfx = trie(Set(PathValue(List("0", "0", "0"))))
    val ic = Map(m("X") -> x, m("P") -> pfx)
    val prog = opt(Restriction(Mention(m("X")), Mention(m("P"))), Vector(m("X"), m("P")))
    assert(prog.isInstanceOf[Space.Restriction], s"the optimizer must leave the restriction: ${prog.show}")
    val p = predict(prog, ic); val mm = measure(prog, ic)
    assertEquals(mm.result, ITrie.restriction(x, pfx), "execZ must still compute the restriction")
    val nX = x.nodeCount.toLong
    println(f"  N(X)=$nX  selected subtree nodes=${mm.result.nodeCount}  |selected|=${mm.result.size}")
    agree("CE3 prefix restriction", p, mm)
    assertEquals(p.forcedVirtual, 3L, "the d-node matching frontier and nothing else")
    assertEquals(p.acceptedLit, 1L, "the selected subtree is returned wholesale")
    assert(p.exact, s"the prediction must be exact: ${p.show}")
    println(f"  ZipperCost.restrict charges alloc = min(N(X),N(P)) = ${math.min(nX, pfx.nodeCount.toLong)}")

    // and the degenerate end of the same law: restriction by {ε} is CONSTANT with no result node
    val eps = ITrie.epsilon
    val ic2 = Map(m("X") -> x, m("P") -> eps)
    val p2 = predict(prog, ic2); val m2 = measure(prog, ic2)
    println(f"  X <| {ε}: PREDICTED ${p2.show}")
    println(f"            MEASURED  ${m2.show}")
    assertEquals(m2.result, x, "X <| {ε} is X, by pointer")
    assertEquals(p2.forcedVirtual, 0L, "restriction by {ε} materialises nothing")
    assertEquals(m2.forcedVirtual, 0L, "and the executor really allocates nothing")
    assertEquals(p2.acceptedLit, 1L); assertEquals(m2.acceptedLit, 1L)
  }

  // ==============================================================================================
  // COUNTEREXAMPLE 4 — composition grafts the right cursor; a LEFT EPSILON is the adversarial case
  // ==============================================================================================

  test("CE4: composition grafts the existing right cursor — left epsilon forces ONE node") {
    println("\n=== CE4  A ∘ B — the right operand is grafted by pointer, not N(A)·N(B) ===")
    val b = trie(uniform(Nil, 6, Seq("0", "1", "2")))
    val nB = b.nodeCount.toLong

    // (a) LEFT EPSILON — the simplest adversarial case
    val ic1 = Map(m("A") -> ITrie.epsilon, m("B") -> b)
    val prog = opt(Composition(Mention(m("A")), Mention(m("B"))), Vector(m("A"), m("B")))
    assert(prog.isInstanceOf[Space.Composition], s"the optimizer must leave the composition: ${prog.show}")
    val p1 = predict(prog, ic1); val m1 = measure(prog, ic1)
    assertEquals(m1.result, b, "{ε} ∘ B is B")
    println(f"  N(B)=$nB, so ZipperCost.compose charges alloc = N(A)·N(B) = ${1 * nB}")
    agree("CE4a left epsilon", p1, m1)
    assertEquals(p1.forcedVirtual, 1L, "ONE fresh node; all of B accepted by pointer")
    assertEquals(p1.acceptedLit, b.children.size.toLong, "B's root children grafted unchanged")
    assert(p1.exact, s"the prediction must be exact: ${p1.show}")

    // (b) a single deep left path: its own spine plus one focus node, and B grafted by pointer
    val d = 5
    val ic2 = Map(m("A") -> ITrie.singletonP(PathValue(List.fill(d)("z"))), m("B") -> b)
    val p2 = predict(prog, ic2); val m2 = measure(prog, ic2)
    println(f"  single depth-$d left path: ZipperCost.compose charges N(A)·N(B) = ${(d + 1) * nB}")
    agree("CE4b deep left path", p2, m2)
    assertEquals(p2.forcedVirtual, (d + 1).toLong, "the left spine plus one focus node")
    assertEquals(p2.acceptedLit, b.children.size.toLong, "B grafted by pointer at the terminal leaf")
    assert(p2.exact, s"the prediction must be exact: ${p2.show}")
  }

  // ==============================================================================================
  // SLOPES — a constant must be PREDICTED as a constant, not merely contained by a linear ceiling
  // ==============================================================================================

  test("SLOPES: forced-node counts stay flat / depth-only as the operands grow geometrically") {
    println("\n=== SLOPES: log2((C(2n)+1)/(C(n)+1)) for the forced-node count against the operand size ===")
    println(f"  ${"case"}%-26s ${"depth"}%5s ${"N(operands)"}%12s ${"pred"}%6s ${"meas"}%6s ${"slope(N)"}%9s")

    def row(label: String, d: Int, nodes: Long, pred: Long, meas: Long, prevNodes: Long, prevPred: Long): Unit =
      val s = if prevNodes <= 0 then Double.NaN
              else slope(prevPred, pred) / math.max(slope(prevNodes, nodes), 1e-9)
      println(f"  $label%-26s $d%5d $nodes%12d $pred%6d $meas%6d " +
              (if s.isNaN then f"${"-"}%9s" else f"$s%9.3f"))

    // (1) disjoint union: constant 1 forced node while N grows exponentially
    var prevN = 0L; var prevP = 0L
    for d <- Seq(7, 9, 11) do
      val (raw, ic, a, b) = disjointUnion(d)
      val prog = opt(raw, Vector(m("A"), m("B")))
      val p = predict(prog, ic); val mm = measure(prog, ic)
      val n = a.nodeCount.toLong + b.nodeCount.toLong
      row("disjoint A ∪ B", d, n, p.forcedVirtual, mm.forcedVirtual, prevN, prevP)
      assertEquals(p.forcedVirtual, 1L, "the disjoint union must stay at ONE forced node")
      assertEquals(mm.forcedVirtual, 1L)
      prevN = n; prevP = p.forcedVirtual

    // (2) restriction by a fixed length-3 prefix over an exponentially growing selected subtree
    prevN = 0L; prevP = 0L
    val pfx = trie(Set(PathValue(List("0", "0", "0"))))
    for d <- Seq(6, 8, 10) do
      val x = trie(uniform(Nil, d, Seq("0", "1")))
      val ic = Map(m("X") -> x, m("P") -> pfx)
      val prog = opt(Restriction(Mention(m("X")), Mention(m("P"))), Vector(m("X"), m("P")))
      val p = predict(prog, ic); val mm = measure(prog, ic)
      row("X <| one 3-prefix", d, x.nodeCount.toLong, p.forcedVirtual, mm.forcedVirtual, prevN, prevP)
      assertEquals(p.forcedVirtual, 3L, "restriction stays at the d-node frontier")
      assertEquals(mm.forcedVirtual, 3L)
      prevN = x.nodeCount.toLong; prevP = p.forcedVirtual

    // (3) Wrap over an exponentially growing source: |p|+1, independent of N(X)
    prevN = 0L; prevP = 0L
    for d <- Seq(6, 8, 10) do
      val x = trie(uniform(Nil, d, Seq("0", "1")))
      val ic = Map(m("X") -> x)
      val prog = opt(Wrap(Mention(m("X")), cpath("p1", "p2", "p3")), Vector(m("X")))
      val p = predict(prog, ic); val mm = measure(prog, ic)
      row("Wrap(X, 3 items)", d, x.nodeCount.toLong, p.forcedVirtual, mm.forcedVirtual, prevN, prevP)
      assertEquals(p.forcedVirtual, 4L); assertEquals(mm.forcedVirtual, 4L)
      prevN = x.nodeCount.toLong; prevP = p.forcedVirtual

    // (4) {ε} ∘ B over an exponentially growing B
    prevN = 0L; prevP = 0L
    for d <- Seq(5, 7, 9) do
      val b = trie(uniform(Nil, d, Seq("0", "1")))
      val ic = Map(m("A") -> ITrie.epsilon, m("B") -> b)
      val prog = opt(Composition(Mention(m("A")), Mention(m("B"))), Vector(m("A"), m("B")))
      val p = predict(prog, ic); val mm = measure(prog, ic)
      row("{ε} ∘ B", d, b.nodeCount.toLong, p.forcedVirtual, mm.forcedVirtual, prevN, prevP)
      assertEquals(p.forcedVirtual, 1L); assertEquals(mm.forcedVirtual, 1L)
      prevN = b.nodeCount.toLong; prevP = p.forcedVirtual
  }

  // ==============================================================================================
  // THE OUTER-CONSUMER CASE the review names: (A ∪ B) ∩ C stays proportional to C
  // ==============================================================================================

  test("the demanded prefix set is set by the OUTER consumer: (A ∪ B) ∩ C tracks C, not A ∪ B") {
    println("\n=== (A ∪ B) ∩ C with C ⊆ A localized and FIXED, |A| = |B| growing ===")
    println(f"  ${"depth"}%5s ${"N(A∪B)"}%10s ${"N(C)"}%6s | ${"pred forced"}%11s ${"meas forced"}%11s ${"pred entries"}%12s ${"meas entries"}%12s")
    val cAlpha = Seq("0", "1")
    var prevN = 0L; var prevP = 0L
    for d <- Seq(8, 10, 12) do
      // A and B share the localized corner "0"."0" (where C lives) and diverge elsewhere.
      val a = trie(uniform(List("0", "0"), 3, cAlpha) ++ uniform(List("1"), d, cAlpha))
      val b = trie(uniform(List("0", "0"), 3, cAlpha) ++ uniform(List("2"), d, cAlpha))
      val c = trie(uniform(List("0", "0"), 3, cAlpha))
      val ic = Map(m("A") -> a, m("B") -> b, m("C") -> c)
      val prog = opt(Intersection(Union(Mention(m("A")), Mention(m("B"))), Mention(m("C"))),
                     Vector(m("A"), m("B"), m("C")))
      val p = predict(prog, ic); val mm = measure(prog, ic)
      assertEquals(mm.result, c, "the result is C")
      val nAB = ITrie.union(a, b).nodeCount.toLong
      println(f"  $d%5d $nAB%10d ${c.nodeCount}%6d | ${p.forcedVirtual}%11d ${mm.forcedVirtual}%11d " +
              f"${p.cursorMapEntries}%12d ${mm.cursorMapEntries}%12d")
      assert(p.forcedVirtual >= mm.forcedVirtual,
             s"the demand analysis must upper-bound the run: ${p.show} vs ${mm.show}")
      assert(mm.forcedVirtual <= 4L * c.nodeCount.toLong,
             s"the run must stay proportional to C (${mm.forcedVirtual} vs N(C)=${c.nodeCount})")
      if prevN > 0 then
        val s = slope(prevP, p.forcedVirtual) / math.max(slope(prevN, nAB), 1e-9)
        println(f"       predicted-forced slope against N(A∪B) = $s%.3f")
        assert(s < 0.25, f"the PREDICTION must stay flat, not merely be contained: slope $s%.3f")
      prevN = nAB; prevP = p.forcedVirtual
  }

  // ==============================================================================================
  // SOUNDNESS — the analysis must never under-predict a real run
  // ==============================================================================================

  test("soundness: the demand analysis upper-bounds a real execZ run on random fused programs") {
    val mentions = Vector(m("a"), m("b"), m("c"))
    def randPath(r: Random) = PathValue(List.fill(1 + r.nextInt(3))(r.nextInt(3).toString))
    def randTrie(r: Random) = trie((0 to r.nextInt(6)).map(_ => randPath(r)).toSet)
    def randSpace(depth: Int, r: Random): Space =
      if depth <= 0 then r.nextInt(4) match
        case 0 => Empty
        case 1 => Singleton(Path.Constant(randPath(r)))
        case _ => Mention(mentions(r.nextInt(mentions.length)))
      else
        def sub() = randSpace(depth - 1, r)
        r.nextInt(9) match
          case 0 => Union(sub(), sub());        case 1 => Intersection(sub(), sub())
          case 2 => Subtraction(sub(), sub());  case 3 => Restriction(sub(), sub())
          case 4 => Raffination(sub(), sub());  case 5 => Composition(sub(), sub())
          case 6 => Wrap(sub(), Path.Constant(randPath(r)))
          case 7 => Unwrap(sub(), Path.Constant(randPath(r)))
          case _ => TailsUnion(sub())
    var checked = 0; var truncated = 0; var exactRows = 0; var exactAgreed = 0
    var worstForced = 1.0; var worstEntries = 1.0; var worstReads = 1.0
    for seed <- 0 until 400 do
      val r = new Random(seed.toLong * 0x9E3779B1L + 17)
      val prog = opt(randSpace(3, r), mentions)
      val ic = mentions.map(v => v -> randTrie(r)).toMap
      val p = predict(prog, ic)
      if p.truncated then truncated += 1
      else
        val mm = measure(prog, ic)
        assertEquals(mm.result, evalI(prog)(using ic = ic), s"execZ must agree with evalI, seed=$seed")
        val ctx = s"seed=$seed\n  ${prog.show}\n  pred ${p.show}\n  meas ${mm.show}\n" +
                  s"  measured events: ${mm.events.showEvents}\n  pred profile ${p.showProfile}"
        // THE COST QUANTITIES ARE UPPER BOUNDS.  (`acceptedLit` is not: an accept is GOOD news, so its
        // sound direction is the other one, and it is only claimed exactly under exact facts below.)
        assert(p.forcedVirtual >= mm.forcedVirtual, s"UNDER-PREDICTED forced nodes $ctx")
        assert(p.freshNodes >= mm.freshNodes, s"UNDER-PREDICTED fresh nodes $ctx")
        assert(p.cursorMapEntries + p.materializeEntries >= mm.cursorMapEntries + mm.materializeEntries,
               s"UNDER-PREDICTED cursor-map visits $ctx")
        assert(p.cursorReads >= mm.cursorReads, s"UNDER-PREDICTED cursor reads $ctx")
        assert(p.virtualAlloc >= mm.virtualAlloc, s"UNDER-PREDICTED virtual allocations $ctx")
        // AND WHERE THE FACTS ARE EXACT, THE ANSWER MUST BE THE MEASUREMENT — not a bound.
        if p.exact then
          exactRows += 1
          assertEquals(p.forcedVirtual, mm.forcedVirtual, s"exact facts must give the exact answer $ctx")
          assertEquals(p.acceptedLit, mm.acceptedLit, s"exact facts must give the exact accepts $ctx")
          assertEquals(p.cursorMapEntries + p.materializeEntries,
                       mm.cursorMapEntries + mm.materializeEntries, s"exact cursor-map visits $ctx")
          assertEquals(p.cursorReads, mm.cursorReads, s"exact cursor reads $ctx")
          assertEquals(p.virtualAlloc, mm.virtualAlloc, s"exact virtual allocations $ctx")
          exactAgreed += 1
        worstForced = math.max(worstForced, (p.forcedVirtual + 1.0) / (mm.forcedVirtual + 1.0))
        worstEntries = math.max(worstEntries,
          (p.cursorMapEntries + p.materializeEntries + 1.0) / (mm.cursorMapEntries + mm.materializeEntries + 1.0))
        worstReads = math.max(worstReads, (p.cursorReads + 1.0) / (mm.cursorReads + 1.0))
        checked += 1
    println(f"\n=== DEMAND SOUNDNESS: $checked random fused programs, $truncated truncated, " +
            f"$exactRows with fully exact facts (all $exactAgreed exact on every counter) ===")
    println(f"  worst slack: forced-node ${worstForced}%.2fx, cursor-map-visit ${worstEntries}%.2fx, " +
            f"cursor-read ${worstReads}%.2fx")
    assert(checked > 300, s"only $checked programs were checkable")
    assert(exactRows > 30, s"only $exactRows programs had exact facts — the exactness claim is untested")
  }

  // ==============================================================================================
  // THE DISABLED PATH — MEASURED, not asserted
  // ==============================================================================================

  test("BENCHMARK: the disarmed zipper-demand sink's cost is measured, not asserted") {
    // (a) the per-hook cost in a tight loop, with nothing to hide behind.
    val n = 100_000_000
    def bare(): Long = { var i = 0; var acc = 0L; while i < n do { acc += i; i += 1 }; acc }
    def guarded(): Long =
      var i = 0; var acc = 0L
      while i < n do { zdemand(ZipperDemandEvent.LitTransformEntry); acc += i; i += 1 }
      acc
    assertEquals(bare(), guarded())
    def best(body: => Long): Double =
      var b = Double.MaxValue
      for _ <- 0 until 5 do
        val t0 = System.nanoTime(); val r = body; val dt = (System.nanoTime() - t0).toDouble
        assert(r >= 0L); if dt < b then b = dt
      b
    val tBare = best(bare()); val tGuard = best(guarded())
    val nsPerHook = (tGuard - tBare) / n
    val hookNs = math.abs(nsPerHook)
    println(f"\n=== ZIPPER DEMAND SINK, disarmed ===")
    println(f"  per-hook cost in a tight loop: ${nsPerHook}%+.4f ns/hook (bare ${tBare / 1e6}%.1f ms vs " +
            f"guarded ${tGuard / 1e6}%.1f ms over $n iterations)" +
            (if nsPerHook < 0 then " — negative, i.e. below the measurement floor" else ""))
    assert(hookNs < 1.0, f"a disarmed hook must be far under 1 ns; measured ${nsPerHook}%.4f ns")

    // (b) executor level: a fused zipper workload that forces real cursor-map work, disarmed vs armed,
    //     with the hook count of the workload in hand — an accounting, not a hope.
    val a = trie(uniform(Nil, 8, Seq("0", "1", "2")))
    val b = trie(uniform(Nil, 8, Seq("0", "1")))
    val ic = Map(m("A") -> a, m("B") -> b)
    val prog = Union(Intersection(Mention(m("A")), Mention(m("B"))), Subtraction(Mention(m("A")), Mention(m("B"))))
    def runN(k: Int): Unit = { var i = 0; while i < k do { execZ(prog)(using ic = ic); i += 1 } }
    runN(40)
    def bestMs(body: => Unit): Double =
      var bb = Double.MaxValue
      for _ <- 0 until 5 do
        val t0 = System.nanoTime(); body; val dt = (System.nanoTime() - t0) / 1e6
        if dt < bb then bb = dt
      bb
    val off = bestMs(runN(40))
    val on = bestMs(ZipperDemandSink.count(runN(40)))
    val zc = ZipperDemandSink.counts(execZ(prog)(using ic = ic))
    val hooksPerRun = zc.cursorMapEntries + zc.materializeEntries + zc.acceptedLit +
                      zc.counts.getOrElse(ZipperDemandEvent.VirtualCursorAlloc, 0L)
    val accountedMs = hooksPerRun * 40.0 * hookNs / 1e6
    val sharePct = 100.0 * accountedMs / off
    println(f"  execZ x40 disarmed ${off}%.2f ms, armed ${on}%.2f ms (armed/disarmed ${on / off}%.2fx); " +
            f"$hooksPerRun hooks per run")
    println(f"  ACCOUNTED disarmed overhead = $hooksPerRun hooks x 40 x ${hookNs}%.4f ns = " +
            f"${accountedMs}%.3f ms of ${off}%.2f ms measured = ${sharePct}%.2f%% of the workload")
    println(f"  events: ${zc.showEvents}")
    assert(sharePct < 5.0, f"disarmed hooks account for ${sharePct}%.2f%% of the fused zipper hot path")
    assert(on < off * 20.0, f"counting is too expensive to use as an oracle: ${on / off}%.1fx")
  }

  // ==============================================================================================
  // THE CORRECTIONS THIS FILE'S ANALYSIS RESTS ON — asserted against the executor, not just claimed
  // ==============================================================================================

  test("the two false Zipper.scala claims, refuted by measurement") {
    println("\n=== the corrected comments, as executable statements ===")
    // (1) `materialize` does NOT visit every logical result node once: a `Lit` result returns an
    //     arbitrarily large trie without visiting it.
    val x = trie(uniform(Nil, 9, Seq("0", "1")))
    val ic = Map(m("X") -> x)
    val idn = opt(Union(Mention(m("X")), Mention(m("X"))), Vector(m("X")))
    val mm = measure(idn, ic)
    println(f"  X ∪ X over an N=${x.nodeCount}-node trie: forcedVirtual=${mm.forcedVirtual}, " +
            f"acceptedLit=${mm.acceptedLit}, result nodes=${mm.result.nodeCount}")
    assertEquals(mm.result, x)
    assertEquals(mm.forcedVirtual, 0L, "a Lit result visits NO node of the result")
    assert(mm.result.nodeCount > 500, "and the result is arbitrarily large")

    // (2) cursor movement is NOT constant time: one `children` call transforms an ENTIRE IntMap, and
    //     the entry count grows with the focus node's branching.
    println(f"  ${"root arity"}%11s ${"cursorMapEntries for one forced union node"}%44s")
    var prev = 0L
    for k <- Seq(4, 8, 16) do
      val wide = trie((0 until k).map(i => PathValue(List("h" + i, "z"))).toSet)
      val other = trie((0 until k).map(i => PathValue(List("g" + i, "z"))).toSet)
      val ic2 = Map(m("A") -> wide, m("B") -> other)
      val prog = opt(Union(Mention(m("A")), Mention(m("B"))), Vector(m("A"), m("B")))
      val z = measure(prog, ic2)
      println(f"  $k%11d ${z.cursorMapEntries}%44d")
      assert(z.cursorMapEntries > prev, "the per-children cost GROWS with the focus branching")
      assertEquals(z.forcedVirtual, 1L, "while the forced-node count stays 1")
      prev = z.cursorMapEntries
  }
end SpatialDemandCheck
