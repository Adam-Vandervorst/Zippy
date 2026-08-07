package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** THE COST ALGEBRA — review.md finding 3.
 *
 *  What these tests establish, and what they do not:
 *
 *   - the algebra's normalisation, idempotence and order are CHECKED (unit + numeric property);
 *   - `dominates` is checked NUMERICALLY against [[Sym.evalAt]] on random valuations — that is
 *     evidence for the sufficient condition, not a proof of it;
 *   - the per-operator transfer constants are a MODEL of the two interpreters read off their code.
 *     No test can validate a modelling choice; what is tested is that the model is compositional,
 *     monotone, and that the two backends genuinely disagree where they should;
 *   - the runtime check is a WEAK rank-correlation sanity check against measured `eval` time, not a
 *     calibration.  `eval` is only ever used as ground truth in tests, never by the analysis. */
class SpatialCostCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
  def p(items: String*): PathValue = PathValue(items.toList)
  /** k distinct one-item paths */
  def litN(k: Int, pre: String = "i"): Space = Space.Literal(SpaceValue((0 until k).map(i => p(pre + i)).toSet))
  /** iterate and return the group head — the review's own head-count observation */
  def headsOf(s: Space): Space =
    Space.Iteration(s, PathRef("h").known(1), SpaceMention("_"), Space.Singleton(Path.Deref(PathRef("h").known(1))))

  val N: Sym = Sym.v("N"); val M: Sym = Sym.v("M")
  val chain: Vector[Sym] = Vector(Sym.one, Sym.log(N), N, N * Sym.log(N), N ** Sym.c(2), Sym.c(2) ** N)

  /** a pool of expressions used by the numeric property tests */
  val pool: Vector[Sym] = Vector(
    Sym.zero, Sym.one, Sym.c(7), N, M, N + M, N * M, N + Sym.c(3), Sym.c(2) * N,
    Sym.log(N), N * Sym.log(N), N ** Sym.c(2), N ** Sym.c(3), M * (N ** Sym.c(2)),
    Sym.c(2) ** N, Sym.c(3) ** N, Sym.maxOf(N, M), Sym.maxOf(N, N ** Sym.c(2)),
    N * Sym.log(M) + Sym.c(5), (N + M) ** Sym.c(2), Sym.log(Sym.log(N)))

  // ==============================================================================================
  // 1. THE ALGEBRA
  // ==============================================================================================

  test("normalisation folds constants and collects like terms") {
    assertEquals((N + N + Sym.c(3) + Sym.c(4)).show, "2*N + 7")
    assertEquals((N * N).show, "N^2")
    assertEquals((N * (M + Sym.c(1))).show, "M*N + N")
    assertEquals((Sym.c(2) * Sym.c(3)).show, "6")
    assertEquals(Sym.log(Sym.c(8)).show, "3", "log is base 2 and folds on constants (ceil)")
    assertEquals((N * Sym.zero).show, "0")
    assertEquals((Sym.Inf * Sym.zero).show, "0", "doing an unbounded-cost thing zero times is free")
    assertEquals((N + Sym.Inf).show, "inf")
    assertEquals((N ** Sym.c(0)).show, "1")
    assertEquals((N ** Sym.c(1)).show, "N")
    // a Max collapses when one alternative dominates the other
    assertEquals(Sym.maxOf(N, Sym.c(2) * N).show, "2*N")
    assertEquals(Sym.maxOf(N, M).show, "max(M, N)")
    // large exponents survive without being expanded (and stay canonical)
    assertEquals((N ** Sym.c(40)).show, "N^40")
  }

  test("normalisation is idempotent, and equal quantities have equal normal forms") {
    for e <- pool do
      val n1 = Sym.normalize(e)
      assertEquals(Sym.normalize(n1), n1, s"not idempotent: ${e.show}")
    // two spellings of the same quantity
    assertEquals(Sym.normalize((N + M) * (N + M)), Sym.normalize(N * N + Sym.c(2) * N * M + M * M))
    assertEquals(Sym.normalize(N * (M + Sym.one)), Sym.normalize(N * M + N))
  }

  test("N, log N, N log N, N^2 and 2^N are ORDERED and DISTINCT (not all INF)") {
    val os = chain.map(Sym.bigO)
    for i <- 0 until os.length - 1 do
      assert(os(i) < os(i + 1), s"${chain(i).show} (${os(i).show}) must be strictly below ${chain(i + 1).show} (${os(i + 1).show})")
    assertEquals(os.distinct.length, os.length, "the order classes must be distinct")
    assertEquals(chain.map(Sym.normalize).distinct.length, chain.length, "the normal forms must be distinct")
    assertEquals(os.map(_.show), Vector("1", "log n", "n", "n log n", "n^2", "2^n"))
    // and none of them is the saturated top
    assert(os.forall(_ != BigO.inf), "no member of the chain may collapse to inf")
    assertEquals(Sym.bigO(Sym.Inf), BigO.inf)
    assertEquals(Sym.bigO(Sym.zero), BigO.zero)
    assert(BigO.zero < BigO.const && BigO.const < BigO.inf)
  }

  test("dominates: the cases it must get right") {
    assert(Sym.dominates(N ** Sym.c(2), N))
    assert(Sym.dominates(N ** Sym.c(2), N * Sym.log(N)), "log x <= x on the domain (x >= 2)")
    assert(Sym.dominates(N * Sym.log(N), N))
    assert(Sym.dominates(N, Sym.log(N)))
    assert(Sym.dominates(Sym.c(2) * N, N))
    assert(Sym.dominates(N + M, N))
    assert(Sym.dominates(Sym.Inf, Sym.c(2) ** N))
    assert(Sym.dominates(Sym.maxOf(N, M), N))
    assert(Sym.dominates(N, Sym.zero))
    // and the ones it must NOT claim
    assert(!Sym.dominates(N, N * Sym.log(N)))
    assert(!Sym.dominates(N * Sym.log(N), N ** Sym.c(2)))
    assert(!Sym.dominates(N, M))
    assert(!Sym.dominates(N ** Sym.c(2), Sym.c(2) ** N))
    assert(!Sym.dominates(Sym.c(2) ** N, Sym.Inf))
    // INCOMPLETENESS, recorded honestly: 2^N >= N holds pointwise but is not derived here
    assert(!Sym.dominates(Sym.c(2) ** N, N), "known incompleteness: no exponential-vs-polynomial rule")
  }

  test("dominates is SOUND against numeric evaluation (random valuations, vars >= 2)") {
    val rng = new java.util.Random(9001)
    var checkedPairs = 0; var checkedPoints = 0
    for a <- pool; b <- pool if Sym.dominates(a, b) do
      checkedPairs += 1
      val names = (Sym.vars(a) ++ Sym.vars(b)).toVector
      for _ <- 0 until 60 do
        val v = names.map(n => n -> (2.0 + rng.nextDouble() * 60.0)).toMap
        val (x, y) = (Sym.evalAt(a, v), Sym.evalAt(b, v))
        assert(x >= y - 1e-9 * (1.0 + math.abs(y)),
               s"dominates(${a.show}, ${b.show}) but $x < $y at $v")
        checkedPoints += 1
    assert(checkedPairs > 40, s"too few dominating pairs exercised ($checkedPairs)")
    println(s"COST: dominates checked on $checkedPairs pairs x 60 valuations = $checkedPoints points")
  }

  test("bigO is monotone under dominates (checked on the pool)") {
    for a <- pool; b <- pool if Sym.dominates(a, b) do
      assert(Sym.bigO(a) >= Sym.bigO(b), s"dominates(${a.show}, ${b.show}) but bigO ${Sym.bigO(a).show} < ${Sym.bigO(b).show}")
  }

  test("tighter picks a sound upper bound, and prefers the declared constant") {
    assertEquals(Sym.tighter(Sym.c(4), N).show, "4")
    assertEquals(Sym.tighter(N, Sym.Inf).show, "N")
    assertEquals(Sym.tighter(N ** Sym.c(2), N).show, "N")
    // tighter always returns ONE of its arguments (so it can never invent an unsound bound)
    for a <- pool; b <- pool do
      val t = Sym.tighter(a, b)
      assert(t == Sym.normalize(a) || t == Sym.normalize(b), s"tighter(${a.show}, ${b.show}) = ${t.show}")
  }

  // ==============================================================================================
  // 2. PER-OPERATOR COST TRANSFERS
  // ==============================================================================================

  private def work(r: SpatialCost.Report): Sym = r.cost.work.symOpt.getOrElse(Sym.Inf)
  private def alloc(r: SpatialCost.Report): Sym = r.cost.alloc.symOpt.getOrElse(Sym.Inf)
  private def rounds(r: SpatialCost.Report): Sym = r.cost.rounds.symOpt.getOrElse(Sym.Inf)
  private def touch(r: SpatialCost.Report): Sym = r.cost.touch.symOpt.getOrElse(Sym.Inf)

  // NOTE ON COMPONENT MEANINGS (changed by the calibration work, review.md finding 2, then item 1).
  //   ALL FOUR components are now DEFINED BY COUNTED EVENTS, so a claim about any of them is a claim
  //   about `Events.work`/`.alloc`/`.rounds`/`.touch` that `SpatialEventsCheck` measures and GATES.
  //   A `Set` union is ONE AstDispatch and ZERO PathValue allocations, however large its operands: the
  //   |a|+|b| element cost lives in `touch`.  For the TRIE-SHAPED backends `touch` is the counted
  //   per-node descent inside the trie algebra (TrieNodeVisit + PatriciaVisit).  For the REFERENCE
  //   backend alone it has no oracle — `eval` does that work inside `Set`, which carries no hooks — so
  //   `ReferenceCost.touchNoOracle` declares it and the rank-correlation test at the end of this file
  //   is the only (secondary) evidence for it.
  test("reference-backend transfers: the shape of each operator's cost") {
    def setO(s: Space) = SpatialCost.analyze(s, SetCost).cost
    // a union is a linear scan of both operands, but the scan happens inside `Set` — so it is a
    // `touch` claim, and the evaluator's own counted work for it is constant
    assertEquals(setO(Space.Union(S"s0", S"s1")).touch.bigO, BigO(0, 1, 0))
    assertEquals(setO(Space.Union(S"s0", S"s1")).work.bigO, BigO.const, "3 AstDispatches, whatever |s0|,|s1| are")
    assertEquals(setO(Space.Union(S"s0", S"s1")).alloc, Amount.Bounded(Sym.zero), "no PathValue is built")
    // a composition builds |a|.|b| FRESH PathValues — that IS counted, as FreshPath
    assertEquals(setO(Space.Composition(S"s0", S"s1")).alloc.bigO, BigO(0, 2, 0))
    assertEquals(setO(Space.Composition(S"s0", S"s1")).touch.bigO, BigO(0, 3, 0), "|a|.|b| concats of length |a|+|b|")
    // a Restriction in `eval` is a NESTED startsWith scan, and every item comparison IS counted
    assertEquals(setO(Space.Restriction(S"s0", S"s1")).work.bigO, BigO(0, 3, 0))
    // `Range` in `eval` is `.toVector.sorted.slice` — a comparison sort through `pathValueOrdering`,
    // which is instrumented, so the log factor lands in the COUNTED component
    assert(setO(Space.Range(S"s0", 0, 3)).work.bigO.logs >= 1, "a set Range must pay for a sort")
    // an Unwrap rebuilds the whole set
    assertEquals(setO(Space.Unwrap(S"s0", "a")).alloc.bigO, BigO(0, 1, 0))
    // and an empty operand costs nothing downstream
    assertEquals(setO(Space.Composition(Space.Empty, S"s1")).touch, Amount.Bounded(Sym.zero))
  }

  test("trie-backend transfers: skipping and sharing show up as different cost") {
    def trieO(s: Space) = SpatialCost.analyze(s, TrieCost).cost
    // an Unwrap descends |p| levels and hands back the SHARED subtrie: no allocation at all
    assertEquals(trieO(Space.Unwrap(S"s0", "a")).alloc, Amount.Bounded(Sym.zero))
    assertEquals(trieO(Space.Wrap(S"s0", "a.b")).alloc, Amount.Bounded(Sym.c(2)), "a 2-node spine over a shared child")
    // ATTRIBUTION FIX (review.md 2, third bullet): the old model claimed the trie `Range` needs "NO
    // SORT".  `ITrie.range` sorts every visited node's child keys by their UN-INTERNED item, so the
    // log factor is real and must appear.  It also computes the recursive `t.size` first.
    assert(trieO(Space.Range(S"s0", 0, 3)).touch.bigO.logs >= 1,
           s"ITrie.range sorts child keys per visited node: ${trieO(Space.Range(S"s0", 0, 3)).show}")
    // restriction descends the prefix trie once instead of scanning pairs: the win is in COMPARISONS
    // (`work`), which is exactly the component `Effort.startsWith` counts for the reference evaluator
    assert(trieO(Space.Restriction(S"s0", S"s1")).work.bigO <
             SpatialCost.analyze(Space.Restriction(S"s0", S"s1"), SetCost).cost.work.bigO)
  }

  test("the SAME facts give the two backends DIFFERENT costs") {
    val cases: Vector[(String, Space)] = Vector(
      "unwrap"      -> Space.Unwrap(S"s0", "a"),
      "wrap"        -> Space.Wrap(S"s0", "a"),
      "range"       -> Space.Range(S"s0", 0, 3),
      "restriction" -> Space.Restriction(S"s0", S"s1"),
      "composition" -> Space.Composition(S"s0", S"s1"),
      "union"       -> Space.Union(S"s0", S"s1"))
    var differing = 0
    for (nm, s) <- cases do
      val (a, b) = SpatialCost.compare(s)
      if a.cost != b.cost then differing += 1
      println(f"COST: $nm%-12s set[${a.cost.showO}]  trie[${b.cost.showO}]")
    assertEquals(differing, cases.length, "every one of these must be priced differently by the two backends")
    // A HEAD-DISJOINT intersection: the trie stops at the head level, the set evaluator cannot.
    //
    // WHY THE HEAD SETS AND NOT THE RESULT (a correction the event calibration forced).  The model used
    // to take "the intersection is PROVABLY EMPTY" as licence to charge one head comparison and ZERO
    // allocations.  Measurement refuted it: `ITrie.intersection`'s empty guard fires on an empty
    // OPERAND, not an empty RESULT, so operands that share HEADS but no full path still descend every
    // shared prefix — 12 counted fresh nodes against a predicted 1, three times over on the corpus.
    // What the executor actually rewards is DISJOINT HEAD SETS, so that is what the model now asks for.
    //
    // The fibers are deliberately FAT (2 heads x 30 tails): the trie's win is that its cost is in the
    // HEAD count while the set evaluator's is in the PATH count, and a 6-path example is too small to
    // show it — at 2 heads x 3 tails the two are within one unit of each other.
    val heads = Vector("a", "b"); val other = Vector("c", "d")
    val av = SpaceValue(heads.flatMap(h => (0 until 30).map(i => p(h, "x" + i))).toSet)
    val bv = SpaceValue(other.flatMap(h => (0 until 30).map(i => p(h, "x" + i))).toSet)
    val (ma, mb) = (SpaceMention("A"), SpaceMention("B"))
    val env = SpatialCost.Env(facts = SpatialTyping.Env(spaces = Map(ma -> SpatialType.of(av), mb -> SpatialType.of(bv))))
    val (ds, dt) = SpatialCost.compare(Space.Intersection(Space.Mention(ma), Space.Mention(mb)), env)
    assertEquals(touch(ds).show, "120", "a set intersection touches all 60+60 paths")
    // The trie compares 2+2 HEADS and stops — and `touch` is now a COUNTED component
    // (EffortEvent.TrieNodeVisit + PatriciaVisit), so the claim is what a run can produce: one
    // ITrie-level entry plus the top Patricia descent over the two head sets, at most 2(m+n) visits.
    assertEquals(touch(dt).show, "13", "1 entry + 3(2+2) for the head-set Patricia descent")
    // and it allocates exactly the ONE root node it builds before discovering the result is empty
    assertEquals(alloc(dt).show, "1", "the merged root node, and nothing below it")
    assert(Sym.dominates(touch(ds), touch(dt)), s"${ds.show}\n${dt.show}")
    // ground truth: the intersection really is empty (eval as ORACLE, never inside the analysis)
    assertEquals(eval(Space.Intersection(Space.Literal(av), Space.Literal(bv))), SpaceValue(Set.empty))
    // an OVERLAPPING intersection gets no skip.  `Mention(A) ∩ Mention(A)` is the SAME trie object,
    // so `ITrie.intersection`'s `a eq b` fires and the trie really is O(1) there — a different fast
    // path from the disjointness skip, and one the reference `Set` evaluator does not have.
    val (os, ot) = SpatialCost.compare(Space.Intersection(Space.Mention(ma), Space.Mention(mb)),
                                       env.copy(shapeFacts = false))
    // 60 paths x 2 items, PLUS the always-present root node (Meas.nodes = 1 + size*len)
    assertEquals(alloc(ot).show, "121", s"no shape tier, no skip: ${ot.show}")
    val (_, selfT) = SpatialCost.compare(Space.Intersection(Space.Mention(ma), Space.Mention(ma)), env)
    assertEquals(alloc(selfT).show, "0", s"x ∩ x is a pointer-identity accept: ${selfT.show}")
    // dropping the shape tier removes the skip: the cost RISES, and the report says why
    val noShape = SpatialCost.analyze(Space.Intersection(Space.Mention(ma), Space.Mention(mb)),
                                      env.copy(shapeFacts = false), TrieCost)
    assert(Sym.dominates(touch(noShape), touch(dt)), s"without the shape the trie must not be cheaper: ${noShape.show}")
    assert(dt.assumptions.exists(_.contains("SpatialShapeCheck")), "a shape-derived skip must be flagged")
    assert(noShape.assumptions.forall(!_.contains("SpatialShapeCheck")))
  }

  test("the model is NOT rigged: each backend wins somewhere") {
    // compared on the WHOLE cost vector's order class (the max over all four components), which is
    // the honest "which executable is asymptotically cheaper here"
    def cheaper(s: Space): String =
      val (a, b) = SpatialCost.compare(s)
      if a.cost.bigO < b.cost.bigO then "set"
      else if b.cost.bigO < a.cost.bigO then "trie" else "tie"
    // a focus, an ordered slice and a prefix descent favour the trie
    assertEquals(cheaper(Space.Unwrap(S"s0", "a")), "trie")
    assertEquals(cheaper(Space.Restriction(S"s0", S"s1")), "trie")
    // a flat set union favours the hash set: a trie merge walks nodes, not paths
    assertEquals(cheaper(Space.Union(S"s0", S"s1")), "set")
    assertEquals(cheaper(Space.TailsUnion(S"s0")), "set")
    // and the reference backend now WINS a full-window Range, because `sliceRange` returns its input
    // while `ITrie.range` still walks every node to compute `t.size` (review.md 2, bullets 2 and 3)
    assertEquals(cheaper(Space.Range(S"s0", 0, 0)), "set")
  }

  // ==============================================================================================
  // 3. LOOPS AND RECURRENCES
  // ==============================================================================================

  test("an iteration's work is (head-groups) x (body work) — the review's own example") {
    val a = lit(p("a", "0"), p("a", "1"), p("a", "2"), p("a", "3"))   // ONE head
    val b = lit(p("a", "0"), p("b", "0"), p("c", "0"), p("d", "0"))   // FOUR heads
    // the length histogram cannot tell these apart at all
    assertEquals(SpatialTypes.infer(a).show, SpatialTypes.infer(b).show)
    val (ra, rb) = (SpatialCost.analyze(headsOf(a), SetCost), SpatialCost.analyze(headsOf(b), SetCost))
    assertEquals(rounds(ra).show, "1", s"A runs one body frame: ${ra.show}")
    assertEquals(rounds(rb).show, "4", s"B runs four body frames: ${rb.show}")
    assert(Sym.dominates(work(rb), work(ra)), "four frames cannot cost less than one")
    // ground truth
    assertEquals(eval(headsOf(a)).paths.size, 1)
    assertEquals(eval(headsOf(b)).paths.size, 4)
    // THE POINT of separating work from rounds.  With a body that squares the rest-set, the source
    // with FEWER, FATTER groups costs MORE work while running FEWER frames — so `rounds` and `work`
    // move in opposite directions on two sources the histogram calls identical.  A single "cost"
    // scalar, and any cardinality bound, cannot express that.
    val heavy = (x: Space) => Space.Iteration(x, PathRef("h").known(1), SpaceMention("t"),
                                              Space.Composition(S"t", S"t"))
    val (ha, hb) = (SpatialCost.analyze(heavy(a), SetCost), SpatialCost.analyze(heavy(b), SetCost))
    assertEquals(rounds(ha).show, "1"); assertEquals(rounds(hb).show, "4")
    // the fat-group source ALLOCATES more (16 fresh concatenated paths against 4), which is the
    // counted `FreshPath` component, and touches more elements
    assert(Sym.dominates(alloc(ha), alloc(hb)) && alloc(ha) != alloc(hb),
           s"one group over 4 tails squares to 16 concats; four groups over 1 tail each to 4:\n${ha.show}\n${hb.show}")
    assert(Sym.dominates(touch(ha), touch(hb)) && touch(ha) != touch(hb), s"${ha.show}\n${hb.show}")
    // ground truth for that direction
    assertEquals(eval(heavy(a)).paths.size, 16)
    assertEquals(eval(heavy(b)).paths.size, 1)
    // a symbolic source gives a symbolic group count, not INF
    val sym = SpatialCost.analyze(headsOf(S"s0"), SetCost)
    assertEquals(rounds(sym).show, "|s0|")
    assert(rounds(sym) != Sym.Inf)
  }

  test("nested iterations accumulate rounds, and an unrunnable loop costs zero rounds") {
    val src = lit(p("a", "x"), p("a", "y"), p("b", "x"), p("b", "y"))
    val nested = Space.Iteration(src, PathRef("h").known(1), SpaceMention("t"),
                   Space.Iteration(S"t", PathRef("g").known(1), SpaceMention("_"),
                     Space.Singleton(Path.Deref(PathRef("g").known(1)))))
    val flat = headsOf(src)
    val (rn, rf) = (SpatialCost.analyze(nested, SetCost), SpatialCost.analyze(flat, SetCost))
    assert(Sym.dominates(rounds(rn), rounds(rf)) && rounds(rn) != rounds(rf),
           s"nested must run strictly more frames: ${rounds(rn).show} vs ${rounds(rf).show}")
    println(s"COST: nested rounds=${rounds(rn).show}  flat rounds=${rounds(rf).show}")
    // an ε-only source has no head-group at all
    val eps = SpatialCost.analyze(headsOf(lit(p())), SetCost)
    assertEquals(rounds(eps), Sym.zero, s"an ε-only source runs no body frame: ${eps.show}")
    assertEquals(eval(headsOf(lit(p()))), SpaceValue(Set.empty))
  }

  test("fixpoint rounds: bounded by the result when monotone, an explicit free variable otherwise") {
    val r = SpaceMention("r")
    val mono = Space.Fixpoint(lit(p("a")), r, Space.Union(Space.Mention(r), lit(p("b"))))
    val rm = SpatialCost.analyze(mono, SetCost)
    assert(rm.assumptions.exists(_.contains("monotone accumulator, so rounds")), rm.show)
    assert(Sym.vars(rounds(rm)).contains("|fix:r|"), s"rounds must be tied to the result size: ${rounds(rm).show}")
    assert(rounds(rm) != Sym.Inf, "never saturate")
    assertEquals(eval(mono).paths.size, 2)

    val nonmono = Space.Fixpoint(lit(p("a", "b", "c")), r, Space.TailsUnion(Space.Mention(r)))
    val rn = SpatialCost.analyze(nonmono, SetCost)
    assert(rn.assumptions.exists(_.contains("no round bound is derivable")), rn.show)
    assert(Sym.vars(rounds(rn)).exists(_.startsWith("R")), s"a fresh symbolic round variable: ${rounds(rn).show}")
    assert(!rn.cost.work.isUnbounded, "the cost stays parametric in the unknown, it does not saturate")
    // and the body work really is multiplied by the round count
    assert(Sym.vars(work(rn)).exists(_.startsWith("R")), work(rn).show)
  }

  test("linear recurrences get closed forms, never a silent saturation") {
    import Recurrence.*
    assertEquals(solve(Linear(Sym.c(5), Sym.c(0), Sym.c(10))), Amount.Bounded(Sym.c(5)))
    assertEquals(solve(Linear(Sym.c(5), Sym.c(1), Sym.c(10))), Amount.Bounded(Sym.c(50)))
    assertEquals(solve(Linear(Sym.c(5), Sym.c(1), N)), Amount.Bounded(Sym.c(5) * N))
    assertEquals(solve(Linear(Sym.c(5), Sym.c(2), N)).show, "5*2^N")
    assertEquals(Sym.bigO(solve(Linear(Sym.c(5), Sym.c(2), N)).symOpt.get), BigO(1, 0, 0), "b=2 is exponential in n")
    assertEquals(Sym.bigO(solve(Linear(Sym.c(5), Sym.c(1), N)).symOpt.get), BigO(0, 1, 0), "b=1 is linear in n")
    // a symbolic branching factor may be 1, so the sound envelope keeps the extra factor n
    assertEquals(solve(Linear(Sym.c(5), Sym.v("B"), Sym.c(4))).show, "20*B^4")
    assertEquals(solve(Linear(Sym.c(5), Sym.c(2), Sym.Inf)), Amount.Unbounded("recursion depth is unbounded"))
    assertEquals(solve(Linear(Sym.c(5), Sym.Inf, Sym.c(3))), Amount.Unbounded("recursive branching factor is unbounded"))
    // numeric check of the closed form against the actual recurrence, T(0)=0
    for a <- Vector(1L, 3L, 7L); b <- Vector(1L, 2L, 3L); n <- Vector(1, 2, 3, 6, 9) do
      var t = 0.0
      for _ <- 0 until n do t = a + b * t
      val closed = Sym.evalAt(solve(Linear(Sym.c(a), Sym.c(b), Sym.c(n.toLong))).symOpt.get, Map.empty)
      assert(closed >= t - 1e-9, s"closed form $closed < actual $t for a=$a b=$b n=$n")
    // and the split that drives it
    assertEquals(Sym.splitLinear(Sym.c(3) + Sym.c(2) * Sym.v("T"), "T"), Some((Sym.c(3), Sym.c(2))))
    assertEquals(Sym.splitLinear(N * Sym.v("T") + M, "T"), Some((M, N)))
    assertEquals(Sym.splitLinear(Sym.v("T") * Sym.v("T"), "T"), None, "degree 2 in T is not a linear recurrence")
    assertEquals(Sym.splitLinear(Sym.log(Sym.v("T")), "T"), None, "T inside an opaque atom is not linear")
    assertEquals(Recurrence.close(Amount.of(Sym.c(3) + Sym.c(2) * Sym.v("T")), "T", Sym.c(5)).show, "96")
    assertEquals(Recurrence.close(Amount.of(Sym.v("T") * Sym.v("T")), "T", Sym.c(5)),
                 Amount.Unbounded("non-linear recurrence in T"))
  }

  test("a routine that drops an item per call gets a DEPTH BOUND and a closed cost") {
    val rp = RoutinePtr("f"); val xs = SpaceMention("xs")
    // f(xs) = xs \/ f(tails(xs)) — the union-recursive shape eval's self-call detection terminates
    val body = Space.Union(Space.Mention(xs), Space.Call(rp, Vector.empty, Vector(Space.TailsUnion(Space.Mention(xs)))))
    val rt = Routine(rp, Vector.empty, Vector(xs), body)
    val rc: PartialFunction[RoutinePtr, Routine] = { case r if r == rp => rt }
    assertEquals(Recurrence.decreasingArg(body, rp, Vector(xs)), Some(0))
    assert(Recurrence.selfTerminating(body, rp))
    assertEquals(Recurrence.depthBound(3).show, "5")
    assertEquals(Recurrence.depthBound(Lower.LenBounds.INF), Sym.Inf)

    val arg = lit(p("a", "b", "c"), p("d", "e", "f"))                 // maximum path length 3
    val prog = Space.Call(rp, Vector.empty, Vector(arg))
    val rep = SpatialCost.analyze(prog, SpatialCost.Env().withRoutines(rc), SetCost)
    assert(!rep.cost.work.isUnbounded, s"the recursion must be closed: ${rep.show}")
    assertEquals(rounds(rep).show, "5", s"depth = maxlen(3) + 2: ${rep.show}")
    assert(rep.assumptions.exists(_.contains("depth bound 5 from maxlen(arg 0) = 3")), rep.show)
    // ground truth: eval really does terminate and produce every suffix
    assertEquals(eval(prog)(using rc = rc).paths.size, 7)
    // a longer argument costs strictly more
    val long = Space.Call(rp, Vector.empty, Vector(lit(p("a", "b", "c", "d", "e"))))
    val repL = SpatialCost.analyze(long, SpatialCost.Env().withRoutines(rc), SetCost)
    assertEquals(rounds(repL).show, "7")
    assert(Sym.dominates(rounds(repL), rounds(rep)))

    // NO decreasing measure -> an explicit Unbounded with a reason, not a bogus number
    val body2 = Space.Union(Space.Mention(xs), Space.Call(rp, Vector.empty, Vector(Space.Mention(xs))))
    val rc2: PartialFunction[RoutinePtr, Routine] = { case r if r == rp => Routine(rp, Vector.empty, Vector(xs), body2) }
    val rep2 = SpatialCost.analyze(Space.Call(rp, Vector.empty, Vector(lit(p("a")))),
                                   SpatialCost.Env().withRoutines(rc2), SetCost)
    assert(rep2.cost.work.isUnbounded, rep2.show)
    assert(rep2.cost.work.show.contains("without a decreasing measure"), rep2.cost.work.show)
    // an UNBOUNDED argument length also refuses to invent a bound
    val rep3 = SpatialCost.analyze(Space.Call(rp, Vector.empty, Vector(S"s0")),
                                   SpatialCost.Env().withRoutines(rc), SetCost)
    assert(rep3.cost.work.isUnbounded, rep3.show)
    assert(rep3.assumptions.exists(_.contains("maximum path length")), rep3.show)
    // a non-self-terminating body gets the bound but MUST flag the assumption
    val body4 = Space.Intersection(Space.Mention(xs), Space.Call(rp, Vector.empty, Vector(Space.TailsUnion(Space.Mention(xs)))))
    val rc4: PartialFunction[RoutinePtr, Routine] = { case r if r == rp => Routine(rp, Vector.empty, Vector(xs), body4) }
    val rep4 = SpatialCost.analyze(Space.Call(rp, Vector.empty, Vector(arg)), SpatialCost.Env().withRoutines(rc4), SetCost)
    assert(rep4.assumptions.exists(_.contains("termination is ASSUMED, not derived")), rep4.show)
  }

  // ==============================================================================================
  // 4. MONOTONICITY
  // ==============================================================================================

  test("MONOTONICITY: bigger inputs never give a smaller cost (symbolic valuations)") {
    val progs: Vector[Space] = Vector(
      Space.Composition(S"s0", S"s1"),
      Space.Restriction(S"s0", S"s1"),
      Space.Union(Space.Unwrap(S"s0", "a"), Space.Wrap(S"s1", "b")),
      Space.Range(Space.Composition(S"s0", S"s1"), 0, 4),
      headsOf(S"s0"),
      Space.Iteration(S"s0", PathRef("h").known(1), SpaceMention("t"), Space.Composition(S"t", S"s1")),
      Space.Fold(S"s0", "z", PathRef("a"), PathRef("h").known(1), SpaceMention("t"), S"t", Path.Deref(PathRef("h").known(1))),
      Space.Fixpoint(S"s0", SpaceMention("r"), Space.Union(Space.Mention(SpaceMention("r")), Space.TailsUnion(Space.Mention(SpaceMention("r"))))))
    var checked = 0
    for prog <- progs; model <- Vector[CostModel](SetCost, TrieCost) do
      val c = SpatialCost.analyze(prog, model).cost
      for comp <- Vector(c.work, c.alloc, c.rounds); e <- comp.symOpt do
        val names = Sym.vars(e).toVector
        var prev = Double.NegativeInfinity
        for k <- Vector(2.0, 3.0, 5.0, 9.0, 17.0, 33.0, 65.0) do
          val cur = Sym.evalAt(e, names.map(_ -> k).toMap)
          assert(cur >= prev - 1e-9, s"cost DECREASED from $prev to $cur at $k for ${e.show} (${model.name}, ${prog.show.take(60)})")
          prev = cur
        checked += 1
    println(s"COST: monotonicity checked on $checked cost components")
  }

  test("MONOTONICITY: a bigger DECLARED input type never gives a smaller cost") {
    val m = SpaceMention("s")
    def costAt(n: Long, prog: Space, model: CostModel): Cost =
      val t = SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(n, n)))
      SpatialCost.analyze(prog, SpatialCost.Env(facts = SpatialTyping.Env(spaces = Map(m -> t))), model).cost
    val progs = Vector[Space](
      Space.Composition(Space.Mention(m), Space.Mention(m)),
      Space.Range(Space.Mention(m), 0, 3),
      headsOf(Space.Mention(m)),
      Space.Restriction(Space.Mention(m), Space.Mention(m)))
    for prog <- progs; model <- Vector[CostModel](SetCost, TrieCost) do
      val sizes = Vector(2L, 4L, 8L, 16L, 64L, 256L)
      val ws = sizes.map(n => costAt(n, prog, model)).map(c => c.work.symOpt.map(Sym.evalAt(_, Map.empty)).getOrElse(Double.PositiveInfinity))
      for i <- 0 until ws.length - 1 do
        assert(ws(i) <= ws(i + 1) + 1e-9,
               s"work fell from ${ws(i)} to ${ws(i + 1)} between |s|=${sizes(i)} and ${sizes(i + 1)} (${model.name}, ${prog.show.take(50)})")
      println(f"COST: ${model.name}%-5s ${prog.show.take(42).replace('\n', ' ')}%-44s work over |s|=${sizes.mkString(",")}: ${ws.map(_.toLong).mkString(",")}")
  }

  // ==============================================================================================
  // 5. GROUND-TRUTH TREND (eval used only as an oracle, never by the analysis)
  // ==============================================================================================

  // DEMOTED (review.md finding 2): this is a SECONDARY trend metric.  It runs against `touch`, the
  // un-oracled element-cost component, because wall-clock time is dominated by `Set`/`ITrie`
  // internals that no event counts.  The PRIMARY evidence is now the containment/slack table in
  // `SpatialEventsCheck`, which compares predicted intervals against counted events per component.
  test("SECONDARY TREND: the reference-backend touch model ranks with measured eval runtime") {
    // families whose predicted set costs differ by construction: k^2 concats, k^2 prefix
    // comparisons, k log k sort comparisons, and a linear scan
    def bigLit(k: Int, pre: String): Space = litN(k, pre)
    def twoItem(k: Int): Space = Space.Literal(SpaceValue((0 until k).map(i => p("a" + i, "b")).toSet))
    val ks = Vector(32, 64, 128, 256)
    val progs: Vector[(String, Space)] =
      ks.map(k => s"compose/$k" -> Space.Composition(bigLit(k, "x"), bigLit(k, "y"))) ++
      ks.map(k => s"restrict/$k" -> Space.Restriction(twoItem(k), bigLit(k, "a"))) ++
      ks.map(k => s"range/$k" -> Space.Range(bigLit(k, "z"), 0, 4)) ++
      ks.map(k => s"union/$k" -> Space.Union(bigLit(k, "u"), bigLit(k, "v")))
    def timeMs(s: Space): Double =
      for _ <- 0 until 3 do eval(s)
      var best = Double.MaxValue
      for _ <- 0 until 5 do
        val t0 = System.nanoTime()
        var i = 0
        while i < 20 do { eval(s); i += 1 }
        best = math.min(best, (System.nanoTime() - t0) / 1e6 / 20.0)
      best
    val rows = progs.map { (nm, s) =>
      val pred = SpatialCost.analyze(s, SetCost).cost.touch.at(Map.empty)
      (nm, pred, timeMs(s))
    }
    val rho = Calibration.spearman(rows.map(_._2), rows.map(_._3))
    for (nm, pred, ms) <- rows.sortBy(_._2) do println(f"COST: $nm%-14s predicted touch=${pred.toLong}%10d  measured eval=$ms%8.3f ms")
    println(f"COST: Spearman rank correlation (predicted set touch vs measured eval time) = $rho%.3f over ${rows.length} programs " +
            "[SECONDARY metric; see SpatialEventsCheck for containment/slack]")
    assert(rho >= 0.5, f"the predicted cost order should track measured runtime; got rho=$rho%.3f")
    // the strongest single claim: the quadratic family really does grow quadratically
    val comp = rows.filter(_._1.startsWith("compose")).map(_._3)
    assert(comp.last > comp.head, s"compose/256 must be slower than compose/32: $comp")
  }

  // ==============================================================================================
  // 6. CORPUS SMOKE
  // ==============================================================================================

  test("corpus: every program gets a report from both backends, and every cost is monotone") {
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    assume(f.exists, "corpus not found")
    val recs = locally {
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()
    }.take(300)
    var bounded = 0; var unbounded = 0; var differing = 0
    val hist = collection.mutable.Map.empty[String, Int]
    var infExample: Option[String] = None
    val t0 = System.nanoTime()
    for r <- recs do
      val (a, b) = SpatialCost.compare(r.prog)
      for rep <- Vector(a, b) do
        if rep.cost.work.isUnbounded then unbounded += 1 else bounded += 1
        // MONOTONICITY on every corpus cost component
        for comp <- Vector(rep.cost.work, rep.cost.alloc, rep.cost.rounds); e <- comp.symOpt do
          val names = Sym.vars(e).toVector
          var prev = Double.NegativeInfinity
          for k <- Vector(2.0, 4.0, 16.0, 64.0) do
            val cur = Sym.evalAt(e, names.map(_ -> k).toMap)
            assert(cur >= prev - 1e-9, s"cost decreased at k=$k for ${e.show} in ${r.prog.show.take(90)}")
            prev = cur
          // and normalisation is stable on real analysis output
          assertEquals(Sym.normalize(e), e, s"analysis emitted a non-normal form: ${e.show}")
      hist(a.cost.work.bigO.show) = hist.getOrElse(a.cost.work.bigO.show, 0) + 1
      if a.cost.work.bigO == BigO.inf && infExample.isEmpty then
        infExample = Some(s"${r.prog.show.take(160).replace('\n', ' ')}\n         -> ${a.cost.show}")
      if a.cost != b.cost then differing += 1
    val ms = (System.nanoTime() - t0) / 1e6
    println(f"COST: ${recs.length} corpus programs x 2 backends in $ms%.0f ms — $bounded bounded / $unbounded unbounded work components")
    println(s"COST: set-backend work order classes: ${hist.toVector.sortBy(_._2).reverse.mkString(", ")}")
    // the whole point of the algebra: unknown growth must NOT all collapse onto one top element
    val classes = hist.keySet
    println(s"COST: ${hist.getOrElse("inf", 0)} / ${recs.length} programs reach the saturated `inf` class")
    infExample.foreach(e => println(s"COST: first `inf` work example:\n      $e"))
    assert(classes.count(_ != "inf") >= 5, s"the corpus should exhibit several distinct order classes, got $classes")
    assert(hist.getOrElse("inf", 0) * 10 <= recs.length,
           s"at most a tenth of the corpus may saturate; got ${hist.getOrElse("inf", 0)}/${recs.length}")
    println(f"COST: the two backends disagree on ${differing} / ${recs.length} corpus programs " +
            f"(${100.0 * differing / recs.length}%.0f%%)")
    assert(differing > recs.length / 4, s"the backends should differ on a large share of the corpus, got $differing")
  }
end SpatialCostCheck
