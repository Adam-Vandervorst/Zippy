package morkl

import munit.FunSuite

/** RELATIONAL FRONTIER COST — the differential and ASYMPTOTIC gate for `SpatialFrontier.scala`
 *.
 *
 *  ==WHAT THE GROUND TRUTH IS==
 *  The review DEFINES the parameter, so this suite computes it rather than measuring it.  [[truth]]
 *  walks two real `Trie` structures and counts exactly
 *
 *  {{{
 *  Q = { u | x_u and y_u both exist, and — for restriction/raffination — no proper prefix of u
 *            has terminal(y_v) }
 *  A = { u in Q | terminal(y_u) is false }        T = Q \ A
 *  gateFan / bothFan = the child-key fan-out at the nodes of A
 *  }}}
 *
 *  which is a hand-derived implementation of the review's own definitions, INDEPENDENT of
 *  `SpatialFrontier` (it reads concrete tries; the model reads abstract `SpatialType`s and never sees
 *  a trie).  The true algebraic case is computed by set arithmetic on the two path sets, again
 *  independently.  Building a `Trie` from a known `SpaceValue` is a projection of a value, not a run:
 *  no `eval`/`evalI`/`evalT`/`exec*` appears anywhere in this file, and the last test proves it.
 *
 *  ==WHAT IS NOT CHECKED HERE==
 *  The EXECUTORS' counters (`EffortEvent.TrieNodeVisit`/`PatriciaVisit`/`FreshTrieNode`) belong to
 *  another owner in this change, so this suite does NOT compare the model against a counted run.  It
 *  compares the model against the review's definition of the parameter, and publishes
 *  predicted-vs-derived slopes and ratios in the form the calibration gate can consume.  The
 *  measured comparison is the gates agent's.
 *
 *  ==THE ASYMPTOTIC GATES==
 *  Every scale family doubles a size parameter and asserts the SLOPE
 *  `log2((C(2n)+1)/(C(n)+1))` of the PREDICTION against the shape of the algorithm — 0 where the
 *  algorithm is constant or depth-only.  Containing the run below a linear ceiling is not a pass. */
class SpatialFrontierCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  // ================================================================================================
  // 0.  values, types, tries
  // ================================================================================================
  def pv(items: PathItem*): PathValue = PathValue(items.toList)
  def sv(ps: Iterable[PathValue]): SpaceValue = SpaceValue(ps.toSet)
  def ty(v: SpaceValue): SpatialType = SpatialType.of(v)
  def tr(v: SpaceValue): Trie = Trie.fromSpaceValue(v)

  /** the complete `arity`-ary trie of depth `depth`, hung under `prefix`: `arity^depth` paths */
  def full(prefix: List[PathItem], arity: Int, depth: Int): SpaceValue =
    def go(d: Int): Set[List[PathItem]] =
      if d == 0 then Set(Nil)
      else for k <- (0 until arity).toSet; t <- go(d - 1) yield s"c$k" :: t
    sv(go(depth).map(t => PathValue(prefix ++ t)))

  /** one path of length `len`, all items equal to `item` */
  def chain(item: PathItem, len: Int): PathValue = PathValue(List.fill(len)(item))

  /** `heads` distinct heads, each carrying the complete binary trie of depth `depth` */
  def bush(heads: Int, depth: Int): SpaceValue =
    sv((0 until heads).flatMap(h => full(List(s"h$h"), 2, depth).paths))

  // ================================================================================================
  // 1.  THE HAND-DERIVED GROUND TRUTH — the review's Q / A / T / J, on real tries
  // ================================================================================================

  /** The derived frontier, PER DEPTH.  The depth index is load-bearing: `J` is a sum of PER-LEVEL
   *  child-map merges and each level has its own two ceilings, so the truth has to be depth-indexed for
   *  the same reason the model is (a depth-`d` bound may not be met against a depth-`e` one). */
  final case class Truth(qPer: Vector[Long], aPer: Vector[Long], tPer: Vector[Long],
                         gatePer: Vector[Long], bothPer: Vector[Long], cases: Set[FrontierCase]):
    def q: Long = qPer.sum
    def a: Long = aPer.sum
    def t: Long = tPer.sum
    def gateFan: Long = gatePer.sum
    def bothFan: Long = bothPer.sum
    /** the fresh nodes the CASE-RETURNING algebra allocates: none at all when the result is an
     *  operand (`Trie.unionR` &c. return `Identity` and the parent reuses the argument object) */
    def rebuilt(op: FrontierOp): Long =
      if FrontierCase.isIdentity(cases) then 0L else if op.prunes then a else q
    /** the counted descents: `Θ(|Q| + J)`, with `J` summed over the levels.  At ONE level the merge
     *  visits at most the nodes of both child-map Patricia trees (`2(fanL + fanR)`) and at most one
     *  bounded search per gating key (`|A_d| + 2·PatriciaBits·gateFan(d)`), whichever is smaller.  The
     *  operation is entered once even when an operand is empty, hence the `max 1`. */
    def work(op: FrontierOp): Long =
      val j = bothPer.indices.map(d =>
        math.min(2 * bothPer(d), aPer(d) + 2 * FrontierConfig.PatriciaBits * gatePer(d))).sum
      math.max(1L, q + j)

  /** `shared` models the executors' `a eq b` short circuit: the algebra answers at the root without
   *  entering the frontier at all (`Trie.unionR`/`ITrie.union` first lines). */
  def truth(op: FrontierOp, x: Trie, y: Trie, xs: Set[PathValue], ys: Set[PathValue],
            shared: Boolean = false): Truth =
    val cs = trueCases(op, xs, ys)
    val z = Vector(0L)
    if shared && op != FrontierOp.Composition then Truth(Vector(1L), z, z, z, z, cs)
    else
      val q = scala.collection.mutable.ArrayBuffer.empty[Long]
      val a = scala.collection.mutable.ArrayBuffer.empty[Long]
      val t = scala.collection.mutable.ArrayBuffer.empty[Long]
      val gate = scala.collection.mutable.ArrayBuffer.empty[Long]
      val both = scala.collection.mutable.ArrayBuffer.empty[Long]
      def at(d: Int): Unit =
        while q.length <= d do { q += 0L; a += 0L; t += 0L; gate += 0L; both += 0L }
      def go(l: Trie, r: Trie, d: Int): Unit =
        at(d)
        q(d) += 1
        if op.prunes && r.terminal then t(d) += 1
        else
          a(d) += 1
          val kl = l.children.keySet; val kr = r.children.keySet
          both(d) += kl.size + kr.size
          gate(d) += (op.gate match
            case FrontierGate.RightGated => kr.size.toLong
            case FrontierGate.Symmetric => kl.size.toLong min kr.size.toLong)
          for k <- kl.intersect(kr) do go(l.children(k), r.children(k), d + 1)
      if x.nonEmpty && y.nonEmpty then go(x, y, 0)
      if q.isEmpty then Truth(z, z, z, z, z, cs)
      else Truth(q.toVector, a.toVector, t.toVector, gate.toVector, both.toVector, cs)

  /** COMPOSITION has a different frontier and therefore a different derived count: `compositionR`
   *  enters every node of the LEFT and builds one fresh node per left node THAT HAS CHILDREN (a leaf
   *  terminal returns `b` by pointer — `Identity(RIGHT)` — and allocates nothing), then merges at each
   *  terminal.  This is the correction: one terminal, but a `d`-node spine. */
  def compTruth(a: Trie): (Long, Long) =
    var internal = 0L; var terminals = 0L
    def go(n: Trie): Unit =
      if n.children.nonEmpty then internal += 1
      if n.terminal then terminals += 1
      for (_, c) <- n.children do go(c)
    go(a)
    (internal, terminals)
  def compWork(a: Trie): Long =
    val (i, t) = compTruth(a); math.max(1L, i + t)

  /** the true algebraic case, by set arithmetic — written out here rather than shared with the model */
  def trueCases(op: FrontierOp, a: Set[PathValue], b: Set[PathValue]): Set[FrontierCase] =
    def under(p: PathValue): Boolean =
      b.exists(q => q.items.length <= p.items.length && p.items.startsWith(q.items))
    val r = op match
      case FrontierOp.Union | FrontierOp.FixpointUnion => a ++ b
      case FrontierOp.Intersection => a.intersect(b)
      case FrontierOp.Subtraction => a.diff(b)
      case FrontierOp.Restriction => a.filter(under)
      case FrontierOp.Raffination => a.filterNot(under)
      case FrontierOp.Composition => for x <- a; y <- b yield PathValue(x.items ++ y.items)
    if r.isEmpty then Set(FrontierCase.Empty)
    else
      var cs = Set.empty[FrontierCase]
      if r == a then cs += FrontierCase.Left
      if r == b && op.mayBeRight then cs += FrontierCase.Right
      if cs.isEmpty then Set(FrontierCase.Bespoke) else cs

  def inIvl(i: Ivl, x: Long): Boolean = i.lo <= x && x <= i.hi

  // ================================================================================================
  // 2.  THE SLOPE HARNESS
  // ================================================================================================

  final case class Row(n: Long, pred: Long, derived: Long)
  /** `log2((C(2n)+1)/(C(n)+1))` — the review's slope, NORMALISED by the actual size ratio so a family
   *  that grows by a factor other than two reports the same exponent. */
  def slope(a: Long, b: Long): Double = math.log((b + 1.0) / (a + 1.0)) / math.log(2.0)
  def slope(ra: Row, rb: Row)(pick: Row => Long): Double =
    val steps = math.log(rb.n.toDouble / ra.n.toDouble) / math.log(2.0)
    if steps <= 0.0 then 0.0 else slope(pick(ra), pick(rb)) / steps

  /** slopes between consecutive scale points, plus the worst predicted/derived ratio */
  final case class Scale(name: String, rows: Vector[Row]):
    def predSlopes: Vector[Double] = rows.sliding(2).map(w => slope(w(0), w(1))(_.pred)).toVector
    def derivedSlopes: Vector[Double] = rows.sliding(2).map(w => slope(w(0), w(1))(_.derived)).toVector
    def worstPredSlope: Double = predSlopes.max
    def worstDerivedSlope: Double = derivedSlopes.max
    def ratios: Vector[Double] = rows.map(r => (r.pred + 1.0) / (r.derived + 1.0))
    def report: String =
      s"  $name\n" +
      rows.map(r => f"    n=${r.n}%-8d predicted=${r.pred}%-10d derived=${r.derived}%-10d ratio=${(r.pred + 1.0) / (r.derived + 1.0)}%8.2f").mkString("\n") +
      f"\n    slope predicted=${predSlopes.map(s => f"$s%.2f").mkString(",")} derived=${derivedSlopes.map(s => f"$s%.2f").mkString(",")}"

  /** THE GATE.  `expected` is the slope the ALGORITHM has; a prediction whose slope exceeds it is a
   *  failure even when it "contains" the derived count. */
  def gate(s: Scale, expected: Double, tol: Double = 0.35): Unit =
    println(s.report)
    for r <- s.rows do
      assert(r.pred >= r.derived,
             s"${s.name}: prediction ${r.pred} under-approximates the derived frontier ${r.derived} at n=${r.n}")
    assert(s.worstPredSlope <= expected + tol,
           f"${s.name}: predicted slope ${s.worstPredSlope}%.3f exceeds the algorithm's ${expected}%.3f")
    assert(s.worstDerivedSlope <= expected + tol,
           f"${s.name}: DERIVED slope ${s.worstDerivedSlope}%.3f exceeds ${expected}%.3f — the generator is wrong, not the model")
    assert(math.abs(s.worstPredSlope - s.worstDerivedSlope) <= tol + 0.15,
           f"${s.name}: predicted slope ${s.worstPredSlope}%.3f does not match the derived ${s.worstDerivedSlope}%.3f")

  /** one scale point: build the operands, summarise, derive the truth */
  def point(op: FrontierOp, xv: SpaceValue, yv: SpaceValue, shared: Boolean = false,
            cfg: FrontierConfig = FrontierConfig.default)
      : (FrontierSummary, Truth) =
    val s = SpatialFrontier.binary(op, ty(xv), ty(yv), shared, cfg)
    val t = truth(op, tr(xv), tr(yv), xv.paths, yv.paths, shared)
    (s, t)

  // ================================================================================================
  // 3.  THE HEADLINE CASES — the two the review states as claims
  // ================================================================================================

  test("restriction by {ε} is CONSTANT with zero allocation, at every scale") {
    val eps = sv(Set(pv()))
    val rows = (3 to 9).map { k =>
      val x = full(Nil, 2, k)
      val (s, t) = point(FrontierOp.Restriction, x, eps)
      assertEquals(s.cases, Set(FrontierCase.Left), "ε prefixes everything: Identity(LEFT)")
      assertEquals(t.cases, Set(FrontierCase.Left))
      assertEquals(s.rebuilt.hi, 0L, s"restriction by {ε} must allocate nothing: ${s.show}")
      assertEquals(t.rebuilt(FrontierOp.Restriction), 0L)
      assert(s.constant, s"restriction by {ε} must be CONSTANT: ${s.show}")
      assert(inIvl(s.accepts, t.t), s"accepts ${s.accepts.show} must bracket the derived ${t.t}")
      Row(x.paths.size.toLong, s.descents.hi, t.work(FrontierOp.Restriction))
    }.toVector
    gate(Scale("restriction by {ε} — descents", rows), expected = 0.0)
  }

  test("CONTINUITY ACROSS THE WIDTH CAP: a key-disjoint union is EXACT on BOTH sides of Shape.MaxHeads") {
    // the P1 first row, MEASURED AS A SWEEP ACROSS THE WIDTH CAP.  A union of two key-disjoint
    // operands under a shared prefix allocates TWO `ITrie` nodes at every scale — the root and the
    // shared-prefix node — because the Patricia merge attaches every branch whole.  The DERIVED
    // frontier (`truth`, which reads the real tries) says so at every n: `|Q| = 2`.
    //
    // THE MODEL USED TO MATCH IT ONLY WHILE BOTH HEAD SETS WERE CLOSED and to lose it at
    // `Shape.MaxHeads`: the width spill kept the untracked COUNT and dropped the head NAMES, so
    // `Shape.possibleHeads` answered `None`, key-disjointness stopped being provable, and `paired(2)`
    // fell back to the count-only pairing `min(K_2, K_2) = n`.  Measured, that was
    // `rebuilt = [2,2]` for n ≤ 12 and `[2, n+2]` for n ≥ 13 — the SAME program family, one more key,
    // and a prediction that changes GROWTH CLASS (`Sym.bigO` from 1 to n) at a fixed cutoff.
    //
    // The untracked-head certificate (`Shape.otherKeys`, channel (e)) is what removes the cliff, and
    // THIS TEST IS THE GATE ON IT: the assertion is now unconditional, so a regression that drops the
    // certificate anywhere on the path — `Shape.mk`, `capDepth`, `widen`, `SpatialAnalysis.capWidth`
    // or `SpatialTypeSystem.constrainShape` — turns this row red instead of merely printing wider.
    val ns = Vector(4, 8, 12, 13, 16, 24, 64, 256, 1024, 4096)
    var shown = Vector.empty[String]
    for n <- ns do
      val l = sv((0 until n).map(i => pv("g", s"x${2 * i}")))
      val r = sv((0 until n).map(i => pv("g", s"x${2 * i + 1}")))
      val (s, t) = point(FrontierOp.Union, l, r)
      shown :+= f"n=$n%-6d rebuilt=${s.rebuilt.show}%-14s |Q|=${s.depth.pairedTotal.show}%-14s " +
                f"derived |Q|=${t.q}  src=${s.source.show}"
      assertEquals(t.q, 2L, s"n=$n: the DERIVED paired frontier is the root and `g` only")
      assert(inIvl(s.depth.pairedTotal, t.q),
             s"n=$n: |Q| ${s.depth.pairedTotal.show} must bracket the derived ${t.q}: ${s.show}")
      assert(!s.isFallback, s"n=$n: this must be a derived frontier, not a ceiling: ${s.show}")
      assert(s.descents.hi < Ivl.INF, s"n=$n: descents must stay finite: ${s.show}")
      assertEquals(s.rebuilt.hi, 2L,
                   s"n=$n: the rebuild count must NOT move at the width cap " +
                   s"(Shape.MaxHeads = ${Shape.MaxHeads}): ${s.show}")
      assertEquals(s.depth.pairedTotal.hi, 2L,
                   s"n=$n: |Q| must NOT move at the width cap: ${s.show}")
    println(s"  KEY-DISJOINT union across the width cap (Shape.MaxHeads = ${Shape.MaxHeads}, " +
            s"Shape.MaxSpillKeys = ${Shape.MaxSpillKeys}) — FLAT:")
    for l <- shown do println("    " + l)
  }

  test("CONTINUITY ACROSS THE DEPTH CAP: exact to MaxDepth+1, and LINEAR IN d past it") {
    // `Shape.capDepth` is the OTHER half of the spill and it lost the names the same way: the
    // collapsed level's tracked keys became an anonymous count.  Four key-disjoint keys under a
    // shared prefix of length d-1 measured `rebuilt = [d,d]` for d ≤ MaxDepth and then `[5,9]`,
    // `[5,10]`, `[5,14]` for d = 5, 6, 7.
    //
    // TWO DIFFERENT CAUSES SAT ON TOP OF EACH OTHER THERE, and only one of them was a defect:
    //  * d = MaxDepth + 1 — the divergent keys land exactly ON the collapsed level, so the names
    //    were available and were thrown away.  The certificate recovers them and the row is now
    //    EXACT.  That is the discontinuity, and it is gone.
    //  * d > MaxDepth + 1 — the divergent keys land BELOW the collapsed level.  Both sides' shapes
    //    truncate to the same shared prefix head, so no certificate can help: the domain genuinely
    //    cannot see where they diverge.  That is the DEPTH BUDGET, an honest precision limit, and
    //    the prediction stays sound and LINEAR in d (a bounded factor over the truth `d`) rather
    //    than becoming a product.  The assertion below says exactly that and no more.
    var shown = Vector.empty[String]
    for d <- 1 to Shape.MaxDepth + 3 do
      val pre = (1 until d).map(i => s"p$i").toList
      val l = sv((0 until 4).map(i => PathValue(pre :+ s"a$i")))
      val r = sv((0 until 4).map(i => PathValue(pre :+ s"b$i")))
      val s = SpatialFrontier.binary(FrontierOp.Union, ty(l), ty(r))
      shown :+= f"depth=$d%-3d rebuilt=${s.rebuilt.show}%-14s |Q|=${s.depth.pairedTotal.show}%-14s src=${s.source.show}"
      if d <= Shape.MaxDepth + 1 then
        assertEquals(s.rebuilt.hi, d.toLong,
                     s"depth=$d: the rebuild count must be EXACT up to Shape.MaxDepth + 1 " +
                     s"(= ${Shape.MaxDepth + 1}) — the collapsed level's names are available: ${s.show}")
      else
        assert(s.rebuilt.hi >= d.toLong, s"depth=$d: unsound, below the truth $d: ${s.show}")
        assert(s.rebuilt.hi <= 3L * d,
               s"depth=$d: past the depth budget the bound must stay LINEAR in d (<= 3d), not " +
               s"become a product: ${s.show}")
    println(s"  KEY-DISJOINT union across the depth cap (Shape.MaxDepth = ${Shape.MaxDepth}) — " +
            s"exact to d = ${Shape.MaxDepth + 1}, linear past it:")
    for l <- shown do println("    " + l)
  }

  test("the prediction's ORDER CLASS is invariant under the config's own width cap") {
    // A cap is a PRECISION knob, not a growth-class knob.  `SpatialConfig.cheap` narrows
    // `shapeWidth` to 6 through `SpatialAnalysis.capWidth`, which spills tracked heads by hand — so
    // it is a second place the certificate can be dropped, and dropping it there would make the
    // cheap config predict a different growth class from the default on the SAME program.
    for n <- Vector(8, 13, 40) do
      val l = sv((0 until n).map(i => pv("g", s"x${2 * i}")))
      val narrowed = SpatialAnalysis.narrow(ty(l).shape, SpatialConfig.cheap)
      assert(narrowed.possibleHeads.isDefined,
             s"n=$n: the config's own width spill dropped the untracked-head certificate: ${narrowed.show}")
      assertEquals(narrowed.possibleHeads.get, Set("g"),
                   s"n=$n: and it must still name exactly the real head: ${narrowed.show}")
  }

  test("head-disjointness needs ENUMERABLE head sets, and the certificate keeps them past the spill") {
    // the same fact as the ROOT-level reject.  The head sets here are WIDE — n keys, one path each —
    // so past `Shape.MaxHeads` the tracked map holds only 12 of them and the rest are untracked.
    // What used to happen: two anonymous counts that could share every key, so no disjointness proof
    // existed and the intersection was `Bespoke` with a positive rebuild.  What happens now: the
    // untracked-head certificate names them, `possibleHeads` answers at every n, and the intersection
    // stays PROVED empty with zero allocation.
    for n <- Vector(4, 6, 12, 13, 64, 512) do
      val l = sv((0 until n).map(i => pv(s"a$i")))
      val r = sv((0 until n).map(i => pv(s"b$i")))
      val s = SpatialFrontier.binary(FrontierOp.Intersection, ty(l), ty(r))
      assert(ty(l).shape.possibleHeads.isDefined,
             s"n=$n: the head set must stay enumerable past the width cap: ${ty(l).shape.show}")
      assertEquals(ty(l).shape.possibleHeads.get, (0 until n).map(i => s"a$i").toSet,
                   s"n=$n: and it must name EXACTLY the real heads: ${ty(l).shape.show}")
      assertEquals(s.cases, Set(FrontierCase.Empty),
                   s"n=$n: head-disjoint intersection is PROVED empty at every n: ${s.show}")
      assert(s.rootOnly, s"n=$n: nothing below the root is paired: ${s.show}")
      assertEquals(s.rebuilt.hi, 0L, s"n=$n: and nothing is allocated: ${s.show}")
      // and the proof is not vacuous: the SAME key set is never disjoint from itself
      val same = SpatialFrontier.binary(FrontierOp.Intersection, ty(l), ty(l))
      assertNotEquals(same.cases, Set(FrontierCase.Empty),
                      s"n=$n: x ∩ x must not be PROVED empty: ${same.show}")
      assert(same.depth.pairedTotal.hi >= n, s"n=$n: x ∩ x pairs every key: ${same.show}")
  }

  test("restriction by ONE present COVERING prefix: Θ(d) descents, zero allocation") {
    // every x-path extends the prefix, so `Trie.restrictionR` propagates Identity(LEFT) to the root
    // and allocates nothing (the review of the restriction paragraph).  n doubles:
    // the selected subtree below the matched prefix grows exponentially.
    val prefix = List("p0", "p1", "p2", "p3")
    val d = prefix.length.toLong
    val rows = (2 to 9).map { k =>
      val x = full(prefix, 2, k)
      val pfx = sv(Set(PathValue(prefix)))
      val (s, t) = point(FrontierOp.Restriction, x, pfx)
      assertEquals(s.cases, Set(FrontierCase.Left), s"every x-path extends the prefix: ${s.show}")
      assertEquals(t.cases, Set(FrontierCase.Left))
      assertEquals(s.rebuilt.hi, 0L, s"the identity propagates: nothing is allocated: ${s.show}")
      assert(inIvl(s.depth.pairedTotal, t.q), s"|Q| ${s.depth.pairedTotal.show} must bracket ${t.q}")
      assert(inIvl(s.depth.activeTotal, t.a), s"|A| ${s.depth.activeTotal.show} must bracket ${t.a}")
      assert(inIvl(s.accepts, t.t))
      assert(s.depthOnly(d), s"restriction by a length-$d prefix must be depth-only: ${s.show}")
      Row(x.paths.size.toLong, s.descents.hi, t.work(FrontierOp.Restriction))
    }.toVector
    gate(Scale("restriction by one covering length-4 prefix — descents", rows), expected = 0.0)

    // THE INTERNED ITrie ALGEBRA on the same input: no Identity to return, so the d-node spine IS
    // rebuilt.  Still flat in the subtree below the prefix, which is the point.
    val alloc = (2 to 9).map { k =>
      val x = full(prefix, 2, k)
      val s = SpatialFrontier.binary(FrontierOp.Restriction, ty(x), ty(sv(Set(PathValue(prefix)))),
                                     cfg = FrontierConfig.interned)
      assert(s.rebuilt.hi <= d + 1, s"expected the $d-node spine, got ${s.rebuilt.show}: ${s.show}")
      Row(x.paths.size.toLong, s.rebuilt.hi, d)
    }.toVector
    gate(Scale("restriction by one covering length-4 prefix — ITrie rebuilt nodes", alloc), expected = 0.0)
  }

  test("a NON-covering prefix rebuilds exactly the d-node spine, and nothing below it") {
    // one branch of a bush is selected: the result is Bespoke, so the spine really is rebuilt
    val target = List("h0", "c0", "c1")
    val d = target.length.toLong
    // k ≥ 3 so that the selected subtree is strictly below the prefix (at k = 2 the result IS the
    // prefix itself, which is `Identity(RIGHT)` and a different case)
    val rows = (3 to 8).map { k =>
      val x = bush(6, k)
      val (s, t) = point(FrontierOp.Restriction, x, sv(Set(PathValue(target))))
      assert(s.cases.contains(FrontierCase.Bespoke), s"only one of six heads is kept: ${s.show}")
      assertEquals(t.cases, Set(FrontierCase.Bespoke))
      assert(inIvl(s.depth.activeTotal, t.a), s"|A| ${s.depth.activeTotal.show} vs derived ${t.a}")
      assert(inIvl(s.rebuilt, t.rebuilt(FrontierOp.Restriction)),
             s"rebuilt ${s.rebuilt.show} vs derived ${t.rebuilt(FrontierOp.Restriction)}")
      assertEquals(s.rebuilt.hi, d, s"exactly the $d-node spine: ${s.show}")
      Row(x.paths.size.toLong, s.descents.hi, t.work(FrontierOp.Restriction))
    }.toVector
    gate(Scale("non-covering length-3 prefix over a growing bush — descents", rows), expected = 0.0)
  }

  test("the prefix spine grows with d and with NOTHING else") {
    // the other half of Θ(d): hold the selected subtree fixed and lengthen the prefix
    val preds = (1 to 8).map { d =>
      val prefix = (0 until d).map(i => s"p$i").toList
      val x = sv(full(prefix, 2, 3).paths ++ full(List("z"), 2, 3).paths)   // NOT covered: z survives
      val (s, t) = point(FrontierOp.Restriction, x, sv(Set(PathValue(prefix))))
      assert(inIvl(s.depth.activeTotal, t.a), s"|A| ${s.depth.activeTotal.show} vs derived ${t.a} at d=$d")
      assert(inIvl(s.rebuilt, t.rebuilt(FrontierOp.Restriction)))
      (d, s.rebuilt.hi, t.rebuilt(FrontierOp.Restriction))
    }.toVector
    println("  prefix-length sweep (rebuilt nodes):")
    for (d, p, t) <- preds do println(f"    d=$d%-3d predicted=$p%-6d derived=$t%-6d")
    assertEquals(preds.map(_._2), preds.map(_._1.toLong), "the spine is exactly d nodes")
    assertEquals(preds.map(_._3), preds.map(_._1.toLong))
  }

  // ================================================================================================
  // 4.  THE SHARING / DISJOINTNESS FAMILIES
  // ================================================================================================

  test("disjoint one-head deep tries: the merge rejects at the root at every depth") {
    val rows = (2 to 12).map { d =>
      val x = sv(Set(chain("a", d)))
      val y = sv(Set(chain("b", d)))
      val (s, t) = point(FrontierOp.Intersection, x, y)
      assertEquals(s.cases, Set(FrontierCase.Empty), s"head-disjoint intersection is ∅: ${s.show}")
      assertEquals(s.rebuilt.hi, 0L)
      assert(s.constant, s"a head-disjoint intersection must be CONSTANT: ${s.show}")
      assert(inIvl(s.depth.pairedTotal, t.q), s"|Q| ${s.depth.pairedTotal.show} vs ${t.q}")
      // the SIZE-ONLY ceiling the review is replacing would be linear in d here
      Row(d.toLong, s.descents.hi, t.work(FrontierOp.Intersection))
    }.toVector
    gate(Scale("disjoint one-head chains — intersection descents", rows), expected = 0.0)

    val sub = (2 to 12).map { d =>
      val x = sv(Set(chain("a", d)))
      val y = sv(Set(chain("b", d)))
      val (s, t) = point(FrontierOp.Subtraction, x, y)
      assertEquals(s.cases, Set(FrontierCase.Left), "disjoint subtraction is left identity")
      assertEquals(s.rebuilt.hi, 0L)
      Row(d.toLong, s.descents.hi, t.work(FrontierOp.Subtraction))
    }.toVector
    gate(Scale("disjoint one-head chains — subtraction descents", sub), expected = 0.0)
  }

  test("a one-path RHS modifying one branch of a huge LHS is depth-only") {
    val target = List("h0", "c0", "c1")
    val rows = (2 to 8).map { k =>
      val x = bush(6, k)                          // 6 heads × 2^k paths each
      val y = sv(Set(PathValue(target)))
      val (s, t) = point(FrontierOp.Subtraction, x, y)
      assert(inIvl(s.depth.pairedTotal, t.q), s"|Q| ${s.depth.pairedTotal.show} vs derived ${t.q}")
      assert(s.rebuilt.hi <= 8L,
             s"only the ${target.length}-node spine may be rebuilt, got ${s.rebuilt.show}: ${s.show}")
      Row(x.paths.size.toLong, s.descents.hi, t.work(FrontierOp.Subtraction))
    }.toVector
    gate(Scale("one-path RHS against a growing LHS — subtraction descents", rows), expected = 0.0)
  }

  test("equal values: SHARED representation is constant, unshared pays the frontier") {
    val sharedRows = (2 to 9).map { k =>
      val v = full(Nil, 2, k)
      val (s, t) = point(FrontierOp.Union, v, v, shared = true)
      assertEquals(s.cases, Set(FrontierCase.Left, FrontierCase.Right), "Identity(BOTH)")
      assertEquals(s.rebuilt.hi, 0L)
      assert(s.constant, s"a shared union must be CONSTANT: ${s.show}")
      Row(v.paths.size.toLong, s.descents.hi, t.work(FrontierOp.Union))
    }.toVector
    gate(Scale("equal values, SHARED representation — union descents", sharedRows), expected = 0.0)

    // unshared: the algebra must WALK the whole common frontier to discover the identity, so the
    // right answer is LINEAR.  The family grows the BRANCHING at a fixed depth so that the shape
    // domain's four tracked levels cover it exactly (see the log-factor test below for what happens
    // when the depth grows past them instead).
    val rows = Vector(2, 3, 4, 6, 8, 11, 16).map { a =>
      val v = full(Nil, a, 3)
      val (s, t) = point(FrontierOp.Union, v, v, shared = false)
      assert(inIvl(s.depth.pairedTotal, t.q), s"|Q| ${s.depth.pairedTotal.show} vs ${t.q}")
      Row(v.paths.size.toLong, s.descents.hi, t.work(FrontierOp.Union))
    }
    gate(Scale("equal values, UNSHARED, fixed depth — union descents", rows), expected = 1.0)
  }

  test("PUBLISHED GAP: past the shape's four tracked levels the frontier carries a log factor") {
    // K_d is bounded by the SHAPE for d ≤ Shape.MaxDepth and only by E_d (the total path count)
    // below it, so `Σ_d min(K_d, K_d)` over a family whose DEPTH grows is `N·len`, not `N`.  That is
    // the same information loss `Meas.nodes = 1 + size·len` already has, and it is published rather
    // than hidden: the frontier model is strictly better than the size-only bound everywhere else and
    // exactly as good here.
    val rows = (2 to 9).map { k =>
      val v = full(Nil, 2, k)
      val (s, t) = point(FrontierOp.Union, v, v, shared = false)
      Row(v.paths.size.toLong, s.descents.hi, t.work(FrontierOp.Union))
    }.toVector
    val sc = Scale("equal values, UNSHARED, growing DEPTH — union descents", rows)
    println(sc.report)
    for r <- sc.rows do assert(r.pred >= r.derived, s"still sound at n=${r.n}")
    println(f"    KNOWN GAP: predicted slope ${sc.worstPredSlope}%.3f against the algorithm's " +
            f"${sc.worstDerivedSlope}%.3f — the log factor is Shape.MaxDepth=${Shape.MaxDepth} tracked levels")
    assert(sc.worstDerivedSlope <= 1.2, "the algorithm itself is linear")
    assert(sc.worstPredSlope <= 2.0, "the gap is a log factor, not a polynomial one")
    assert(sc.worstPredSlope > sc.worstDerivedSlope, "the gap is real and is being published")
  }

  test("subset / superset pairs") {
    // small enough to be PINNED to exact values: the identity is proved and nothing is rebuilt
    val small = sv(Set(pv("a"), pv("a", "b")))
    val big = sv(Set(pv("a"), pv("a", "b"), pv("a", "c"), pv("b")))
    val u = SpatialFrontier.binary(FrontierOp.Union, ty(small), ty(big))
    assertEquals(u.cases, Set(FrontierCase.Right), s"subset union is Identity(RIGHT): ${u.show}")
    assertEquals(u.rebuilt.hi, 0L)
    assertEquals(u.source, FrontierSource.Exact)
    val i = SpatialFrontier.binary(FrontierOp.Intersection, ty(small), ty(big))
    assertEquals(i.cases, Set(FrontierCase.Left), s"a contained operand is returned: ${i.show}")
    assertEquals(i.rebuilt.hi, 0L)
    val d = SpatialFrontier.binary(FrontierOp.Subtraction, ty(small), ty(big))
    assertEquals(d.cases, Set(FrontierCase.Empty))

    // at SCALE the containment is no longer provable (the shape tracks four levels), so the model
    // predicts the paired frontier.  That is the honest answer for `descents` — the algebra really
    // does walk it — and it is published as an over-prediction for `rebuilt`.
    val rows = Vector(2, 3, 4, 6, 8, 11, 16).map { ar =>
      val a = full(List("h0"), ar, 3)
      val b = sv(a.paths ++ full(List("h1"), ar, 3).paths)
      val (s, t) = point(FrontierOp.Union, a, b)
      assert(inIvl(s.depth.pairedTotal, t.q), s"|Q| ${s.depth.pairedTotal.show} vs ${t.q}")
      assert(s.rebuilt.hi >= t.rebuilt(FrontierOp.Union))
      Row(a.paths.size.toLong, s.descents.hi, t.work(FrontierOp.Union))
    }
    gate(Scale("subset union at scale — descents", rows), expected = 1.0)
    println("    (rebuilt is OVER-predicted at scale: subset is not provable from a 4-level shape)")
  }

  test("ε / empty operands are constant on every operator") {
    val big = full(Nil, 2, 8)
    val eps = sv(Set(pv()))
    val nil = SpaceValue(Set.empty)
    for op <- FrontierOp.values.toVector do
      val withEmpty = SpatialFrontier.binary(op, ty(big), ty(nil))
      assert(withEmpty.constant, s"$op with an empty right operand must be constant: ${withEmpty.show}")
      assertEquals(withEmpty.rebuilt.hi, 0L)
      val emptyLeft = SpatialFrontier.binary(op, ty(nil), ty(big))
      assert(emptyLeft.constant, s"$op with an empty left operand must be constant: ${emptyLeft.show}")
    // {ε} is the composition unit on both sides, and restriction's annihilator
    val cl = SpatialFrontier.binary(FrontierOp.Composition, ty(eps), ty(big))
    assertEquals(cl.cases, Set(FrontierCase.Right), s"{ε}·B == B: ${cl.show}")
    assert(cl.constant)
    val cr = SpatialFrontier.binary(FrontierOp.Composition, ty(big), ty(eps))
    assertEquals(cr.cases, Set(FrontierCase.Left), s"A·{ε} == A: ${cr.show}")
    assert(cr.constant)
    val raf = SpatialFrontier.binary(FrontierOp.Raffination, ty(big), ty(eps))
    assertEquals(raf.cases, Set(FrontierCase.Empty), "ε ∈ y annihilates the raffination")
    assert(raf.constant)
  }

  test("composition of a single deep path grafts B by pointer: Θ(|A|), flat in |B|") {
    val a = sv(Set(chain("a", 5)))
    val rows = (2 to 9).map { k =>
      val b = full(Nil, 2, k)
      val s = SpatialFrontier.binary(FrontierOp.Composition, ty(a), ty(b))
      assert(s.notes.exists(_.contains("LEAF")),
             s"the single terminal of a one-path left operand is a leaf: ${s.show}")
      // The review: ONE terminal, but the d-node spine IS rebuilt
      assert(s.rebuilt.hi >= 5L && s.rebuilt.hi <= 12L,
             s"expected the 6-node spine and no per-graft merge, got ${s.rebuilt.show}")
      Row(b.paths.size.toLong, s.descents.hi, compWork(tr(a)))
    }.toVector
    gate(Scale("composition, one-path left — descents", rows), expected = 0.0)

    // the other direction: the LEFT operand grows, and the cost grows with it — one entry and one
    // fresh node per left node, which is what `O(#terminals(A))` (Trie.scala:294-304) gets wrong
    val byLeft = (1 to 8).map { d =>
      val l = sv(Set(chain("a", d)))
      val s = SpatialFrontier.binary(FrontierOp.Composition, ty(l), ty(full(Nil, 2, 3)))
      assert(s.rebuilt.hi >= compTruth(tr(l))._1,
             s"the ${d}-node spine is rebuilt even though A has ONE terminal: ${s.show}")
      (d, s.rebuilt.hi, compTruth(tr(l))._1)
    }.toVector
    println("  composition, growing one-path left (rebuilt nodes):")
    for (d, p, t) <- byLeft do println(f"    |p|=$d%-3d predicted=$p%-6d derived-internal=$t%-6d")
    assert(slope(byLeft.head._2, byLeft.last._2) > 0.0, "composition of a longer path costs more")
  }

  // ================================================================================================
  // 5.  SOUNDNESS DIFFERENTIAL over a finite universe
  // ================================================================================================

  test("every component brackets the hand-derived frontier over the whole finite universe") {
    val items = Vector("a", "b")
    val universe = SpatialGamma.universe(items, 2)     // 128 spaces
    var checked = 0L
    var identityProved = 0L
    var fallbacks = 0L
    for op <- FrontierOp.values.toVector; xv <- universe; yv <- universe do
      val s = SpatialFrontier.binary(op, ty(xv), ty(yv))
      val t = truth(op, tr(xv), tr(yv), xv.paths, yv.paths)
      checked += 1
      if s.isFallback then fallbacks += 1
      assert(t.cases.subsetOf(s.cases),
             s"$op ${xv.pretty} vs ${yv.pretty}: derived case ${FrontierCase.show(t.cases)} not in ${FrontierCase.show(s.cases)}")
      if s.identity then
        identityProved += 1
        assert(FrontierCase.isIdentity(t.cases),
               s"$op ${xv.pretty} vs ${yv.pretty}: model claims an identity, the truth is ${FrontierCase.show(t.cases)}")
      // COMPOSITION's frontier is the LEFT's node set plus its graft merges, not a paired-prefix
      // frontier, so it is bracketed against its own derived count instead
      if op == FrontierOp.Composition then
        if !s.isFallback && !s.identity then
          assert(s.rebuilt.hi >= compTruth(tr(xv))._1,
                 s"composition ${xv.pretty}·${yv.pretty}: rebuilt ${s.rebuilt.show} below the left's internal nodes ${compTruth(tr(xv))._1}")
          assert(s.descents.hi >= compWork(tr(xv)),
                 s"composition ${xv.pretty}·${yv.pretty}: descents ${s.descents.show} below the derived ${compWork(tr(xv))}")
      else if !s.isFallback then
        assert(inIvl(s.depth.pairedTotal, t.q),
               s"$op ${xv.pretty} vs ${yv.pretty}: |Q| ${s.depth.pairedTotal.show} vs derived ${t.q}")
        assert(inIvl(s.depth.activeTotal, t.a),
               s"$op ${xv.pretty} vs ${yv.pretty}: |A| ${s.depth.activeTotal.show} vs derived ${t.a}")
        assert(inIvl(s.accepts, t.t),
               s"$op ${xv.pretty} vs ${yv.pretty}: accepts ${s.accepts.show} vs derived ${t.t}")
        assert(inIvl(s.rebuilt, t.rebuilt(op)),
               s"$op ${xv.pretty} vs ${yv.pretty}: rebuilt ${s.rebuilt.show} vs derived ${t.rebuilt(op)}")
        assert(s.descents.lo <= t.work(op) && t.work(op) <= s.descents.hi,
               s"$op ${xv.pretty} vs ${yv.pretty}: descents ${s.descents.show} vs derived ${t.work(op)}")
    println(f"  universe differential: $checked%d (op, x, y) triples, $identityProved%d identities proved, $fallbacks%d fallbacks")
    assertEquals(fallbacks, 0L, "no finite exact operand pair may need the coarse ceiling")
    assert(identityProved > 0, "the model must prove SOME identity on this universe")
  }

  // ================================================================================================
  // 6.  THE FALLBACK IS MARKED, AND ONLY USED WHEN THERE IS NO FRONTIER
  // ================================================================================================

  test("an unbounded operand falls back to the coarse ceiling, and SAYS SO") {
    val top = SpatialType.top
    val s = SpatialFrontier.binary(FrontierOp.Union, top, top)
    assert(s.isFallback, s"⊤ against ⊤ has no frontier bound: ${s.show}")
    assertEquals(s.source, FrontierSource.SizeCeiling)
    assert(s.notes.exists(_.contains("not derivable")))
    // the symbolic bridge keeps the MIN-gated rebuild bound even in the fallback, because a rebuilt
    // node is a paired node and therefore a node of BOTH operands — a structural law, not a fit
    val nl = Sym.v("NL"); val nr = Sym.c(7)
    val sy = s.syms(nl, nr, Sym.c(3) * (nl + nr))
    assert(sy.fallback)
    assertEquals(sy.rebuilt, Sym.tighter(nl, nr))
    assertEquals(Sym.bigO(sy.rebuilt), BigO.const, s"min(N(L), 7) is CONSTANT, not linear: ${sy.rebuilt.show}")

    // one bounded side is enough: min(K_d(L), K_d(R)) is zero past the bounded side's depth
    val fin = ty(sv(Set(pv("a", "b"))))
    val half = SpatialFrontier.binary(FrontierOp.Restriction, top, fin)
    assert(!half.isFallback, s"a bounded RIGHT operand bounds the restriction frontier: ${half.show}")
    assert(half.depth.pairedTotal.hi <= 3L, s"|Q| ≤ N(right) = 3: ${half.show}")
    assert(half.depthOnly(2L), s"restriction by a length-2 prefix set is depth-only: ${half.show}")
  }

  test("the two backends differ by a SLOPE on the identity cases, not by a constant") {
    // the same input, the two algebras.  `ITrie` has no `Identity` result, so where the case-returning
    // form reuses the argument object it rebuilds the whole frontier.
    val prefix = List("p0", "p1", "p2", "p3")
    val big = full(prefix, 2, 7)
    val pfx = sv(Set(PathValue(prefix)))
    val opt = SpatialFrontier.binary(FrontierOp.Restriction, ty(big), ty(pfx))
    val itr = SpatialFrontier.binary(FrontierOp.Restriction, ty(big), ty(pfx), cfg = FrontierConfig.interned)
    assertEquals(opt.rebuilt.hi, 0L, s"Trie.restrictionR propagates Identity(LEFT): ${opt.show}")
    assertEquals(itr.rebuilt.hi, 5L, s"ITrie.restriction rebuilds the 4-node spine plus its root: ${itr.show}")
    assert(itr.notes.exists(_.contains("INTERNED")))
    // the explicit fast paths ARE in the interned code, so the ε case stays cheap on both
    val eps = SpatialFrontier.binary(FrontierOp.Restriction, ty(big), ty(sv(Set(pv()))),
                                     cfg = FrontierConfig.interned)
    assert(eps.rebuilt.hi <= 1L, s"`if prefixes.terminal then x` allocates nothing: ${eps.show}")
  }

  // ================================================================================================
  // 7.  THE OPTIMIZED PROGRAM  (the estimate belongs on the residual, not the definitional form)
  // ================================================================================================

  test("summarize reads the OPTIMIZED routine's decorated siblings") {
    val prefix = List("p0", "p1", "p2")
    val big = full(prefix, 2, 7)                  // 128 paths below the matched prefix
    val x = SpaceMention("x")
    val body: Space = Space.Restriction(Space.Mention(x), Space.Literal(sv(Set(PathValue(prefix)))))
    val r = Routine(RoutinePtr("sel"), Vector.empty, Vector(x), body).optimized
    val env = SpatialTyping.Env(spaces = Map(x -> ty(big)))
    val a = SpatialAnalysis.of(r.body, env)
    val rows = SpatialFrontier.summarize(a)
    println("  optimized residual:\n" + r.body.show.linesIterator.map("    " + _).mkString("\n"))
    println(SpatialFrontier.report(rows).linesIterator.map("  " + _).mkString("\n"))
    val restr = rows.filter(_._2.op == FrontierOp.Restriction)
    assert(restr.nonEmpty, s"the restriction survived optimization: ${r.body.show}")
    for (_, s) <- restr do
      assert(!s.isFallback, s"the declared input type bounds the frontier: ${s.show}")
      assert(s.depthOnly(prefix.length.toLong),
             s"restriction by a length-${prefix.length} prefix is depth-only even over 128 selected paths: ${s.show}")
      assert(s.rebuilt.hi <= prefix.length.toLong, s"a ${prefix.length}-node spine: ${s.show}")
  }

  test("two occurrences of the SAME mention are the `same` case; two literals are the same object") {
    val m = SpaceMention("m")
    assert(SpatialFrontier.sameObject(Space.Mention(m), Space.Mention(m)))
    val lit = sv(Set(pv("a"), pv("b")))
    assert(SpatialFrontier.sameObject(Space.Literal(lit), Space.Literal(lit)),
           "the identity-keyed literal cache hands back one object")
    assert(!SpatialFrontier.sameObject(Space.Singleton(Path.Constant(pv("a"))),
                                       Space.Singleton(Path.Constant(pv("a")))),
           "two Singleton evaluations build two tries")

    val big = full(Nil, 2, 7)
    val body: Space = Space.Union(Space.Mention(m), Space.Mention(m))
    val a = SpatialAnalysis.of(body, SpatialTyping.Env(spaces = Map(m -> ty(big))))
    val s = SpatialFrontier.atNode(a, NodeId(Vector.empty)).get
    assertEquals(s.cases, Set(FrontierCase.Left, FrontierCase.Right), s"x ∪ x is Identity(BOTH): ${s.show}")
    assert(s.constant, s"the pointer-identity short circuit fires: ${s.show}")
    assertEquals(s.rebuilt.hi, 0L)
  }

  test("fixpoint-union: an absorbed iterate rebuilds nothing") {
    val acc = ty(full(Nil, 2, 6))
    val it = ty(full(List("c0"), 2, 4))
    val plain = SpatialFrontier.fixpointUnion(acc, it)
    val absorbed = SpatialFrontier.fixpointUnion(acc, it, absorbed = true)
    assertEquals(absorbed.cases, Set(FrontierCase.Left))
    assertEquals(absorbed.rebuilt.hi, 0L, s"an absorbed iterate needs no rebuild: ${absorbed.show}")
    assert(plain.rebuilt.hi >= absorbed.rebuilt.hi)
    // the whole fixpoint is the per-round frontier times the rounds
    val whole = SpatialFrontier.scaled(plain, Ivl(1, 4))
    assertEquals(whole.descents.hi, Ivl.mul(plain.descents.hi, 4L))
    assert(whole.notes.exists(_.contains("rounds")))
  }

  test("every operator names its frontier and the whole-subtree case the size bound loses") {
    for op <- FrontierOp.values.toVector do
      assert(op.frontier.nonEmpty && op.wholeSubtree.nonEmpty)
      println(f"  ${op.show}%-14s frontier: ${op.frontier}")
      println(" " * 17 + s"lost by size-only: ${op.wholeSubtree}")
    // the structural law: `a ∖ b == b` is impossible unless everything is empty
    assert(!FrontierOp.Subtraction.mayBeRight)
    assert(!FrontierOp.Raffination.mayBeRight)
    assert(FrontierOp.Restriction.prunes && FrontierOp.Raffination.prunes)
    assert(!FrontierOp.Union.prunes)
    assertEquals(FrontierOp.Restriction.gate, FrontierGate.RightGated)
    assertEquals(FrontierOp.Subtraction.gate, FrontierGate.RightGated)
    assertEquals(FrontierOp.Union.gate, FrontierGate.Symmetric)
  }

  // ================================================================================================
  // 8.  NO EVALUATION
  // ================================================================================================

  test("no frontier summary ever runs the subject program") {
    val bomb: Space = Space.GroundedSS(Space.Empty,
      _ => throw RuntimeException("a frontier summary evaluated its subject"))
    val t = SpatialTyping.infer(bomb)
    for op <- FrontierOp.values.toVector do
      SpatialFrontier.binary(op, t, t)
      SpatialFrontier.binary(op, t, ty(full(Nil, 2, 4)))
      SpatialFrontier.binary(op, ty(full(Nil, 2, 4)), t)
    SpatialFrontier.fixpointUnion(t, t)
    val body: Space = Space.Union(bomb, Space.Literal(sv(Set(pv("a")))))
    val a = SpatialAnalysis.of(body)
    assert(SpatialFrontier.summarize(a).nonEmpty)
    SpatialFrontier.report(SpatialFrontier.summarize(a))
    // the sentinel really would throw
    intercept[RuntimeException] { eval(bomb) }
  }
