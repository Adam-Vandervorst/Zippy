package morkl

import munit.FunSuite
import scala.collection.immutable.SortedMap

/** ==================================================================================================
 *  THE CERTIFICATE'S BUDGETS, ON BOTH SIDES OF EVERY ONE OF THEM.
 *
 *  `1C.5` puts two budgets in `SpatialConfig` — `certKeys` and `certDepth` — with a widening rule and
 *  a record of every degradation.  `1C.6` is the gate, and it asks for three things at once, because
 *  a budget can fail in three different ways and only the third is obvious:
 *
 *    1. EXACT DISJOINTNESS BELOW the budget.  A bound that is not exact where it is cheap is not
 *       worth having.
 *    2. A RECORDED DEGRADATION ABOVE it, naming the rule.  A budget that quietly weakens the answer
 *       is worse than one that fails loudly: `SpatialCost`'s report reads the record, so a bound
 *       weakened by a budget rather than by the program says so.
 *    3. THE PREDICTED GROWTH CLASS UNCHANGED ACROSS THE CROSSING.  This is the one the whole tier
 *       exists for.  Both flat certificate channels had a size at which they degraded to ⊤, so a
 *       key-disjoint family's predicted allocation jumped from `Θ(1)` to `Θ(n)` at a fixed key count
 *       — first at `MaxHeads` (12), then at `MaxSpillKeys` (4096) once channel (f) moved the cliff
 *       instead of removing it.  A budget is allowed to cost PRECISION.  It is not allowed to change
 *       the ASYMPTOTIC, because then the answer depends on where the cap happens to sit.
 *
 *  ==WHY THE RULE IS TESTED AT SMALL BUDGETS AS WELL AS THE REAL ONES==
 *  `Shape.CertKeys` is 4096 and `Shape.CertDepth` is 12.  Crossing the width budget with a family
 *  that has real SUB-STRUCTURE means 4097 distinct sub-tries, which is a slow test of a rule that
 *  does not depend on the number.  So the rule is exercised directly through `Cert.widen` at budgets
 *  of 1–3, where every case is enumerable, AND the domain's own budgets are crossed with the family
 *  the cliff actually broke (a wide key-disjoint union).  The first says the rule is right; the second
 *  says the rule is what the domain runs.
 *  ================================================================================================== */
class SpatialCertBudgetCheck extends FunSuite, CalibrationProbe:
  import Cert.{Outside, Degradation}
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def pv(items: PathItem*): PathValue = PathValue(items.toList)
  def sv(ps: Iterable[PathValue]): SpaceValue = SpaceValue(ps.toSet)
  def ty(v: SpaceValue): SpatialType = SpatialType.of(v)

  /** `n` keys, each carrying its OWN distinct sub-trie — the family the width fold is about */
  def wideStructured(n: Int): Cert =
    Cert.of(false, SortedMap.from((0 until n).map(i => s"k$i" -> Cert.path(List(s"t$i", s"u$i")))),
            Outside.Closed)

  /** `n` keys carrying nothing — a pure name set, i.e. exactly what the old channels (e)/(f) held */
  def wideNames(n: Int): Cert = Cert.named((0 until n).map(i => s"k$i").toSet)

  /** one spine of depth `d`, then a two-way branch — the family the depth cut is about.  `tag`
   *  distinguishes otherwise-identical spines, which matters because interning makes two equal
   *  sub-tries ONE object and the width budget counts DISTINCT sub-tries. */
  def deep(d: Int, tag: String = ""): Cert =
    val leaf = Cert.of(false, SortedMap(s"a$tag" -> Cert.epsOnly, s"b$tag" -> Cert.epsOnly),
                       Outside.Closed)
    (1 to d).foldLeft(leaf)((c, i) => Cert.of(false, SortedMap(s"p$i" -> c), Outside.Closed))

  /** every path of `c`, up to `lim` items — the soundness oracle for a widening */
  def paths(c: Cert, lim: Int): Set[List[PathItem]] =
    val out = collection.mutable.HashSet.empty[List[PathItem]]
    def go(x: Cert, acc: List[PathItem], d: Int): Unit =
      if d <= lim then
        if x.eps then out += acc.reverse
        for (k, ch) <- x.keys do go(ch, k :: acc, d + 1)
        // an `Unbounded`/`Bounded` outside stands for names we cannot enumerate, so it contributes
        // nothing HERE — which is right: this oracle is the set of paths the trie NAMES, and the
        // soundness law below is "every named path survives the widening".
    go(c, Nil, 0)
    out.toSet

  // ================================================================================================
  // 1.  THE WIDTH BUDGET
  // ================================================================================================
  test("WIDTH, below and above: names survive at any width, sub-structure folds and SAYS SO") {
    for maxKeys <- Vector(1, 2, 3) do
      for n <- Vector(1, maxKeys, maxKeys + 1, 2 * maxKeys + 1, 4 * maxKeys) do
        val c = wideStructured(n)
        val w = Cert.widen(c, 0, maxKeys)                       // depth budget off
        // SOUNDNESS FIRST, at every n: every named path survives.
        assert(paths(c, 6).forall(w.admits),
               s"maxKeys=$maxKeys n=$n: the fold dropped a path: ${c.show} -> ${w.show}")
        // THE NAMES SURVIVE AT EVERY n.  This is the property both flat channels lost at a fixed
        // size, and it is the only thing a disjointness argument needs.
        assertEquals(w.headNames, Some((0 until n).map(i => s"k$i").toSet),
                     s"maxKeys=$maxKeys n=$n: the fold must keep the head NAMES: ${w.show}")
        assertEquals(w.headBound, n.toLong)
        if n <= maxKeys then
          assertEquals(w, c, s"maxKeys=$maxKeys n=$n: inside the budget, widen is the identity")
          assertEquals(w.degradationsBelow, Set.empty[Degradation],
                       s"maxKeys=$maxKeys n=$n: nothing fired, so nothing may be recorded")
          // and the PER-KEY sub-structure is intact below the budget
          for i <- 0 until n do
            assert(w.under(s"k$i").admits(List(s"t$i", s"u$i")),
                   s"maxKeys=$maxKeys n=$n: key k$i lost its own sub-trie: ${w.show}")
            assert(!w.under(s"k$i").admits(List(s"t${(i + 1) % n}", s"u${(i + 1) % n}")) || n == 1,
                   s"maxKeys=$maxKeys n=$n: key k$i sees another key's sub-trie below the budget")
        else
          assert(w.degradationsBelow.contains(Degradation.WidthFold),
                 s"maxKeys=$maxKeys n=$n: over the budget and no WidthFold recorded: " +
                 s"${Degradation.show(w.degradationsBelow)} on ${w.show}")
          // what the fold gave up, stated as a check: every key now sees the JOIN, so the per-key
          // sub-structure is gone and the aggregate is still a bound
          val shared = w.under("k0")
          for i <- 1 until n do assertEquals(w.under(s"k$i"), shared,
            s"maxKeys=$maxKeys n=$n: the fold must leave ONE shared sub-trie: ${w.show}")
        assert(Cert.withinBudget(w, 0, maxKeys),
               s"maxKeys=$maxKeys n=$n: widen left its own budget violated: ${w.show}")

      // A PURE NAME SET IS NEVER FOLDED, at any width — zero distinct sub-tries, nothing to bound.
      for n <- Vector(maxKeys + 1, 10 * maxKeys + 7) do
        val nm = wideNames(n)
        assertEquals(Cert.widen(nm, 0, maxKeys), nm,
                     s"maxKeys=$maxKeys n=$n: a pure name set has no sub-structure to fold")
        assertEquals(nm.degradationsBelow, Set.empty[Degradation])
    println("CERTBUDGET: width rule checked at maxKeys ∈ {1,2,3}, n up to 4·maxKeys, names exact at every n")
  }

  test("WIDTH: the GROWTH CLASS of a key-disjoint union does not move at Shape.CertKeys") {
    // THE FAMILY THE CLIFF ACTUALLY BROKE.  `n` keys on each side, disjoint, one path each: the truth
    // is that the merge rejects at the root and allocates nothing, at every `n`.  Both flat channels
    // reported that below their cap and `Θ(n)` above it — first at `MaxHeads` = 12, then at
    // `MaxSpillKeys` = 4096.  The list crosses `Shape.CertKeys` in both directions.
    val ns = Vector(4, 12, 13, 64, 1024, Shape.CertKeys - 1, Shape.CertKeys, Shape.CertKeys + 1,
                    3 * Shape.CertKeys)
    var shown = Vector.empty[String]
    for n <- ns do
      val l = sv((0 until n).map(i => pv(s"a$i")))
      val r = sv((0 until n).map(i => pv(s"b$i")))
      val tl = ty(l)
      val s = SpatialFrontier.binary(FrontierOp.Intersection, tl, ty(r))
      shown :+= f"n=$n%-6d rebuilt=${s.rebuilt.show}%-10s |Q|=${s.depth.pairedTotal.show}%-10s " +
                f"cases=${s.cases.toVector.map(_.toString).sorted.mkString(",")}%-8s " +
                f"cert=${Degradation.show(tl.shape.certDegradations)}"
      // (1) exact disjointness, on BOTH sides of the budget
      assertEquals(s.cases, Set(FrontierCase.Empty),
                   s"n=$n: a key-disjoint intersection must be PROVED empty: ${s.show}")
      assertEquals(s.rebuilt.hi, 0L, s"n=$n: and allocate nothing: ${s.show}")
      assert(s.rootOnly, s"n=$n: nothing below the root is paired: ${s.show}")
      // (3) the growth class: the prediction is the same NUMBER at every n, so the slope is 0
      assertEquals(tl.shape.possibleHeads.map(_.size), Some(n),
                   s"n=$n: the head set must stay exactly enumerable: ${tl.shape.show}")
      // and above the width cap the certificate is genuinely the thing answering
      if n > Shape.MaxHeads then
        assert(!tl.shape.headsClosed && tl.shape.certBounded,
               s"n=$n: the root must be OPEN with a certificate, or this row proves nothing")
      // (2) …and a pure name set is not degraded at ANY of these widths
      assertEquals(tl.shape.certDegradations, Set.empty[Degradation],
                   s"n=$n: a name set must not be degraded — the width fold bounds sub-tries, and " +
                   s"this family has none: ${tl.shape.show}")
    println(s"CERTBUDGET: key-disjoint intersection across Shape.CertKeys = ${Shape.CertKeys} — FLAT:")
    for l <- shown do println("    " + l)
  }

  // ================================================================================================
  // 2.  THE DEPTH BUDGET
  // ================================================================================================
  test("DEPTH, below and above: the levels above the cut are intact, the cut SAYS SO") {
    for maxDepth <- Vector(1, 2, 4) do
      for d <- Vector(0, maxDepth - 1, maxDepth, maxDepth + 1, 2 * maxDepth + 2).filter(_ >= 0) do
        val c = deep(d)
        val w = Cert.widen(c, maxDepth, 0)                      // width budget off
        assert(paths(c, 3 * maxDepth + 6).forall(w.admits),
               s"maxDepth=$maxDepth d=$d: the cut dropped a path: ${c.show} -> ${w.show}")
        assert(Cert.withinBudget(w, maxDepth, 0),
               s"maxDepth=$maxDepth d=$d: widen left its own budget violated: ${w.show}")
        // EVERY LEVEL ABOVE THE CUT IS INTACT — the cut keeps the levels it did not reach, which is
        // the difference between a depth budget and a degradation to ⊤.
        var cur = w
        for i <- 0 until math.min(d, maxDepth - 1) do
          val name = s"p${d - i}"                               // the spine's OUTERMOST key is p_d
          assertEquals(cur.headNames, Some(Set(name)),
                       s"maxDepth=$maxDepth d=$d: level $i ($name) lost its name: ${w.show}")
          cur = cur.under(name)
        if Cert.withinBudget(c, maxDepth, 0) then
          assertEquals(w, c, s"maxDepth=$maxDepth d=$d: inside the budget, widen is the identity")
          assertEquals(w.degradationsBelow, Set.empty[Degradation],
                       s"maxDepth=$maxDepth d=$d: nothing fired, so nothing may be recorded")
        else
          assert(w.degradationsBelow.contains(Degradation.DepthCut),
                 s"maxDepth=$maxDepth d=$d: over the budget and no DepthCut recorded: " +
                 s"${Degradation.show(w.degradationsBelow)} on ${w.show}")
    println("CERTBUDGET: depth rule checked at maxDepth ∈ {1,2,4}, d up to 2·maxDepth+2")
  }

  test("DEPTH: the GROWTH CLASS of a key-disjoint union does not move at Shape.CertDepth") {
    // the same key-disjoint family, but growing the SHARED PREFIX rather than the branching, so the
    // divergence lands past `Shape.MaxDepth` and then past `Shape.CertDepth`.  The truth is `d`
    // rebuilt nodes — one per spine level — and the prediction has to be `d` on both sides of the
    // certificate's own depth budget, not just below it.
    var shown = Vector.empty[String]
    for d <- Vector(1, Shape.MaxDepth, Shape.MaxDepth + 1, Shape.CertDepth - 1, Shape.CertDepth,
                    Shape.CertDepth + 1, 2 * Shape.CertDepth) do
      val pre = (1 until d).map(i => s"p$i").toList
      val l = sv((0 until 4).map(i => PathValue(pre :+ s"a$i")))
      val r = sv((0 until 4).map(i => PathValue(pre :+ s"b$i")))
      val s = SpatialFrontier.binary(FrontierOp.Union, ty(l), ty(r))
      shown :+= f"d=$d%-4d rebuilt=${s.rebuilt.show}%-12s |Q|=${s.depth.pairedTotal.show}%-12s " +
                f"src=${s.source.show}%-12s cert=${Degradation.show(ty(l).shape.certDegradations)}"
      assert(s.rebuilt.hi >= d.toLong, s"d=$d: UNSOUND, below the truth: ${s.show}")
      if d <= Shape.CertDepth then
        // BELOW THE BUDGET: exact.  This is the range the old flat certificate lost at
        // `Shape.MaxDepth` = 4, and the whole depth range up to `certDepth` is now free of it.
        assertEquals(s.rebuilt.hi, d.toLong,
                     s"d=$d: the rebuild count must be EXACT up to Shape.CertDepth " +
                     s"(= ${Shape.CertDepth}) — the certificate carries every level to there: ${s.show}")
      else
        // ABOVE IT: the divergence lands below the cut, so the claim there is ⊤ and the prediction
        // over-counts.  WHAT MUST NOT CHANGE IS THE GROWTH CLASS, which is what `1C.6` asks: the
        // prediction stays LINEAR in `d` with a bounded constant.  MEASURED over
        // d = 13 … 2·certDepth: `hi = 2d + 1`, so `2d + 2` holds at every row and a super-linear
        // regression fails here.  The old flat certificate changed the class at `MaxDepth` instead
        // of the constant, which is the difference this row exists to hold onto.
        assert(s.rebuilt.hi <= 2 * d.toLong + 2,
               s"d=$d: past Shape.CertDepth the over-prediction must stay LINEAR in d " +
               s"(measured 2d+1); it grew, which is a growth-class regression: ${s.show}")
    println(s"CERTBUDGET: key-disjoint union across Shape.CertDepth = ${Shape.CertDepth} — " +
            s"exact to d = ${Shape.CertDepth}, linear past it:")
    for l <- shown do println("    " + l)
  }

  // ================================================================================================
  // 3.  THE RECORD REACHES THE PRICED RESULT
  // ================================================================================================
  test("a degradation is REPORTED, not just recorded — the cost model reads it") {
    // `1C.5` asks for the degradation to be recorded IN THE RESULT.  The record lives on the `Cert`
    // value, `Shape.certDegradations` rolls it up, and `SpatialCost.refine` turns it into an
    // assumption on the report.  This is the end-to-end check that the wiring exists: a shape whose
    // certificate was folded must reach `Shape.certDegradations` non-empty.
    val folded = Cert.widen(wideStructured(8), 0, 2)
    assert(folded.degradationsBelow.contains(Degradation.WidthFold), folded.show)
    val sh = Shape.ofCert(folded)
    assert(sh.certDegradations.contains(Degradation.WidthFold),
           s"the record must survive the trip back into the shape domain: ${sh.show}")
    // and the exact certificate reports nothing, so the channel is not noise
    assertEquals(Shape.ofCert(wideStructured(2)).certDegradations, Set.empty[Degradation])
    println(s"CERTBUDGET: ${Degradation.show(sh.certDegradations)} reported through Shape.certDegradations")
  }

  test("1C.7: the certificate's OWN cost is priced in the frontier summary") {
    // The tier's benefit is priced all over `SpatialFrontier`; its cost has to be too, or the
    // accounting is one-sided.  `Cert.costNote` names the four quantities and the operation each one
    // prices, and `SpatialFrontier` puts it in the summary's notes.
    val n = 64
    val l = sv((0 until n).map(i => pv(s"a$i")))
    val r = sv((0 until n).map(i => pv(s"b$i")))
    val s = SpatialFrontier.binary(FrontierOp.Intersection, ty(l), ty(r))
    val note = s.notes.find(_.startsWith("certificate:"))
    assert(note.isDefined,
           s"the certificate's cost must be quoted where its benefit is: ${s.notes.mkString(" | ")}")
    for x <- note do
      println("CERTBUDGET: " + x)
      assert(x.contains("trie nodes retained"), x)     // construction + retained memory
      assert(x.contains("one map probe per level"), x) // lookup
      assert(x.contains("key-set intersection"), x)    // intersection
      assert(x.contains("the claim is exact"), x)      // and the degradation record, here empty
    // a ⊤ certificate on both sides costs nothing and says nothing
    assertEquals(Cert.costNote(Cert.top, Cert.top), None)
    // and a degraded one says so in the same line
    val dgNote = Cert.costNote(Cert.widen(wideStructured(8), 0, 2), Cert.top)
    assert(dgNote.exists(_.contains("DEGRADED by a budget rule")), dgNote.toString)
  }

  test("both budgets at once: the two rules compose and both are recorded") {
    // deep AND wide, past both budgets — the case where one rule's output is the other's input, and
    // where the fold's re-widening (`Cert.widen`'s note) has to hold.
    // TWO MISTAKES THIS SHAPE AVOIDS, both of which the first drafts made:
    //  * the six sub-tries must be DISTINCT, or there is nothing to fold — interning makes six equal
    //    `deep(5)`s ONE object and `distinctSubs` is then 1;
    //  * they must differ ABOVE the depth cut.  With the difference only at the leaf, the depth rule
    //    truncates all six to the same prefix, `distinctSubs` drops to 1, and the width rule never
    //    fires — the depth cut SUBSUMES it, which is correct behaviour and a vacuous test.
    // So each key branches immediately (`t_i`, inside `maxDepth`) and then runs deep (past it).
    val c = Cert.of(false, SortedMap.from((0 until 6).map(i =>
              s"k$i" -> Cert.of(false, SortedMap(s"t$i" -> deep(5)), Outside.Closed))),
                    Outside.Closed)
    val w = Cert.widen(c, 3, 2)
    assert(paths(c, 12).forall(w.admits), s"the composed widening dropped a path: ${w.show}")
    assert(Cert.withinBudget(w, 3, 2), s"the composed widening violated its own budgets: ${w.show}")
    assertEquals(w.headNames, Some((0 until 6).map(i => s"k$i").toSet),
                 s"the names must survive both rules: ${w.show}")
    val ds = w.degradationsBelow
    assert(ds.contains(Degradation.WidthFold) && ds.contains(Degradation.DepthCut),
           s"both rules fired and both must be recorded: ${Degradation.show(ds)} on ${w.show}")
    println(s"CERTBUDGET: composed rules recorded as ${Degradation.show(ds)}")
  }
end SpatialCertBudgetCheck
