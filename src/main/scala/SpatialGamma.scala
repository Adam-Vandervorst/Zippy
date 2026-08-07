package morkl

/** THE SEMANTIC LAYER OF THE SPATIAL DOMAIN — γ, α, the order that IS γ-containment, and the lattice
 *  operations of the HISTOGRAM component.
 *
 *  ==WHO OWNS WHAT (review.md 6)==
 *  This file is the OWNER of the length-histogram component's laws — [[gammaSpace]], [[leqSpace]],
 *  [[lubSpace]], [[meetSpace]] — because `SpaceType`'s own file (SpatialTypes.scala) carries the
 *  count TRANSFERS and its normalisation, and there was nowhere else the four semantic operations
 *  could live without a third spelling.  Everything else here DELEGATES and states nothing of its
 *  own:  the shape's γ/order/join/meet/widening belong to [[Shape]], and the product's to
 *  [[SpatialType]].  The `gammaShape`/`leqShape`/`lubShape` entry points below are one-line
 *  forwarders kept for their call sites, not second implementations.
 *
 *  The operator table, the finite universes and the grounded fixtures now live in
 *  [[SpatialGamma.TestOnly]] and are re-exported for source compatibility; nothing in the production
 *  analysis path may read them (review.md 6 — they were only ever consumed by tests).
 *
 *  review.md 6 asks for the law family the corpus is missing:
 *
 *      eval(s, concreteEnv) ∈ γ(infer(s, abstractEnv))          -- per-operator simulation
 *      γ(a op# b) ⊇ γ(a) op γ(b)                                 -- local soundness of a transfer
 *      specialize(s, facts) ≡ s under facts                      -- conditional rewrite
 *
 *  None of those can even be *stated* until γ is a concrete, total, executable predicate on the
 *  actual abstract carrier ([[SpatialType]] = [[Shape]] × [[SpaceType]]).  That is what this file
 *  provides; `SpatialLawCheck` is the executable checker and `proofs/spatial-semantic/` holds the
 *  finite-first-order fragments discharged by z3.
 *
 *  ==NO EVALUATION==
 *  Nothing here calls `eval`/`evalI`/`evalT`/`exec*`.  γ is a *predicate on a value that the caller
 *  already has*, not a way to obtain one; α abstracts a value the caller already has.  Neither is
 *  reachable from any transfer in `SpatialTypes`/`SpatialTyping`, and the operator table below is
 *  data (constructors), not an interpreter.  The only place evaluation happens is the *test*, which
 *  is allowed to use it as ground truth.
 *
 *  ==WHAT γ MEANS HERE==
 *  Two readings of the shape component are provided, because the code is ambiguous about which one
 *  it implements and the difference is exactly where the must/may bugs live:
 *
 *    - [[gammaShape]] (STRONG): `eps = Must` means ε really is a member, a tracked head whose child
 *      forces ε means that path really is present, and `others.lo` is a real lower bound on the
 *      number of untracked heads.  This is the reading `Shape.restrict` needs (`prefixes.eps.mustBe
 *      ⇒ result = x`) and the one `Shape.of` produces for a literal.
 *    - [[gammaShapeMay]] (WEAK, = strong γ of [[weakenAll]]): every Must is demoted to May and every
 *      `others.lo` to 0.  This is the reading the class comment on `Shape.definitelyNonEmpty`
 *      claims ("V1 IS MAY-ONLY"), and it is what `Fact`, `headCount`, `mayHavePrefix` and
 *      `isProvablyEmpty` actually consume.
 *
 *  `SpatialLawCheck` reports both, separately, per operator.  A transfer that is sound for the weak
 *  reading but not the strong one is not "nearly sound": it means the Must channel leaks and must
 *  not be consumed. */
object SpatialGamma:
  import scala.collection.immutable.SortedMap
  import Lower.{LenBounds, SizeBounds}

  // ==============================================================================================
  // 1. CONCRETIZATION
  // ==============================================================================================

  /** γ for the LENGTH-INDEXED COUNT component.
   *
   *  `v ∈ γ(t)` iff every tracked class brackets the concrete count of paths of that length, every
   *  concrete length is either tracked or inside the spill window, and the TOTAL count at untracked
   *  lengths lies in the spill interval.  This is the representation invariant `SpaceType.at` and
   *  `SpaceType.size` already assume (see the `disjoin` comment in SpatialTypes.scala) read as a
   *  membership predicate. */
  def gammaSpace(t: SpaceType, v: SpaceValue): Boolean =
    val cnt: Map[Long, Long] =
      v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap
    val trackedOk = t.byLen.forall { (l, c) => val n = cnt.getOrElse(l, 0L); c.lo <= n && n <= c.hi }
    if !trackedOk then false
    else
      val residual = cnt.filter((l, _) => !t.byLen.contains(l))
      val lensOk = residual.forall { (l, n) =>
        n == 0L || (t.rest.hi > 0 && !t.restLens.isEmpty && t.restLens.lo <= l && l <= t.restLens.hi) }
      var tot = 0L
      for (_, n) <- residual do tot = Ivl.add(tot, n)
      lensOk && t.rest.lo <= tot && tot <= t.rest.hi

  /** THE HISTOGRAM MEET.  `Some(c)` with `γ(a) ∩ γ(b) ⊆ γ(c)`; `None` PROVES the intersection empty.
   *  The two operands are sound approximations of the SAME concrete space, so per length class both
   *  brackets hold and the tighter one survives.  Two subtleties, both about the single spill bucket:
   *
   *    - a length one side TRACKS and the other only covers with its spill becomes a tracked class of
   *      the result, whose interval is `[max lo, min hi]` — `at(l)` already answers `[0, rest.hi]` for
   *      the spill side, which is the sound reading;
   *    - the result's spill counts the paths at lengths NEITHER side tracks.  Its upper is the min of
   *      the two spill uppers.  Its LOWER cannot be `max` of the two spill lowers: some of the paths
   *      a side's spill was counting may now sit in a class the OTHER side contributed, so a side's
   *      lower bound only survives when the result tracks nothing new inside that side's window. */
  def meetSpace(a: SpaceType, b: SpaceType): Option[SpaceType] =
    val keys = (a.byLen.keySet ++ b.byLen.keySet).toVector.sorted
    var bad = false
    val cls = keys.map { l =>
      val x = a.at(l); val y = b.at(l)
      val i = Ivl(x.lo max y.lo, x.hi min y.hi)
      if i.lo > i.hi then bad = true
      l -> i
    }
    if bad then None
    else
      def newlyTracked(t: SpaceType): Boolean =
        t.rest.hi > 0 && !t.restLens.isEmpty &&
          keys.exists(l => !t.byLen.contains(l) && t.restLens.lo <= l && l <= t.restLens.hi)
      def resid(t: SpaceType): Ivl =
        if t.rest.hi == 0 then Ivl.zero
        else Ivl(if newlyTracked(t) then 0L else t.rest.lo, t.rest.hi)
      val (ra, rb) = (resid(a), resid(b))
      val rest = Ivl(ra.lo max rb.lo, ra.hi min rb.hi)
      if rest.lo > rest.hi then None
      else
        val win =
          if rest.hi == 0 then LenBounds.empty
          else LenBounds(a.restLens.lo max b.restLens.lo, a.restLens.hi min b.restLens.hi)
        if rest.lo >= 1 && win.isEmpty then None
        else
          val live = cls.filter(_._2.hi > 0)
          // a class the meet zeroes must not be re-admitted by the spill window, so a window that
          // spans it would be a widening: `SpatialTypes.widen` re-establishes disjointness by folding
          // such a class INTO the bucket, which only ever loosens (sound for the ⊇ direction).
          Some(SpatialTypes.widen(SpaceType(SortedMap.from(live),
                                            if win.isEmpty then Ivl.zero else rest,
                                            if win.isEmpty then LenBounds.empty else win)))

  /** γ for the SHAPE component, STRONG reading (Must is a real must) — the ONE implementation lives
   *  in the domain that owns the carrier ([[Shape.contains]]); this is a forwarder so the law
   *  statements in this file read as one piece. */
  def gammaShape(sh: Shape, v: SpaceValue): Boolean = Shape.contains(sh, v)

  /** drop EVERY must claim from a shape, at every depth: `Must ↦ May`, `others.lo ↦ 0`.  The
   *  code's own `Shape.weaken` stops at `MaxDepth` and keeps `definitelyEmpty` nodes intact; this
   *  one is total, because γ must be. */
  def weakenAll(s: Shape): Shape = weakenAll(s, 64)
  private def weakenAll(s: Shape, d: Int): Shape =
    if d <= 0 then Shape.top
    else Shape(if s.eps == Presence.Must then Presence.May else s.eps,
               SortedMap.from(s.heads.view.mapValues(weakenAll(_, d - 1))),
               Ivl(0, s.others.hi), s.otherTail.map(weakenAll(_, d - 1)))

  /** γ for the shape, WEAK (may-only) reading. */
  def gammaShapeMay(sh: Shape, v: SpaceValue): Boolean = gammaShape(weakenAll(sh), v)

  /** γ for the reduced product — the predicate review.md 6 asks for.  The product's own γ
   *  ([[SpatialType.accepts]]) additionally checks the two REDUCED PROJECTIONS, so it is the
   *  stronger predicate and the one the gates use; this is the componentwise conjunction the law
   *  statements in this file are written against. */
  def gamma(t: SpatialType): SpaceValue => Boolean =
    v => !t.uninhabited && gammaShape(t.shape, v) && gammaSpace(t.lens, v)
  /** the may-only variant (shape Musts demoted; the histogram is unchanged) */
  def gammaMay(t: SpatialType): SpaceValue => Boolean =
    v => gammaShapeMay(t.shape, v) && gammaSpace(t.lens, v)

  // ==============================================================================================
  // 2. ABSTRACTION
  // ==============================================================================================

  /** the POINT abstraction — exactly what the analysis uses for a `Literal`. */
  def alpha(v: SpaceValue): SpatialType = SpatialType.of(v)

  /** the SET abstraction α : ℘(SpaceValue) → SpatialType, the lub of the point abstractions.  This
   *  is the α of the Galois connection; `alpha` above is its restriction to singletons.  An empty
   *  set has no least abstraction in a domain without a syntactic ⊥, so it maps to `SpaceType.empty`
   *  paired with `Shape.empty` (γ = {∅}), which is the least element that is actually representable
   *  — stated, not hidden, because it makes α(∅) NOT the true bottom. */
  def alphaSet(vs: Iterable[SpaceValue]): SpatialType =
    if vs.isEmpty then SpatialType.empty
    else vs.iterator.map(alpha).reduce(lub)

  // ==============================================================================================
  // 3. THE LATTICE JOIN  (NOT SpatialTypes.join — see the note)
  // ==============================================================================================

  /** THE LUB.  `SpatialTypes.join` is *not* this: it is the UNION TRANSFER (per class it takes
   *  `lo = max(lo_a, lo_b)` and `hi = hi_a + hi_b`, which is right for `|A ∪ B|` and wrong for a
   *  join — `γ(a) ⊄ γ(join(a,b))` whenever `lo_b > lo_a`).  The `Fixpoint` transfer's
   *  `join(t, F#(t)).within(t)` check therefore compares against a union, which is what the
   *  concrete `Fixpoint` accumulates, so the usage is coherent; but the name in
   *  docs/design_spatial_lattice.md §2 ("join/meet are the lub/glb") does not describe the code's
   *  `join`.  See `proofs/spatial-semantic/gsem_join_not_lub.smt2`. */
  def lub(a: SpatialType, b: SpatialType): SpatialType = SpatialType.join(a, b)

  /** the shape lub.  There is exactly ONE implementation and it lives in the domain that owns the
   *  carrier ([[Shape.lub]]) — the `Fixpoint` transfer needs the same join this file's laws check, and
   *  two spellings of a join is how the two-orders confusion above got in in the first place.  Its
   *  channel-by-channel justification is on `Shape.lub`; the essentials: `others` takes the MAX of the
   *  two uppers and no lower bound (`U_result(V) ⊆ U_side(V)`), the ε channel becomes `May` unless the
   *  two agree, and `otherTail` must admit both sides' summaries.  `Shape.mk` re-establishes the
   *  MAY-ONLY `otherTail` invariant every transfer in SpatialShape.scala relies on
   *  (`proofs/spatial-semantic/gsem_l2_union_sound.smt2` is refuted without it: an untracked head of
   *  one operand need not be present in the other, so a Must in the summary would be attributed to a
   *  head whose tail-set is empty on that side). */
  def lubShape(a: Shape, b: Shape): Shape = Shape.joinAlternatives(a, b)

  /** the histogram lub.  Only the classes tracked on BOTH sides keep exact per-class information
   *  (elsewhere one side's count is hidden inside a spill aggregate); everything else is folded
   *  into one residual bucket whose interval is derived from the two size projections. */
  def lubSpace(a: SpaceType, b: SpaceType): SpaceType =
    if a.rest.hi == 0 && b.rest.hi == 0 then
      val keys = (a.byLen.keySet ++ b.byLen.keySet).toVector
      SpatialTypes.widen(SpaceType(SortedMap.from(keys.map { l =>
        val (x, y) = (a.at(l), b.at(l)); l -> Ivl(x.lo min y.lo, x.hi max y.hi) }),
        Ivl.zero, LenBounds.empty))
    else
      val keys = (a.byLen.keySet intersect b.byLen.keySet).toVector
      val kept = keys.map { l => val (x, y) = (a.at(l), b.at(l)); l -> Ivl(x.lo min y.lo, x.hi max y.hi) }
      def outside(t: SpaceType): Ivl =
        var loK = 0L; var hiK = 0L
        for l <- keys do { val c = t.at(l); loK = Ivl.add(loK, c.lo); hiK = Ivl.add(hiK, c.hi) }
        val s = t.size
        val lo = if s.lo == Ivl.INF || hiK == Ivl.INF then 0L else Ivl.relu(s.lo - hiK)
        val hi = if s.hi == Ivl.INF then Ivl.INF else Ivl.relu(s.hi - loK)
        Ivl(lo, hi)
      val (oa, ob) = (outside(a), outside(b))
      val r = Ivl(oa.lo min ob.lo, oa.hi max ob.hi)
      def win(t: SpaceType): LenBounds =
        val ls = t.byLen.keysIterator.filter(l => !keys.contains(l) && t.at(l).hi > 0).toVector
        val lo0 = if t.rest.hi > 0 then t.restLens.lo else LenBounds.INF
        val hi0 = if t.rest.hi > 0 then t.restLens.hi else 0L
        if ls.isEmpty then LenBounds(lo0, hi0) else LenBounds(lo0 min ls.min, hi0 max ls.max)
      val (wa, wb) = (win(a), win(b))
      val w = if wa.isEmpty then wb else if wb.isEmpty then wa else LenBounds(wa.lo min wb.lo, wa.hi max wb.hi)
      if r.hi == 0 then SpatialTypes.widen(SpaceType(SortedMap.from(kept), Ivl.zero, LenBounds.empty))
      else SpatialTypes.widen(SpaceType(SortedMap.from(kept), r, if w.isEmpty then LenBounds.unknown else w))

  // ==============================================================================================
  // 4. THE ORDER
  // ==============================================================================================

  /** `leq(a, b)` ⇒ `γ(a) ⊆ γ(b)`.  This is the domain order *as γ-containment*, decided
   *  structurally: no upper-envelope shortcut, both endpoints of every class, the spill aggregate
   *  in both directions, and the shape's ε/head/`others`/`otherTail` channels.
   *
   *  It is SOUND (the implication above is what `SpatialLawCheck` checks exhaustively on a finite
   *  universe of concrete values) and INCOMPLETE: it does not attempt the integer-partition
   *  reasoning that would be needed to decide containment exactly when a spill bucket on one side
   *  faces tracked classes on the other.  `SpatialLawCheck` measures the incompleteness against
   *  [[gammaLeqOn]], which decides containment EXACTLY on a finite universe.
   *
   *  ==HOW `SpaceType.within` DIFFERS==
   *  `within` compares UPPER envelopes only (`at(l).hi ≤ that.at(l).hi`, `rest.hi ≤ that.rest.hi`)
   *  and ignores every lower bound.  So `within` is strictly weaker than `leq` and does NOT imply
   *  γ-containment: `{len 1: [0,3]}.within({len 1: [2,5]})` holds, yet the concrete value ∅ is in
   *  γ of the first and not of the second.  (`proofs/spatial/sp_gamma_order.smt2` already refutes
   *  the envelope-only reading for a single interval; `gsem_within_not_containment.smt2` restates
   *  it for the class-indexed type with a spill bucket, and `SpatialLawCheck` exhibits the concrete
   *  witness.)  `within` is used only as the `Fixpoint` post-fixpoint test, where the lower bounds
   *  are re-supplied from `init` — so what it licenses is the upper half, exactly as
   *  docs/design_spatial_lattice.md §4 says. */
  def leq(a: SpatialType, b: SpatialType): Boolean = SpatialType.leq(a, b)

  // ----------------------------------------------------------------------------------------------
  // THE CANONICAL FORM OF A HISTOGRAM  (review.md 4, second half)
  // ----------------------------------------------------------------------------------------------
  /** THE γ-PRESERVING CANONICAL FORM.  `γ(canonSpace(t)) = γ(t)`, EXACTLY — not ⊇, not ⊆.  It is not
   *  a widening and not a reduction; it rewrites the REPRESENTATION so that two types denoting the
   *  same set of concrete spaces are compared through the same length partition.  Three rewrites,
   *  each exact:
   *
   *    1. A spill bucket whose window admits exactly ONE untracked length `w` is exactly the tracked
   *       class `w ↦ rest`: γ's clause "the total at untracked lengths lies in `rest`, and they all
   *       lie in the window" degenerates to "the count at `w` lies in `rest`".  This is the rewrite
   *       review.md 4 asks for — it ALIGNS a spilled partition with a tracked one — and the exact
   *       count-vector measurement in `SpatialLawCheck` attributes 28 of the 29 non-vacuous false
   *       negatives to the pair of partitions it repairs.  (If the window admits NO untracked length
   *       the bucket is vacuous and disappears — or, when something is forced into it, the type is
   *       ⊥ and [[unsatSpace]] says so.)
   *    2. Exactly ONE path has length 0 (ε is unique), so an ε class may not permit two.  `hi` is
   *       clamped to 1.  A `lo ≥ 2` is left alone: that type is ⊥, and clamping would have to
   *       represent ⊥, which this function must not invent.
   *    3. A spill bucket that can hold nothing, and a class that neither permits nor forces anything,
   *       carry no information and are dropped — again only when nothing is FORCED, so ⊥ survives
   *       as ⊥.
   *
   *  IDEMPOTENT: after (1) the window admits ≥2 untracked lengths or is gone, after (2) the ε class
   *  permits ≤1, after (3) there is no empty bucket and no dead class — so a second application
   *  changes nothing.  Both properties are checked executably (`SpatialLawCheck`, "canonSpace
   *  preserves γ exactly and is idempotent"). */
  def canonSpace(t: SpaceType): SpaceType =
    var by = t.byLen; var rest = t.rest; var win = t.restLens
    // (1) align a spilled partition with a tracked one.  Counted, not collected: this runs on the
    // order's hot path (`SpatialType.leq` inside every fixpoint), so it allocates nothing.
    var dirty = false
    if rest.hi > 0 && !win.isEmpty && win.hi != LenBounds.INF && win.hi - win.lo < 64L then
      var free = 0L; var n = 0; var l = win.lo
      while l <= win.hi && n <= 1 do
        if !by.contains(l) then { free = l; n += 1 }
        l += 1
      if n == 1 then { by = by.updated(free, rest); rest = Ivl.zero; win = LenBounds.empty; dirty = true }
      else if n == 0 && rest.lo == 0 then { rest = Ivl.zero; win = LenBounds.empty; dirty = true }
    // (3a) a bucket that cannot hold anything is not a bucket
    if rest.hi == 0 && rest.lo == 0 then
      if !win.isEmpty then { win = LenBounds.empty; dirty = true }
    else if win.isEmpty && rest.lo == 0 then
      if rest != Ivl.zero then { rest = Ivl.zero; dirty = true }
    // (2) ε is unique
    by.get(0L) match
      case Some(c) if c.hi > 1 && c.lo <= 1 => by = by.updated(0L, Ivl(c.lo, 1)); dirty = true
      case _ => ()
    // (3b) a class that permits nothing and forces nothing says nothing — unless the window would
    // then re-admit that length, which the disjointness invariant rules out but this does not assume.
    // Guarded by a short-circuiting `exists` so the common case allocates no new map.
    val covered = (l: Long) => rest.hi > 0 && !win.isEmpty && win.lo <= l && l <= win.hi
    if by.exists((l, c) => c.hi == 0 && c.lo == 0 && !covered(l)) then
      by = by.filter((l, c) => c.hi > 0 || c.lo > 0 || covered(l)); dirty = true
    if dirty then SpaceType(by, rest, win) else t

  /** A SOUND syntactic proof that NO concrete space is admitted: `true` ⇒ `γ(t) = ∅`.  Deliberately
   *  incomplete — it exists because `⊥ ⊑ everything` and the order could not see it: on the exact
   *  count-vector universe an unsatisfiable left-hand side was 1711 of 1740 false negatives, and
   *  every one of those 1711 was the same missed fact, that only one path has length 0. */
  def unsatSpace(t: SpaceType): Boolean = unsatCanon(canonSpace(t))
  /** the same on a type already in canonical form — so the order pays for one `canonSpace`, not two */
  private def unsatCanon(c: SpaceType): Boolean =
    c.byLen.exists((_, i) => i.lo > i.hi) || c.byLen.get(0L).exists(_.lo >= 2) ||
      c.rest.lo > c.rest.hi || (c.rest.lo >= 1 && c.restLens.isEmpty)

  def leqSpace(a: SpaceType, b: SpaceType): Boolean = leqSpaceMask(a, b) == 0

  /** WHY [[leqSpace]] said no — the bit positions of [[leqSpaceMask]].  There is no second
   *  implementation of the order here: `leqSpace` IS `leqSpaceMask == 0`, and the mask exists so the
   *  incompleteness measurement in `SpatialLawCheck` can attribute a false negative to a channel
   *  instead of guessing.  (review.md 4: "find the actual cause with a measurement".) */
  object LeqSpaceWhy:
    val PointwiseHi = 1   // some length where `a` permits more paths than `b` does
    val PointwiseLo = 2   // some length where `b` FORCES more paths than `a` guarantees
    val Window = 4        // `a`'s spill window is not inside `b`'s spill window
    val AggHi = 8         // the aggregate at b-untracked lengths exceeds `b.rest.hi`
    val AggLo = 16        // `b.rest.lo` is not discharged by the aggregate
    val names: Vector[(Int, String)] = Vector(PointwiseHi -> "space:pointwise-hi",
      PointwiseLo -> "space:pointwise-lo", Window -> "space:window", AggHi -> "space:agg-hi",
      AggLo -> "space:agg-lo")
    def show(m: Int): Vector[String] = names.collect { case (bit, n) if (m & bit) != 0 => n }

  private[morkl] def leqSpaceMask(a0: SpaceType, b0: SpaceType): Int =
    import LeqSpaceWhy.*
    val a = canonSpace(a0)
    if unsatCanon(a) then 0                         // γ(a) = ∅ ⊆ γ(b) for every b
    else
      val b = canonSpace(b0)
      var m = 0
      // ---- (b) PER-LENGTH counts.  `at(0)` can report a spill bucket's whole capacity for length 0,
      // but ε is unique, so ONE is the true ceiling there — on both sides.  (`canonSpace` already
      // clamped a TRACKED ε class; this is the window-covered case it cannot rewrite, because the
      // bucket's capacity is shared with the window's other lengths.)
      def atCapped(t: SpaceType, l: Long): Ivl =
        val c = t.at(l)
        if l == 0L && c.hi > 1L then Ivl(c.lo, 1L) else c
      val keys = (a.byLen.keySet ++ b.byLen.keySet).toVector
      for l <- keys do
        val x = atCapped(a, l); val y = atCapped(b, l)
        if x.hi > y.hi then m |= PointwiseHi
        if y.lo > x.lo then m |= PointwiseLo
      // ---- the FREE lengths of `a`: covered by its spill window and not by a tracked class -------
      val aw = a.restLens
      val aFree = a.rest.hi > 0 && !aw.isEmpty
      /** is there a length in `[lo, hi]` that `a` leaves free and `p` accepts?  The shortcut is exact:
       *  an interval with more integers than the two sides TRACK in total must contain one that
       *  neither names, and `p` holds of every such length at both call sites below. */
      def someFree(lo: Long, hi: Long)(p: Long => Boolean): Boolean =
        if lo > hi then false
        else if hi == LenBounds.INF || hi - lo >= a.byLen.size.toLong + b.byLen.size.toLong then true
        else (lo to hi).exists(l => !a.byLen.contains(l) && p(l))
      val untrackedByB: Long => Boolean = l => !b.byLen.contains(l)
      // ---- (c) SUPPORT.  Every length `a` may put a path at, `b` must permit — by TRACKING it or by
      // covering it with its own spill window.  Requiring `b`'s WINDOW to contain a's was the
      // review.md 4 defect: with `a`'s spill window aligned onto classes `b` tracks, containment can
      // hold with `b` carrying no spill bucket at all.  `canonSpace` has already folded a
      // single-length window into a tracked class, so what remains here is the multi-length case.
      val windowOk =
        !aFree || {
          val bw = b.restLens
          val bHasWin = b.rest.hi > 0 && !bw.isEmpty
          val parts =
            if !bHasWin then Vector((aw.lo, aw.hi))
            else Vector((aw.lo, if bw.lo == 0L then -1L else aw.hi min (bw.lo - 1L)),
                        if bw.hi == LenBounds.INF then (1L, 0L) else (aw.lo max (bw.hi + 1L), aw.hi))
          parts.forall((lo, hi) => !someFree(lo, hi)(untrackedByB))
        }
      if !windowOk then m |= Window
      // ---- (d) the AGGREGATE at lengths `b` does not track ---------------------------------------
      // `a`'s spill mass lands outside `b`'s tracked classes only if some free length of `a` is
      // untracked by `b`; when every free length of `a` is a class of `b`, the whole bucket is
      // absorbed by those classes (each of which the pointwise clause above already checked against
      // `a.rest.hi`, the most that can land at one length) and contributes NOTHING here.
      var hiOut = if aFree && someFree(aw.lo, aw.hi)(untrackedByB) then a.rest.hi else 0L
      // …and symmetrically for the lower bound: `a`'s forced spill mass can hide inside a class `b`
      // tracks, so the guarantee does not survive.  Without this term the order was not even
      // REFLEXIVE for a spill-carrying type (`leqSpace(x, x)` was false whenever `x.rest.lo >= 1`),
      // which the decorated analysis' "root is never weaker than `infer`" law needs.
      var loOut =
        if a.rest.lo == 0 || !aFree then 0L
        else if b.byLen.keysIterator.exists(l => aw.lo <= l && l <= aw.hi && !a.byLen.contains(l)) then 0L
        else a.rest.lo
      for (l, c) <- a.byLen if !b.byLen.contains(l) do
        hiOut = Ivl.add(hiOut, c.hi); loOut = Ivl.add(loOut, c.lo)
      if hiOut > b.rest.hi then m |= AggHi
      if b.rest.lo > loOut then m |= AggLo
      m

  /** the shape half of [[leq]] — the STRONG-γ reading.  One implementation, in the domain that owns
   *  the carrier: [[Shape.leqStrong]] (its may-only sibling is `Shape.leq`, and the table on those two
   *  states the four channels where the readings differ). */
  def leqShape(a: Shape, b: Shape): Boolean = Shape.leqStrong(a, b)

  // ==============================================================================================
  // 5. TEST SUPPORT — NOT part of the analysis (review.md 6)
  // ==============================================================================================

  /** THE FINITE UNIVERSES, THE OPERATOR TABLE, the grounded fixtures and the callee routine.  Only
   *  tests consume these: they are the data the differential matrices and the simulation squares
   *  iterate, and the exhaustive γ-containment decision procedure those matrices measure the order's
   *  incompleteness against.  They live inside an explicitly test-only object so that reading
   *  `SpatialGamma`'s API cannot mistake a generator for an analysis, and so a production dependency
   *  on them is visible as `SpatialGamma.TestOnly.…` at the call site.
   *
   *  MIGRATION: the `export` at the bottom keeps the old unqualified spellings (`SpatialGamma.ops`,
   *  `SpatialGamma.universe`, `import SpatialGamma.*` in `SpatialLawCheck`) compiling.  Once
   *  `SpatialLawCheck` / `SpatialSoundnessHunt` name the object explicitly, delete the export and this
   *  object moves wholesale into test support — nothing in `src/main` refers to it.  (Doing the move
   *  now would break two test files this change does not own.) */
  object TestOnly {

  /** every path over `items` of at most `maxLen` items */
  def allPaths(items: Vector[PathItem], maxLen: Int): Vector[PathValue] =
    var acc = Vector(PathValue(Nil))
    var cur = Vector(PathValue(Nil))
    for _ <- 1 to maxLen do
      cur = cur.flatMap(p => items.map(i => PathValue(p.items :+ i)))
      acc = acc ++ cur
    acc

  /** ALL space values over that path set — the finite universe on which γ-containment is DECIDED
   *  exactly (no envelope shortcut, no sampling).  `|U| = 2^|paths|`, so keep it small:
   *  `universe(Vector("a","b"), 2)` is 2^7 = 128 values. */
  def universe(items: Vector[PathItem], maxLen: Int): Vector[SpaceValue] =
    allPaths(items, maxLen).toSet.subsets().map(SpaceValue.apply).toVector

  /** EXACT γ-containment restricted to `u`: `∀ v ∈ u. v ∈ γ(a) ⇒ v ∈ γ(b)`.  A `false` here is a
   *  genuine refutation of containment; a `true` is containment *on that universe*. */
  def gammaLeqOn(u: Vector[SpaceValue])(a: SpatialType, b: SpatialType): Boolean =
    val ga = gamma(a); val gb = gamma(b)
    u.forall(v => !ga(v) || gb(v))
  def gammaLeqWitness(u: Vector[SpaceValue])(a: SpatialType, b: SpatialType): Option[SpaceValue] =
    val ga = gamma(a); val gb = gamma(b)
    u.find(v => ga(v) && !gb(v))

  // ---- the operator table --------------------------------------------------------------------
  /** binder names used by the binder-carrying operators.  Distinct from the operand names so a
   *  generated body can mention both. */
  val bindSym: PathRef = PathRef("h$")
  val bindRest: SpaceMention = SpaceMention("r$")
  val bindAcc: PathRef = PathRef("acc$")
  val bindRec: SpaceMention = SpaceMention("rec$")
  /** operand slots */
  val opSpaces: Vector[SpaceMention] = Vector("s$0", "s$1").map(SpaceMention.apply)
  val opPaths: Vector[PathRef] = Vector("p$0", "p$1").map(PathRef.apply)

  enum BodyKind:
    case NoBody, Iter, Fold, Fix
  /** One operator of the Space algebra: how many space operands and path operands it takes, what
   *  kind of body (if any) it binds, and how to build the node.  EVERY constructor of `Space` has a
   *  row; `SpatialLawCheck` iterates this table for the simulation squares and prints one line per
   *  row, so a new operator cannot be added to the language without showing up unchecked. */
  final case class Op(name: String, arity: Int, pathArity: Int, body: BodyKind,
                      build: (Vector[Space], Vector[Path], Space) => Space)

  private def P(i: Int)(ps: Vector[Path]): Path = ps(i)

  val ops: Vector[Op] = Vector(
    Op("Empty", 0, 0, BodyKind.NoBody, (_, _, _) => Space.Empty),
    Op("Mention", 1, 0, BodyKind.NoBody, (xs, _, _) => xs(0)),
    Op("Singleton", 0, 1, BodyKind.NoBody, (_, ps, _) => Space.Singleton(ps(0))),
    Op("Union", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Union(xs(0), xs(1))),
    Op("Intersection", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Intersection(xs(0), xs(1))),
    Op("Subtraction", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Subtraction(xs(0), xs(1))),
    Op("Restriction", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Restriction(xs(0), xs(1))),
    Op("Raffination", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Raffination(xs(0), xs(1))),
    Op("Composition", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Composition(xs(0), xs(1))),
    Op("Wrap", 1, 1, BodyKind.NoBody, (xs, ps, _) => Space.Wrap(xs(0), ps(0))),
    Op("Unwrap", 1, 1, BodyKind.NoBody, (xs, ps, _) => Space.Unwrap(xs(0), ps(0))),
    Op("TailsUnion", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.TailsUnion(xs(0))),
    Op("TailsIntersection", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.TailsIntersection(xs(0))),
    Op("Range", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.Range(xs(0), 0, 2)),
    Op("RangeNeg", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.Range(xs(0), -2, 0)),
    Op("RangeExact", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.Range(xs(0), 2, 3)),
    Op("Iteration", 1, 0, BodyKind.Iter, (xs, _, b) => Space.Iteration(xs(0), bindSym, bindRest, b)),
    Op("Fold", 1, 1, BodyKind.Fold, (xs, ps, b) =>
      Space.Fold(xs(0), ps(0), bindAcc, bindSym, bindRest, b, Path.Concat(Path.Deref(bindAcc), Path.Deref(bindSym)))),
    Op("Fixpoint", 1, 0, BodyKind.Fix, (xs, _, b) => Space.Fixpoint(xs(0), bindRec, b)),
    Op("Call", 2, 1, BodyKind.NoBody, (xs, ps, _) => Space.Call(callee, Vector(ps(0)), xs)),
    Op("GroundedPS", 0, 1, BodyKind.NoBody, (_, ps, _) => Space.GroundedPS(ps(0), groundedPS)),
    Op("GroundedSS", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.GroundedSS(xs(0), groundedSS)))

  /** the callee used by the `Call` row: a fixed, deterministic two-parameter routine.  Its body is
   *  an ordinary term, so the interprocedural transfer has something to analyse. */
  val callee: RoutinePtr = RoutinePtr("gsem$callee")
  val calleeRefs: Vector[PathRef] = Vector(PathRef("q$0"))
  val calleeMentions: Vector[SpaceMention] = Vector(SpaceMention("m$0"), SpaceMention("m$1"))
  val calleeRoutine: Routine = Routine(callee, calleeRefs, calleeMentions,
    Space.Union(Space.Wrap(Space.Mention(calleeMentions(0)), Path.Deref(calleeRefs(0))),
                Space.TailsUnion(Space.Mention(calleeMentions(1)))))
  val routineTable: PartialFunction[RoutinePtr, Routine] = { case `callee` => calleeRoutine }

  /** deterministic grounded functions for the two opaque rows (compared by closure identity by the
   *  rest of the engine, so they must be stable `val`s) */
  val groundedPS: PathValue => SpaceValue =
    (p: PathValue) => SpaceValue(p.items.indices.map(i => PathValue(p.items.take(i + 1))).toSet)
  val groundedSS: SpaceValue => SpaceValue =
    (s: SpaceValue) => SpaceValue(s.paths.map(p => PathValue(p.items.reverse)))
  }
  /** source compatibility only — see the note on [[TestOnly]]; delete once the two test files that
   *  `import SpatialGamma.*` name the object explicitly. */
  export TestOnly.*
end SpatialGamma
