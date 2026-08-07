package morkl

/** THE SPATIAL TYPE — a reduced product of the SHAPE (a bounded abstract trie, [[Shape]]) and the
 *  LENGTH-INDEXED COUNTS ([[SpaceType]]), analysed together and reduced against each other.
 *
 *  Why a product rather than either alone: the histogram knows how many paths of each length a
 *  space holds but cannot tell `{a.0,a.1,a.2,a.3}` from `{a.0,b.0,c.0,d.0}`; the trie knows the
 *  heads and prefixes but is capped in depth and width, so beyond the cap the histogram is the only
 *  thing still saying anything.
 *
 *  ==WHAT "REDUCED" MEANS HERE, EXACTLY  (review.md 5)==
 *  [[SpatialType.reduce]] is a TERMINATING BIDIRECTIONAL REDUCER with eight named rules — four that
 *  let the shape constrain the histogram and four the other way — iterated to a fixed point under an
 *  explicit round cap ([[SpatialConfig.reduceRounds]]).  It is applied at EVERY node of
 *  [[SpatialAnalysis]]'s traversal, and the tightened child is what the parent transfer sees (that is
 *  the part a root-only reduction cannot do).  `SpatialTyping.infer` — the standalone query — still
 *  runs one shape traversal and one histogram traversal and reduces the pair; it is the decorated
 *  traversal that reduces per node.  A contradiction between the two components does not widen: it
 *  collapses to the EXPLICIT BOTTOM [[SpatialType.bottom]], whose γ is empty (it rejects even ∅).
 *
 *  Facts are exposed as VALIDATED PROPOSITIONS ([[Fact]]), never as raw numbers: `len.lo >= 3` on
 *  the empty space is `INF >= 3`, which would "prove" three extractable items from nothing.  Each
 *  proposition encodes the conjunction its meaning requires, once.
 *
 *  ==ONE OWNER (review.md 6)==
 *  This file owns the PRODUCT's lattice operations, each delegating componentwise and never
 *  restating a component's law:
 *
 *  | law               | product                  | shape half                  | histogram half            |
 *  |-------------------|--------------------------|-----------------------------|---------------------------|
 *  | γ                 | [[SpatialType.accepts]]  | `Shape.contains`            | `SpatialGamma.gammaSpace` |
 *  | order (γ)         | [[SpatialType.leq]]      | `Shape.leqStrong`           | `SpatialGamma.leqSpace`   |
 *  | join (lub)        | [[SpatialType.join]]     | `Shape.joinAlternatives`    | `SpatialGamma.lubSpace`   |
 *  | meet (glb)        | [[SpatialType.meet]]     | `Shape.meet`                | `SpatialGamma.meetSpace`  |
 *  | reduction         | [[SpatialType.reduce]]   | — both, against each other —                            |
 *  | widening          | [[SpatialType.widen]]    | `Shape.widen`               | count channels opened     | */
final case class SpatialType(shape: Shape, lens: SpaceType, uninhabited: Boolean = false):
  import Lower.{LenBounds, SizeBounds}
  def size: SizeBounds =
    if uninhabited then SizeBounds(0, 0, 0)
    else
      val a = lens.size; val b = shape.size
      val lo = a.lo max b.lo
      SizeBounds(lo, a.loHeaded max (if shape.eps.mayBe then Ivl.relu(b.lo - 1) else b.lo), a.hi min b.hi)
  def len: LenBounds =
    if uninhabited then LenBounds.empty
    else
      val a = lens.len; val b = shape.lens
      if a.isEmpty || b.isEmpty then LenBounds.empty else LenBounds(a.lo max b.lo, a.hi min b.hi)
  /** no path can be present.  TRUE of [[SpatialType.bottom]] as well, VACUOUSLY: bottom admits no
   *  concrete space at all, so every ∀-path claim about "the" value holds.  A consumer that needs to
   *  tell "the value is the empty space" from "there is no value" must read [[uninhabited]]. */
  def isProvablyEmpty: Boolean = uninhabited || lens.isProvablyEmpty || shape.definitelyEmpty || size.hi == 0
  /** the DISTINCT-head count — the group count of an iteration, invisible to the histogram */
  def headCount: Ivl =
    if uninhabited then Ivl.zero else Ivl(shape.headCount.lo, shape.headCount.hi min size.hi)
  /** `E_d` — how many paths have AT LEAST `d` items, read off the histogram (whispers.md §1).  The
   *  spill bucket contributes its whole lower bound only when EVERY length it may cover reaches `d`,
   *  nothing when none does, and only its upper bound in between; adding `rest.lo` whenever
   *  `restLens.hi >= d` would be unsound, since the required paths may all sit in the shorter part. */
  def pathsAtDepth(d: Int): Ivl =
    require(d >= 0, s"depth must be non-negative, got $d")
    if uninhabited then Ivl.zero
    else
      var lo = 0L; var hi = 0L
      for (l, c) <- lens.byLen if l >= d do { lo = Ivl.add(lo, c.lo); hi = Ivl.add(hi, c.hi) }
      if lens.rest.hi > 0 && !lens.restLens.isEmpty && lens.restLens.hi >= d then
        if lens.restLens.lo >= d then { lo = Ivl.add(lo, lens.rest.lo); hi = Ivl.add(hi, lens.rest.hi) }
        else hi = Ivl.add(hi, lens.rest.hi)
      Ivl(lo, if hi < lo then lo else hi)
  /** `K_d` — how many distinct length-`d` prefixes the SHAPE permits, met with `E_d` (every
   *  qualifying path lies in exactly one fibre, so `K_d ≤ E_d`, and `E_d > 0` forces `K_d > 0`).
   *  whispers.md §1 `require`s consistency here and throws on a hand-built inconsistent product; this
   *  returns the reduced interval and leaves the contradiction to [[SpatialType.reduce]], which has an
   *  explicit bottom to collapse to. */
  def prefixesAt(d: Int): Ivl =
    if uninhabited then Ivl.zero
    else
      val raw = shape.prefixesAt(d)
      val e = pathsAtDepth(d)
      val lo = raw.lo max (if e.lo > 0 then 1L else 0L)
      val hi = raw.hi min e.hi
      if lo > hi then Ivl(lo, lo) else Ivl(lo, hi)   // inconsistent ⇒ `reduce` reports bottom
  def show: String =
    if uninhabited then "⊥ (no concrete space is admitted)" else s"shape ${shape.show}  lens ${lens.show}"

object SpatialType:
  import Lower.{LenBounds, SizeBounds}
  import scala.collection.immutable.SortedMap
  val top: SpatialType = SpatialType(Shape.top, SpaceType.unknown)
  /** the EMPTY SPACE — γ = {∅}.  NOT the bottom of the lattice. */
  val empty: SpatialType = SpatialType(Shape.empty, SpaceType.empty)
  /** THE EXPLICIT BOTTOM — γ = ∅: no concrete space at all, not even `∅`.  Produced only by
   *  [[reduce]]/[[meet]] on a CONTRADICTION between two sound claims about the same value, which can
   *  only happen when an input annotation is itself unsatisfiable (or a transfer is unsound — which is
   *  why `SpatialAnalysisCheck` gates "no corpus term reduces to bottom"). */
  val bottom: SpatialType = SpatialType(Shape.empty, SpaceType.empty, uninhabited = true)
  def of(v: SpaceValue): SpatialType = SpatialType(Shape.of(v), SpaceType.of(v))

  // ---- γ, order, join, meet, widening: the product composes, the components own the laws ---------

  /** FULL γ-MEMBERSHIP of a concrete space in an abstract one — sound AND complete for this carrier.
   *  `Shape.contains` decides the four shape channels, `SpatialGamma.gammaSpace` the histogram's
   *  representation invariant, and the two reduced projections are checked as well because γ of the
   *  product constrains them directly.  This is the predicate the corpus soundness gates assert. */
  def accepts(t: SpatialType, v: SpaceValue): Boolean =
    !t.uninhabited && Shape.contains(t.shape, v) && SpatialGamma.gammaSpace(t.lens, v) && {
      val n = v.paths.size.toLong; val sz = t.size
      sz.lo <= n && n <= sz.hi
    } && {
      val b = t.len
      v.paths.forall(p => !b.isEmpty && b.lo <= p.items.length && p.items.length <= b.hi)
    }

  /** the ORDER (`γ(a) ⊆ γ(b)`), SOUND and deliberately INCOMPLETE — see `SpatialGamma.leq`.  The
   *  shape half is the STRONG-γ reading ([[Shape.leqStrong]]), matching [[accepts]]; the may-only
   *  sibling `Shape.leq` is the Kleene-chain order and is NOT this one. */
  def leq(a: SpatialType, b: SpatialType): Boolean =
    a.uninhabited || (!b.uninhabited && Shape.leqStrong(a.shape, b.shape) && SpatialGamma.leqSpace(a.lens, b.lens))

  /** the JOIN — an upper bound of both ALTERNATIVES (not the `A ∪ B` transfer). */
  def join(a: SpatialType, b: SpatialType): SpatialType =
    if a.uninhabited then b else if b.uninhabited then a
    else SpatialType(Shape.joinAlternatives(a.shape, b.shape), SpatialGamma.lubSpace(a.lens, b.lens))

  /** THE MEET — the only sound way to combine two INDEPENDENTLY DERIVED sound approximations of the
   *  same value (which is what the decorated analysis does with its compositional per-node histogram
   *  and the authoritative one, and what a reduced product does with its two components).  Bottom
   *  when the two are contradictory. */
  def meet(a: SpatialType, b: SpatialType): SpatialType =
    if a.uninhabited || b.uninhabited then bottom
    else (Shape.meet(a.shape, b.shape), SpatialGamma.meetSpace(a.lens, b.lens)) match
      case (Some(sh), Some(ls)) => reduce(SpatialType(sh, ls))
      case _ => bottom

  /** the WIDENING: open every count channel, keep the length support and the head sets. */
  def widen(t: SpatialType): SpatialType =
    if t.uninhabited then t
    else SpatialType(Shape.widen(t.shape),
      SpaceType(SortedMap.from(t.lens.byLen.iterator.map((l, _) => l -> Ivl(t.lens.at(l).lo, Ivl.INF))),
                if t.lens.rest.hi == 0 then Ivl.zero else Ivl(t.lens.rest.lo, Ivl.INF), t.lens.restLens))

  // ================================================================================================
  // THE REDUCER  (review.md 5: "in both directions after every transfer" — made true)
  // ================================================================================================

  /** THE BIDIRECTIONAL REDUCER.  Eight rules; `S*` let the shape constrain the histogram, `H*` the
   *  histogram constrain the shape.  Every rule NARROWS (it removes concrete values from γ and adds
   *  none), and each is individually justified below.
   *
   *  {{{
   *  S1  total cap        no length class holds more paths than the shape's whole-space upper
   *  S2  length window    a class outside the shape's ∀-path length hull is EMPTY; the spill window
   *                       is clipped to the hull
   *  S3  forced class     the shape proves ≥ k paths and only ONE class can hold them ⇒ that class'
   *                       lower bound is k  (k from the shape size and from K_1, the must-present
   *                       head count)
   *  S4  contradiction    the shape proves emptiness while the histogram forces a path (or vice
   *                       versa) ⇒ ⊥
   *  H1  head count       a depth-d node's heads each need a path of ≥ d+1 items, so its head count
   *                       is capped by E_(d+1); E_(d+1) = 0 closes the node's head set entirely
   *  H2  epsilon          a depth-d node's ε IS a path of exactly d items, so `at(d).hi == 0` forces
   *                       `eps = No`; at the ROOT (one fibre only) `at(0).lo >= 1` forces `eps = Must`
   *  H3  depth pruning    beyond the histogram's maximum length there are no heads at all — this is
   *                       H1 with `E_(d+1) = 0`, applied down the whole trie
   *  H4  forced presence  the histogram proves the space non-empty and the shape leaves exactly ONE
   *                       place a path can be ⇒ that place is forced (a MUST channel gained from the
   *                       count domain)
   *  }}}
   *
   *  ==TERMINATION==
   *  One round is a narrowing: `γ(reduceOnce(t)) ⊆ γ(t)`, and structurally it only ever (i) deletes a
   *  tracked head or a length class, (ii) strengthens a `Presence` along `May → {No, Must}`, or
   *  (iii) moves an interval endpoint inward.  So the measure
   *
   *      μ(t) = (live shape nodes, May-presences, live length classes)  ∈  ℕ³ lexicographic
   *
   *  never increases, and every round that changes the value either decreases μ or narrows an
   *  interval.  Interval narrowing alone could in principle descend for a very long time (endpoints
   *  are `Long`), so the loop is ALSO capped at [[SpatialConfig.reduceRounds]] rounds and stops early
   *  at the fixed point — the cap is what makes termination unconditional, and
   *  `SpatialAnalysisCheck` measures how many rounds are actually used: ONE, over a 225-type pool that
   *  spans every representation, and `reduce` is idempotent on all of them. */
  def reduce(t: SpatialType): SpatialType = reduce(t, SpatialConfig.default)
  def reduce(t: SpatialType, cfg: SpatialConfig): SpatialType =
    var cur = t
    var k = 0
    var stop = false
    while !stop && k < cfg.reduceRounds do
      val next = reduceOnce(cur)
      if next.uninhabited || next == cur then { cur = next; stop = true } else { cur = next; k += 1 }
    cur

  /** how many rounds [[reduce]] needed (for the termination measurement in the test suite) */
  private[morkl] def reduceRounds(t: SpatialType, cfg: SpatialConfig = SpatialConfig.default): Int =
    var cur = t; var k = 0; var stop = false
    while !stop && k < cfg.reduceRounds do
      val next = reduceOnce(cur)
      if next.uninhabited || next == cur then stop = true else { cur = next; k += 1 }
    k

  private def reduceOnce(t: SpatialType): SpatialType =
    if t.uninhabited then t
    else
      val sz = t.size
      val ln = t.len
      // ---- S4 / H-side contradictions ---------------------------------------------------------
      // Both components bound the SAME count and the SAME length hull, so an empty meet is a proof
      // that no concrete space satisfies both — not an occasion to widen.
      if sz.lo > sz.hi then SpatialType.bottom
      else if ln.isEmpty && sz.lo >= 1 then SpatialType.bottom
      else if t.shape.definitelyEmpty && t.lens.size.lo >= 1 then SpatialType.bottom
      else if t.lens.isProvablyEmpty && t.shape.definitelyNonEmpty then SpatialType.bottom
      else if t.lens.at(0).lo >= 1 && t.shape.eps == Presence.No then SpatialType.bottom
      else if t.shape.eps == Presence.Must && t.lens.at(0).hi == 0 then SpatialType.bottom
      else if t.shape.definitelyEmpty || t.lens.isProvablyEmpty then SpatialType.empty
      else
        // ---- H1/H2/H3: the histogram reshapes the trie, level by level ---------------------------
        val sh1 = constrainShape(t, t.shape, 0)
        if sh1.isEmpty then SpatialType.bottom
        else
          val sh = sh1.get
          // ---- H4: non-empty + a unique possible location ⇒ that location is FORCED --------------
          val sh2 = if sz.lo >= 1 then forceInhabited(sh) else Some(sh)
          if sh2.isEmpty then SpatialType.bottom
          else
            val shape = sh2.get
            // ---- S1/S2/S3: the shape reshapes the histogram ---------------------------------------
            val cap = shape.size.hi
            val hull = shape.lens
            if hull.isEmpty && shape.possiblyNonEmpty then SpatialType.bottom
            else
              val kept = t.lens.byLen.iterator.map { (l, c) =>
                val dead = !hull.isEmpty && (l < hull.lo || l > hull.hi)           // S2
                if dead then l -> Ivl(0, 0)
                else l -> Ivl(c.lo, if cap == Ivl.INF then c.hi else c.hi min cap) // S1
              }.toVector
              if kept.exists((_, c) => c.lo > c.hi) then SpatialType.bottom
              else
                val restHi = if cap == Ivl.INF then t.lens.rest.hi else t.lens.rest.hi min cap
                val restWin =                                                       // S2
                  if t.lens.rest.hi == 0 || hull.isEmpty then t.lens.restLens
                  else LenBounds(t.lens.restLens.lo max hull.lo, t.lens.restLens.hi min hull.hi)
                if t.lens.rest.lo > restHi || (t.lens.rest.lo >= 1 && restWin.isEmpty) then SpatialType.bottom
                else
                  val lens1 = SpaceType(SortedMap.from(kept.filter(_._2.hi > 0)),
                                        if restWin.isEmpty then Ivl.zero else Ivl(t.lens.rest.lo, restHi),
                                        if restWin.isEmpty then LenBounds.empty else restWin)
                  val lens2 = forceClass(lens1, shape)                              // S3
                  val out = SpatialType(shape, lens2)
                  if out.size.lo > out.size.hi then SpatialType.bottom else out

  /** H1 + H2 + H3.  At depth `d` the node abstracts ONE prefix fibre of the whole space: its ε is a
   *  path of exactly `d` items and each of its heads needs a path of at least `d + 1` items.  Both
   *  are counted by the histogram, and both bound the fibre even though the histogram counts across
   *  ALL fibres (a fibre's paths are a subset of the space's).  `None` = contradiction. */
  private def constrainShape(t: SpatialType, s: Shape, d: Int): Option[Shape] =
    if d > Shape.MaxDepth + 1 then Some(s)
    else
      val here = t.lens.at(d.toLong)          // paths of EXACTLY d items — the fibre's ε
      val below = t.pathsAtDepth(d + 1)       // paths of at least d+1 items — the fibre's heads
      val eps =
        if here.hi == 0 then                                     // H2 (may direction)
          if s.eps == Presence.Must then return None else Presence.No
        else if d == 0 && here.lo >= 1 then                       // H2 (must direction, root only)
          if s.eps == Presence.No then return None else Presence.Must
        else s.eps
      if below.hi == 0 then                                       // H1/H3: no heads are possible
        if s.heads.exists((_, c) => c.definitelyNonEmpty) || s.others.lo >= 1 then None
        else Some(Shape(eps, scala.collection.immutable.SortedMap.empty, Ivl.zero, None))
      else
        var dead = false
        val kids = Vector.newBuilder[(PathItem, Shape)]
        for (h, c) <- s.heads if !dead do
          constrainShape(t, c, d + 1) match
            case None => dead = true
            case Some(c2) => kids += (h -> c2)
        if dead then None
        else
          val kept = kids.result()
          // discount only the MUST-present tracked heads: a merely may-present one need not consume
          // any of the `below.hi` paths, so discounting it would under-count the untracked room.
          val forced = kept.count((_, c) => c.definitelyNonEmpty).toLong
          val othersHi = s.others.hi min Ivl.relu(below.hi - forced)        // H1
          if s.others.lo > othersHi then None
          else
            // the untracked side is constrained too, MATERIALISING the ⊤ summary when there was
            // none: at depth d+1 the fibre obeys the same per-depth counts, so "nothing longer than
            // L" prunes the untracked branches as well as the tracked ones (H3).
            val ot = if othersHi == 0 then None
                     else constrainShape(t, s.otherTail.getOrElse(Shape.top), d + 1).filter(!_.isTop)
            // `Shape.mk`'s invariant, re-established by hand (it is private): an untracked head has a
            // NON-EMPTY tail-set by definition, so a definitely-empty summary means there are no
            // untracked heads at all — and if one was FORCED, that is a contradiction.
            val emptyTail = ot.exists(_.definitelyEmpty)
            if emptyTail && s.others.lo >= 1 then None
            else
              val hi = if emptyTail then 0L else othersHi
              Some(Shape(eps, scala.collection.immutable.SortedMap.from(kept.filter(_._2.possiblyNonEmpty)),
                         if hi == 0 then Ivl.zero else Ivl(s.others.lo, hi),
                         if hi == 0 then None else ot))

  /** H4.  The space is known NON-EMPTY (from the histogram); if the shape leaves exactly one place a
   *  path could be, that place is forced — a MUST claim the count domain paid for.  `None` =
   *  contradiction (non-empty, but nowhere for a path to be). */
  private def forceInhabited(s: Shape): Option[Shape] =
    if s.definitelyNonEmpty then Some(s)
    else
      val live = s.heads.iterator.filter((_, c) => c.possiblyNonEmpty).toVector
      val places = (if s.eps.mayBe then 1 else 0) + live.size + (if s.others.hi > 0 then 1 else 0)
      if places == 0 then None
      else if places > 1 then Some(s)
      else if s.eps.mayBe then Some(s.copy(eps = Presence.Must))
      else if live.size == 1 then
        forceInhabited(live.head._2).map(c => s.copy(heads = s.heads.updated(live.head._1, c)))
      else Some(s.copy(others = Ivl(s.others.lo max 1L, s.others.hi)))

  /** S3.  The shape proves at least `k` paths exist (its own size lower bound, and `K_1` — the number
   *  of MUST-present heads — which is a lower bound on the number of paths with ≥ 1 item).  If only
   *  one length class can hold them, that class' lower bound rises to `k`. */
  private def forceClass(l: SpaceType, shape: Shape): SpaceType =
    def raise(need: Long, headed: Boolean): SpaceType => SpaceType = t =>
      if need <= 0 then t
      else
        val live = t.byLen.iterator.filter((k, c) => c.hi > 0 && (!headed || k >= 1)).map(_._1).toVector
        val spill = t.rest.hi > 0 && (!headed || t.restLens.hi >= 1)
        if live.size == 1 && !spill then
          val k = live.head
          val c = t.at(k)
          SpaceType(t.byLen.updated(k, Ivl(c.lo max need, c.hi)), t.rest, t.restLens)
        else if live.isEmpty && spill then
          SpaceType(t.byLen, Ivl(t.rest.lo max need, t.rest.hi), t.restLens)
        else t
    val withTotal = raise(shape.size.lo, headed = false)(l)
    raise(shape.prefixesAt(1).lo, headed = true)(withTotal)
end SpatialType

/** A validated proposition about a space — the safe API an optimizer should consume.  Each case
 *  bundles the conjunction its meaning requires, so a client cannot read `len.lo` off an empty
 *  space and conclude something about paths that do not exist. */
enum Fact:
  case DefinitelyEmpty
  case DefinitelyNonEmpty
  case MinimumCardinality(k: Long)          // at least k paths, AND the space is non-empty
  case MaximumCardinality(k: Long)
  case AllPathsHaveAtLeast(items: Long)     // every path has ≥ items items, AND ≥1 path exists
  case MaximumPathLength(items: Long)
  case ExactHeadSet(heads: Set[PathItem])   // the head set is EXACTLY this: closed AND all must
  case HeadSetWithin(heads: Set[PathItem])  // the head set is a subset of this (closed, some may)
  case MinimumHeadCount(k: Long)            // ≥ k distinct heads, so an iteration definitely runs
  case MaximumHeadCount(k: Long)
  case PrefixAbsent(prefix: List[PathItem]) // no path starts with this prefix
  def show: String = toString

object Fact:
  /** everything this type licenses, each with its precondition already discharged */
  def from(t: SpatialType): Vector[Fact] = from(t, Nil)

  /** the same, plus the answer to a PREFIX QUERY for each probe.
   *
   *  `PrefixAbsent` used to be a public case that `from` never emitted (review.md 6): the shape can
   *  prove an unbounded family of prefixes absent (every item outside a closed head set), so there is
   *  no finite "all of them" to enumerate — the fact only exists relative to prefixes somebody asks
   *  about.  [[SpatialAnalysis]] asks about the CONSTANT PATHS THE TERM ITSELF MENTIONS, which is
   *  exactly the finite set an optimizer can act on ("this `Unwrap`'s prefix is provably absent, the
   *  result is ∅"). */
  def from(t: SpatialType, probes: Iterable[List[PathItem]]): Vector[Fact] =
    val out = Vector.newBuilder[Fact]
    val sz = t.size; val ln = t.len
    if t.isProvablyEmpty then out += Fact.DefinitelyEmpty
    else
      if sz.lo >= 1 then out += Fact.DefinitelyNonEmpty
      if sz.lo >= 1 then out += Fact.MinimumCardinality(sz.lo)
      if sz.hi != Ivl.INF then out += Fact.MaximumCardinality(sz.hi)
      // a length claim is only meaningful once the space is known non-empty
      if sz.lo >= 1 && !ln.isEmpty && ln.lo >= 1 then out += Fact.AllPathsHaveAtLeast(ln.lo)
      if !ln.isEmpty && ln.hi != LenBounds.INF then out += Fact.MaximumPathLength(ln.hi)
      if t.shape.headsClosed then
        val live = t.shape.heads.keySet.filter(h => t.shape.heads(h).possiblyNonEmpty)
        // "EXACTLY these heads" needs every one of them to be MUST-present; otherwise the closed
        // head set only bounds the head set from above.
        if live.forall(h => t.shape.heads(h).definitelyNonEmpty) then out += Fact.ExactHeadSet(live)
        else out += Fact.HeadSetWithin(live)
      val hc = t.headCount
      if hc.lo >= 1 then out += Fact.MinimumHeadCount(hc.lo)
      if hc.hi != Ivl.INF then out += Fact.MaximumHeadCount(hc.hi)
      for p <- probes.iterator.filter(_.nonEmpty).toVector.distinct
          if SpatialTyping.prefixAbsent(t, p) do out += Fact.PrefixAbsent(p)
    out.result()
  private val LenBounds = Lower.LenBounds

/** The analysis over the reduced product.  Same discipline as [[SpatialTypes]]: no evaluation, only
 *  the term's syntax, the declared input types, and the transfers.
 *
 *  The shape transfers are documented, with their may/must justification, in the table at the top of
 *  SpatialShape.scala.  Real transfers: Empty, Literal, Singleton, Union, Intersection, Subtraction,
 *  Restriction, Raffination, Wrap, Unwrap, TailsUnion, TailsIntersection, Composition, Range,
 *  Iteration, Fold, Fixpoint, Call, Mention — including the non-constant-path arms of `Singleton`,
 *  `Wrap` and `Unwrap`, which stay informative as long as the path's LENGTH is bounded.
 *  Degraded to ⊤, and only these: `GroundedPS`/`GroundedSS` (an arbitrary Scala function), a `Call`
 *  whose routine is absent from the table or already on the call stack, an `Unwrap` by a path of
 *  unbounded length, a `Mention` with no declared type, a `Fixpoint` with no verified post-fixpoint,
 *  and anything reached after the node budget runs out.
 *
 *  ==ONE TRAVERSAL==
 *  [[goShape]] is the ONLY shape traversal in the tree.  It takes a [[ShapeVisitor]]: with
 *  `ShapeVisitor.Off` it is the standalone `infer` query it always was, and with the recorder
 *  [[SpatialAnalysis]] installs it becomes the decorated per-node analysis — same transfers, same
 *  numbers, one code path.  The visitor may return a TIGHTENED shape for a node, and that is what the
 *  parent transfer then consumes. */
object SpatialTyping:
  import Lower.{LenBounds, SizeBounds}

  /** input types for the shape domain: shapes for mentions, KNOWN VALUES for path refs (an
   *  iteration binds its head symbol to a concrete item, which is what lets the body distinguish
   *  one head from another).  `opaque` are refs that ARE bound but whose value is unknown — an
   *  iteration head of an untracked group, a fold accumulator — carrying only a length bound.  They
   *  must shadow any outer binding, or a body would read a stale constant. */
  final case class Env(spaces: Map[SpaceMention, SpatialType] = Map.empty,
                       paths: Map[PathRef, PathValue] = Map.empty,
                       lenv: SpatialEnv = SpatialEnv(),
                       opaque: Map[PathRef, Lower.LenBounds] = Map.empty):
    def lengths: SpatialEnv = lenv.copy(spaces = spaces.view.mapValues(_.lens).toMap,
                                        paths = paths.view.mapValues(p => LenBounds(p.items.length, p.items.length)).toMap
                                                  ++ lenv.paths ++ opaque)

  /** the analysis is linear in the term, but `Iteration`/`Fold` fork per head group and `Fixpoint`
   *  iterates, so the product is bounded by an explicit node budget rather than by hope.  Running
   *  out yields ⊤, which is always sound. */
  private final class Budget(var left: Int):
    def spend(): Boolean = { left -= 1; left > 0 }

  /** A listener on the ONE shape traversal.  `visit` is called on every node in POST-ORDER with the
   *  node's lexical position, the binder environment it was analysed in, and the shape the transfer
   *  produced; whatever it returns is what the PARENT transfer sees.  `Off` is the identity, so
   *  `infer` is exactly the query it has always been. */
  private[morkl] trait ShapeVisitor:
    def visit(pos: Vector[Int], s: Space, env: Env, sh: Shape, cause: String): Shape
  private[morkl] object ShapeVisitor:
    object Off extends ShapeVisitor:
      def visit(pos: Vector[Int], s: Space, env: Env, sh: Shape, cause: String): Shape = sh

  def infer(s: Space): SpatialType = infer(s, Env())
  /** Analyse the shape ONCE over the term, analyse the length/count component once, and reduce the
   *  two at the root.  An earlier draft re-ran the whole histogram analysis at every node, which is
   *  quadratic and overflowed the stack on corpus terms — [[SpatialAnalysis]] is the compositional
   *  answer to that; this remains the cheap standalone query. */
  def infer(s: Space, env: Env): SpatialType =
    SpatialType.reduce(SpatialType(shapeOf(s, env), SpatialTypes.infer(s, env.lengths)))

  /** just the shape component (used by the differential operator matrix) */
  def shapeOf(s: Space, env: Env = Env()): Shape =
    goShape(s, env, 0, Vector.empty, "root")(using new Budget(SpatialConfig.default.nodeBudget), ShapeVisitor.Off)

  /** the shape traversal with a recorder installed — [[SpatialAnalysis]]'s entry point */
  private[morkl] def shapeWith(s: Space, env: Env, cfg: SpatialConfig, v: ShapeVisitor): Shape =
    goShape(s, env, 0, Vector.empty, "root")(using new Budget(cfg.nodeBudget), v)

  /** the constant value of a path expression, when the term and the env determine it */
  private def constPath(p: Path, env: Env): Option[List[PathItem]] = p match
    case Path.Constant(pv) => Some(pv.items)
    case Path.Deref(pr) => if env.opaque.contains(pr) then None else env.paths.get(pr).map(_.items)
    case Path.Concat(l, r) => for a <- constPath(l, env); b <- constPath(r, env) yield a ++ b
    case _ => None

  /** the ITEM-length interval of a path expression under the shape env.  Annotations
   *  (`PathRef.lengthHint`) and declared entries are trusted exactly as `SpatialTypes.pathLen`
   *  trusts them — see docs/design_spatial_lattice.md §0 for why that is a legitimate source. */
  private def pathLenOf(p: Path, env: Env): LenBounds = p match
    case Path.Constant(pv) => LenBounds(pv.items.length, pv.items.length)
    case Path.Deref(pr) => env.opaque.get(pr) match
      case Some(k) => k
      case None => env.paths.get(pr) match
        case Some(pv) => LenBounds(pv.items.length, pv.items.length)
        case None => env.lenv.paths.getOrElse(pr,
          if pr.lengthHint >= 0 then LenBounds(pr.lengthHint, pr.lengthHint) else LenBounds.unknown)
    case Path.Concat(l, r) =>
      val (a, b) = (pathLenOf(l, env), pathLenOf(r, env))
      LenBounds(Ivl.add(a.lo, b.lo), Ivl.add(a.hi, b.hi))
    case _ => LenBounds.unknown

  /** THE shape traversal.  `pos` is the lexical position of `s` — the child index path from the root
   *  — and is what gives a decorated node its identity: two structurally identical subterms in
   *  different positions get different `pos`.  A binder's body is visited once per HEAD GROUP (and a
   *  fixpoint's once per round) at the SAME position, each with its own environment; the recorder
   *  keeps every one of those observations. */
  private def goShape(s: Space, env: Env, depth: Int, pos: Vector[Int], cause: String)
                     (using b: Budget, v: ShapeVisitor): Shape =
    if depth > SpatialConfig.default.termDepth || !b.spend() then v.visit(pos, s, env, Shape.top, "budget")
    else
      def rec(i: Int, x: Space) = goShape(x, env, depth + 1, pos :+ i, "child")
      val out = s match
        case Space.Empty => Shape.empty
        case Space.Literal(vv) => Shape.of(vv)
        case Space.Singleton(p) => constPath(p, env) match
          case Some(items) => Shape.ofPath(PathValue(items))
          case None => Shape.oneUnknownPath(pathLenOf(p, env))   // exactly ONE path, content unknown
        case Space.Union(a, bb) => Shape.unionTransfer(rec(0, a), rec(1, bb))
        case Space.Intersection(a, bb) => Shape.inter(rec(0, a), rec(1, bb))
        case Space.Subtraction(a, bb) => Shape.sub(rec(0, a), rec(1, bb))
        case Space.Restriction(a, bb) => Shape.restrict(rec(0, a), rec(1, bb))
        // x \| y = x ∖ (x <| y).  Sound because `restrict`'s must under-approximates the true
        // restriction (so subtracting it never removes a member that survives) and its may
        // over-approximates it (so the must that survives is a genuine must).
        case Space.Raffination(a, bb) =>
          val x = rec(0, a); Shape.sub(x, Shape.restrict(x, rec(1, bb)))
        case Space.Wrap(a, p) => constPath(p, env) match
          case Some(items) => Shape.wrap(items, rec(0, a))
          case None => Shape.wrapUnknown(pathLenOf(p, env), rec(0, a))
        case Space.Unwrap(a, p) => constPath(p, env) match
          case Some(items) => Shape.unwrap(items, rec(0, a))   // proves absent prefixes
          case None => Shape.unwrapUnknown(pathLenOf(p, env), rec(0, a))
        case Space.TailsUnion(a) => Shape.tailsUnion(rec(0, a))
        case Space.TailsIntersection(a) => Shape.tailsInter(rec(0, a))
        case Space.Composition(a, bb) => Shape.comp(rec(0, a), rec(1, bb))
        case Space.Mention(m) => env.spaces.get(m).map(_.shape).getOrElse(Shape.top)

        case Space.Range(x, lo, hi) =>
          val src = rec(0, x)
          val sz = src.size
          val whole = (lo == 0 && hi == 0) ||
            (sz.lo == sz.hi && sz.hi != Ivl.INF && sz.hi <= Int.MaxValue &&
              RangeBounds.normalize(sz.hi.toInt, lo, hi) == (0, sz.hi.toInt))
          Shape.range(src, windowWidth(sz, lo, hi), whole)

        case Space.Iteration(src, sym, rest, body) =>
          // THE shape payoff: the group count is the number of DISTINCT HEADS, not the path count,
          // and each group is analysed with its head bound to that item and `rest` bound to that
          // head's tail-set.  `{a.0,a.1,a.2,a.3}` has ONE group and `{a.0,b.0,c.0,d.0}` has FOUR —
          // indistinguishable to a length histogram.
          groupUnion(rec(0, src), env, sym, rest, body, depth, Map.empty, pos)

        case Space.Fold(src, _, acc, sym, rest, body, _) =>
          // the same head-group union, but the ACCUMULATOR is opaque: its value depends on the
          // group order and on `update`, neither of which this domain models.  A body that does not
          // read the accumulator therefore keeps full precision, and one that does degrades exactly
          // where it reads it.  The accumulator's own contribution to the RESULT is nil — `Fold`
          // returns the union of the bodies, not the accumulator.
          groupUnion(rec(0, src), env, sym, rest, body, depth, Map(acc -> LenBounds.unknown), pos)

        case Space.Fixpoint(init, recm, body) => fixpoint(init, recm, body, env, depth, pos)

        case Space.Call(rp, refs, mentions) =>
          val table = env.lenv.routines
          if table.isDefinedAt(rp) && !env.lenv.active(rp) then
            val Routine(_, refns, mentionns, cbody) = table(rp)
            // INTERPROCEDURAL: a routine body denotes a function of its parameters, so analysing it
            // with the parameters bound to the ARGUMENT shapes is sound, must channels included.
            // The callee scope starts empty — inheriting the caller's bindings would let a body read
            // a mention it does not have.
            val argShapes = mentionns.zip(mentions.zipWithIndex.map((m, i) =>
              SpatialType(rec(i, m), SpaceType.unknown))).toMap
            val argPathsAll = refns.zip(refs.map(p => constPath(p, env) -> pathLenOf(p, env)))
            val known = argPathsAll.collect { case (n, (Some(items), _)) => n -> PathValue(items) }.toMap
            val opaque = argPathsAll.collect { case (n, (None, k)) => n -> k }.toMap
            val callee = Env(spaces = argShapes, paths = known, opaque = opaque,
                             lenv = env.lenv.copy(spaces = Map.empty, paths = Map.empty,
                                                  active = env.lenv.active + rp))
            // the callee's body belongs to ANOTHER routine's lexical tree, so it is analysed but not
            // decorated: a position under this term would be a lie about where the node lives.
            goShape(cbody, callee, depth + 1, pos, "callee")(using b, ShapeVisitor.Off)
          else Shape.top

        // an arbitrary Scala function: NOTHING is claimed
        case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => Shape.top
      v.visit(pos, s, env, out, cause)

  /** the head-group union shared by `Iteration` and `Fold`.  A group whose head is only MAY-present
   *  need not run, so its body cannot contribute must information; a MUST-present head's group DOES
   *  run and contributes fully.  An open head set adds ONE extra weakened body, analysed with the
   *  head symbol opaque (length 1 — `sp_iter_head_one`) and `rest` bound to the weakened
   *  `otherTail`; without that arm the whole transfer had to degrade to ⊤. */
  private def groupUnion(x: Shape, env: Env, sym: PathRef, rest: SpaceMention, body: Space,
                         depth: Int, extraOpaque: Map[PathRef, LenBounds], pos: Vector[Int])
                        (using b: Budget, v: ShapeVisitor): Shape =
    if x.definitelyEmpty || x.headCount.hi == 0 then Shape.empty
    else
      def bind(head: Option[PathItem], tail: Shape): Env =
        val base = env.copy(spaces = env.spaces + (rest -> SpatialType(tail, SpaceType.unknown)),
                            opaque = env.opaque ++ extraOpaque)
        head match
          case Some(h) => base.copy(paths = base.paths + (sym -> PathValue(List(h))),
                                    opaque = base.opaque - sym)
          case None => base.copy(paths = base.paths - sym,
                                 opaque = base.opaque + (sym -> LenBounds(1, 1)))
      val parts = Vector.newBuilder[Shape]
      for (h, tail) <- x.heads.toVector if tail.possiblyNonEmpty do
        val bs = goShape(body, bind(Some(h), tail), depth + 1, pos :+ 1, s"head=$h")
        parts += (if tail.definitelyNonEmpty then bs else Shape.weaken(bs))
      if x.others.hi > 0 then
        val ot = Shape.weaken(x.otherTail.getOrElse(Shape.top))
        val bs = goShape(body, bind(None, ot), depth + 1, pos :+ 1, "untracked-heads")
        // there may be up to `others.hi` untracked groups, and the result is the union of ALL of
        // them.  One body shape bounds ONE group; unioning an unknown number of sets each admitted
        // by it is only sound once the count channels are opened (`openCounts`).  Adding the arm
        // once, weakened, was a soundness bug — found by the nested operator matrix on
        // `Fold(GroundedSS(…), …, Wrap(rest, acc), …)`, where two head groups each produced one head
        // and the transfer claimed at most one.
        parts += (if x.others.hi <= 1 then Shape.weaken(bs) else Shape.openCounts(bs))
      val ps = parts.result()
      if ps.isEmpty then Shape.empty else ps.reduce((p, q) => Shape.unionTransfer(p, q))

  /** FIXPOINT — Kleene iteration over shapes.
   *
   *  ==THE CONCRETE OPERATOR (MORKL.scala:235)==
   *  {{{ cur₀ = init;  cur_{k+1} = F(cur_k);  acc₀ = cur₀;  acc_{k+1} = acc_k ∪ cur_{k+1} }}}
   *  and the RESULT is `acc`, while the recursive mention is bound to `cur` — the LAST iterate, not
   *  the accumulation.  Two distinct obligations follow, and conflating them was a real unsoundness:
   *
   *  (1) EVERY ITERATE must be admitted by one candidate `c`.  That needs `c` to be an upper bound in
   *      the ORDER: `init ⊑ c` and `F#(c) ⊑ c`.  The previous version ascended with
   *      [[Shape.unionTransfer]], which is the transfer for the set operation `A ∪ B` — it keeps the
   *      left operand's MUST claims (sound for a union, since `A ∪ B ⊇ A`) and ADDS the untracked-head
   *      counts.  Neither holds for a value drawn from one side, so the union transfer is not a join
   *      and the chain claimed musts no single iterate has.  Witness (delta-debugged from 71 raw
   *      cases):
   *      {{{ Singleton("c.b.b").fix(k){TailsIntersection(k)}
   *          eval    = {b, b.b, c.b.b, ε}
   *          claimed = shape {b·{b·{ε?}}, c·{b·{b·{ε!}}}}  —  eps = No, so ε was PROVED absent }}}
   *      The chain now ascends with [[Shape.joinAlternatives]] and every iterate is kept MAY-ONLY
   *      ([[Shape.weaken]]).  May-only is what makes the whole argument close: for a may-only `c`,
   *      `γ_may(c) = γ(c)`, so [[Shape.leq]] — which is a γ_may order and ignores must channels — is
   *      exactly the right certificate, while the body is still analysed by the ordinary transfers in
   *      the STRONG reading they are sound in.  A must-consuming transfer (`sub`, `tailsInter`,
   *      raffination) is NOT sound when its input is read may-only, so this direction is the only one
   *      available; see the KNOWN-OPEN note in build.log.
   *
   *  (2) THE RESULT is an unbounded UNION of iterates, and `γ(c)` is not union-closed: `{a}` and
   *      `{b}` can both be in `γ({+[0,1] more})` while `{a,b}` is not.  What survives an arbitrary
   *      union of members of `γ(c)` is exactly [[Shape.openCounts]] — ε stays absent if it was absent
   *      in every iterate (union-closed), a CLOSED head set stays closed (union-closed), an open one
   *      loses its count, and the per-head summaries recurse.  So the accumulation is bounded by
   *      `openCounts(c)`.
   *
   *  MUST comes from `init` ALONE — `acc ⊇ eval(init)` always, and nothing else is guaranteed (the
   *  body may contribute nothing) — hence the final `unionTransfer(i0, openCounts(c))`, where the
   *  union transfer is legitimately what the operator does this time. */
  private def fixpoint(init: Space, recm: SpaceMention, body: Space, env: Env, depth: Int,
                       pos: Vector[Int])(using b: Budget, v: ShapeVisitor): Shape =
    val i0 = goShape(init, env, depth + 1, pos :+ 0, "child")
    val w0 = Shape.weaken(i0)
    var round = 0
    def step(t: Shape): Shape =
      val r = Shape.weaken(goShape(body, env.copy(spaces = env.spaces + (recm -> SpatialType(t, SpaceType.unknown))),
                                   depth + 1, pos :+ 1, s"fixpoint-round=$round"))
      round += 1
      r
    var t = w0
    var k = 0
    var ok = false
    while k < SpatialConfig.default.fixpointRounds && !ok do
      val j = Shape.joinAlternatives(t, step(t))
      if Shape.leq(j, t) then ok = true
      else { t = if k >= SpatialConfig.default.fixpointWiden then Shape.widen(j) else j; k += 1 }
    // the certificate, re-checked on the accepted candidate; widen once and retry if it fails
    def certified(c: Shape): Boolean = Shape.leq(step(c), c) && Shape.leq(w0, c)
    val cand = if ok && certified(t) then Some(t)
               else { val w = Shape.widen(t); if certified(w) then Some(w) else None }
    cand match
      case Some(c) => Shape.unionTransfer(i0, Shape.openCounts(c))
      case None => Shape.unionTransfer(i0, Shape.top)   // no certified post-fixpoint ⇒ ⊤
    end match

  /** an upper bound on how many paths a `Range(_, start, end)` window keeps, from the source's SHAPE
   *  size and the static arithmetic of [[RangeBounds.normalize]].  Windows whose width depends on the
   *  (unknown) source size fall back to that size. */
  private def windowWidth(src: Ivl, start: Int, end: Int): Long =
    val static: Long =
      if start == 0 && end == 0 then Ivl.INF
      else if end > 0 && start > 0 then Ivl.relu(end.toLong - start.toLong)
      else if end > 0 && start == 0 then end.toLong
      else if end < 0 && start < 0 then Ivl.relu(end.toLong - start.toLong)
      else if end == 0 && start < 0 then -start.toLong
      else Ivl.INF
    static min src.hi

  // ---- the consumer-facing entry points ---------------------------------------------------------
  /** every validated proposition the analysis licenses about `s` under `env`.  For facts at a
   *  SPECIFIC OCCURRENCE, under the binder environment that occurrence was analysed in, use
   *  [[SpatialAnalysis.of]] and index by [[NodeId]] — this entry point re-infers from scratch. */
  def facts(s: Space, env: Env = Env()): Vector[Fact] = Fact.from(infer(s, env))

  /** THE PREFIX QUERY.  `true` PROVES that no path of any space admitted by `t` starts with
   *  `prefix` — a closed head set, or a tracked head whose subtree does not continue that way.  This
   *  is what makes `Fact.PrefixAbsent` a fact somebody can obtain (review.md 6). */
  def prefixAbsent(t: SpatialType, prefix: List[PathItem]): Boolean =
    t.uninhabited || t.isProvablyEmpty || !t.shape.mayHavePrefix(prefix)

  /** A specialisation carries its PRECONDITION as data.  `eliminateIn` used to hand back a bare
   *  `Routine` with the same name, so nothing stopped a caller installing a conditionally-valid
   *  body as a general replacement (review.md 5).  A `SpecializedRoutine` cannot be mistaken for
   *  one: the environment it assumed is attached, and [[accepts]] decides an actual input against
   *  it, which is what a guarded dispatcher needs. */
  final case class SpecializedRoutine(precondition: Map[SpaceMention, SpatialType],
                                      residual: Routine, facts: Vector[Fact]):
    /** may this specialisation be used for these actual arguments?  Decided with the EXACT predicate
     *  [[accepts]], not the weaker [[withinEnvelope]]: a dispatcher that admits an argument outside
     *  the precondition installs a conditionally-valid body on an input that violates the condition,
     *  which is the failure review.md 5 is about. */
    def applicableTo(args: Map[SpaceMention, SpaceValue]): Boolean =
      precondition.forall((m, t) => args.get(m).exists(v => SpatialTyping.accepts(v, t)))

  /** THE WEAK ENVELOPE CHECK — deliberately WEAKER than γ, and named so.
   *
   *  The SHAPE half is exact — it is full γ-membership ([[Shape.contains]]).  The HISTOGRAM half is
   *  an ENVELOPE check: it verifies every class the value actually populates plus the totals, but it
   *  does not verify a per-class LOWER bound for a class the value leaves empty.  That gap is real
   *  and is exhibited by `SpatialLawCheck`: this predicate ADMITS VALUES OUTSIDE γ, so a dispatcher
   *  built on it can select a conditionally-valid body for an input the condition excludes.
   *  [[accepts]] is the version without the gap, and it is what every gate and every dispatcher
   *  uses.  (Renamed from `satisfies` — review.md 1: the attractive everyday verb must not name the
   *  unsafe operation.) */
  def withinEnvelope(v: SpaceValue, t: SpatialType): Boolean =
    if t.uninhabited then false
    else
      val n = v.paths.size.toLong
      val sz = t.size
      val byLen = v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap
      sz.lo <= n && n <= sz.hi &&
        byLen.forall((l, c) => { val i = t.lens.at(l); i.lo <= c && c <= i.hi }) &&
        byLen.keys.forall(l => { val b = t.len; !b.isEmpty && b.lo <= l && l <= b.hi }) &&
        Shape.contains(t.shape, v)

  // `satisfies` is GONE, not deprecated: review.md 1 calls the attractive everyday verb on the unsafe
  // operation an API trap, and a deprecated alias leaves the trap reachable.  Use `accepts` for γ,
  // `withinEnvelope` when the weak envelope is genuinely what is wanted (only the gap measurement in
  // `SpatialLawCheck` wants it).

  /** FULL γ-MEMBERSHIP on the reduced product — THE canonical name (review.md 1).  Delegates to the
   *  single implementation, [[SpatialType.accepts]]; the local copy this file used to carry (a second
   *  spelling of `Shape.contains` plus a second spelling of the histogram invariant) is gone. */
  def accepts(v: SpaceValue, t: SpatialType): Boolean = SpatialType.accepts(t, v)
  /** the previous name of [[accepts]], kept as an alias to save churn (review.md 1 allows it) */
  def gammaMember(v: SpaceValue, t: SpatialType): Boolean = accepts(v, t)
end SpatialTyping
