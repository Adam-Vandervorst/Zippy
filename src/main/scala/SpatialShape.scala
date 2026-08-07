package morkl

import scala.collection.immutable.SortedMap

/** SPATIAL SHAPE — a bounded abstract trie, the shape component the length histogram cannot express.
 *
 *  `SpaceType` (SpatialTypes.scala) counts paths per LENGTH, so it identifies spaces that differ
 *  structurally: `{a.0, a.1, a.2, a.3}` and `{a.0, b.0, c.0, d.0}` are both `{len 2: [4,4]}`, yet
 *  iterating and returning the group head yields ONE path for the first and FOUR for the second.
 *  Head grouping is the semantics of `Iteration`, prefix sharing is the dominant fact about a trie,
 *  and both are invisible to a histogram.  This domain adds them.
 *
 *  ==THE CARRIER AND ITS γ (the four channels)==
 *  A `Shape` abstracts a `SpaceValue` (a finite set of `PathValue`).  Write `groups(V)` for
 *  `{h ↦ {t : h::t ∈ V}}` and `U(V) = groups(V).keys ∖ heads.keys` (the UNTRACKED heads).
 *  `V ∈ γ(sh)` iff all four channels hold:
 *
 *    (a) EPSILON.  `eps = No` ⇒ ε ∉ V;  `eps = Must` ⇒ ε ∈ V;  `eps = May` ⇒ either.
 *    (b) TRACKED HEADS.  for every `h ↦ c` in `heads`: `groups(V)(h) ∈ γ(c)` (with `∅` when `h` is
 *        concretely absent — so a child that forces ε *is* the claim "the path h is present").
 *    (c) UNTRACKED-HEAD COUNT.  `others.lo ≤ |U(V)| ≤ others.hi`.  `others.hi = 0` (`headsClosed`)
 *        is the closed-head-set case: it is what licenses exact head counts and absent-prefix facts.
 *    (d) OTHER-TAIL SUMMARY.  `otherTail = Some(ot)` ⇒ for EVERY `h ∈ U(V)`, `groups(V)(h) ∈ γ(ot)`
 *        (per-head, NOT the union — see the note below);  `None` means ⊤.
 *
 *  [[Shape.contains]] IS this predicate, and it is the only implementation of it in the tree:
 *  `SpatialGamma.gammaShape` and `SpatialType.accepts` both forward here (review.md 6 — there used to
 *  be three copies).  The PER-HEAD reading of (d) is the
 *  one deliberately chosen: it makes every binary transfer's `otherTail` a per-head-to-per-head
 *  obligation (sound by induction), and it costs precision in exactly one place — [[tailsUnion]],
 *  which aggregates ACROSS heads and therefore has to open the count channels of `ot`
 *  ([[openCounts]]) before folding it in.
 *
 *  ==FINITENESS==
 *  [[Shape.MaxDepth]] levels and [[Shape.MaxHeads]] tracked heads per level.  Excess depth collapses
 *  to an untracked-head count ([[capDepth]]); excess width spills into `others` + `otherTail`
 *  ([[mk]]).  Both only ever loosen.  Every transfer carries a budget `d` and every value produced
 *  by `mk` satisfies `depth ≤ MaxDepth`, so `Shape` is a finite tree.
 *
 *  ==NO EVALUATION==
 *  Every fact here comes from the term's syntax (literal paths, constant path prefixes), from
 *  declared input shapes, or from a transfer.  Nothing in this file or in [[SpatialTyping]] calls
 *  `eval`/`evalI`/`evalT`/`exec*`.  `contains` is a predicate on a value the caller already has.
 *
 *  ==ONE OWNER (review.md 6)==
 *  THIS OBJECT owns every lattice operation of the SHAPE carrier, and no other file may restate one:
 *
 *  | law                                   | the one implementation      | who delegates to it                      |
 *  |---------------------------------------|-----------------------------|------------------------------------------|
 *  | γ (full membership, four channels)    | [[Shape.contains]]          | `SpatialGamma.gammaShape`, `SpatialType.accepts` |
 *  | the ORDER `γ_may(a) ⊆ γ_may(b)`       | [[Shape.leq]]               | `SpatialGamma.leqShape`, `SpatialRecursion.leq`  |
 *  | the JOIN (lub of alternatives)        | [[Shape.joinAlternatives]]  | `SpatialGamma.lubShape`, `SpatialType.join`      |
 *  | the MEET (glb / reduction)            | [[Shape.meet]]              | `SpatialType.meet`, `SpatialType.reduce`         |
 *  | the WIDENING                          | [[Shape.widen]]             | `SpatialTyping.fixpoint`, `SpatialRecursion`     |
 *  | the UNION TRANSFER (`A ∪ B`)          | [[Shape.unionTransfer]]     | every `Union`-shaped transfer                    |
 *
 *  The two operations that are constantly confused have names that make the law visible at the call
 *  site: [[unionTransfer]] is the transfer for the set operation `A ∪ B` (it keeps the left operand's
 *  MUST claims and ADDS the untracked-head counts), [[joinAlternatives]] is the lattice lub (it keeps
 *  no lower bound and MAXes the counts).  Using the first where the second is meant is what made the
 *  `Fixpoint` Kleene chain unsound; the old spellings `union`/`lub`/`widenShape` remain as deprecated
 *  aliases so no call site breaks while the tree migrates.
 *
 *  ==============================================================================================
 *  THE PER-OPERATOR MAY/MUST TABLE  (written before the code — review.md finding 1)
 *  ==============================================================================================
 *  Four soundness bugs were found bringing this domain up and every one was the same family: an
 *  operation that can DELETE members (`∩`, `∖`, `<|`, `Range`, an iteration group that need not run,
 *  anything meeting ⊤) leaking MUST information through one of the four channels.  The previous fix
 *  was to make the whole domain may-only.  Below, MUST is restored channel by channel with the
 *  argument that licenses it; where no argument exists the entry says MAY-ONLY and why.
 *
 *  Legend: `x`,`y` operands; `c_x(h) = x.under(h)`; "may" = the upper (γ-permitting) claim, "must" =
 *  the lower (γ-forcing) claim.  ✓ = MUST restored, ∅ = deliberately may-only.
 *
 *  | op            | (a) eps                    | (b) tracked head h          | (c) others                                  | (d) otherTail            |
 *  |---------------|----------------------------|-----------------------------|---------------------------------------------|--------------------------|
 *  | Empty         | No ✓                       | none                        | [0,0] ✓                                     | None                     |
 *  | Literal/of    | Must/No exactly ✓          | exact child ✓               | [0,0], or exact count at the depth cap ✓     | ⊤ at the cap             |
 *  | Singleton p   | p≡ε: Must ✓; \|p\|≥1: No ✓ | none (content unknown)      | \|p\|≥1 ⇒ [1,1] ✓ (exactly one head)         | ⊤                        |
 *  | Union         | `or` ✓ (A∪B ⊇ A)           | `unionTransfer` of children ✓| lo = max over sides MINUS the keys the other side newly tracks ✓ (max alone is UNSOUND: b may track a's untracked head); hi = sum | `unionTransfer` of both ots |
 *  | Intersection  | `and` ✓ (ε in both ⇒ ε in ∩)| `inter` of children ✓ — must survives only through the ε chain, which is the only member two sets are both KNOWN to share | lo = 0 ∅ (∩ deletes); hi = min; closed on either side closes the result | `inter`, weakened        |
 *  | Subtraction   | `minus` ✓                  | `sub`; when `y` is CLOSED and h ∉ y.keys the subtrahend is exactly ∅, so the child passes through UNCHANGED ✓ | lo = x.others.lo minus \|y's live keys the result does not track\|, only when y is closed ✓; else 0 ∅. hi = x.others.hi | weaken(x.ot)             |
 *  | Restriction   | `and` ✓ (only ε prefixes ε) | y.eps=Must ⇒ child = c_x(h) unchanged ✓; y.eps=May ⇒ union(weaken x, restrict(x, y∖ε)) — must from the ε-free part ✓; else `restrict` | lo = 0 ∅ (a prefix set deletes); hi = min; closed on either side closes | weaken(x.ot)             |
 *  | Raffination   | via `sub(x, restrict(x,y))` — sound because `restrict`'s MUST under-approximates (so the subtracted upper is a true upper) and its MAY over-approximates (so the surviving must is a true must) | as sub | as sub | as sub |
 *  | Wrap p (const)| No ✓ (\|p\|≥1)             | the single head p₀, child = wrap(rest) ✓ — a bijection, so MUST is exact | [0,0] ✓                    | None                     |
 *  | Wrap p (open) | \|p\|≥1 ⇒ No ✓             | none                        | [1,1] if x is must-nonempty ✓ (all results share p's first item) | ⊤             |
 *  | Unwrap p (const)| c = descend(p) exactly ✓  | c's children ✓              | c's ✓                                       | c's ✓                    |
 *  | Unwrap p (open) | MAY-ONLY ∅ — a subset of the union of the level-\|p\| tail-sets (`tailsUnion` iterated), which is real structure and not ⊤ whenever `\|p\|` is bounded | ∅ | ∅ | ∅ |
 *  | TailsUnion    | `or` over children ✓ (a child that forces ε forces its head, so its head IS present) | union of children ✓ | union's ✓                  | openCounts(weaken(ot)) — the ONE place the per-head reading of (d) costs precision |
 *  | TailsInter    | Must only when the head set is CLOSED and every live head is MUST-present, i.e. the participant set is exactly known ✓; otherwise ∅ — intersecting children of MAY-present heads is UNSOUND (an absent head does not participate, so the true result can be LARGER than the intersection) | as eps | lo = 0 ∅ | as eps |
 *  | Composition   | `and` ✓ (ε = ε·ε only)     | graft: c(h) = comp(c_x(h), y) ✓; plus (ε ∈ x ⇒ all of y) ✓ | lo = x.others.lo when y is must-nonempty ✓; hi = x.others.hi | comp(x.ot, y)  |
 *  | Range(lo,hi)  | whole window ⇒ x unchanged ✓; else MAY-ONLY ∅ — a positional slice deletes, and which paths it keeps depends on a global order the trie does not model | ∅ | lo = 0 ∅; hi = min(x.others.hi, window width) | x's, weakened |
 *  | Iteration     | union over head-groups; a group whose head is only MAY-present need not run, so its body is weakened; a MUST-present head's group DOES run and contributes must ✓.  An open head set adds one weakened body analysed with the head symbol UNBOUND and `rest` bound to weaken(ot) | as eps | as eps | as eps |
 *  | Fold          | same as Iteration but the accumulator ref is UNBOUND (⊤ wherever the body reads it).  MUST survives for bodies that do not read the accumulator ✓ | as eps | as eps | as eps |
 *  | Fixpoint      | Kleene over shapes with [[leq]] as the order, [[widen]] as the widening, and the post-fixpoint checked on `union(t, F#(t)) ⊑ t` — the SAME order.  The result is `union(shape(init), weaken(t))`: MAY from the verified post-fixpoint, MUST from `init` only, because the concrete accumulator provably contains `init` and nothing else is guaranteed ✓ | as eps | as eps | as eps |
 *  | Call          | interprocedural: the callee body under parameters bound to the argument shapes, guarded by an active set.  MUST flows through because a body denotes a function of its parameters ✓.  A recursive occurrence ⇒ ⊤ | as eps | as eps | as eps |
 *  | GroundedPS/SS | ⊤ — an arbitrary Scala function; NOTHING is claimed ∅ | ∅ | ∅ | ∅ |
 *  | Mention       | the declared input shape, or ⊤ ∅ | | | |
 *
 *  MEETING ⊤ never yields MUST: `x.under(h)` for an untracked `h` of an open shape returns
 *  `weaken(otherTail | ⊤)`, so no transfer can read a must claim out of the untracked side.
 *
 *  Everything above is an argument, not a machine proof.  What has actually been checked is stated
 *  in `SpatialShapeCheck`: the corpus γ-gate and the randomized per-operator differential matrix. */
enum Presence:
  case No, May, Must
  def mayBe: Boolean = this != Presence.No
  def mustBe: Boolean = this == Presence.Must
  /** the union of two presences: ε ∈ A ∪ B iff ε ∈ A or ε ∈ B */
  def or(o: Presence): Presence =
    if this == Presence.Must || o == Presence.Must then Presence.Must
    else if this == Presence.May || o == Presence.May then Presence.May else Presence.No
  /** the intersection: ε ∈ A ∩ B iff ε ∈ A and ε ∈ B */
  def and(o: Presence): Presence =
    if this == Presence.No || o == Presence.No then Presence.No
    else if this == Presence.Must && o == Presence.Must then Presence.Must else Presence.May
  /** `this` minus `o` */
  def minus(o: Presence): Presence =
    if this == Presence.No || o == Presence.Must then Presence.No
    else if this == Presence.Must && o == Presence.No then Presence.Must else Presence.May
  /** drop the must claim, keep the may claim */
  def weak: Presence = if this == Presence.Must then Presence.May else this
  /** the MEET: both claims hold at once.  `None` is a CONTRADICTION (`No` against `Must`), which is
   *  the only way two sound presences about the same set can be inconsistent. */
  def meet(o: Presence): Option[Presence] = (this, o) match
    case (Presence.No, Presence.Must) | (Presence.Must, Presence.No) => None
    case (Presence.No, _) | (_, Presence.No) => Some(Presence.No)
    case (Presence.Must, _) | (_, Presence.Must) => Some(Presence.Must)
    case _ => Some(Presence.May)

final case class Shape(eps: Presence,
                       heads: SortedMap[PathItem, Shape],
                       others: Ivl,
                       otherTail: Option[Shape]):
  import Lower.LenBounds

  /** number of levels below this node — memoised so [[Shape.capDepth]] is a no-op when it can be */
  lazy val depth: Int =
    var d = -1
    for (_, t) <- heads do d = d max t.depth
    for t <- otherTail do d = d max t.depth
    d + 1

  /** is the head set exactly `heads.keys`? — the property that licenses exactness */
  def headsClosed: Boolean = others.hi == 0
  /** no information at all — the fixed point of every widening, and the recursion stopper */
  def isTop: Boolean = eps == Presence.May && heads.isEmpty && others == Ivl.unknown && otherTail.isEmpty

  /** the number of DISTINCT heads: the group count of an `Iteration` over this space.  The lower
   *  bound counts MUST-present heads (a tracked head whose tail-set is definitely non-empty, plus
   *  `others.lo`); the upper counts every head that MAY be present. */
  def headCount: Ivl =
    Ivl(Ivl.add(heads.count((_, t) => t.definitelyNonEmpty).toLong, others.lo),
        Ivl.add(heads.count((_, t) => t.possiblyNonEmpty).toLong, others.hi))

  def definitelyEmpty: Boolean =
    eps == Presence.No && others.hi == 0 && heads.forall((_, t) => t.definitelyEmpty)
  /** MUST-non-emptiness.  Justified by exactly the three must channels: a forced ε, a forced
   *  untracked head, or a tracked head whose tail-set is itself forced non-empty. */
  def definitelyNonEmpty: Boolean =
    eps == Presence.Must || others.lo >= 1 || heads.exists((_, t) => t.definitelyNonEmpty)
  def possiblyNonEmpty: Boolean = !definitelyEmpty

  /** the cardinality this shape implies.  Lower: the disjoint sum of the forced parts (ε, each
   *  tracked child's minimum, one path per forced untracked head).  Upper: `others.hi` untracked
   *  heads each carrying at most `otherTail`'s worth of tails (the PER-HEAD reading of channel d). */
  def size: Ivl =
    if definitelyEmpty then Ivl.zero
    else
      var lo = if eps == Presence.Must then 1L else 0L
      var hi = if eps.mayBe then 1L else 0L
      for (_, t) <- heads do
        val c = t.size
        lo = Ivl.add(lo, c.lo); hi = Ivl.add(hi, c.hi)
      lo = Ivl.add(lo, others.lo)
      if others.hi > 0 then
        hi = otherTail match
          case Some(t) => Ivl.add(hi, Ivl.mul(others.hi, t.size.hi))
          case None => Ivl.INF
      Ivl(lo, if hi < lo then lo else hi)

  /** the path lengths this shape permits (`lo > hi` marks the empty space).  This is a ∀-path MAY
   *  fact — "every path present has length in [lo, hi]" — so it is read off the may channels. */
  def lens: LenBounds =
    if definitelyEmpty then LenBounds.empty
    else
      var lo = LenBounds.INF; var hi = 0L; var any = false
      def bump(child: LenBounds): Unit =
        if !child.isEmpty then
          any = true
          lo = lo min Ivl.add(1L, child.lo)
          hi = if child.hi == LenBounds.INF || hi == LenBounds.INF then LenBounds.INF else hi max (child.hi + 1)
      if eps.mayBe then { lo = 0L; any = true }
      for (_, t) <- heads if t.possiblyNonEmpty do bump(t.lens)
      if others.hi > 0 then
        otherTail match
          case Some(t) => bump(t.lens)
          case None => any = true; lo = lo min 1L; hi = LenBounds.INF
      if !any then LenBounds.empty else LenBounds(lo, hi)

  /** `K_d` — the number of DISTINCT length-`d` prefixes the shape permits.  At depth 0 there is one
   *  prefix (ε) iff the space is non-empty; at depth 1 every untracked head is one prefix; BELOW
   *  depth 1 `otherTail` is a may-only PER-UNTRACKED-HEAD summary, so it supplies an upper bound and
   *  no positive lower bound.  (The formula is whispers.md §1's `rawPrefixesAt`, taken as-is: the
   *  `d == 1` special case is the load-bearing part.)
   *
   *  This is the quantity the reducer meets against the histogram's `E_d` (paths with at least `d`
   *  items): every qualifying path lies in exactly one prefix fibre, so `K_d ≤ E_d`, and `E_d > 0`
   *  forces `K_d > 0`. */
  def prefixesAt(d: Int): Ivl =
    require(d >= 0, s"prefix depth must be non-negative, got $d")
    if d == 0 then
      if definitelyEmpty then Ivl.zero
      else if definitelyNonEmpty then Ivl(1, 1)
      else Ivl(0, 1)
    else
      var lo = 0L; var hi = 0L
      for (_, child) <- heads do
        val c = child.prefixesAt(d - 1)
        lo = Ivl.add(lo, c.lo); hi = Ivl.add(hi, c.hi)
      if others.hi > 0 then
        if d == 1 then { lo = Ivl.add(lo, others.lo); hi = Ivl.add(hi, others.hi) }
        else hi = Ivl.add(hi, Ivl.mul(others.hi, otherTail.getOrElse(Shape.top).prefixesAt(d - 1).hi))
      Ivl(lo, if hi < lo then lo else hi)

  /** may this space contain a path starting with `items`? — `false` is a PROOF of absence */
  def mayHavePrefix(items: List[PathItem]): Boolean = items match
    case Nil => possiblyNonEmpty
    case h :: t => heads.get(h) match
      case Some(c) => c.mayHavePrefix(t)
      case None => !headsClosed          // an untracked head could be `h`
  /** is `h` DEFINITELY a head of this space? */
  def mustHaveHead(h: PathItem): Boolean = heads.get(h).exists(_.definitelyNonEmpty)

  /** descend under a known head.  For an untracked head of an OPEN shape this is the `otherTail`
   *  summary, WEAKENED: channel (d) is a may-only summary of a set we cannot name, so reading a must
   *  claim out of it would be exactly the ⊤-meets-must leak this domain kept hitting. */
  def under(h: PathItem): Shape =
    heads.getOrElse(h, if headsClosed then Shape.empty else Shape.weaken(otherTail.getOrElse(Shape.top)))

  def show: String =
    if definitelyEmpty then "∅"
    else
      val e = if eps == Presence.Must then Vector("ε!") else if eps == Presence.May then Vector("ε?") else Vector.empty
      val hs = heads.iterator.filter(_._2.possiblyNonEmpty).map((h, t) => s"${h}·${t.show}").toVector
      val o = if others.hi == 0 then Vector.empty else Vector(s"+${others.show} more")
      "{" + (e ++ hs ++ o).mkString(", ") + "}"

object Shape:
  import Lower.LenBounds
  /** THE budgets, read from the ONE analysis configuration ([[SpatialConfig]]) rather than spelled
   *  out here — review.md 6 asks for a single value carrying every budget.  They stay `val`s because
   *  the carrier's finiteness argument is about the whole domain, not about one query: a `Shape`
   *  built under one depth cap must be comparable with one built under another, so the cap belongs to
   *  the domain, not to a call.  A per-call cap would need `Shape` to carry its own budget. */
  val MaxDepth: Int = SpatialConfig.default.shapeDepth
  val MaxHeads: Int = SpatialConfig.default.shapeWidth

  val empty: Shape = Shape(Presence.No, SortedMap.empty, Ivl.zero, None)
  /** no information: ε may be there and any heads may be there */
  lazy val top: Shape = Shape(Presence.May, SortedMap.empty, Ivl.unknown, None)
  /** exactly the empty path */
  val epsOnly: Shape = Shape(Presence.Must, SortedMap.empty, Ivl.zero, None)

  // -----------------------------------------------------------------------------------------------
  // γ  (a local copy of SpatialGamma.gammaShape, so this domain's own gate is self-contained)
  // -----------------------------------------------------------------------------------------------
  /** `contains(sh, v)` decides `v ∈ γ(sh)` over the four channels documented on [[Shape]]. */
  def contains(sh: Shape, v: SpaceValue): Boolean = contains(sh, v, 64)
  private def contains(sh: Shape, v: SpaceValue, d: Int): Boolean =
    if d <= 0 then true
    else
      val hasEps = v.paths.contains(PathValue(Nil))
      val epsOk = sh.eps match
        case Presence.No => !hasEps
        case Presence.Must => hasEps
        case Presence.May => true
      if !epsOk then false
      else
        val groups: Map[PathItem, SpaceValue] =
          v.paths.iterator.collect { case PathValue(h :: t) => (h, PathValue(t)) }
            .toVector.groupMap(_._1)(_._2).view.mapValues(ts => SpaceValue(ts.toSet)).toMap
        val tracked = groups.filter((h, _) => sh.heads.contains(h))
        val untracked = groups.filter((h, _) => !sh.heads.contains(h))
        val n = untracked.size.toLong
        sh.others.lo <= n && n <= sh.others.hi &&
          tracked.forall((h, tv) => contains(sh.heads(h), tv, d - 1)) &&
          sh.heads.forall((h, c) => tracked.contains(h) || contains(c, SpaceValue(Set.empty), d - 1)) &&
          (sh.otherTail match
            case Some(ot) => untracked.forall((_, tv) => contains(ot, tv, d - 1))
            case None => true)

  // -----------------------------------------------------------------------------------------------
  // structural utilities
  // -----------------------------------------------------------------------------------------------
  /** drop every MUST claim at every depth, keeping the may structure: what survives an operation
   *  that can delete members.  Total (the previous version stopped at `MaxDepth` and left the
   *  deepest level's musts intact, which is a leak, not an imprecision). */
  def weaken(s: Shape): Shape =
    if s.definitelyEmpty then s
    else Shape(s.eps.weak, SortedMap.from(s.heads.view.mapValues(weaken)), Ivl(0, s.others.hi), s.otherTail.map(weaken))

  /** open every COUNT channel.  Head-set membership and closedness are union-closed facts, but "at
   *  most k untracked heads" is not, so this is what survives aggregating an unknown number of sets
   *  each admitted by `s` — used by [[tailsUnion]] on the per-head `otherTail` summary. */
  def openCounts(s: Shape): Shape =
    if s.definitelyEmpty then s
    else Shape(s.eps.weak, SortedMap.from(s.heads.view.mapValues(openCounts)),
               if s.others.hi == 0 then Ivl.zero else Ivl(0, Ivl.INF), s.otherTail.map(openCounts))

  /** collapse everything below level `d` into an untracked-head count.  Sound in both directions:
   *  `headCount` brackets the real number of heads and the tails become ⊤. */
  def capDepth(s: Shape, d: Int): Shape =
    if s.depth <= d then s
    else if d <= 0 then
      val hc = s.headCount
      if hc.hi == 0 then Shape(s.eps, SortedMap.empty, Ivl.zero, None)
      else Shape(s.eps, SortedMap.empty, hc, None)
    else Shape(s.eps, SortedMap.from(s.heads.view.mapValues(capDepth(_, d - 1))), s.others,
               s.otherTail.map(capDepth(_, d - 1)))

  /** THE normalising smart constructor.  Establishes every representation invariant:
   *  children are ≤ `MaxDepth-1` deep and never definitely-empty (a definitely-absent head is
   *  simply not tracked), `otherTail` is may-only and never definitely-empty, `others` is a
   *  consistent interval, and at most `MaxHeads` heads are tracked. */
  private def mk(eps: Presence, hs: Iterable[(PathItem, Shape)], others0: Ivl, ot0: Option[Shape]): Shape =
    val live = hs.iterator.map((h, t) => h -> capDepth(t, MaxDepth - 1))
      .filter(_._2.possiblyNonEmpty).toVector.sortBy(_._1)
    val ot1 = ot0.map(t => weaken(capDepth(t, MaxDepth - 1)))
    // an untracked head has a NON-EMPTY tail-set by definition, so a definitely-empty summary means
    // there are no untracked heads at all
    val (others1, ot2) = ot1 match
      case Some(t) if t.definitelyEmpty => (Ivl.zero, None)
      case x => (others0, x)
    val hiC = if others1.hi < 0 then 0L else others1.hi
    val loC = if others1.lo < 0 then 0L else others1.lo min hiC
    val others = Ivl(loC, hiC)
    val ot = if hiC == 0 then None else ot2
    if live.size <= MaxHeads then Shape(eps, SortedMap.from(live), others, ot)
    else
      val keep = live.take(MaxHeads); val spill = live.drop(MaxHeads)
      val base = if hiC == 0 then empty else ot.getOrElse(top)
      val tail = spill.foldLeft(base)((a, kv) => unionTransfer(a, weaken(kv._2)))
      val cnt = Ivl(Ivl.add(others.lo, spill.count((_, t) => t.definitelyNonEmpty).toLong),
                    Ivl.add(others.hi, spill.size.toLong))
      Shape(eps, SortedMap.from(keep), cnt,
            if tail.isTop then None else Some(weaken(capDepth(tail, MaxDepth - 1))))

  /** the ORDER: `leq(a, b)` ⇒ every value `b`'s may channels reject, `a`'s reject too, i.e.
   *  `γ_may(a) ⊆ γ_may(b)`.  Conservative and incomplete — a `false` on a genuine inclusion only
   *  costs the `Fixpoint` iteration another widening round.  This is the order the post-fixpoint
   *  check uses, and it is the same one used to decide convergence.
   *
   *  It compares the union of BOTH live key sets, not just `a`'s.  Comparing only `a`'s was unsound:
   *  a key `h` that `a` leaves UNTRACKED (so `a` admits it via `others`/`otherTail`) but that `b`
   *  TRACKS has to satisfy `b`'s child for `h`, and nothing else in the check looks at that pair.
   *  Witness found by the randomized order matrix (129 raw cases):
   *  `leq({ε!, +[1,inf] more}, {ε?, a·{b·{…}}, …, +[0,inf] more})` was accepted, yet `{a, ε}` is in
   *  γ_may of the first and not of the second (`b`'s child for `a` has `eps = No`).
   *  `a.under(h)` already returns the right thing for an untracked `h` — `∅` when `a` is closed
   *  (so the arm is vacuous) and the weakened `otherTail` when it is open. */
  /** THE TWO READINGS OF THE ORDER, side by side, in the one file that owns the carrier.  They are
   *  NOT duplicates and neither may be deleted; what was wrong (review.md 6) was having them in two
   *  files under one name.  [[leq]] is the MAY-ONLY order used by the `Fixpoint` Kleene chain (whose
   *  iterates are deliberately may-only) and by `SpatialRecursion`'s may-only summaries; [[leqStrong]]
   *  is the STRONG-γ order (`γ(a) ⊆ γ(b)`, must channels included) that `SpatialGamma.leq` /
   *  `SpatialType.leq` publish.  They differ in exactly four places:
   *
   *  | channel        | [[leq]]  (γ_may)                          | [[leqStrong]]  (γ)                        |
   *  |----------------|-------------------------------------------|-------------------------------------------|
   *  | a = ∅          | `true` (∅ is in every γ_may)              | no short-circuit: `b` must ADMIT ∅        |
   *  | ε              | `b.eps = No ⇒ a.eps = No`                 | `b.eps ∈ {May} ∨ b.eps = a.eps`           |
   *  | others.lo      | ignored (no must claims)                  | `b.others.lo = 0` required                |
   *  | otherTail      | via `b.under(h)` on both key sets         | `a`'s b-untracked heads against `b.ot`    |
   */
  def leq(a: Shape, b: Shape): Boolean = leq(a, b, MaxDepth + 2)
  private def leq(a: Shape, b: Shape, d: Int): Boolean =
    if a.definitelyEmpty then true
    else if b.isTop then true
    else if d <= 0 then false
    else if a.eps.mayBe && !b.eps.mayBe then false
    else
      val aLive = a.heads.iterator.filter((_, t) => t.possiblyNonEmpty).map(_._1).toSet
      val bLive = b.heads.iterator.filter((_, t) => t.possiblyNonEmpty).map(_._1).toSet
      // heads b does NOT track: a's own extra tracked ones, plus a's untracked ones
      val slack = Ivl.add(a.others.hi, (aLive diff bLive).size.toLong)
      if slack > b.others.hi then false
      else (aLive ++ bLive).forall(h => leq(a.under(h), b.under(h), d - 1)) &&
        (a.others.hi == 0 || leq(a.otherTail.getOrElse(top), b.otherTail.getOrElse(top), d - 1))

  /** the STRONG-γ order: `leqStrong(a, b)` ⇒ `γ(a) ⊆ γ(b)` with the must channels included.  Sound
   *  and deliberately INCOMPLETE — it does not attempt the integer-partition reasoning a spill bucket
   *  facing tracked classes would need; `SpatialLawCheck` measures that incompleteness against
   *  `SpatialGamma.gammaLeqOn`, which decides containment exactly on a finite universe.  Moved here
   *  verbatim from `SpatialGamma.leqShape`, which now forwards. */
  def leqStrong(a: Shape, b: Shape): Boolean = leqStrongMask(a, b, 32, full = false) == 0

  /** WHY [[leqStrong]] said no — the bit positions of [[leqStrongMask]].  `leqStrong` IS
   *  `leqStrongMask == 0`, so this is attribution, not a second order: review.md 4 asks for the
   *  cause of every avoidable `Unknown` to be MEASURED, and a boolean cannot be measured.
   *  `Child` marks "some head's sub-comparison failed"; the channel bits are OR-ed up from that
   *  sub-comparison too, so the mask names the root-cause channels of the whole tree. */
  object LeqShapeWhy:
    val Eps = 1        // (a) b's ε presence does not admit a's
    val CntLo = 2      // (c) b FORCES more untracked heads than a guarantees
    val CntHi = 4      // (c) a permits more untracked heads than b does
    val Tail = 8       // (d) some a-side tail-set is not inside b's otherTail summary
    val Depth = 16     // the 32-level comparison budget ran out on a non-⊤ right-hand side
    val Child = 32     // (b) a tracked/untracked head's sub-comparison failed
    val names: Vector[(Int, String)] = Vector(Eps -> "shape:eps", CntLo -> "shape:others.lo",
      CntHi -> "shape:others.hi", Tail -> "shape:otherTail", Depth -> "shape:depth-cap",
      Child -> "shape:child")
    def show(m: Int): Vector[String] = names.collect { case (bit, n) if (m & bit) != 0 => n }

  /** `full = false` reproduces [[leqStrong]]'s short-circuit exactly (so the production order pays
   *  nothing for the instrumentation); `full = true` visits every channel and every head, which is
   *  what the incompleteness histogram needs. */
  private[morkl] def leqStrongMask(a: Shape, b: Shape): Int = leqStrongMask(a, b, 32, full = true)
  private def leqStrongMask(a: Shape, b: Shape, d: Int, full: Boolean): Int =
    import LeqShapeWhy.*
    if d <= 0 then (if b.isTop then 0 else Depth)
    else if b.isTop then 0
    else
      var m = 0
      if !(b.eps == Presence.May || b.eps == a.eps) then m |= Eps
      if m != 0 && !full then m
      else
        val keys = a.heads.keySet ++ b.heads.keySet
        var cm = 0
        val it = keys.iterator
        while it.hasNext && (full || cm == 0) do
          val h = it.next()
          cm |= leqStrongMask(a.under(h), b.under(h), d - 1, full)
        if cm != 0 then m |= Child | cm
        if m != 0 && !full then m
        else
          // heads untracked in b: a's own extra tracked heads, plus a's untracked ones
          val hiOut = Ivl.add(a.heads.count((h, t) => !b.heads.contains(h) && t.possiblyNonEmpty).toLong, a.others.hi)
          // …and a LOWER bound on the same quantity, so `b`'s must claim can be discharged instead of
          // simply rejected.  Requiring `b.others.lo == 0` made the order NON-REFLEXIVE — `leqStrong(x, x)`
          // was false for every `x` with a forced untracked head — which the decorated analysis' "the root
          // is never weaker than `infer`" law needs (it failed on 24 of 400 corpus terms).  `a`'s own
          // forced untracked heads survive only after discounting the keys `b` newly TRACKS (they leave the
          // untracked set), the same discount `unionTransfer` and `meet` need.
          val bOnly = b.heads.keySet.diff(a.heads.keySet).size.toLong
          val loOut = Ivl.add(Ivl.relu(a.others.lo - bOnly),
                              a.heads.count((h, t) => !b.heads.contains(h) && t.definitelyNonEmpty).toLong)
          if b.others.lo > loOut then m |= CntLo
          if hiOut > b.others.hi then m |= CntHi
          if m != 0 && !full then m
          else
            b.otherTail match
              case None => m
              case Some(bt) =>
                var tm = 0
                val ti = a.heads.iterator
                while ti.hasNext && (full || tm == 0) do
                  val (h, t) = ti.next()
                  if !b.heads.contains(h) && t.possiblyNonEmpty then
                    tm |= leqStrongMask(t, bt, d - 1, full)
                if (full || tm == 0) && a.others.hi != 0 then
                  tm |= leqStrongMask(a.otherTail.getOrElse(top), bt, d - 1, full)
                if tm != 0 then m |= Tail
                m

  /** THE LATTICE JOIN — a ⊑-upper bound of both ALTERNATIVES: `γ(a) ⊆ γ(join(a,b)) ⊇ γ(b)`.
   *
   *  This is NOT [[unionTransfer]], and the names are what keep the two apart at the call site.
   *  `unionTransfer` abstracts the set operation `A ∪ B`: it may keep `a`'s MUST claims, because
   *  `A ∪ B ⊇ A` is a fact about the union, and it ADDS the untracked-head counts, because both
   *  operands' heads appear in the result.  Neither is true of a value drawn from ONE side, which is
   *  what a join has to admit.  Using the union transfer as a join is what made the `Fixpoint` Kleene
   *  chain unsound (see `SpatialTyping.fixpoint`).
   *
   *  Channel by channel, for `V ∈ γ(a)`: (a) `May` unless the two presences already agree; (b) the
   *  result tracks `a.heads.keys ∪ b.heads.keys`, and `a.under(h)` is a sound abstraction of
   *  `groups(V)(h)` for every one of those keys (`∅` when `a` is closed and does not track `h`);
   *  (c) `U_result(V) ⊆ U_a(V)`, so `max` of the two uppers bounds it and no lower bound survives
   *  the choice of side; (d) an untracked head of the result was untracked on whichever side `V`
   *  came from, so the summary must admit both. */
  def joinAlternatives(a: Shape, b: Shape): Shape = lub(a, b, MaxDepth)
  /** the old spelling — [[joinAlternatives]] says which of the two joins this is */
  @deprecated("use Shape.joinAlternatives (the lattice lub) or Shape.unionTransfer (the A ∪ B transfer)", "consolidation")
  def lub(a: Shape, b: Shape): Shape = lub(a, b, MaxDepth)
  private def lub(a: Shape, b: Shape, d: Int): Shape =
    // NO `definitelyEmpty` short-circuit.  `∅` is NOT below a must-carrying shape: γ(∅) = {∅} and a
    // shape with `eps = Must` (or a forced head) rejects `∅`, so `lub(∅, b) = b` loses a member.  The
    // general path is what handles it — it demotes b's musts because ∅ has to be admitted.  (The
    // short-circuit was written first and the order matrix caught it: 9417 raw cases.)
    if a.isTop || b.isTop then top
    else if d <= 0 then
      Shape(if a.eps == b.eps then a.eps else Presence.May, SortedMap.empty,
            Ivl(0, a.headCount.hi max b.headCount.hi), None)
    else
      val keys = a.heads.keySet ++ b.heads.keySet
      val hs = keys.toVector.map(h => h -> lub(a.under(h), b.under(h), d - 1))
      val others = Ivl(0, a.others.hi max b.others.hi)
      val ot =
        if others.hi == 0 then None
        else
          val at = if a.headsClosed then empty else a.otherTail.getOrElse(top)
          val bt = if b.headsClosed then empty else b.otherTail.getOrElse(top)
          val t = lub(at, bt, d - 1)
          if t.isTop then None else Some(t)
      mk(if a.eps == b.eps then a.eps else Presence.May, hs, others, ot)

  /** the WIDENING for the `Fixpoint` Kleene chain: open every count channel and every head set, so
   *  the only remaining growth is the (finite) tracked key sets and the (3-valued) ε channel. */
  def widen(s: Shape): Shape =
    if s.definitelyEmpty then s
    else Shape(s.eps, SortedMap.from(s.heads.view.mapValues(widen)), Ivl(s.others.lo, Ivl.INF), None)
  /** the old spelling of [[widen]] */
  @deprecated("use Shape.widen", "consolidation")
  def widenShape(s: Shape): Shape = widen(s)

  // -----------------------------------------------------------------------------------------------
  // THE MEET  (the glb — the operation the reduced product needs, review.md 5)
  // -----------------------------------------------------------------------------------------------
  /** THE MEET.  `meet(a, b) = Some(c)` with `γ(a) ∩ γ(b) ⊆ γ(c) ⊆ γ(a) ∩ γ(b)` up to the carrier's
   *  representation limits; `None` PROVES `γ(a) ∩ γ(b) = ∅`, i.e. no concrete space is admitted by
   *  both.  This is the operation a reduced product is built from, and the only sound way to combine
   *  two independently-derived sound approximations of the SAME value: both channels' strongest claim
   *  survives.
   *
   *  Channel by channel, for `V ∈ γ(a) ∩ γ(b)` and `K = a.heads.keys ∪ b.heads.keys` (the keys the
   *  result tracks):
   *
   *    (a) ε: [[Presence.meet]] — `No` against `Must` is the contradiction.
   *    (b) tracked head `h ∈ K`: `groups(V)(h)` is in both children's γ, so the child is their meet;
   *        a `None` there means NO tail-set qualifies, hence no `V` at all.
   *    (c) `U_result(V) = heads(V) ∖ K ⊆ U_a(V)`, so `min` of the two uppers bounds it.  The LOWER
   *        bound may not be `max` of the two: a head `a` leaves untracked may be TRACKED by `b` and
   *        therefore leave the result's untracked set, so each side's lower bound is discounted by the
   *        number of live keys the OTHER side newly tracks (exactly the discount [[unionTransfer]]
   *        needs, for the same reason).  `lo > hi` is a contradiction.
   *    (d) an untracked head of the result is untracked on BOTH sides, so its tail-set is in both
   *        summaries: the summaries meet.  A contradictory summary means there can be no untracked
   *        head at all, which forces `others = [0,0]` — and a contradiction if `others.lo > 0`.
   *
   *  `mk` then re-establishes the carrier invariants (may-only `otherTail`, no definitely-empty
   *  child, the depth/width caps), each of which only loosens — so the result is still an upper bound
   *  of the intersection, which is the direction soundness needs. */
  def meet(a: Shape, b: Shape): Option[Shape] = meetGo(a, b, MaxDepth)
  private def meetGo(a: Shape, b: Shape, d: Int): Option[Shape] =
    if a.isTop then Some(capDepth(b, d))
    else if b.isTop then Some(capDepth(a, d))
    else a.eps.meet(b.eps) match
      case None => None
      case Some(e) =>
        val aLive = a.heads.iterator.filter((_, t) => t.possiblyNonEmpty).map(_._1).toSet
        val bLive = b.heads.iterator.filter((_, t) => t.possiblyNonEmpty).map(_._1).toSet
        val oLo = Ivl.relu(a.others.lo - (bLive diff aLive).size.toLong) max
                  Ivl.relu(b.others.lo - (aLive diff bLive).size.toLong)
        val oHi = a.others.hi min b.others.hi
        if oLo > oHi then None
        else if d <= 0 then
          // out of budget: keep ε and the meet of the two head counts
          val hc = Ivl(a.headCount.lo max b.headCount.lo, a.headCount.hi min b.headCount.hi)
          if hc.lo > hc.hi then None
          else if hc.hi == 0 then Some(Shape(e, SortedMap.empty, Ivl.zero, None))
          else Some(Shape(e, SortedMap.empty, hc, None))
        else
          val keys = a.heads.keySet ++ b.heads.keySet
          val kids = Vector.newBuilder[(PathItem, Shape)]
          var dead = false
          for h <- keys if !dead do
            meetGo(a.under(h), b.under(h), d - 1) match
              case None => dead = true
              case Some(c) => kids += (h -> c)
          if dead then None
          else
            val (others, ot) =
              if oHi == 0 then (Ivl.zero, None)
              else
                val at = if a.headsClosed then empty else a.otherTail.getOrElse(top)
                val bt = if b.headsClosed then empty else b.otherTail.getOrElse(top)
                meetGo(at, bt, d - 1) match
                  case Some(t) if t.possiblyNonEmpty => (Ivl(oLo, oHi), if t.isTop then None else Some(t))
                  // no tail-set can inhabit an untracked head: there are none
                  case _ => if oLo > 0 then (Ivl(1, 0), None) else (Ivl.zero, None)
            if others.lo > others.hi then None
            else Some(mk(e, kids.result(), others, ot))

  // -----------------------------------------------------------------------------------------------
  // abstraction of a concrete value
  // -----------------------------------------------------------------------------------------------
  /** the EXACT trie of a literal, cut off at [[MaxDepth]] (where it keeps the exact head COUNT) */
  def of(v: SpaceValue, depth: Int = MaxDepth): Shape =
    if v.paths.isEmpty then empty
    else
      val hasEps = v.paths.contains(PathValue(Nil))
      val e = if hasEps then Presence.Must else Presence.No
      val groups = v.paths.iterator.collect { case PathValue(h :: t) => h -> PathValue(t) }
        .toVector.groupMap(_._1)(_._2)
      if depth <= 0 then
        Shape(e, SortedMap.empty, Ivl(groups.size.toLong, groups.size.toLong), None)
      else mk(e, groups.view.mapValues(ts => of(SpaceValue(ts.toSet), depth - 1)).toSeq, Ivl.zero, None)

  /** the shape of a single known path */
  def ofPath(p: PathValue, depth: Int = MaxDepth): Shape = of(SpaceValue(Set(p)), depth)

  /** exactly one path whose CONTENT is unknown but whose item-length is bracketed by `k` */
  def oneUnknownPath(k: LenBounds): Shape =
    if k.isEmpty then empty
    else if k.hi == 0 then epsOnly
    else if k.lo >= 1 then Shape(Presence.No, SortedMap.empty, Ivl(1, 1), None)
    else Shape(Presence.May, SortedMap.empty, Ivl(0, 1), None)

  // -----------------------------------------------------------------------------------------------
  // the transfers
  // -----------------------------------------------------------------------------------------------
  /** THE UNION TRANSFER — the abstraction of the set operation `A ∪ B`.  NOT a lattice join: see
   *  [[joinAlternatives]] for that, and the note there for why confusing the two was unsound. */
  def unionTransfer(a: Shape, b: Shape): Shape = union(a, b, MaxDepth)
  /** the old spelling — [[unionTransfer]] says which of the two joins this is */
  @deprecated("use Shape.unionTransfer (the A ∪ B transfer) or Shape.joinAlternatives (the lattice lub)", "consolidation")
  def union(a: Shape, b: Shape): Shape = union(a, b, MaxDepth)
  private def union(a: Shape, b: Shape, d: Int): Shape =
    if a.definitelyEmpty then capDepth(b, d)
    else if b.definitelyEmpty then capDepth(a, d)
    else if d <= 0 then
      Shape(a.eps.or(b.eps), SortedMap.empty,
            Ivl(a.headCount.lo max b.headCount.lo, Ivl.add(a.headCount.hi, b.headCount.hi)), None)
    else
      val ak = a.heads.keySet; val bk = b.heads.keySet
      val hs = (ak ++ bk).toVector.map(h => h -> union(a.under(h), b.under(h), d - 1))
      val others =
        if a.headsClosed && b.headsClosed then Ivl.zero
        else
          // a head untracked in `a` may be TRACKED in the result because `b` tracks it, so `max` of
          // the two lower bounds is UNSOUND on its own; discount the keys the other side adds.
          val loA = Ivl.relu(a.others.lo - (bk diff ak).size.toLong)
          val loB = Ivl.relu(b.others.lo - (ak diff bk).size.toLong)
          Ivl(loA max loB, Ivl.add(a.others.hi, b.others.hi))
      val ot =
        if others.hi == 0 then None
        else
          val at = if a.headsClosed then empty else a.otherTail.getOrElse(top)
          val bt = if b.headsClosed then empty else b.otherTail.getOrElse(top)
          val u = union(at, bt, d - 1)
          if u.isTop then None else Some(u)
      mk(a.eps.or(b.eps), hs, others, ot)

  def inter(a: Shape, b: Shape): Shape = inter(a, b, MaxDepth)
  private def inter(a: Shape, b: Shape, d: Int): Shape =
    if a.definitelyEmpty || b.definitelyEmpty then empty
    else if d <= 0 then
      Shape(a.eps.and(b.eps), SortedMap.empty, Ivl(0, a.headCount.hi min b.headCount.hi), None)
    else
      // a head survives only if BOTH sides may have it; either side being closed closes the result
      val keys =
        if a.headsClosed && b.headsClosed then a.heads.keySet intersect b.heads.keySet
        else if a.headsClosed then a.heads.keySet
        else if b.headsClosed then b.heads.keySet
        else a.heads.keySet ++ b.heads.keySet
      val hs = keys.toVector.map(h => h -> inter(a.under(h), b.under(h), d - 1))
      val others = if a.headsClosed || b.headsClosed then Ivl.zero else Ivl(0, a.others.hi min b.others.hi)
      val ot =
        if others.hi == 0 then None
        else
          val i = inter(a.otherTail.getOrElse(top), b.otherTail.getOrElse(top), d - 1)
          if i.isTop then None else Some(weaken(i))
      mk(a.eps.and(b.eps), hs, others, ot)

  def sub(a: Shape, b: Shape): Shape = sub(a, b, MaxDepth)
  private def sub(a: Shape, b: Shape, d: Int): Shape =
    if a.definitelyEmpty then empty
    else if b.definitelyEmpty then capDepth(a, d)
    else if d <= 0 then Shape(a.eps.minus(b.eps), SortedMap.empty, Ivl(0, a.headCount.hi), None)
    else
      val keys = a.heads.keySet
      val hs = keys.toVector.map(h => h -> sub(a.under(h), b.under(h), d - 1))
      // an untracked head of `a` that is not a head of `b` at all keeps its whole tail-set, so it
      // survives; only a CLOSED `b` lets us count how many could be hit.
      val lo =
        if b.headsClosed then
          Ivl.relu(a.others.lo - b.heads.count((h, t) => t.possiblyNonEmpty && !keys.contains(h)).toLong)
        else 0L
      val others = if a.headsClosed then Ivl.zero else Ivl(lo, a.others.hi)
      mk(a.eps.minus(b.eps), hs, others, if a.headsClosed then None else a.otherTail.map(weaken))

  /** prepend a known constant prefix — a bijection, so MUST is exact */
  def wrap(items: List[PathItem], s: Shape): Shape =
    if s.definitelyEmpty then empty else wrapGo(items, s, MaxDepth)
  private def wrapGo(items: List[PathItem], s: Shape, d: Int): Shape = items match
    case Nil => capDepth(s, d)
    case h :: t =>
      if d <= 0 then Shape(Presence.No, SortedMap.empty, Ivl(if s.definitelyNonEmpty then 1 else 0, 1), None)
      else mk(Presence.No, List(h -> wrapGo(t, s, d - 1)), Ivl.zero, None)

  /** prepend a prefix of UNKNOWN content.  With `|p| ≥ 1` known, every result path shares the
   *  prefix's first item, so there is exactly one head (or none, if `s` may be empty) — that is real
   *  information, not ⊤.  But when `|p|` may be ZERO the wrap may be the IDENTITY, in which case
   *  every head of `s` survives, so the result must admit both readings.  Claiming the single-head
   *  shape unconditionally was a soundness bug (found by the randomized operator matrix: `Wrap` in
   *  the unknown-path mode, and through it `Fold`'s accumulator and an interprocedural `Call`). */
  def wrapUnknown(k: LenBounds, s: Shape): Shape =
    if s.definitelyEmpty || k.isEmpty then empty
    else if k.hi == 0 then capDepth(s, MaxDepth)      // the prefix is ε: wrap is the identity
    else if k.lo >= 1 then
      // one head, and under it the wrap by the REMAINING |p|-1 unknown items — so the depth
      // structure survives even though the items do not
      val inner = if k.lo == k.hi then wrapUnknown(LenBounds(k.lo - 1, k.hi - 1), s) else top
      Shape(Presence.No, SortedMap.empty, Ivl(if s.definitelyNonEmpty then 1 else 0, 1),
            if inner.isTop then None else Some(weaken(capDepth(inner, MaxDepth - 1))))
    else unionTransfer(weaken(capDepth(s, MaxDepth)), Shape(Presence.No, SortedMap.empty, Ivl(0, 1), None))

  /** drop a prefix of UNKNOWN content but bounded length.  `Unwrap(s, p)` with `|p| = j` keeps a
   *  SUBSET of the level-`j` tail-sets, and the union of all level-`j` tail-sets is [[tailsUnion]]
   *  applied `j` times — so the union over `j ∈ k` bounds it from above.  MAY-ONLY: which subtree
   *  survives depends on the unknown items, and the result may be empty. */
  def unwrapUnknown(k: LenBounds, s: Shape): Shape =
    if s.definitelyEmpty || k.isEmpty then empty
    else if k.hi == LenBounds.INF || k.hi > MaxDepth + 2 then weaken(top)
    else
      var acc = empty
      var cur = s
      var j = 0L
      while j <= k.hi do
        if j >= k.lo then acc = unionTransfer(acc, cur)
        cur = tailsUnion(cur)
        j += 1
      weaken(acc)

  /** drop a known constant prefix, keeping only the paths that HAVE it.  This is where a shape
   *  domain earns its keep: `Unwrap(Literal({b}), "a")` is provably ∅ because `a` is not a head of
   *  a closed head set — a length histogram cannot see that.  Descending into a TRACKED head is
   *  exact, so MUST passes through untouched. */
  def unwrap(items: List[PathItem], s: Shape): Shape = items match
    case Nil => s
    case h :: t =>
      if s.heads.contains(h) then unwrap(t, s.heads(h))
      else if s.headsClosed then empty            // PROVED absent
      else unwrap(t, weaken(s.otherTail.getOrElse(top)))

  /** the union of every head's tail-set.  A child that forces ε forces its own head to be present,
   *  so a tracked child's MUST is a genuine must about the union.  The untracked contribution has
   *  its counts opened: channel (d) is a PER-HEAD summary and this aggregates across heads. */
  def tailsUnion(s: Shape): Shape =
    val parts = s.heads.values.toVector ++
      (if s.others.hi > 0 then Vector(openCounts(s.otherTail.getOrElse(top))) else Vector.empty)
    if parts.isEmpty then empty else parts.reduce((x, y) => unionTransfer(x, y))

  /** the intersection of every head's tail-set (∅ when there is no head).  UNSOUND to intersect the
   *  children of heads that are only MAY-present: an absent head does not participate, so the true
   *  result can be strictly LARGER than the intersection.  MUST is therefore restored only when the
   *  participant set is exactly known (closed head set, every live head must-present). */
  def tailsInter(s: Shape): Shape =
    val live = s.heads.values.filter(_.possiblyNonEmpty).toVector
    val must = s.heads.values.filter(_.definitelyNonEmpty).toVector
    if s.headsClosed && live.isEmpty then empty
    else if s.headsClosed && must.size == live.size && must.nonEmpty then must.reduce((x, y) => inter(x, y))
    else
      val upper = if must.nonEmpty then must.reduce((x, y) => inter(x, y)) else tailsUnion(s)
      weaken(upper)

  /** keep the paths of `x` that start with some path of `prefixes` */
  def restrict(x: Shape, prefixes: Shape): Shape = restrict(x, prefixes, MaxDepth)
  private def restrict(x: Shape, prefixes: Shape, d: Int): Shape =
    if x.definitelyEmpty || prefixes.definitelyEmpty then empty
    // ε is a prefix of everything, so a MUST-ε prefix set keeps x exactly (must included)
    else if prefixes.eps.mustBe then capDepth(x, d)
    // an unknown prefix set: the result is SOME subset of x, and it may still contain ε
    else if prefixes.isTop || (prefixes.heads.isEmpty && !prefixes.headsClosed) then weaken(capDepth(x, d))
    // ε only MAY be a prefix: the result lies between `restrict(x, prefixes ∖ ε)` and `x`.  Taking
    // the may side from `x` and the must side from the ε-free restriction is exactly that interval;
    // treating a may-ε as ABSENT made this return ∅ for a non-empty restriction, which was unsound.
    else if prefixes.eps.mayBe then
      union(weaken(capDepth(x, d)), restrict(x, prefixes.copy(eps = Presence.No), d), d)
    else if d <= 0 then weaken(capDepth(x, d))
    else
      // heads(result) ⊆ heads(x) ∩ heads(prefixes).  Intersecting only the TRACKED key sets while
      // treating the result as closed was the corpus soundness bug: with `x` open and `prefixes`
      // closed, an untracked head of `x` equal to a prefix head was dropped and the result claimed ∅.
      val keys =
        if x.headsClosed && prefixes.headsClosed then x.heads.keySet intersect prefixes.heads.keySet
        else if x.headsClosed then x.heads.keySet
        else if prefixes.headsClosed then prefixes.heads.keySet
        else x.heads.keySet ++ prefixes.heads.keySet
      val hs = keys.toVector.map { h =>
        val pt = prefixes.under(h)
        h -> (if pt.eps.mustBe then capDepth(x.under(h), d - 1) else restrict(x.under(h), pt, d - 1))
      }
      val others =
        if x.headsClosed || prefixes.headsClosed then Ivl.zero
        else Ivl(0, x.others.hi min prefixes.others.hi)
      mk(Presence.No, hs, others, if others.hi == 0 then None else x.otherTail.map(weaken))

  /** COMPOSITION — graft `y` at every leaf of `x`.  `{p ++ q : p ∈ x, q ∈ y}` splits as
   *  `⋃_h h·(tails_x(h) · y)  ∪  (if ε ∈ x then y)`, which is exactly the recursion below. */
  def comp(x: Shape, y: Shape): Shape = comp(x, y, MaxDepth)
  private def comp(x: Shape, y: Shape, d: Int): Shape =
    if x.definitelyEmpty || y.definitelyEmpty then empty
    else if d <= 0 then
      // out of budget: ε only if both may be ε, and any number of heads
      Shape(x.eps.and(y.eps), SortedMap.empty, Ivl(0, Ivl.INF), None)
    else
      val hs = x.heads.toVector.map((h, t) => h -> comp(t, y, d - 1))
      val others =
        if x.headsClosed then Ivl.zero
        else Ivl(if y.definitelyNonEmpty then x.others.lo else 0L, x.others.hi)
      val ot = if x.headsClosed then None else x.otherTail.map(t => weaken(comp(t, y, d - 1)))
      val headPart = mk(Presence.No, hs, others, ot)
      x.eps match
        case Presence.No => headPart
        case Presence.Must => union(headPart, capDepth(y, d), d)
        case Presence.May => union(headPart, weaken(capDepth(y, d)), d)

  /** RANGE — a positional slice in the canonical path order.  The result is SOME subset of the
   *  source of at most `width` paths; which subset depends on a total order over the whole space
   *  that a trie truncated at `MaxDepth` does not model, so this is MAY-ONLY except when the window
   *  provably covers everything (`whole`), where it is the identity and MUST passes through. */
  def range(x: Shape, width: Long, whole: Boolean): Shape =
    if whole then x
    else if width <= 0 then empty
    else
      val s = weaken(x)
      if s.others.hi <= width then s
      else mk(s.eps, s.heads, Ivl(0, width), s.otherTail)
end Shape
