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
 *  ==THE CARRIER AND ITS γ (FIVE channels)==
 *
 *  IT WAS FOUR, THEN FIVE, THEN SIX, AND IT IS FIVE AGAIN.  (a)-(d) are the original shape/count
 *  channels.  (e) is the CERTIFICATE, and it is now ONE channel rather than two: a [[Cert]] prefix
 *  trie replaces the flat `otherKeys` name set and the interned `headAtoms` form of the same claim.
 *  The trie subsumes both — a name set is a trie whose keys carry ⊤, and one
 *  interned reference holds a set of any size, which was channel (f)'s whole job — and it says the
 *  one thing neither could: what is BELOW a level the width spill or the depth cut collapsed.
 *  Every "four-channel" and "six-channel" description in this tree was stale and is corrected where
 *  it appeared.
 *  A `Shape` abstracts a `SpaceValue` (a finite set of `PathValue`).  Write `groups(V)` for
 *  `{h ↦ {t : h::t ∈ V}}` and `U(V) = groups(V).keys ∖ heads.keys` (the UNTRACKED heads).
 *  `V ∈ γ(sh)` iff every channel holds:
 *
 *    (a) EPSILON.  `eps = No` ⇒ ε ∉ V;  `eps = Must` ⇒ ε ∈ V;  `eps = May` ⇒ either.
 *    (b) TRACKED HEADS.  for every `h ↦ c` in `heads`: `groups(V)(h) ∈ γ(c)` (with `∅` when `h` is
 *        concretely absent — so a child that forces ε *is* the claim "the path h is present").
 *    (c) UNTRACKED-HEAD COUNT.  `others.lo ≤ |U(V)| ≤ others.hi`.  `others.hi = 0` (`headsClosed`)
 *        is the closed-head-set case: it is what licenses exact head counts and absent-prefix facts.
 *    (d) OTHER-TAIL SUMMARY.  `otherTail = Some(ot)` ⇒ for EVERY `h ∈ U(V)`, `groups(V)(h) ∈ γ(ot)`
 *        (per-head, NOT the union — see the note below);  `None` means ⊤.
 *
 *  ==WHAT (c)/(d) COST, AND WHERE THE MISSING CHANNEL WOULD GO==
 *  (c)/(d) ANONYMISE the untracked heads: past [[Shape.MaxHeads]] the width spill keeps a COUNT and a
 *  per-head tail summary and throws the KEYS away.  Two spilled shapes are then never provably
 *  head-disjoint, whatever their keys, so a key-disjoint union's paired-prefix frontier collapses to
 *  `min(K_d, K_d) = n` and `SpatialFrontier` predicts `Θ(n)` fresh nodes where the Patricia merge
 *  attaches whole branches and allocates 2.  RAISING `MaxHeads` only moves that crossover.
 *
 *  The two queries the frontier needs are already isolated here — [[Shape.possibleHeads]] ("the head
 *  set, when the carrier can enumerate it") and [[Shape.mayHaveHead]] ("could `h` be a head?") — and
 *  today both answer from a CLOSED head set only.  A key certificate is what would make them answer
 *  past the spill; `SpatialScaleCheck`'s LIM-5 records the two ways to carry one and what each costs.
 *
 *  [[Shape.contains]] IS this predicate, and it is the only implementation of it in the tree:
 *  `SpatialGamma.gammaShape` and `SpatialType.accepts` both forward here (the review — there used to
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
 *  ==ONE OWNER==
 *  THIS OBJECT owns every lattice operation of the SHAPE carrier, and no other file may restate one:
 *
 *  | law                                   | the one implementation      | who delegates to it                      |
 *  |---------------------------------------|-----------------------------|------------------------------------------|
 *  | γ (full membership, six channels)     | [[Shape.contains]]          | `SpatialGamma.gammaShape`, `SpatialType.accepts` |
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
 *  THE PER-OPERATOR MAY/MUST TABLE  (written before the code)
 *  ==============================================================================================
 *  Four soundness bugs were found bringing this domain up and every one was the same family: an
 *  operation that can DELETE members (`∩`, `∖`, `<|`, `Range`, an iteration group that need not run,
 *  anything meeting ⊤) leaking MUST information through one of the channels.  The previous fix
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
                       otherTail: Option[Shape],
                       /** (e)+(f) THE CERTIFICATE — ONE CHANNEL, AND IT IS A PREFIX TRIE.
                        *
                        *  `L(this) ⊆ L(cert)`: every path this shape admits is admitted by the
                        *  certificate.  [[Cert.top]] is "no claim" and is the default, so a
                        *  construction site that says nothing here is exactly as strong as it was.
                        *
                        *  ==WHAT IT REPLACED==
                        *  Two flat channels: `otherKeys: Option[Set[PathItem]]` (the untracked-head
                        *  name set) and `headAtoms: Set[Int]` (the same set, interned, so that a
                        *  spill past `MaxSpillKeys` kept a usable bound instead of degrading to ⊤).
                        *  Both were claims about ONE LEVEL.  A `Cert` claims about the whole
                        *  language, so the sub-structure of a level that `capDepth`/`capWidth`
                        *  collapses SURVIVES the collapse — which is the precision 1B.5 needs and
                        *  which no flat name set can carry.
                        *
                        *  ==WHY THE OLD (f) IS NOT NEEDED, RATHER THAN LOST==
                        *  Channel (f)'s one job was to hold an arbitrarily large key set behind one
                        *  `Int`, so the carrier stayed small.  A `Cert` IS one reference: the trie
                        *  lives once in [[Cert.arena]] and every shape that shares the bound shares
                        *  the pointer.  Unlike an atom id it is meaningful without the table —
                        *  shapes outlive their analysis (`SpatialPipeline` reads a stored
                        *  `SpatialAnalysis`), and an id into a process-wide table did not.
                        *
                        *  IT IS AN UPPER BOUND AND NOTHING ELSE.  A certificate never licenses
                        *  `others.hi := |names|` and never makes [[under]] return a MUST claim:
                        *  reading a must claim out of the untracked side is the ⊤-meets-must leak
                        *  the per-operator table below keeps warning about.
                        *
                        *  IT JOINS EVERY CHANNEL TEST, because [[isTop]]'s comment is right about
                        *  what happens otherwise. */
                       cert: Cert = Cert.top):
  import Lower.LenBounds

  /** THE SHAPE'S LANGUAGE BOUND, ONE LEVEL DEEP — the form every PER-NODE consumer uses.
   *
   *  `cert` is only installed where the structural channels lose something (a width spill, a level
   *  collapse), so reading it alone would treat every unspilled shape as ⊤ and throw a closed shape's
   *  exact head set away.  This adds that head set back, and NOTHING BELOW IT, which is the whole
   *  point: it is the claim the old `possibleHeadsCert` made, at the same cost.
   *
   *  ==WHY NOT THE DEEP WALK, WHICH IS WHAT THIS USED TO BE==
   *  The first version was `Shape.certOf(this)` — the whole language, read off every channel — as a
   *  `lazy val`, so once per shape INSTANCE.  Shapes are created constantly, and the lattice asks for
   *  this at every union, meet, lub and order comparison, so "once per instance" is still one walk
   *  per lattice edge.  MEASURED on `SpatialAcceptance`'s latency gate: puzzle15's decorated analysis
   *  went to 49046 ms against a plain `infer` of 1068 ms — 45.9x, past the 12x structural budget.
   *
   *  Every per-node consumer only needs a SOUND bound, and a weaker one costs precision and never
   *  soundness: `Cert.join` of two weaker bounds still admits both sides, `Cert.meet` of them still
   *  admits what both admit, and `keysExceed` refusing more often only makes the order more
   *  incomplete.  The DEEP walk stays where depth IS the point — `Shape.certOf`, called by the width
   *  spill and the level collapse, which are the sites the tier exists for. */
  lazy val langLevel: Cert =
    if definitelyEmpty then Cert.empty
    else
      val ks = SortedMap.from(heads.iterator.collect {
        case (h, c) if c.possiblyNonEmpty => h -> Cert.top })
      // `Closed` ONLY WHEN THE HEAD SET REALLY IS CLOSED.  Reading `cert.outside` here was unsound:
      // it produced a one-level bound naming exactly the TRACKED heads and closed, and the meet with
      // the shape's own certificate then INTERSECTED the two name sets and deleted the spilled ones.
      // MEASURED: puzzle15's 16 cells became `HeadSetWithin` of the 12 tracked ones with
      // `others.hi = 0` — `MaximumHeadCount(12)` for a 16-head value — and nqueens' inferred size
      // collapsed to `[0, 0]` against a true 32 (`SpatialAcceptance` 5 and 5b).
      //
      // With an open bucket the one-level claim is `Unbounded`, which the canonicalisation in
      // `Cert.of` turns into `Cert.top` (⊤ keys under `Unbounded` carry nothing), so the meet is the
      // shape's stored certificate unchanged — exactly right, and free.
      val out = if others.hi == 0 then Cert.Outside.Closed else Cert.Outside.Unbounded
      Cert.meet(cert, Cert.of(eps.mayBe, ks, out))

  /** number of levels below this node — memoised so [[Shape.capDepth]] is a no-op when it can be */
  lazy val depth: Int =
    var d = -1
    for (_, t) <- heads do d = d max t.depth
    for t <- otherTail do d = d max t.depth
    d + 1

  /** is the head set exactly `heads.keys`? — the property that licenses exactness */
  def headsClosed: Boolean = others.hi == 0

  /** THE COMPLETE HEAD SET, when the carrier can enumerate it — THE query every relational
   *  disjointness argument goes through (`SpatialFrontier.headDisjoint` and the relational walk's
   *  paired-key count).
   *
   *  It answers on a CLOSED head set from `heads` alone, and on an OPEN one from the untracked-head
   *  certificate (e).  Before (e) existed it returned `None` for every open shape, so nothing above
   *  `MaxHeads` keys could ever be shown head-disjoint again and the frontier fell back to
   *  `min(K_d, K_d) = n` paired keys where the truth is 0. */
  def possibleHeads: Option[Set[PathItem]] =
    val live = heads.iterator.filter(_._2.possiblyNonEmpty).map(_._1).toSet
    if others.hi == 0 then Some(live) else certNames.map(ks => live union ks)

  /** is there a certificate to reason with at all? */
  def certBounded: Boolean = !cert.isTop

  /** the certificate's HEAD NAMES.  `None` is ⊤ — no claim about which heads may occur.
   *
   *  With the flat channels this needed the atoms enumerated, which was the one size-dependent step
   *  in the domain; a trie names its heads at the top node, so this is `keys.keySet`. */
  def certNames: Option[Set[PathItem]] = cert.headNames

  /** does the certificate admit `h` as a head?  O(1). */
  def certAdmits(h: PathItem): Boolean = cert.admitsHead(h)

  /** an upper bound on how many heads the certificate allows.  `Ivl.INF` when ⊤. */
  def certSize: Long = cert.headBound

  /** WHICH BUDGET RULES WEAKENED THIS SHAPE'S CERTIFICATE.  Empty means the claim is
   *  exactly what the transfers derived; a non-empty set names the rule that gave something up, and
   *  `SpatialCost` reports it in the priced result's assumptions. */
  def certDegradations: Set[Cert.Degradation] = cert.degradationsBelow

  /** THE UNTRACKED BUCKET'S TAIL BOUND, certificate included.
   *
   *  `weaken(otherTail)` is channel (d)'s per-head summary and was the only answer here.  The
   *  certificate's own tails-union over the untracked heads is a second, independent bound on the
   *  same object, so meeting them can only tighten — and it is the one that survives a level
   *  collapse, which is the case the relational walk cares about. */
  def untrackedTailBound(tracked: Set[PathItem]): Shape =
    val base = Shape.weaken(otherTail.getOrElse(Shape.top))
    val c = Cert.tailsUnionExcept(cert, tracked)
    if c.isTop then base
    else
      val fromCert = Shape.ofCert(c)
      if fromCert.isTop then base else if base.isTop then fromCert
      else Shape.inter(base, fromCert)

  /** THE CERTIFICATE FOR THE TAILS UNDER `h`, AS A SHAPE — the sub-structure a collapsed level keeps.
   *  `Shape.top` when the certificate says nothing, so meeting it is always sound
   *  and is a no-op where there is no claim. */
  def certUnder(h: PathItem): Shape = Shape.ofCert(cert.under(h))

  /** no information at all — the fixed point of every widening, and the recursion stopper.
   *
   *  ANY NEW CHANNEL HAS TO JOIN THIS TEST.  A prototype key certificate that did not was caught by
   *  the randomized order matrix in one pass: `{ε?, +[0,inf] more of 2 named}` looked like ⊤ to
   *  `leqStrong`'s `if b.isTop then 0` short circuit, so the order accepted a left-hand side with
   *  thirteen heads while γ — which enforced the certificate — rejected its values. */
  def isTop: Boolean =
    eps == Presence.May && heads.isEmpty && others == Ivl.unknown && otherTail.isEmpty &&
      cert.isTop

  /** the number of DISTINCT heads: the group count of an `Iteration` over this space.  The lower
   *  bound counts MUST-present heads (a tracked head whose tail-set is definitely non-empty, plus
   *  `others.lo`); the upper counts every head that MAY be present. */
  def headCount: Ivl =
    Ivl(Ivl.add(heads.count((_, t) => t.definitelyNonEmpty).toLong, others.lo),
        Ivl.add(heads.count((_, t) => t.possiblyNonEmpty).toLong, others.hi))

  /** ==============================================================================================
   *  THE RANK ABSTRACTION: the LEAST and GREATEST path this shape's language can
   *  contain, when the shape determines them.
   *
   *  ==WHY THIS TIER AND NOT THE LENGTH TIER==
   *  `Range(x, start, end)` is a POSITIONAL operator: every backend slices it by
   *  `pathValueOrdering` (MORKL.scala), which is item-wise `String.compareTo` and then
   *  shorter-is-less on a shared prefix.  So the ordering is exactly the ORDER THE SHAPE IS BUILT
   *  IN — `heads` is a `SortedMap[PathItem, Shape]` and ε, having length 0 and being a prefix of
   *  everything, is the minimum.  The length histogram cannot say anything about position; the
   *  shape can say a great deal, and `Shape.range` was throwing all of it away (it kept `heads` and
   *  capped the count, so `Range(x, 0, 1)` reported "one path, any head").
   *
   *  ==WHAT `None` MEANS, WHICH IS THE WHOLE CORRECTNESS ARGUMENT==
   *  `None` is "not determined by this shape", and the two places it comes from are the two places
   *  a positional claim can fail:
   *
   *    * `others.hi > 0` — an UNTRACKED head exists, and an untracked head has NO KNOWN POSITION:
   *      its item could sort before every tracked head, after all of them, or between any two.  No
   *      rank claim survives that, in either direction.
   *    * `eps == May` for `orderMin` — ε is the minimum WHEN PRESENT and absent otherwise, so a
   *      may-present ε makes the least element undetermined.  `orderMax` is unaffected by a
   *      may-present ε unless there is nothing else, because ε is the SMALLEST element.
   *
   *  Both are the conservative direction: an undetermined rank leaves `Shape.range` exactly where it
   *  was.  ============================================================================================== */
  def orderMin: Option[PathValue] =
    if definitelyEmpty then None
    else if others.hi > 0 then None                    // an untracked head could sort anywhere
    else if eps == Presence.Must then Some(PathValue(Nil))   // ε is the minimum when it is there
    else if eps == Presence.May then None              // …and undetermined when it might not be
    else
      // the least head whose tail-set can be non-empty, recursed
      heads.iterator.filter((_, t) => t.possiblyNonEmpty).nextOption().flatMap { (h, t) =>
        // it must also be FORCED, or the least element could be under a later head
        if !t.definitelyNonEmpty then None
        else t.orderMin.map(tail => PathValue(h :: tail.items))
      }

  /** the GREATEST path, dual to [[orderMin]].  ε is the smallest element, so it is the greatest only
   *  when the shape has nothing else. */
  def orderMax: Option[PathValue] =
    if definitelyEmpty then None
    else if others.hi > 0 then None
    else
      val live = heads.iterator.filter((_, t) => t.possiblyNonEmpty).toVector
      if live.isEmpty then
        if eps == Presence.Must then Some(PathValue(Nil)) else None
      else
        val (h, t) = live.last
        // the greatest head must be FORCED; if it might be empty the greatest element could be
        // under an earlier head, and which one is not determined
        if !t.definitelyNonEmpty then None
        else t.orderMax.map(tail => PathValue(h :: tail.items))

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

  /** THE LARGEST TAIL-SET UNDER ANY DEPTH-`j` PREFIX.
   *
   *  `Unwrap(x, p)` with `|p| = j` KNOWN selects the tail-set under ONE depth-`j` prefix, so its
   *  cardinality is bounded by the largest of them — NOT by their sum, which is what
   *  `unwrapUnknown`'s `tailsUnion` gives and what the length histogram's `Unwrap` transfer gives.
   *  Both of those are bounds on the UNION over prefixes, and the union is the wrong object: the
   *  operator picks one.
   *
   *  MEASURED on puzzle15.  `ass`, the rest of `.iter(P"act", S"ass", ...)`, is `map(l) x t` where
   *  `map(l)` is `Unwrap(map, Deref(l))` with `|l| = 1`.  `map` has 16 tracked cell heads, so the
   *  tails-union sums 16 tail-sets where the operator reads one, and that factor then multiplies
   *  through `Sliding.collapse`'s 15-fold `Composition`.
   *
   *  `Ivl.INF` when the shape cannot bound it — an untracked bucket with no `otherTail` summary is
   *  ⊤ and so is the answer.  The untracked bucket contributes its PER-HEAD summary's size and not
   *  `others.hi` times it, which is the whole point: channel (d) is a per-head claim. */
  def maxTailSize(j: Int): Long =
    if j <= 0 then size.hi
    else if definitelyEmpty then 0L
    else
      var best = 0L
      for (_, c) <- heads do best = best max c.maxTailSize(j - 1)
      if others.hi > 0 then
        best = best max (otherTail match
          case Some(ot) => ot.maxTailSize(j - 1)
          case None => Ivl.INF)
      best

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
   *  no positive lower bound.  (The formula is the design note's `rawPrefixesAt`, taken as-is: the
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

  /** may `h` be a head of this space? — `false` is a PROOF of absence.  An untracked head of an OPEN
   *  shape could be `h` and the carrier cannot say otherwise (see [[possibleHeads]]). */
  def mayHaveHead(h: PathItem): Boolean = heads.get(h) match
    case Some(c) => c.possiblyNonEmpty
    case None => others.hi > 0 && certAdmits(h)

  /** may this space contain a path starting with `items`? — `false` is a PROOF of absence */
  def mayHavePrefix(items: List[PathItem]): Boolean = items match
    case Nil => possiblyNonEmpty
    case h :: t => heads.get(h) match
      case Some(c) => c.mayHavePrefix(t)
      case None => mayHaveHead(h)          // an untracked head could be `h`
  /** is `h` DEFINITELY a head of this space? */
  def mustHaveHead(h: PathItem): Boolean = heads.get(h).exists(_.definitelyNonEmpty)

  /** descend under a known head.  For an untracked head of an OPEN shape this is the `otherTail`
   *  summary, WEAKENED: channel (d) is a may-only summary of a set we cannot name, so reading a must
   *  claim out of it would be exactly the ⊤-meets-must leak this domain kept hitting.
   *
   *  ==AND THE CERTIFICATE IS CONSULTED HERE, WHICH IS THE WHOLE POINT OF THE TIER==
   *  `cert.under(h)` is the sub-trie the width spill or the level collapse kept, and meeting it with
   *  the summary is how a spilled head's own structure re-enters the domain.  Two things it fixes:
   *
   *   - PRECISION, which is what it was built for.  `Sliding.collapse`'s `Unwrap(state, c_i)` reads a
   *     cell that spilled past `shapeWidth`; with the summary alone that is `|state|` and with the
   *     sub-trie it is one tile.
   *   - SOUNDNESS OF THE ORDER, which was not optional.  `leqStrong` compares operands through
   *     `under`, so a certificate this method ignored was a claim γ enforced and the order did not.
   *     `SpatialSoundnessHunt` HUNT 8 produced the witness in one pass:
   *     `leqStrong({b·{b·⊤}}, {+[0,2] more of {a,b}})` with the right-hand certificate
   *     `{a/{ε}, b/{ε}}` — every path exactly one item long — was accepted, and `{b.b}` is in γ of
   *     the left and not of the right.  With the certificate read here, `right.under(b)` is ε-only
   *     and the child comparison refutes the pair.
   *
   *  THE COMMON CASES COST NOTHING: `Cert.top` (no certificate) and a ⊤ summary each skip the meet,
   *  and an unspilled shape has no certificate at all. */
  def under(h: PathItem): Shape = heads.get(h) match
    case Some(x) => x                                  // tracked: its own sub-shape is the answer
    case None =>
      if !mayHaveHead(h) then Shape.empty
      else
        val base = Shape.weaken(otherTail.getOrElse(Shape.top))
        // THE CERTIFICATE IS READ ONLY WHERE THE SUMMARY SAYS NOTHING, and that is a cost decision
        // with a measurement behind it.  `under` is called inside `leq`, `union`, `inter`, `lub` and
        // `meet`, so running `Shape.inter` here put a whole lattice operation on every descent —
        // puzzle15's decorated analysis went to 45.9x the plain query (`SpatialAcceptance` 5c).  The
        // case the tier is for is exactly the one kept: a head that spilled, whose `otherTail`
        // summary is ⊤ and whose sub-trie the certificate still has.  Where the summary already says
        // something, it is kept as-is and the certificate's extra precision is available on demand
        // through [[certUnder]] — which is what the `Unwrap` transfer and the frontier's
        // [[untrackedTailBound]] use.
        if !base.isTop then base
        else
          val c = cert.under(h)
          if c.isTop then base else Shape.ofCert(c)

  def show: String =
    if definitelyEmpty then "∅"
    else
      val e = if eps == Presence.Must then Vector("ε!") else if eps == Presence.May then Vector("ε?") else Vector.empty
      val hs = heads.iterator.filter(_._2.possiblyNonEmpty).map((h, t) => s"${h}·${t.show}").toVector
      val o =
        if others.hi == 0 then Vector.empty
        else
          val named = cert.headNames match
            case Some(ks) if ks.size <= 6 => s" of {${ks.toVector.sorted.mkString(",")}}"
            case Some(ks) => s" of ${ks.size} named"
            case None => ""
          val sub = if cert.isTop || !cert.hasSubStructure then "" else s" cert=${cert.show}"
          if named.isEmpty && sub.isEmpty then Vector(s"+${others.show} more")
          else Vector(s"+${others.show} more$named$sub")
      "{" + (e ++ hs ++ o).mkString(", ") + "}"

object Shape:
  import Lower.LenBounds
  /** THE budgets, read from the ONE analysis configuration ([[SpatialConfig]]) rather than spelled
   *  out here — the review asks for a single value carrying every budget.  They stay `val`s because
   *  the carrier's finiteness argument is about the whole domain, not about one query: a `Shape`
   *  built under one depth cap must be comparable with one built under another, so the cap belongs to
   *  the domain, not to a call.  A per-call cap would need `Shape` to carry its own budget. */
  val MaxDepth: Int = SpatialConfig.default.shapeDepth
  val MaxHeads: Int = SpatialConfig.default.shapeWidth
  /** THE CERTIFICATE'S BUDGETS, read from the ONE analysis configuration.
   *
   *  `certKeys` bounds how many NAMES one certificate level carries and `certDepth` how many levels
   *  it carries at all.  Both are WORK bounds and not precision cliffs, which is the difference from
   *  the `MaxSpillKeys` they replace: over `MaxSpillKeys` the flat certificate degraded to ⊤ and a
   *  key-disjoint family's predicted asymptotic CHANGED at a fixed size, whereas
   *  [[Cert.widen]] over-wide keeps every sub-trie inside one `Bounded` outside and over-deep keeps
   *  every level above the cut.  `SpatialCertBudgetCheck` is the gate that the growth class does not
   *  change across either crossing. */
  val CertKeys: Int = SpatialConfig.default.certKeys
  val CertDepth: Int = SpatialConfig.default.certDepth

  val empty: Shape = Shape(Presence.No, SortedMap.empty, Ivl.zero, None, Cert.empty)
  /** no information: ε may be there and any heads may be there */
  lazy val top: Shape = Shape(Presence.May, SortedMap.empty, Ivl.unknown, None, Cert.top)
  /** exactly the empty path */
  val epsOnly: Shape = Shape(Presence.Must, SortedMap.empty, Ivl.zero, None, Cert.epsOnly)

  /** A SHAPE WHOSE ONLY CLAIM IS A CERTIFICATE.
   *
   *  This is how the sub-structure a collapsed level keeps re-enters the shape domain: `certUnder`
   *  hands back `ofCert(cert.under(h))` and the caller MEETS it with whatever the count/summary
   *  channels say.  Every channel but the certificate is ⊤ here, so the meet can only tighten. */
  /** MEMOISED ON THE INTERNED CERTIFICATE.  `Shape.under` asks for this on every descent into an
   *  untracked head, so without the memo the conversion was re-run once per lattice edge —
   *  MEASURED: `SpatialSoundnessHunt` went from 40s to just over 6 minutes.  Weak-keyed and
   *  answer-preserving for the same reason `Cert.arena` is. */
  private val ofCertMemo =
    java.util.Collections.synchronizedMap(new java.util.WeakHashMap[Cert, Shape]())

  def ofCert(c: Cert): Shape =
    if c.isTop then top
    else
      val hit = ofCertMemo.get(c)
      if hit != null then hit
      else
        val s = ofCert(c, MaxDepth)
        ofCertMemo.put(c, s)
        s

  private def ofCert(c: Cert, d: Int): Shape =
    if c.isTop then top
    else if c.isEmpty then empty
    else
      val eps = if c.eps then Presence.May else Presence.No
      val hb = c.headBound
      val cnt = Ivl(0, hb)
      // THE CERTIFICATE ITSELF IS ALWAYS CARRIED, at the depth cap as well as below it: it is the
      // channel that does not have a depth cap, so cutting the shape here loses nothing that matters.
      if hb == 0 then Shape(eps, SortedMap.empty, Ivl.zero, None, c)
      else if d <= 0 then Shape(eps, SortedMap.empty, cnt, None, c)
      else Shape(eps, SortedMap.empty, cnt, Some(ofCert(c.tailsUnion, d - 1)), c)

  /** THE CERTIFICATE OF A SHAPE: a sound bound on its whole language, read off the structural
   *  channels and MET with the certificate the shape already carries.
   *
   *  `capDepth`/`capWidth` call this on the level they are about to throw away, and that is the whole
   *  mechanism of the tier: what used to become ⊤ becomes a claim the carrier can still consult. */
  def certOf(s: Shape): Cert = certOf(s, MaxDepth + 2)
  private def certOf(s: Shape, d: Int): Cert =
    if s.definitelyEmpty then Cert.empty
    else if d <= 0 then s.cert
    else
      val ks = SortedMap.from(s.heads.view.mapValues(certOf(_, d - 1)))
      val out =
        if s.others.hi == 0 then Cert.Outside.Closed
        else s.otherTail match
          case Some(ot) => Cert.Outside.Bounded(certOf(ot, d - 1))
          case None => Cert.Outside.Unbounded
      Cert.meet(s.cert, Cert.of(s.eps.mayBe, ks, out))

  /** a certificate for `prefix ++ L(inner)`: one trie spine, then the operand's own claim */
  private def certWrap(prefix: List[PathItem], inner: Cert): Cert = prefix match
    case Nil => inner
    case h :: tl => Cert.of(false, SortedMap(h -> certWrap(tl, inner)), Cert.Outside.Closed)

  /** the EXACT certificate of a known value — no depth cap, because a literal's trie IS the claim */
  private def certOfValue(v: SpaceValue): Cert =
    if v.paths.isEmpty then Cert.empty
    else
      val eps = v.paths.contains(PathValue(Nil))
      val groups = v.paths.iterator.collect { case PathValue(h :: tl) => h -> PathValue(tl) }
        .toVector.groupMap(_._1)(_._2)
      Cert.of(eps, SortedMap.from(groups.view.mapValues(ts => certOfValue(SpaceValue(ts.toSet)))),
              Cert.Outside.Closed)

  /** the JOIN of two certificates, budgeted.  A union's language is the union of the two languages,
   *  so [[Cert.join]] is exact and the only reason to widen is the budget. */
  private def certJoin(a: Shape, b: Shape): Cert =
    Cert.widen(Cert.join(a.cert, b.cert), CertDepth, CertKeys)

  /** the MEET's certificate: a meet's language is inside BOTH, so [[Cert.meet]] is sound and is the
   *  tighter of the two available answers. */
  private def certMeet(a: Shape, b: Shape): Cert =
    Cert.widen(Cert.meet(a.cert, b.cert), CertDepth, CertKeys)

  /** THE LANGUAGE JOIN, READ OFF BOTH OPERANDS IN FULL.
   *
   *  `a.cert` alone is not enough: a CLOSED shape carries no certificate (its structural channels say
   *  everything) and joining `Cert.top` with anything is `Cert.top`, which would throw the closed
   *  side's exact head set away.  [[certOf]] supplies it, memoised per shape as [[Shape.langLevel]],
   *  so the cost is one walk per distinct shape rather than one per lattice step.  This is the exact
   *  role the old `possibleHeadsCert` had, at the language level instead of the head level. */
  private def certJoinL(a: Shape, b: Shape): Cert =
    Cert.widen(Cert.join(a.langLevel, b.langLevel), CertDepth, CertKeys)

  /** the same for a meet: both bounds hold of a value in both operands, so they INTERSECT — the
   *  standard reduced-product step, and the tighter of the two answers. */
  private def certMeetL(a: Shape, b: Shape): Cert =
    Cert.widen(Cert.meet(a.langLevel, b.langLevel), CertDepth, CertKeys)

  // -----------------------------------------------------------------------------------------------
  // γ  (a local copy of SpatialGamma.gammaShape, so this domain's own gate is self-contained)
  // -----------------------------------------------------------------------------------------------
  /** `contains(sh, v)` decides `v ∈ γ(sh)` over the six channels documented on [[Shape]]. */
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
            case None => true) &&
          // (e)+(f) THE CERTIFICATE: every path of the value must be admitted by the certificate.
          // `Cert.top` is ⊤ and admits everything, so a shape that carries no certificate is exactly
          // as permissive as it was.  THIS IS STRONGER THAN THE CLAIM IT REPLACES — the flat channels
          // could only constrain the untracked HEADS, and the trie constrains the whole language,
          // which is the point of the tier: `Cert.under` is only worth consulting if γ enforces it.
          v.paths.forall(pv => sh.cert.admits(pv.items))

  // -----------------------------------------------------------------------------------------------
  // structural utilities
  // -----------------------------------------------------------------------------------------------
  /** drop every MUST claim at every depth, keeping the may structure: what survives an operation
   *  that can delete members.  Total (the previous version stopped at `MaxDepth` and left the
   *  deepest level's musts intact, which is a leak, not an imprecision). */
  def weaken(s: Shape): Shape =
    if s.definitelyEmpty then s
    // (e) SURVIVES WEAKENING: it is a ∀-untracked-head MAY claim, not a must claim and not a count,
    // and dropping MUST information cannot introduce a head that was not already possible.
    else Shape(s.eps.weak, SortedMap.from(s.heads.view.mapValues(weaken)), Ivl(0, s.others.hi),
               s.otherTail.map(weaken), s.cert)

  /** open every COUNT channel.  Head-set membership and closedness are union-closed facts, but "at
   *  most k untracked heads" is not, so this is what survives aggregating an unknown number of sets
   *  each admitted by `s` — used by [[tailsUnion]] on the per-head `otherTail` summary. */
  def openCounts(s: Shape): Shape =
    if s.definitelyEmpty then s
    // (e) SURVIVES OPENING THE COUNTS, and that is the whole point of separating the two channels:
    // a union of an UNKNOWN NUMBER of sets each of whose heads lie in `ks` still has its heads in
    // `ks`.  Opening the count is not opening the domain.
    else
      val cnt = if s.others.hi == 0 then Ivl.zero
                else capOthersCert(Ivl(0, Ivl.INF), s.cert, s.heads.keySet.toSet)
      Shape(s.eps.weak, SortedMap.from(s.heads.view.mapValues(openCounts)), cnt,
            s.otherTail.map(openCounts), s.cert)

  /** collapse everything below level `d` into an untracked-head count.  Sound in both directions:
   *  `headCount` brackets the real number of heads and the tails become ⊤. */
  def capDepth(s: Shape, d: Int): Shape =
    if s.depth <= d then s
    else if d <= 0 then
      val hc = s.headCount
      // THE DEPTH HALF OF THE SPILL, and it used to lose the names exactly as the width half did:
      // the collapsed level's TRACKED keys become untracked, so the certificate is the whole
      // possible-head set (tracked ∪ certificate), not `None`.  Same measured discontinuity — a
      // key-disjoint union under a shared prefix went from `rebuilt = [d,d]` at depth ≤ MaxDepth to
      // `[5,9]` at depth 5 — and the same one-line cause.
      val kept = Cert.widen(certOf(s), CertDepth, CertKeys)
      // THE COLLAPSED LEVEL'S certificate survives, and now survives at ANY WIDTH: `capKeys2` puts
      // the overflow in channel (f) instead of degrading to ⊤ at `MaxSpillKeys`.
      //
      // THE DEPTH HALF IS NO LONGER OPEN.  The levels below the collapse still
      // get `otherTail = None` = ⊤ on the SUMMARY channel — that channel is a per-head tail bound and
      // has nothing to say about a level it does not have — but the CERTIFICATE keeps the whole
      // sub-trie, and the two consumers that used to lose the pair now read it:
      //   * `Shape.under`/`Shape.untrackedTailBound` meet the summary with `cert.under(h)`, so a
      //     query about a collapsed head is answered from the trie instead of from ⊤;
      //   * `SpatialFrontier`'s relational walk descends its untracked summary frame with
      //     `untrackedTailBound` (1C.4), which is exactly the "consult the tail certificates too"
      //     the previous revision of this note said was needed and was a change to the frontier
      //     rather than to this carrier.
      // MEASURED: `SpatialFrontierCheck`'s growing-DEPTH family was a published log factor and is now
      // EXACT at every point — see the RETIRED GAP test, which asserts equality rather than
      // soundness so the retirement cannot rot.
      //
      // THE ORDER SURVIVED IT, which the earlier prototype did not: `keysExceed` compares the two
      // TRIES (`Cert.leq`) rather than starting a shape-level `leq(a.otherTail, b.otherTail)`, so the
      // comparison is on the channel that carries the claim and `SpatialAnalysisCheck`'s "every
      // decorated node admits the real value" gate stays green.
      if hc.hi == 0 then Shape(s.eps, SortedMap.empty, Ivl.zero, None, kept)
      else Shape(s.eps, SortedMap.empty, hc, None, kept)
    else Shape(s.eps, SortedMap.from(s.heads.view.mapValues(capDepth(_, d - 1))), s.others,
               s.otherTail.map(capDepth(_, d - 1)), s.cert)

  /** THE SPILL CERTIFICATE: the shapes leaving the tracked set, kept as one trie.
   *
   *  `SpatialAnalysis.capWidth` and [[mk]]'s width spill both drop tracked heads into the untracked
   *  bucket, and both used to keep only the NAMES.  Keeping the sub-tries is the difference the tier
   *  is for: a spilled head's own structure is still consultable through [[Shape.certUnder]].
   *
   *  The `carried` certificate — whatever the shape already claimed about the untracked bucket — is
   *  JOINED, not met: after the spill the bucket holds both what it held before and what spilled
   *  into it, so the bound has to admit either. */
  private[morkl] def spillCertOf(eps: Presence, kept: Iterable[PathItem],
                                 spilled: Iterable[(PathItem, Shape)],
                                 preSpillOthers: Ivl, ot: Option[Shape], carried: Cert): Cert =
    val others = preSpillOthers
    // THE KEPT heads get no constraint (their own sub-shapes are still tracked and consulted
    // directly); the SPILLED ones get their whole sub-shape, which is the information this exists to
    // preserve; and the unnamed bucket gets whatever `ot` bounds.  The head set is CLOSED exactly
    // when it was closed before the spill.
    val ks = SortedMap.from(kept.iterator.map(_ -> Cert.top)) ++
             SortedMap.from(spilled.iterator.map((h, sh) => h -> certOf(sh)))
    val out =
      if others.hi == 0 then Cert.Outside.Closed
      else ot match
        case Some(t) => Cert.Outside.Bounded(certOf(t))
        case None => Cert.Outside.Unbounded
    // both are sound bounds on the SAME language, so the meet is sound and is the tighter answer
    Cert.widen(Cert.meet(carried, Cert.of(eps.mayBe, ks, out)), CertDepth, CertKeys)

  /** THE CONSISTENCY LAW BETWEEN (c) AND (e): a certificate naming `k` untracked heads caps the
   *  untracked COUNT at `k`.  Without it the carrier can hold `others = [0, ∞]` beside
   *  `otherKeys = Some(∅)` — "any number of untracked heads, none of which may exist" — and γ then
   *  rejects a value that every count channel accepts, which is exactly what
   *  `SpatialCheck`'s membership mirror reported as a failure with NO channel named.  It is also a
   *  free tightening: `Shape.widen` opens the count to ∞ and the certificate pulls it straight back
   *  to the number of names it kept. */
  private def capOthers(others: Ivl, ok: Option[Set[PathItem]]): Ivl = ok match
    case Some(ks) =>
      val hi = others.hi min ks.size.toLong
      Ivl(others.lo min hi, hi)
    case None => others

  /** the count cap against the certificate — the consistency law between channel (c) and the
   *  certificate.  A certificate naming `k` heads caps the untracked COUNT at `k`. */
  private def capOthersCert(others: Ivl, c: Cert, tracked: Set[PathItem]): Ivl =
    val n = Cert.headBoundExcluding(c, tracked)
    if n >= Ivl.INF then others
    else
      val hi = others.hi min n
      Ivl(others.lo min hi, hi)

  /** THE normalising smart constructor.  Establishes every representation invariant:
   *  children are ≤ `MaxDepth-1` deep and never definitely-empty (a definitely-absent head is
   *  simply not tracked), `otherTail` is may-only and never definitely-empty, `others` is a
   *  consistent interval, and at most `MaxHeads` heads are tracked. */
  private def mk(eps: Presence, hs: Iterable[(PathItem, Shape)], others0: Ivl, ot0: Option[Shape],
                 allCert: Cert = Cert.top): Shape =
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
    // THE RESULT'S LANGUAGE BOUND.  A CLOSED result needs no certificate at all: `possibleHeads`
    // answers from `heads` alone and the tracked sub-shapes are consulted directly.  An OPEN one
    // carries the caller's bound — every transfer below passes the language image of its operation
    // (union joins, the deleting operators keep a bound on the left operand's, composition grafts),
    // and `Cert.top` is always sound.
    //
    // THE CERTIFICATE IS ONLY INSTALLED WHERE INFORMATION WOULD OTHERWISE BE LOST, which is what
    // keeps it cheap: an unspilled shape's structural channels already say everything the trie could,
    // so duplicating them here would double the carrier for nothing.  The two places that DO lose
    // information — the width spill just below and `capDepth`'s level collapse — build it.
    if live.size <= MaxHeads then
      val cert0 = Cert.widen(allCert, CertDepth, CertKeys)
      val cnt0 = capOthersCert(others, cert0, live.iterator.map(_._1).toSet)
      Shape(eps, SortedMap.from(live), cnt0, if cnt0.hi == 0 then None else ot, cert0)
    else
      val keep = live.take(MaxHeads); val spill = live.drop(MaxHeads)
      val base = if hiC == 0 then empty else ot.getOrElse(top)
      val tail = spill.foldLeft(base)((a, kv) => unionTransfer(a, weaken(kv._2)))
      val cnt = Ivl(Ivl.add(others.lo, spill.count((_, t) => t.definitelyNonEmpty).toLong),
                    Ivl.add(others.hi, spill.size.toLong))
      // THE WIDTH SPILL, AND WHAT IT NO LONGER LOSES.  The count and the per-head
      // tail summary survive as before.  What channel (e) recovered was the spilled head NAMES; what
      // the certificate recovers now is their WHOLE SUB-SHAPES, so a query about a spilled head can
      // still be answered — `Shape.certUnder` hands the sub-trie back as a shape and the caller meets
      // it with the summary.
      //
      // THE OLD CLIFF IS GONE IN BOTH DIRECTIONS.  `MaxSpillKeys` degraded the certificate to ⊤ at
      // 4096 names, so a key-disjoint family's predicted rebuild still jumped from `Θ(1)` to `Θ(n)`
      // at a fixed size.  A `Cert` is ONE interned reference however many names it holds, and
      // `Cert.widen`'s width rule folds an over-wide level into a `Bounded` outside that still bounds
      // every sub-trie rather than dropping the claim.
      val cert2 = spillCertOf(eps, keep.iterator.map(_._1).toVector, spill, others, ot, allCert)
      val cnt2 = capOthersCert(cnt, cert2, keep.iterator.map(_._1).toSet)
      Shape(eps, SortedMap.from(keep), cnt2,
            if cnt2.hi == 0 || tail.isTop then None else Some(weaken(capDepth(tail, MaxDepth - 1))),
            cert2)

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
   *  NOT duplicates and neither may be deleted; what was wrong was having them in two
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
      // (e): `a`'s untracked heads (its own certificate plus the live keys `b` does not track) must
      // all be admitted by `b`'s certificate.  `Cert.top` on the right is ⊤ and accepts anything.
      else !keysExceed(a, b) &&
        (aLive ++ bLive).forall(h => leq(a.under(h), b.under(h), d - 1)) &&
        (a.others.hi == 0 || leq(a.otherTail.getOrElse(top), b.otherTail.getOrElse(top), d - 1))

  /** does `a` permit a path `b`'s certificate forbids?  `true` REFUTES `a ⊑ b`.
   *
   *  ==THIS IS ONE TRIE COMPARISON AND IT HAS TO BE ==
   *  γ enforces `L(v) ⊆ L(b.cert)` for every `v ∈ γ(b)`, so the order has to enforce the same
   *  containment or it accepts pairs γ rejects.  The flat channels let this be a HEAD-NAME test,
   *  because a flat certificate only ever claimed about heads.  A trie claims about the language, and
   *  a head-name test does not see the rest of it: `SpatialSoundnessHunt` HUNT 8 produced
   *  `leqStrong({b·{b·⊤}}, {+[0,2] more of {a,b}})` with the right-hand certificate `{a/{ε}, b/{ε}}` —
   *  every path exactly one item long — accepted, with `{b.b}` in γ of the left and not the right.
   *
   *  `a.langLevel` rather than `a.cert`: an unspilled shape carries no certificate (its structural
   *  channels say everything), and reading `Cert.top` on the left would refuse every pair.  The
   *  language bound is the same claim read off all the channels, memoised per shape.
   *
   *  Conservative and deliberately so: [[Cert.leq]] is sound and incomplete, and a `false` on a
   *  genuine containment costs the `Fixpoint` iteration another widening round and nothing else. */
  private def keysExceed(a: Shape, b: Shape): Boolean =
    b.certBounded && {
      // THE LEFT-HAND BOUND IS AS DEEP AS THE RIGHT-HAND CLAIM, AND NO DEEPER.
      //
      // `langLevel` is the cheap one-level bound and it is what almost every pair needs: a
      // certificate is usually a pure NAME SET (depth 1), where a deeper left-hand claim cannot
      // change the answer.  Where the right-hand certificate carries SUB-STRUCTURE — the case
      // `capDepth`'s collapse and `mk`'s spill produce, i.e. the case the tier exists for — the
      // one-level bound is ⊤ below the head and `Cert.leq(⊤, x)` is `false`, so the order refused
      // pairs whose languages ARE contained.  MEASURED: `SpatialPipelineCheck`'s narrow-weakens gate
      // on `narrow({ε!, a·{ε!, c·{b·{ε!}}}, c·{b·{ε!}}})`, where the collapsed level's certificate is
      // `{b/{ε}}` and the one-level left-hand claim `{b}` could not be shown inside it.
      //
      // So the deep walk is paid for exactly where it can pay: `Cert.depth > 1` on the right.  That
      // keeps the 45.9x latency regression closed (`SpatialAcceptance` 5c) — a name-set certificate,
      // which is what a width spill produces and what most of the corpus carries, still takes the
      // cheap path.
      val left = if b.cert.hasSubStructure then certOf(a) else a.langLevel
      !Cert.leq(left, b.cert)
    }

  /** the STRONG-γ order: `leqStrong(a, b)` ⇒ `γ(a) ⊆ γ(b)` with the must channels included.  Sound
   *  and deliberately INCOMPLETE — it does not attempt the integer-partition reasoning a spill bucket
   *  facing tracked classes would need; `SpatialLawCheck` measures that incompleteness against
   *  `SpatialGamma.gammaLeqOn`, which decides containment exactly on a finite universe.  Moved here
   *  verbatim from `SpatialGamma.leqShape`, which now forwards. */
  def leqStrong(a: Shape, b: Shape): Boolean = leqStrongMask(a, b, 32, full = false) == 0

  /** WHY [[leqStrong]] said no — the bit positions of [[leqStrongMask]].  `leqStrong` IS
   *  `leqStrongMask == 0`, so this is attribution, not a second order: the review asks for the
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
    val Keys = 64      // (e) a permits an untracked head b's certificate forbids
    val names: Vector[(Int, String)] = Vector(Eps -> "shape:eps", CntLo -> "shape:others.lo",
      CntHi -> "shape:others.hi", Tail -> "shape:otherTail", Depth -> "shape:depth-cap",
      Child -> "shape:child", Keys -> "shape:cert")
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
      if keysExceed(a, b) then m |= Keys
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
            Ivl(0, a.headCount.hi max b.headCount.hi), None, certJoinL(a, b))
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
      // THE CERTIFICATE OF A JOIN ADMITS BOTH SIDES, so the two language bounds are JOINED.
      mk(if a.eps == b.eps then a.eps else Presence.May, hs, others, ot, certJoinL(a, b))

  /** the WIDENING for the `Fixpoint` Kleene chain: open every count channel and every head set, so
   *  the only remaining growth is the (finite) tracked key sets and the (3-valued) ε channel. */
  def widen(s: Shape): Shape =
    if s.definitelyEmpty then s
    // (e) IS KEPT THROUGH THE WIDENING.  Dropping it would re-introduce the discontinuity INSIDE a
    // `Fixpoint` — the accumulator's head set is exactly what a key-disjoint recursion needs to keep
    // — and it cannot block convergence: the channel is a finite lattice of height
    // bounded by `Cert.widen`'s budgets under `⊆` (finitely many tries of bounded depth and width
    // over the run's finitely many items), and the widening is applied to a chain that only grows.
    else
      val cnt = capOthersCert(Ivl(s.others.lo, Ivl.INF), s.cert, s.heads.keySet.toSet)
      Shape(s.eps, SortedMap.from(s.heads.view.mapValues(widen)), cnt, None, s.cert)
  /** the old spelling of [[widen]] */
  @deprecated("use Shape.widen", "consolidation")
  def widenShape(s: Shape): Shape = widen(s)

  // -----------------------------------------------------------------------------------------------
  // THE MEET  (the glb — the operation the reduced product needs)
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
          else if hc.hi == 0 then Some(Shape(e, SortedMap.empty, Ivl.zero, None, certMeetL(a, b)))
          else Some(Shape(e, SortedMap.empty, hc, None, certMeetL(a, b)))
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
            else
              // (e) BOTH claims hold of a value in γ(a) ∩ γ(b), so the bounds INTERSECT — the
              // standard reduced-product step.  An empty intersection with a FORCED untracked head
              // is a contradiction: there is nowhere for that head to be.
              val ks = certMeetL(a, b)
              if ks.headBound == 0 && others.lo > 0 then None
              else Some(mk(e, kids.result(), others, ot, ks))

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
        // the value is KNOWN, so the collapsed level's head names are exact
        // THE VALUE IS KNOWN, so the collapsed level's certificate is EXACT — and now it is exact
        // BELOW the level too: each group's own sub-value becomes that key's sub-trie
        // instead of ⊤, so `Unwrap(literal, k)` past `MaxDepth` still knows what is under `k`.
        Shape(e, SortedMap.empty, Ivl(groups.size.toLong, groups.size.toLong), None,
              Cert.widen(certOfValue(v), CertDepth, CertKeys))
      else mk(e, groups.view.mapValues(ts => of(SpaceValue(ts.toSet), depth - 1)).toSeq, Ivl.zero, None,
              Cert.named(groups.keySet.toSet))

  /** the shape of a single known path */
  def ofPath(p: PathValue, depth: Int = MaxDepth): Shape = of(SpaceValue(Set(p)), depth)

  /** exactly one path whose CONTENT is unknown but whose item-length is bracketed by `k` */
  def oneUnknownPath(k: LenBounds): Shape =
    if k.isEmpty then empty
    else if k.hi == 0 then epsOnly
    // the head EXISTS but its name is unknown, so (e) is ⊤ — the honest answer
    else if k.lo >= 1 then Shape(Presence.No, SortedMap.empty, Ivl(1, 1), None, Cert.top)
    else Shape(Presence.May, SortedMap.empty, Ivl(0, 1), None, Cert.top)

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
            Ivl(a.headCount.lo max b.headCount.lo, Ivl.add(a.headCount.hi, b.headCount.hi)), None,
            certJoinL(a, b))
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
      // `L(A ∪ B) = L(A) ∪ L(B)` — exactly, so the certificate is the JOIN and loses nothing.
      mk(a.eps.or(b.eps), hs, others, ot, certJoinL(a, b))

  def inter(a: Shape, b: Shape): Shape = inter(a, b, MaxDepth)
  private def inter(a: Shape, b: Shape, d: Int): Shape =
    if a.definitelyEmpty || b.definitelyEmpty then empty
    else if d <= 0 then
      Shape(a.eps.and(b.eps), SortedMap.empty, Ivl(0, a.headCount.hi min b.headCount.hi), None,
            certMeetL(a, b))
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
      // `L(A ∩ B) ⊆ L(A) ∩ L(B)`; either side's bound alone is still an upper bound, and the meet
      // is the tighter of the two.
      mk(a.eps.and(b.eps), hs, others, ot, certMeetL(a, b))

  def sub(a: Shape, b: Shape): Shape = sub(a, b, MaxDepth)
  private def sub(a: Shape, b: Shape, d: Int): Shape =
    if a.definitelyEmpty then empty
    else if b.definitelyEmpty then capDepth(a, d)
    else if d <= 0 then
      // THE THIRD ⊤-DEGRADING SITE: `sub` out of budget used to keep only the left
      // operand's head NAMES.  `A ∖ B ⊆ A`, so the left operand's whole language bound is sound here
      // and the sub-structure survives the cut.
      Shape(a.eps.minus(b.eps), SortedMap.empty, Ivl(0, a.headCount.hi), None,
            Cert.widen(certOf(a), CertDepth, CertKeys))
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
      // SUBTRACTION ONLY DELETES, so `A ∖ B ⊆ A` and `a`'s whole language bound carries.
      mk(a.eps.minus(b.eps), hs, others, if a.headsClosed then None else a.otherTail.map(weaken),
         a.langLevel)

  /** prepend a known constant prefix — a bijection, so MUST is exact */
  def wrap(items: List[PathItem], s: Shape): Shape =
    if s.definitelyEmpty then empty else wrapGo(items, s, MaxDepth)
  private def wrapGo(items: List[PathItem], s: Shape, d: Int): Shape = items match
    case Nil => capDepth(s, d)
    case h :: t =>
      // the single head is `h` and it is KNOWN, at the cap as well as below it
      if d <= 0 then
        // AT THE CAP THE WRAP'S OWN STRUCTURE SURVIVES NOW: the whole known prefix, and under it the
        // operand's language.  `Some(Set(h))` kept only the first item's name.
        //
        // IT IS THE WHOLE PREFIX AND NOT JUST `h`: this node stands for `wrap(h :: t, s)`, so a
        // certificate `{h -> L(s)}` claims `h ++ q` for `q ∈ s` and the real language is
        // `h ++ t ++ q`.  `SpatialSoundnessHunt` reported that as a `Wrap` γ violation (57 raw cases
        // in HUNT 5, which is the hunt that goes past the caps and therefore reaches this arm).
        Shape(Presence.No, SortedMap.empty, Ivl(if s.definitelyNonEmpty then 1 else 0, 1), None,
              Cert.widen(certWrap(items, certOf(s)), CertDepth, CertKeys))
      else mk(Presence.No, List(h -> wrapGo(t, s, d - 1)), Ivl.zero, None, Cert.named(Set(h)))

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
      // the head is the prefix's unknown first item: (e) is ⊤
      Shape(Presence.No, SortedMap.empty, Ivl(if s.definitelyNonEmpty then 1 else 0, 1),
            if inner.isTop then None else Some(weaken(capDepth(inner, MaxDepth - 1))), Cert.top)
    else unionTransfer(weaken(capDepth(s, MaxDepth)),
                       Shape(Presence.No, SortedMap.empty, Ivl(0, 1), None, Cert.top))

  /** drop a prefix of UNKNOWN content but bounded length.  `Unwrap(s, p)` with `|p| = j` keeps a
   *  SUBSET of the level-`j` tail-sets, and the union of all level-`j` tail-sets is [[tailsUnion]]
   *  applied `j` times — so the union over `j ∈ k` bounds it from above.  MAY-ONLY: which subtree
   *  survives depends on the unknown items, and the result may be empty. */
  def unwrapUnknown(k: LenBounds, s: Shape): Shape =
    if s.definitelyEmpty || k.isEmpty then empty
    else if k.hi == LenBounds.INF || k.hi > MaxDepth + 2 then weaken(top)
    else
      // ONE PREFIX AT EACH DEPTH, AND ONE DEPTH AMONG `k`.  Both aggregations are
      // ALTERNATIVES and neither is a union: `Unwrap(x, p)` selects the tail-set under the single
      // depth-`|p|` prefix `p`, and when `|p|` is only bracketed by `k` the depth is unknown but
      // still one of them.  So the descent is `tailsAlternative` (the lub over per-head tail-sets)
      // and the fold across depths is `joinAlternatives`, where both used to be the union transfer
      // and both therefore SUMMED counts the operator reads one of.
      var acc = empty
      var cur = s
      var j = 0L
      while j <= k.hi do
        if j >= k.lo then acc = if acc.definitelyEmpty then cur else joinAlternatives(acc, cur)
        cur = tailsAlternative(cur)
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
      (if s.others.hi == 0 then Vector.empty else Vector(untrackedTails(s)))
    if parts.isEmpty then empty else parts.reduce((x, y) => unionTransfer(x, y))

  /** THE UNTRACKED BUCKET'S CONTRIBUTION TO [[tailsUnion]], WITH THE COUNTS OPENED ONLY WHEN THERE
   *  IS SOMETHING TO AGGREGATE OVER.
   *
   *  `otherTail` is a PER-HEAD summary: every untracked head's tail-set is admitted by it.  Turning
   *  that into a bound on the UNION of those tail-sets needs the counts opened, because "at most `k`
   *  untracked heads" is not union-closed — with two untracked heads each carrying one tail the
   *  union carries two.  That is [[openCounts]] and it is what the general case must do.
   *
   *  ==THE ONE CASE WHERE IT MUST NOT==
   *  `others.hi <= 1` says there is AT MOST ONE untracked head, so the union over the untracked heads
   *  is either empty or that single head's tail-set — and `otherTail` bounds that set directly.  There
   *  is no aggregation, so there is nothing to open: the only must-information that has to go is the
   *  head's own presence, and only when it is not forced (`others.lo == 0`), which is [[weaken]].
   *
   *  ==WHY THIS IS THE puzzle15 BOUND (measured)==
   *  `Sliding.superpose`'s per-cell arm is `iterN(res, refs, _, labeled)` over `res = Singleton(tupleP)`
   *  — one path of `n-1` DEREFS, so every level's source has exactly one untracked head.  `labeled`'s
   *  own shape is exact: `{c0?{_?{eps}}, c1?{+[1,1] more}, ...}`, size `[13, 28]`, one tile per cell.
   *  With the counts opened at every one of the 15 levels that `[1,1]` became `[0, inf]` and then, once
   *  the width spill and the certificate cap had bounded it, `[0, 38654705664]` — so the assignment
   *  `Unwrap(state, c_i)` in `Sliding.collapse` cost `|state| = 3584` per cell instead of one tile, and
   *  `collapse`'s 15-fold `Composition` cost `3584^15 = 2.068e+53`.  That product IS the reported
   *  `alloc = 7.6e+55`; the diagnosis is in `build.log` under 1B.5. */
  private def untrackedTails(s: Shape): Shape =
    val t = s.otherTail.getOrElse(top)
    if s.others.hi > 1 then openCounts(t)
    else if s.others.lo >= 1 then t
    else weaken(t)

  /** THE TAIL-SET OF *ONE* HEAD, WHICHEVER IT IS — the ALTERNATIVE over the per-head tail-sets, not
   *  their union.
   *
   *  ==THE DISTINCTION, AND WHY IT IS THE WHOLE OF `Unwrap`'s PRICE==
   *  [[tailsUnion]] abstracts `⋃_h tails(h)`: `unionTransfer` is the transfer for a set union, so it
   *  ADDS the untracked-head counts, because both operands' heads appear in the result.  That is
   *  right for `TailsUnion`, which really does take the union.  `Unwrap(x, p)` does not: it selects
   *  the tail-set under ONE prefix, so the result is one ALTERNATIVE among them and the right
   *  operation is the lattice lub — [[joinAlternatives]], whose `others` is the MAX of the two and
   *  whose must channels are only what both alternatives force.
   *
   *  MEASURED on puzzle15, which is what this is for: `Sliding.collapse`'s state is `map(l) x t`
   *  where `map(l)` is `Unwrap(map, Deref(l))` with `|l| = 1` over a 16-head `map`, so the union's
   *  sum charged 16 tail-sets where the operator reads one — and that factor multiplied through a
   *  15-fold `Composition`.  This is the shape-tier twin of `Shape.maxTailSize`, which does the same
   *  arithmetic on the count channel in `SpatialCost`; they are deliberately adjacent so neither can
   *  be improved without the other being noticed.
   *
   *  THE UNTRACKED CONTRIBUTION IS `otherTail` ITSELF, not `openCounts(otherTail)`: channel (d) is a
   *  PER-HEAD summary and picking one head is exactly the reading it was written for.  That is the
   *  second place the union transfer had to be conservative and this one does not. */
  def tailsAlternative(s: Shape): Shape =
    val parts = s.heads.values.toVector ++
      (if s.others.hi > 0 then Vector(s.otherTail.getOrElse(top)) else Vector.empty)
    if parts.isEmpty then empty else parts.reduce((x, y) => joinAlternatives(x, y))

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
      // (e) `heads(x <| p) ⊆ heads(x) ∩ heads(p)`: a surviving path starts with an x-head that is
      // also the head of some accepted prefix (the ε-prefix case is handled by the arms above).
      // THE CERTIFICATE IS `x`'s ALONE, and meeting it with `prefixes`' was a γ violation:
      // `x <| p` keeps the paths of `x` that START WITH a path of `p`, so a surviving path is
      // `q ++ r` with `q ∈ p` — it is a member of `x`'s language and NOT in general of `p`'s.
      // `SpatialSoundnessHunt` reported it on `Restriction` in every one of the five hunts.
      mk(Presence.No, hs, others, if others.hi == 0 then None else x.otherTail.map(weaken),
         x.langLevel)

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
      // (e) the GRAFT keeps `x`'s heads exactly — `{p ++ q}` starts where `p` starts.  The `ε ∈ x`
      // contribution (all of `y`) is added by the `union` below, which takes the union of bounds.
      val headPart = mk(Presence.No, hs, others, ot, Cert.named(x.possibleHeads.getOrElse(Set.empty))
        match { case c => if x.possibleHeads.isDefined then c else Cert.top })
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
      // (e) a positional slice only DELETES, so `x`'s head-set bound carries
      else mk(s.eps, s.heads, Ivl(0, width), s.otherTail, s.langLevel)

  /** ==============================================================================================
   *  THE RANKED `Range` TRANSFER.
   *
   *  [[range]] above knows only the WIDTH of the window: it keeps every head and caps the count, so
   *  `Range(x, 0, 1)` over a four-head literal reports "one path, any of four heads".  That is
   *  sound and it is nearly useless — the optimiser cannot rewrite a first-path selection it cannot
   *  localise, and the cost model prices a descent into every head.
   *
   *  This transfer LOCALISES the window.  With `others.hi == 0` the head order IS the position
   *  order (see [[orderMin]]), so each tracked head occupies a contiguous BLOCK of positions, and a
   *  head whose block cannot overlap `[lo, hi)` is DEFINITELY NOT SELECTED and is dropped.
   *
   *  ==THE BLOCK ARITHMETIC, AND WHY IT IS AN INTERVAL==
   *  A head's block start is the number of paths before it — `ε` (0 or 1) plus the sizes of every
   *  earlier head — and each of those is an INTERVAL, so the block is `[start.lo, end.hi)`.  Head
   *  `h` survives iff its block can overlap the window:
   *
   *      start.lo < hi   and   end.hi > lo
   *
   *  and is dropped otherwise.  Using `start.lo` and `end.hi` — the widest reading of the block — is
   *  what makes dropping sound: a head is discarded only when even its most generous placement
   *  misses the window.
   *
   *  ==THE WINDOW HAS TO BE KNOWN, AND FOR HALF THE FORMS IT IS FREE==
   *  `RangeBounds.normalize(size, start, end)` needs `size` for a bound that counts from the END.
   *  A FRONT-ANCHORED window (`start >= 0 && end > 0`) does not: `lo` and `hi` come out of `start`
   *  and `end` alone, and the clamp to `size` can only SHRINK the window, which only ever drops more
   *  heads.  So `Range(x, 0, 1)` — the first path, the common case — is localisable whatever the
   *  size interval says, while `Range(x, -1, 0)` — the last path — needs an exact size.  The caller
   *  passes `sizeExact` for that.
   *
   *  ==AND THE SINGLETON CASE IS EXACT==
   *  When the window is exactly one position AND the rank is determined, the result is not "one path
   *  under one head" but that ONE PATH: `Range(x, 0, 1) = {orderMin}` and, at an exact size,
   *  `Range(x, -1, 0) = {orderMax}`.  That is `Shape.of` on a singleton, which is as strong as the
   *  domain gets.
   *  ============================================================================================== */
  def rangeAt(x: Shape, start: Int, end: Int): Option[Shape] =
    // THE ARITHMETIC READS `x`, NOT `weaken(x)`, AND THE FIRST VERSION GOT THIS WRONG.
    //
    // `range` above weakens its operand because a positional slice may DELETE any path, so the
    // result's must-channels have to open.  That is right for the RESULT and wrong for the
    // COMPUTATION: the window indexes into the SOURCE's ordered path list, so every position, every
    // block boundary and both rank endpoints are properties of `x`.  `weaken` recursively does
    // `eps.weak` and `Ivl(0, others.hi)`, which makes `definitelyNonEmpty` false everywhere — and
    // `orderMin`/`orderMax` require the extreme head to be FORCED, so after weakening they return
    // `None` for every shape.  MEASURED: with `s = weaken(x)` the transfer was sound (A, B, C all
    // green) and tightened NOTHING — `Range({a,b}, 0, 1)` still reported `orderMin = None`, which is
    // exactly the failure mode of an abstraction that is only ever compared with itself.
    val s = x
    val sz = s.size
    val exact: Option[Long] = if sz.lo == sz.hi && sz.hi != Ivl.INF then Some(sz.hi) else None
    // ---- the window, when it is known --------------------------------------------------------
    val window: Option[(Long, Long)] = exact match
      case Some(n) if n <= Int.MaxValue =>
        val (l, h) = RangeBounds.normalize(n.toInt, start, end)
        Some((l.toLong, h.toLong))
      case _ =>
        // front-anchored only; `RangeBounds.lower/upper` read `size` for every other form
        if start >= 0 && end > 0 then
          val l = if start == 0 then 0L else (start - 1).toLong
          val h = if start == 0 then end.toLong else (end - 1).toLong
          if h <= l then Some((0L, 0L)) else Some((l, h))
        else None
    window match
      // `None` — NOT a shape.  `rangeAt` must never compute a WIDTH of its own, and the first
      // version did: it fell back to `range(x, windowWidthOf(sz, start, end))` with
      // `windowWidthOf` reading `sz.hi` alone.  THAT IS UNSOUND, because the window width is NOT
      // MONOTONE IN THE SIZE once a bound counts from the end — `normalize(1, -2, 2)` gives width 1
      // and `normalize(3, -2, 2)` gives width 0, so the width at `sz.hi` bounds nothing.
      // `SpatialTypeSystem.windowCard` exists precisely to do that breakpoint analysis, and the
      // comment on the deleted helper claimed to reuse it while re-deriving it.
      //
      // MEASURED: `SpatialSoundnessHunt` HUNT 2 produced the witness on the first run —
      // `Rng($s1.fix(k$1){TU(($k$1 <| gSS($s2)))}, -2, 2)` evaluates to `{b.c}` and the analysis
      // reported `DefinitelyEmpty`.  Returning `Option` removes the possibility: the caller already
      // holds the correct width and this function only ever ADDS rank information.
      case None => None
      case Some((lo, hi)) if hi <= lo => Some(empty)
      case Some((lo, hi)) =>
        // ---- the EXACT singleton, when the rank is determined -------------------------------
        val pinned =
          if hi - lo != 1 then None
          else if lo == 0 then s.orderMin
          else if exact.exists(_ == hi) then s.orderMax
          else None
        pinned match
          case Some(pv) => Some(of(SpaceValue(Set(pv))))
          case None if s.others.hi > 0 =>
            // an untracked head has NO POSITION, so nothing can be localised.  `None`: the caller's
            // width-only reading is the whole answer here.
            None
          case None =>
            // ---- drop every head whose block cannot overlap the window ------------------------
            var startLo = if s.eps == Presence.Must then 1L else 0L
            var endHi = if s.eps.mayBe then 1L else 0L
            val kept = Vector.newBuilder[(PathItem, Shape)]
            for (h, t) <- s.heads do
              val c = t.size
              val blockStartLo = startLo
              val blockEndHi = Ivl.add(endHi, c.hi)
              if blockStartLo < hi && blockEndHi > lo then kept += (h -> t)
              startLo = Ivl.add(startLo, c.lo)
              endHi = blockEndHi
            val keptHeads = kept.result()
            // ε occupies position 0 when present, so it survives only a window that reaches 0
            val eps2 = if lo == 0 then s.eps.weak else Presence.No
            if keptHeads.isEmpty && !eps2.mayBe then Some(empty)
            else Some(
              // THE RESULT IS WEAKENED, which is what `range` weakens its operand for: a positional
              // slice may delete any path, so no must-channel of `x` survives into the result.  The
              // WINDOW is the source's and is computed above from the un-weakened `x`; only what is
              // built here is weak.  Each surviving head keeps its own (weakened) tail-set — a slice
              // never adds a path and never lengthens one.
              mk(eps2, keptHeads.map((h, t) => h -> weaken(t)), Ivl.zero, None, s.langLevel))
end Shape
