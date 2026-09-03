package morkl

import scala.collection.immutable.SortedMap

/** ==================================================================================================
 *  THE UNTRACKED-HEAD CERTIFICATE, AS A PREFIX TRIE (plan.md 1C.1).
 *
 *  ==WHAT IT REPLACES, AND WHY A FLAT NAME SET WAS NOT ENOUGH==
 *  `Shape` used to carry the certificate in TWO flat channels: (e) `otherKeys: Option[Set[PathItem]]`
 *  — "every untracked head is named in this set" — and (f) `headAtoms: Set[Int]`, the same claim with
 *  the set interned so that a spill of a million names stayed usable.  Both are claims about ONE
 *  LEVEL.  Below that level the carrier kept only `otherTail`, a per-head SUMMARY whose counts get
 *  opened the moment they are aggregated, so everything the analysis knew about the sub-structure of
 *  a collapsed level was thrown away with the level.
 *
 *  MEASURED CONSEQUENCE, which is why this tier exists (plan.md 1B.5): `Sliding.superpose`'s per-cell
 *  arm types EXACTLY — `{c0?{_?{eps}}, c1?{+[1,1] more}, ...}`, size `[13, 28]`, one tile per cell —
 *  and `shapeDepth = 4` cannot hold a 15-item path, so `capDepth` collapsed the level and the
 *  `+[1,1]` became `+[0, 38654705664]`.  `Sliding.collapse`'s `Unwrap(state, c_i)` then cost the
 *  WHOLE state (3584) per cell instead of one tile, and its 15-fold `Composition` cost
 *  `3584^15 = 2.068e+53` — puzzle15's reported `alloc`.  A certificate that keeps SUB-STRUCTURE below
 *  the collapsed level is what makes that `[1,1]` survive, and a flat name set cannot express it.
 *
 *  ==THE CLAIM==
 *  A `Cert` denotes a SET OF PATHS and the claim is one-directional and pure MAY:
 *
 *      every path of the certified bucket is admitted by the certificate
 *
 *  There are no counts and no must channels here on purpose.  Counts are (c)'s job and presence is
 *  (a)/(b)'s; mixing either in is how a certificate turns into a second, unsynchronised copy of the
 *  shape lattice.  `Cert` answers exactly one question — IS THIS PATH POSSIBLE — and the two things
 *  the analysis needs from it, disjointness and sub-structure, are both answers to that question.
 *
 *  ==IDENTITY IS A VALUE, AND THE ARENA IS ONLY A CACHE==
 *  [[HeadAtoms]] handed out generation-free `Int` ids into a process-wide append-only table, so a
 *  `Shape` was only meaningful while that table was alive.  Shapes OUTLIVE their analysis —
 *  `SpatialPipeline` reads a stored `SpatialAnalysis` after the run returns — so identity has to be
 *  carried by the value.  [[equals]] and [[hashCode]] here are STRUCTURAL: the interning arena
 *  ([[Cert.arena]]) makes structurally equal certificates the same object, which turns the common
 *  comparison into a pointer test and shares sub-tries, but nothing depends on it.  Clear the arena
 *  mid-run and every answer is unchanged; that is the property `HeadAtoms` did not have.
 *  ================================================================================================== */
final class Cert private (val eps: Boolean,
                          val keys: SortedMap[PathItem, Cert],
                          val outside: Cert.Outside,
                          /** WHICH BUDGET RULES WERE APPLIED TO GET HERE (plan.md 1C.5).
                            *
                            *  `1C.5` asks for every degradation to be RECORDED IN THE RESULT and
                            *  justified by the rule that caused it.  It is carried on the value and
                            *  not in a side table for the same reason the certificate itself is: a
                            *  `Shape` outlives its analysis, and a record that lives in a
                            *  process-wide log is gone by the time `SpatialPipeline` reads the
                            *  stored `SpatialAnalysis`.
                            *
                            *  It is part of [[equals]] and [[hashCode]] deliberately: two
                            *  structurally equal certificates, one exact and one the result of a
                            *  fold, are different claims about how much to trust the bound, and
                            *  interning them together would erase the distinction the record
                            *  exists to make. */
                          val degraded: Set[Cert.Degradation]):

  /** memoised, because the trie is a DAG under interning and a structural hash would otherwise be
   *  recomputed once per parent edge */
  override val hashCode: Int =
    var h = if eps then 0x9e3779b9 else 0x85ebca6b
    h = h * 31 + outside.hashCode + degraded.hashCode * 7
    for (k, c) <- keys do h = h * 31 + k.hashCode * 17 + c.hashCode
    h

  override def equals(o: Any): Boolean = o match
    case c: Cert =>
      (this eq c) ||
        (hashCode == c.hashCode && eps == c.eps && outside == c.outside &&
         degraded == c.degraded && keys == c.keys)
    case _ => false

  /** every degradation anywhere in this trie — what a consumer reports.  A degradation deep in the
   *  trie still weakens the claim a query about that level gets, so the roll-up is the honest
   *  summary and the per-node [[degraded]] says where. */
  def degradationsBelow: Set[Cert.Degradation] =
    val seen = collection.mutable.HashSet.empty[Cert]
    var acc = Set.empty[Cert.Degradation]
    def walk(c: Cert): Unit =
      if seen.add(c) then
        acc = acc union c.degraded
        for (_, x) <- c.keys do walk(x)
        c.outside match
          case Cert.Outside.Bounded(x) => walk(x)
          case _ => ()
    walk(this)
    acc

  /** NO CLAIM AT ALL — the fixed point of the widening and the recursion stopper.  Every channel test
   *  in `Shape.isTop` has to include this one; see the note there on the prototype that did not. */
  def isTop: Boolean = eps && keys.isEmpty && outside == Cert.Outside.Unbounded

  /** the certificate admits NO path: the certified bucket is provably empty */
  def isEmpty: Boolean = !eps && keys.isEmpty && outside == Cert.Outside.Closed

  /** is the HEAD SET named?  `true` ⇒ every path's first item is a key of [[keys]]. */
  def headsNamed: Boolean = outside == Cert.Outside.Closed

  /** the head names, when they are named.  `None` ⇒ no claim about the head set. */
  def headNames: Option[Set[PathItem]] =
    if headsNamed then Some(keys.keySet.toSet) else None

  /** the certificate for the tails under head `h`.  An unnamed head falls to [[outside]]. */
  def under(h: PathItem): Cert = keys.get(h) match
    case Some(c) => c
    case None => outside match
      case Cert.Outside.Closed => Cert.empty
      case Cert.Outside.Unbounded => Cert.top
      case Cert.Outside.Bounded(c) => c

  /** does the certificate admit `p`? — γ's question, and the one every other query reduces to */
  def admits(p: List[PathItem]): Boolean = p match
    case Nil => eps
    case h :: t => keys.get(h) match
      case Some(c) => c.admits(t)
      case None => outside match
        case Cert.Outside.Closed => false
        case Cert.Outside.Unbounded => true
        case Cert.Outside.Bounded(c) => c.admits(t)

  /** does the certificate admit `h` as a head? — the O(1) membership query the shape's `under` needs */
  def admitsHead(h: PathItem): Boolean =
    keys.contains(h) || outside != Cert.Outside.Closed

  /** the union over the heads: a bound on the TAIL-SETS, which is what a level collapse keeps.
   *
   *  This is the operation that makes the tier pay: `capDepth` throws a level away and the tails
   *  below it stay bounded by this, instead of by ⊤. */
  def tailsUnion: Cert =
    val parts = keys.values.toVector ++ (outside match
      case Cert.Outside.Closed => Vector.empty
      case Cert.Outside.Unbounded => Vector(Cert.top)
      case Cert.Outside.Bounded(c) => Vector(c))
    if parts.isEmpty then Cert.empty else parts.reduce(Cert.join)

  /** AN UPPER BOUND ON THE NUMBER OF PATHS admitted.  `Ivl.INF` when unbounded.  Used for the count
   *  channel's cap, never for a lower bound: a certificate is a may claim and admits the empty set. */
  def cardinality: Long =
    if outside == Cert.Outside.Unbounded then Ivl.INF
    else
      var n = if eps then 1L else 0L
      val sub = outside match
        case Cert.Outside.Bounded(_) => Ivl.INF   // unboundedly many unnamed heads
        case _ => 0L
      if sub == Ivl.INF then Ivl.INF
      else
        for (_, c) <- keys do n = Ivl.add(n, c.cardinality)
        n

  /** AN UPPER BOUND ON THE NUMBER OF HEADS admitted.  `Ivl.INF` when the head set is not named. */
  def headBound: Long = if headsNamed then keys.size.toLong else Ivl.INF

  /** does any named head carry a claim of its OWN, rather than ⊤?
   *
   *  This is the predicate that decides whether a DEEP left-hand bound can change an order answer,
   *  and `depth > 1` is not it: `{b/{ε}}` has depth 1 — `Cert.epsOnly` is a leaf — and it constrains
   *  `b`'s tails to the empty path, which a one-level ⊤ bound cannot be shown inside.  A pure NAME
   *  SET, which is what a width spill produces and what most of the corpus carries, has every key at
   *  ⊤ and answers `false`.  Under `Unbounded` there are no ⊤ keys left to look at (`Cert.of` drops
   *  them), so this is also cheap there. */
  def hasSubStructure: Boolean =
    keys.valuesIterator.exists(!_.isTop) || (outside match
      case Cert.Outside.Bounded(_) => true
      case _ => false)

  /** the trie's node count — [[SpatialConfig.certNodes]]'s subject.  Counted over the DAG's distinct
   *  nodes, because interning shares them and the budget is about retained memory. */
  def nodes: Int =
    val seen = collection.mutable.HashSet.empty[Cert]
    def walk(c: Cert): Unit =
      if seen.add(c) then
        for (_, x) <- c.keys do walk(x)
        c.outside match
          case Cert.Outside.Bounded(x) => walk(x)
          case _ => ()
    walk(this)
    seen.size

  /** levels below this node that carry a claim */
  lazy val depth: Int =
    var d = -1
    for (_, c) <- keys do d = d max c.depth
    outside match
      case Cert.Outside.Bounded(c) => d = d max c.depth
      case _ => ()
    d + 1

  def show: String =
    (if degraded.isEmpty then "" else "!") + showBody
  private def showBody: String =
    if isTop then "*"
    else if isEmpty then "0"
    else
      val ks = keys.iterator.map((k, c) => if c.isTop then k else s"$k/${c.show}").mkString(",")
      val o = outside match
        case Cert.Outside.Closed => ""
        case Cert.Outside.Unbounded => if ks.isEmpty then "*" else ",*"
        case Cert.Outside.Bounded(c) => (if ks.isEmpty then "" else ",") + s"?/${c.show}"
      s"{${(if eps then "e" + (if ks.isEmpty && o.isEmpty then "" else ",") else "")}$ks$o}"

  override def toString: String = show
end Cert

object Cert:

  /** what the certificate claims about heads OUTSIDE [[Cert.keys]].
   *
   *  Three states and not two: `Closed` is the (e) claim ("the head set is exactly these names"),
   *  `Unbounded` is ⊤ at this level, and `Bounded` is the one a flat name set could not express —
   *  "there may be names I cannot list, but whatever hangs below them is inside this". */
  enum Outside:
    case Closed
    case Unbounded
    case Bounded(c: Cert)

  /** A BUDGET RULE THAT WAS APPLIED, with the rule as the identity of the record (plan.md 1C.5).
   *
   *  There are exactly two, because [[Cert.widen]] has exactly two rules, and each names what it
   *  gave up rather than merely that something was given up. */
  enum Degradation:
    /** `certDepth` reached: the claim BELOW this level was dropped and every level above it kept. */
    case DepthCut
    /** `certKeys` reached: the per-key sub-tries at this level were replaced by their JOIN, so the
     *  head NAMES survive and which name goes with which sub-trie does not. */
    case WidthFold
  object Degradation:
    def show(ds: Set[Degradation]): String =
      if ds.isEmpty then "exact"
      else ds.toVector.map {
        case DepthCut => s"depth-cut at certDepth"
        case WidthFold => s"width-fold at certKeys"
      }.sorted.mkString("+")

  /** THE INTERNING ARENA — A CACHE AND NOTHING MORE.
   *
   *  It maps a certificate to the canonical instance with that structure, so [[Cert.of]] returns the
   *  same object for the same value and sub-tries are shared.  Two properties are deliberate:
   *
   *   - it is keyed on the `Cert` itself, using the STRUCTURAL `equals`/`hashCode` above, so a hit
   *     is correct by construction rather than by an invariant about ids;
   *   - clearing it is always safe.  [[reset]] exists for the budget suite, which measures retained
   *     size, and for `GlobalState` — a table whose occupancy changes an ANSWER would not be
   *     resettable, and `HeadAtoms` was not.
   *
   *  It is weak-keyed so that a per-analysis arena really is per-analysis: certificates the analysis
   *  has dropped do not pin the table. */
  private val arena =
    java.util.Collections.synchronizedMap(new java.util.WeakHashMap[Cert, java.lang.ref.WeakReference[Cert]]())

  def arenaSize: Int = arena.size

  /** HOW MANY CERTIFICATES THIS PROCESS HAS CONSTRUCTED — the DETERMINISTIC probe.
   *
   *  [[arenaSize]] is not one and must not be probed for determinism: the arena is WEAK-keyed, so its
   *  occupancy depends on when the collector ran.  `scripts/check_determinism.sh` reported it as a
   *  differing PROBE line across two runs of `SpatialEventsCheck` (28 against 41) — correctly, and
   *  the quantity is simply not a determinism signal.
   *
   *  This counter is: it advances once per [[Cert.of]] call, so a run that builds the same
   *  certificates in the same order reports the same number whatever the collector does.  It also
   *  answers the question the probe is actually for — how much certificate work a suite did. */
  private val constructions = new java.util.concurrent.atomic.AtomicLong(0L)
  def constructed: Long = constructions.get

  /** drop the cache.  Cannot change any answer — see the note on [[arena]]. */
  def reset(): Unit = arena.clear()

  private def intern(c: Cert): Cert =
    val r = arena.get(c)
    if r != null then
      val hit = r.get()
      if hit != null then return hit
    arena.put(c, new java.lang.ref.WeakReference(c))
    c

  /** THE SMART CONSTRUCTOR: normalises, then interns.
   *
   *  Normalisation matters for the order, not just for tidiness: `{eps, *}` with no keys IS ⊤, and a
   *  key mapped to the empty certificate admits nothing and must not make the head set look larger
   *  than it is (`possibleHeads` reads `keys.keySet`). */
  def of(eps: Boolean, keys: SortedMap[PathItem, Cert], outside: Outside,
         degraded: Set[Degradation] = Set.empty): Cert =
    val live = keys.filter((_, c) => !c.isEmpty)
    // NORMALISATION MUST NOT SWALLOW A RECORD (plan.md 1C.5).  Both rewrites below DELETE a
    // sub-certificate, and if that sub-certificate was the one a budget rule degraded then the record
    // disappears with it — `SpatialCertCheck` G caught exactly that: a depth cut one level down
    // produced a ⊤ child, `Bounded(⊤)` normalised to `Unbounded`, and the whole certificate came back
    // as ⊤ claiming to be exact.  The same applies to a dropped empty child.
    var dg = degraded
    for (_, c) <- keys if c.isEmpty do dg = dg union c.degradationsBelow
    val out = outside match
      case Outside.Bounded(c) if c.isTop => dg = dg union c.degradationsBelow; Outside.Unbounded
      case Outside.Bounded(c) if c.isEmpty => dg = dg union c.degradationsBelow; Outside.Closed
      case o => o
    // ==A CERTIFICATE THAT ADMITS EVERYTHING IS `Cert.top`, AND HAS TO BE SPELLED THAT WAY==
    //
    // Under `Unbounded` an unnamed head is already unconstrained, so naming a head and giving it ⊤
    // adds NOTHING: `of(true, {b -> top}, Unbounded)` and `Cert.top` admit exactly the same paths.
    // Keeping the key made the two spellings distinct, and `Cert.leq(top, that)` is `false` by its
    // `a.isTop` arm — so the ORDER refused a pair whose languages are equal.
    //
    // MEASURED: `SpatialPipelineCheck`'s "the per-analysis trie caps only WEAKEN" gate.  A shape with
    // no `otherTail` (⊤ tails) narrowed to one whose summary carried the certificate
    // `{ε, b/{ε, b, *}, *}` — whose language is everything, level by level — and `leqStrong` reported
    // `shape:otherTail` because the untracked-tail comparison pitted ⊤ against it.  Dropping ⊤ keys
    // under `Unbounded` collapses that certificate to `Cert.top` recursively (the inner `{ε, b, *}`
    // goes first, which makes the outer key ⊤, which then goes too) and the pair is accepted.
    //
    // This is exactly the hazard `Shape.isTop`'s note records for the first key-certificate
    // prototype, arriving from the other direction: there a non-⊤ certificate LOOKED like ⊤ to the
    // order, here a ⊤ certificate did not.
    val live2 =
      if out == Outside.Unbounded then
        val dropped = live.filter((_, c) => c.isTop)
        for (_, c) <- dropped do dg = dg union c.degradationsBelow
        live.filter((_, c) => !c.isTop)
      else live
    constructions.incrementAndGet()
    intern(new Cert(eps, live2, out, dg))

  /** the same certificate with extra degradation records — used where a short circuit returns one
   *  operand and the other's record would otherwise be dropped */
  private def withDegraded(c: Cert, ds: Set[Degradation]): Cert =
    if ds.subsetOf(c.degraded) then c else of(c.eps, c.keys, c.outside, c.degraded union ds)

  val top: Cert = of(true, SortedMap.empty, Outside.Unbounded)
  val empty: Cert = of(false, SortedMap.empty, Outside.Closed)
  val epsOnly: Cert = of(true, SortedMap.empty, Outside.Closed)

  /** the (e) CERTIFICATE, translated: "every head is named in `ks`, nothing claimed below".  This is
   *  the exact meaning `otherKeys = Some(ks)` had, so every former (e) site maps to this and keeps
   *  its old strength. */
  def named(ks: Set[PathItem]): Cert =
    // `eps = true`: this is a claim about HEADS and ε has none.  The first draft had `false` and γ
    // then rejected every value containing the empty path against a shape whose `eps` was `May` —
    // the same shape of bug the old `reCap` note records for `Some(∅)`.
    of(true, SortedMap.from(ks.iterator.map(_ -> top)), Outside.Closed)

  /** one path, as a certificate — the sharpest thing a `Singleton(Constant(p))` can say */
  def path(p: List[PathItem]): Cert = p match
    case Nil => epsOnly
    case h :: t => of(false, SortedMap(h -> path(t)), Outside.Closed)

  /** THE JOIN: a certificate for the union of the two certified sets.  `admits` is monotone in it, and
   *  that is the whole soundness obligation — `join(a,b).admits(p)` whenever either side does. */
  def join(a: Cert, b: Cert): Cert =
    if (a eq b) then a
    else if a.isEmpty then withDegraded(b, a.degraded)
    else if b.isEmpty then withDegraded(a, b.degraded)
    else if a.isTop || b.isTop then withDegraded(top, a.degraded union b.degraded)
    else
      val out = (a.outside, b.outside) match
        case (Outside.Unbounded, _) | (_, Outside.Unbounded) => Outside.Unbounded
        case (Outside.Closed, Outside.Closed) => Outside.Closed
        case (Outside.Closed, o) => o
        case (o, Outside.Closed) => o
        case (Outside.Bounded(x), Outside.Bounded(y)) => Outside.Bounded(join(x, y))
      // a key tracked on one side only still needs the OTHER side's `outside` folded in: a path under
      // that head is admitted by the other side exactly when its `outside` admits the tail.
      var ks = SortedMap.empty[PathItem, Cert]
      for k <- a.keys.keySet union b.keys.keySet do
        ks = ks + (k -> join(a.under(k), b.under(k)))
      of(a.eps || b.eps, ks, out, a.degraded union b.degraded)

  /** THE MEET: a certificate for any set both certify.  Sound in the only direction that matters —
   *  a path both sides admit is admitted by the meet — and it is where two independent certificates
   *  combine, which is how a certified operand tightens an uncertified one. */
  def meet(a: Cert, b: Cert): Cert =
    if (a eq b) then a
    else if a.isTop then withDegraded(b, a.degraded)
    else if b.isTop then withDegraded(a, b.degraded)
    else if a.isEmpty || b.isEmpty then withDegraded(empty, a.degraded union b.degraded)
    else
      val out = (a.outside, b.outside) match
        case (Outside.Closed, _) | (_, Outside.Closed) => Outside.Closed
        case (Outside.Unbounded, o) => o
        case (o, Outside.Unbounded) => o
        case (Outside.Bounded(x), Outside.Bounded(y)) => Outside.Bounded(meet(x, y))
      // ONLY the keys both sides can admit as heads survive.  A key one side does not track is
      // admitted by that side only through its `outside`, which `under` already returns.
      val cand = if a.headsNamed && b.headsNamed then a.keys.keySet intersect b.keys.keySet
                 else if a.headsNamed then a.keys.keySet
                 else if b.headsNamed then b.keys.keySet
                 else a.keys.keySet union b.keys.keySet
      var ks = SortedMap.empty[PathItem, Cert]
      for k <- cand do ks = ks + (k -> meet(a.under(k), b.under(k)))
      of(a.eps && b.eps, ks, out, a.degraded union b.degraded)

  /** `a` admits nothing `b` does not — the certificate half of `Shape.leq`. */
  def leq(a: Cert, b: Cert): Boolean =
    if (a eq b) || b.isTop || a.isEmpty then true
    else if a.isTop then false
    else if (a.eps && !b.eps) then false
    else
      val outOk = (a.outside, b.outside) match
        case (Outside.Closed, _) => true          // `a` has no unnamed head, so there is nothing to check
        case (_, Outside.Unbounded) => true       // `b` claims nothing there
        case (_, Outside.Closed) => false         // `a` may have a head `b` forbids
        case (Outside.Unbounded, _) => false      // `a` claims nothing where `b` does
        case (Outside.Bounded(x), Outside.Bounded(y)) => leq(x, y)
      // BOTH KEY SETS, NOT JUST `a`'s.  A key `b` TRACKS but `a` reaches through its `outside` has to
      // satisfy `b`'s child for that key, and the `outside` comparison above does not look at it:
      // `leq({a/X, ?/T}, {ε, b/Y, *})` was accepted because `a` has no key `b` and `b`'s outside is
      // ⊤, while `a` admits `b·t` for `t ∈ T` and `b` admits it only for `t ∈ Y`.
      // `SpatialCertCheck` D found it against exhaustive containment on the first run — the same
      // defect, on this channel, that `Shape.leq`'s own note records ("It compares the union of BOTH
      // live key sets, not just `a`'s").
      outOk && (a.keys.keySet union b.keys.keySet).forall(k => leq(a.under(k), b.under(k)))

  /** AN UPPER BOUND ON THE UNTRACKED HEAD COUNT: the named heads MINUS the ones already tracked.
   *
   *  `headBound` counts every head the certificate names, and with the whole-language reading that
   *  includes the TRACKED ones — they are part of the shape's language too.  The count channel (c) is
   *  about the UNTRACKED bucket alone, so capping it with `headBound` over-counts by exactly the
   *  tracked heads the certificate also names.
   *
   *  MEASURED: `SpatialAcceptance`'s puzzle15 precision entry.  The flat certificate held
   *  `complete MINUS tracked` (4 names past `MaxHeads = 12`) so `others.hi <= 4` and the head count
   *  was `12 + 4 = 16`; the trie names all 16, so the same cap gave `others.hi <= 16` and the head
   *  count regressed to 28.  Subtracting here restores 16 and keeps the trie's whole-language reading,
   *  which is what everything else in the tier depends on. */
  def headBoundExcluding(c: Cert, tracked: Set[PathItem]): Long =
    c.headNames match
      case None => Ivl.INF
      case Some(ks) => (ks diff tracked).size.toLong

  /** the union over the heads NOT in `tracked` — the bound on what an open shape's untracked bucket
   *  holds below the level, which is what the relational frontier walk descends into (plan.md 1C.4).
   *
   *  It differs from [[Cert.tailsUnion]] in exactly the way the walk needs: the tracked heads have
   *  their own frames already, so folding their sub-tries in here would make the summary frame
   *  describe paths the walk is counting twice. */
  def tailsUnionExcept(c: Cert, tracked: Set[PathItem]): Cert =
    val parts = c.keys.iterator.collect { case (k, v) if !tracked.contains(k) => v }.toVector ++
      (c.outside match
        case Outside.Closed => Vector.empty
        case Outside.Unbounded => Vector(top)
        case Outside.Bounded(x) => Vector(x))
    if parts.isEmpty then empty else parts.reduce(join)

  /** DO THE TWO CERTIFICATES SHARE A HEAD? — the query the whole tier exists for.  `false` means the
   *  two certified sets are HEAD-DISJOINT, so a union of them is a concatenation and not a merge.
   *
   *  Answered from the named half alone, which is the point: it costs one set intersection over the
   *  keys at this level and never descends. */
  def headsDisjoint(a: Cert, b: Cert): Boolean =
    if a.isEmpty || b.isEmpty then true
    else if !a.headsNamed || !b.headsNamed then false
    else (a.keys.keySet intersect b.keys.keySet).isEmpty

  /** WHAT THE CERTIFICATE ITSELF COSTS, as one line for `FrontierSummary.notes` (plan.md 1C.7).
   *
   *  The tier adds a channel to a carrier every lattice operation recurses over, so its own cost has
   *  to be quoted rather than assumed small.  Four quantities, each named with the operation it
   *  prices:
   *
   *   - CONSTRUCTION: `nodes`, the DISTINCT trie nodes reachable — interning shares them, so this is
   *     what was actually built and not what a naive walk would count.
   *   - LOOKUP (`Cert.under`, which `Shape.under` calls on every descent into an untracked head): one
   *     `SortedMap` lookup per level, so `depth` bounds it.
   *   - INTERSECTION (`Cert.headsDisjoint`, the query the whole tier exists for): ONE set
   *     intersection over the smaller top-level key set, `min(headBound)` comparisons — and O(1) when
   *     interning has made the two tries the same object, which is the common case for two
   *     occurrences of one mention.
   *   - RETAINED MEMORY: the shape holds ONE reference; the nodes live once in the weak-keyed arena,
   *     whose current occupancy is quoted so a run that retains an unexpected amount is visible.
   *
   *  A ⊤ certificate on both sides costs nothing and produces no note. */
  def costNote(a: Cert, b: Cert): Option[String] =
    if a.isTop && b.isTop then None
    else
      val cmp = if a.headsNamed && b.headsNamed then (a.keys.size min b.keys.size).toString
                else "not named: no intersection to run"
      val dg = a.degradationsBelow union b.degradationsBelow
      Some(s"certificate: ${a.nodes}+${b.nodes} distinct trie nodes retained (depth ${a.depth}/" +
           s"${b.depth}, heads ${show(a.headBound)}/${show(b.headBound)}); lookup is one map probe " +
           s"per level; head-disjointness is one key-set intersection over $cmp keys, O(1) when the " +
           s"two are the same interned object; the shape holds ONE reference and the arena " +
           s"${arenaSize} nodes" +
           (if dg.isEmpty then "; the claim is exact"
            else s"; DEGRADED by a budget rule (${Degradation.show(dg)}), so the bound is weaker " +
                 "than the transfers derived"))

  private def show(n: Long): String = if n >= Ivl.INF then "unnamed" else n.toString

  /** THE WIDENING (plan.md 1C.5): bring a certificate inside the budgets, RECORDING nothing here —
   *  the caller records, because only the caller knows which shape degraded.
   *
   *  Two budgets, and each degrades in the one direction that stays sound:
   *
   *   - DEPTH: below `maxDepth` the trie is replaced by `Unbounded`, i.e. the sub-structure claim is
   *     dropped and the head claims above it are kept.  This is the only cut that keeps the levels
   *     that carry the disjointness argument.
   *   - WIDTH: above `maxKeys` DISTINCT sub-tries at one level, every child is replaced by the JOIN
   *     of all the children — one shared sub-trie instead of one per key.  THE NAMES SURVIVE, which is the whole
   *     difference from the flat certificate this replaces: over its cap that degraded to ⊤ and a
   *     key-disjoint family's predicted rebuild jumped from `Θ(1)` to `Θ(n)` at exactly 4097 keys
   *     (MEASURED — `SpatialFrontierCheck`'s "CONTINUITY ACROSS THE WIDTH CAP" reported
   *     `rebuilt = [2, 4099]` against a truth of 2).  THE BUDGET COUNTS DISTINCT SUB-TRIES AND NOT
   *     KEYS, and that is the whole design: the recursive walk costs one visit per distinct sub-trie
   *     (interning makes shared ones one object), while the key set itself is one interned
   *     `SortedMap` held once in the arena and compared by pointer.  Counting keys instead would
   *     make the fold's own output violate the budget it just enforced — `SpatialCertCheck` G
   *     reported exactly that.
   *
   *     A level whose children are all ⊤ — a pure name set, i.e. exactly what the old channels
   *     (e)/(f) could express — has ZERO distinct sub-tries and is left alone at any width.  So the
   *     disjointness argument, which is the only thing a name set is for, has no size at which it
   *     expires.
   *
   *  `maxDepth <= 0` or `maxKeys <= 0` mean "no budget". */
  def widen(c: Cert, maxDepth: Int, maxKeys: Int): Cert =
    def go(x: Cert, d: Int): Cert =
      if x.isTop || x.isEmpty then x
      else if maxDepth > 0 && d >= maxDepth then
        // the claim below is dropped; ε and the head names at this level are not this cut's business
        of(true, SortedMap.empty, Outside.Unbounded, Set(Degradation.DepthCut))
      else
        val kids = SortedMap.from(x.keys.view.mapValues(go(_, d + 1)))
        val out = x.outside match
          case Outside.Bounded(t) => Outside.Bounded(go(t, d + 1))
          case o => o
        if maxKeys > 0 && distinctSubs(kids) > maxKeys then
          // THE FOLD'S OWN OUTPUT IS RE-WIDENED, and it has to be: `join` does not preserve the width
          // budget.  Two children each inside it — say `{a/X, b/X}` and `{a/P, b/P}` — join to
          // `{a/join(X,P), b/join(Y,Q)}`, whose level can hold more distinct sub-tries than either
          // input did.  `SpatialCertCheck` G caught it as `withinBudget(widen(c, 3, 1))` being false:
          // the rule was enforcing a budget its own result then violated.  `go` on the join
          // re-establishes it, and terminates because the join is strictly shallower than the level
          // that produced it.
          val folded = go(kids.values.reduce(join), d + 1)
          of(x.eps, SortedMap.from(kids.keysIterator.map(_ -> folded)), out,
             x.degraded + Degradation.WidthFold)
        else of(x.eps, kids, out, x.degraded)
    go(c, 0)

  /** the number of DISTINCT non-⊤ sub-tries at one level — what [[widen]]'s width budget bounds and
   *  what the recursive walk over the level costs.  ⊤ children are not counted: they carry no
   *  structure to walk, which is why a pure name set is inside every width budget. */
  private def distinctSubs(keys: SortedMap[PathItem, Cert]): Int =
    keys.valuesIterator.filter(!_.isTop).toSet.size

  /** is `c` inside the budgets? — so a caller can record a degradation only when one happened */
  def withinBudget(c: Cert, maxDepth: Int, maxKeys: Int): Boolean =
    def go(x: Cert, d: Int): Boolean =
      if x.isTop || x.isEmpty then true
      else if maxDepth > 0 && d >= maxDepth then false
      else if maxKeys > 0 && distinctSubs(x.keys) > maxKeys then false
      else x.keys.forall((_, k) => go(k, d + 1)) && (x.outside match
        case Outside.Bounded(t) => go(t, d + 1)
        case _ => true)
    go(c, 0)
end Cert
