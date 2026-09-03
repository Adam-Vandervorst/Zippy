package morkl

import scala.collection.immutable.{IntMap, IntTrieOps}
import scala.collection.mutable

/** Global, constant-time interner for [[PathItem]] <-> Int.  Interning is global because it is
 *  O(1) amortized (a ConcurrentHashMap lookup + an append on first sight) and ids are stable
 *  for the process, so the same symbol always maps to the same int across all tries. */
object Interner:
  private val toId = new java.util.concurrent.ConcurrentHashMap[PathItem, Integer]()
  private val fromId = new java.util.ArrayList[PathItem]()
  def intern(p: PathItem): Int =
    val e = toId.get(p)
    if e != null then e.intValue
    else synchronized {
      val again = toId.get(p)
      if again != null then again.intValue
      else { val id = fromId.size; fromId.add(p); toId.put(p, Integer.valueOf(id)); id }
    }
  def unintern(id: Int): PathItem = fromId.get(id)
  def internPath(items: List[PathItem]): List[Int] = items.map(intern)
  def uninternPath(ids: List[Int]): List[PathItem] = ids.map(unintern)
  def size: Int = fromId.size

/** A persistent path-trie whose children are keyed by INTERNED int path items, backed by
 *  `IntMap` (a big-endian Patricia trie).  This lets the ring operations use IntMap's
 *  structural, O(n+m) simultaneous descents directly — they line up exactly with the algebra
 *  (union = merge-with-recursive-union, intersection = merge-with-recursive-intersection).
 *  Evaluation over [[ITrie]] never touches a [[PathItem]]: it only combines interned ints;
 *  un-interning happens only at the [[toSpaceValue]] boundary. */
final case class ITrie(terminal: Boolean, children: IntMap[ITrie]):
  def isEmpty: Boolean = !terminal && children.isEmpty
  def nonEmpty: Boolean = !isEmpty

  /** CACHED TERMINAL COUNT.
   *
   *  `ITrie.range` used to recompute the full recursive size on EVERY query, *before* its own
   *  identity check, so even a full-window slice walked every node of the operand.  The count is now
   *  computed at most once per node object and read in O(1) afterwards, which is what makes a full
   *  `Range` genuinely O(1) and what lets the order-statistic slice accept or reject a whole subtrie
   *  by comparing offsets instead of enumerating it.
   *
   *  The per-node walk is still counted — but only on the pass that computes it — so the `touch`
   *  oracle stays honest: a cache hit really is one `int` load and the events say so.
   *
   *  A plain non-volatile `int`: the write is idempotent and `int` writes do not tear, so a benign
   *  race can only recompute.  It also costs no extra memory in practice, fitting the padding of the
   *  existing (header + boolean + one reference) layout. */
  private var szc: Int = -1
  /** the cached count, or `-1` when it has not been computed — for cheap rejection in [[ITrie.equalT]],
   *  which must not FORCE a full walk just to compare two iterates. */
  private[morkl] def countIfKnown: Int = szc
  def count: Int =
    var s = szc
    if s < 0 then
      effort(EffortEvent.TrieNodeVisit)
      s = (if terminal then 1 else 0) + children.valuesIterator.map(_.count).sum
      szc = s
    s
  /** number of paths (terminals) in the set — O(1) once computed, see [[count]] */
  def size: Int = count

  // Every other recursive walk below counts ONE EffortEvent.TrieNodeVisit per node it examines.
  // These are the per-node descents the review says were uncounted; `SpatialCost`'s `touch`
  // component is defined by them (plus EffortEvent.PatriciaVisit), which is what makes `touch`
  // calibratable at all.
  def nodeCount: Int =
    effort(EffortEvent.TrieNodeVisit)
    1 + children.valuesIterator.map(_.nodeCount).sum
  def prefixCount(n: Int): Int =
    effort(EffortEvent.TrieNodeVisit)
    if n == 0 then (if nonEmpty then 1 else 0) else children.valuesIterator.map(_.prefixCount(n - 1)).sum
  def toSpaceValue: SpaceValue = SpaceValue(ITrie.toPaths(this))

object ITrie:
  val empty: ITrie = ITrie(false, IntMap.empty)
  val epsilon: ITrie = ITrie(true, IntMap.empty)

  /** THE ONE ALLOCATION SITE of the algebra.  Every `ITrie` node this file builds goes through here
   *  and counts one [[EffortEvent.FreshTrieNode]], so `alloc` has an oracle on all three trie-shaped
   *  executables.  `empty`/`epsilon` are process-wide vals and allocate nothing per operation.
   *
   *  `SpaceZipper.materialize` builds its nodes in Zipper.scala and counts [[EffortEvent.FreshNode]]
   *  instead, so the two never double-count the same object. */
  private[morkl] inline def node(terminal: Boolean, children: IntMap[ITrie]): ITrie =
    effort(EffortEvent.FreshTrieNode)
    ITrie(terminal, children)

  def singleton(ids: List[Int]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    ids.foldRight(epsilon)((id, acc) => node(false, IntMap.singleton(id, acc)))
  def singletonP(p: PathValue): ITrie = singleton(Interner.internPath(p.items))
  /** Deliberately a LEFT FOLD, not [[joinAll]]: `union(acc, singleton)` is `O(|p|)` because the
   *  singleton's child map is a `Tip`, so the fold is already `O(sum of path lengths)` — the same
   *  order as the n-ary pass — while the n-ary pass would first buffer one `ITrie` per path and
   *  identity-dedupe them.  On a million-path literal that buffer is the whole cost. */
  def fromSpaceValue(sv: SpaceValue): ITrie = sv.paths.foldLeft(empty)((t, p) => union(t, singletonP(p)))

  def toPaths(t: ITrie): Set[PathValue] =
    val out = Set.newBuilder[PathValue]
    def go(n: ITrie, acc: List[Int]): Unit =
      effort(EffortEvent.TrieNodeVisit)
      if n.terminal then out += PathValue(Interner.uninternPath(acc.reverse))
      n.children.foreach { case (k, c) => go(c, k :: acc) }
    go(t, Nil); out.result()

  // ================================================================================================
  // THE CASE-RETURNING ALGEBRA
  // ================================================================================================

  /** Per-node outcome of a set-algebraic operation, RELATIVE to its arguments — `Trie.AlgebraicResult`
   *  (Trie.scala), which mirrors pathmap's `AlgebraicResult<V>` (ring.rs), moved ONTO THE INTERNED
   *  PATRICIA REPRESENTATION so that `evalI` — the executable `Backend.Trie` actually names — is the
   *  optimal one rather than a second-best cousin of an uninstrumented reference algebra.
   *
   *    - `Identity(mask)` — the result IS an argument (LEFT bit / RIGHT bit; both bits assert the
   *      arguments denote the same set).  The caller reuses the argument NODE OBJECT unchanged: no
   *      allocation, no re-traversal, structural sharing preserved all the way up.  This is the
   *      "accept an entire left subspace by pointer" case; it is counted
   *      ([[EffortEvent.AlgebraIdentityLeft]] / [[EffortEvent.AlgebraIdentityRight]] and
   *      [[EffortEvent.SubtrieAcceptedByPointer]]) precisely because a cost model cannot express it
   *      otherwise.
   *    - `Empty` — the result is the empty set; the parent prunes the key instead of storing an empty
   *      child.  Where both `Empty` and `Identity` hold (all arguments empty), `Empty` wins — the
   *      ring.rs convention.
   *    - `Bespoke(t)` — the result genuinely mixes the arguments; a fresh node was built.
   *
   *  Case inventory (exact characterizations, identical to `Trie.AlgebraicResult`'s):
   *    union         Identity(L) ⟺ b ⊆ a;  Identity(R) ⟺ a ⊆ b;  both ⟺ a == b;
   *                  Empty ⟺ both arguments empty.
   *    intersection  Identity ⟺ that argument is contained in the other;  Empty ⟺ disjoint.
   *    subtraction   Identity(L) ⟺ a ∩ b == ∅;  Empty ⟺ a ⊆ b.  Result == right is not a case.
   *    restriction   Identity(L) ⟺ every left path extends some right prefix (ε ∈ right is the
   *                  degenerate case);  Identity(R) ⟺ the result equals right as a set;  Empty ⟺
   *                  either side empty or nothing extends anything.
   *    raffination   Identity(L) ⟺ no left path extends a right prefix;  Empty ⟺ every one does.
   *    composition   Identity(L) ⟺ b == {ε};  Identity(R) ⟺ a == {ε};  Empty ⟺ either side empty.
   *
   *  ==BIT SOUNDNESS AND THE ONE DOCUMENTED UNDER-REPORT==
   *
   *  A SET bit is always true: `Identity(LEFT)` really does mean "the result equals the left argument
   *  as a set", because it is concluded from PONTER equality of the merged children map with the
   *  argument's own children map (plus a terminal-flag check), and the children maps are canonical —
   *  no empty values, no duplicate keys — so pointer equality implies set equality.
   *
   *  An UNSET bit is sound but, unlike `Trie`'s explicitly book-kept version, not complete: when the
   *  two arguments denote the same set through DIFFERENT node objects, the merge preserves one of the
   *  two maps by pointer (the left, by convention) and reports `Identity(LEFT)` rather than
   *  `Identity(BOTH)`.  Detecting `BOTH` there would need a second content comparison, which is
   *  exactly the traversal identity propagation exists to avoid.  `OptimalTrieCheck` asserts
   *  soundness of every bit and completeness of the LEFT bit against the characterizations above,
   *  and pins this under-report so it cannot silently widen. */
  enum AlgebraicResult:
    case Empty
    case Identity(mask: Int)
    case Bespoke(t: ITrie)

  object AlgebraicResult:
    inline val LEFT = 1
    inline val RIGHT = 2
    inline val BOTH = 3

  import AlgebraicResult.{LEFT, RIGHT, BOTH}
  private val IdentL = AlgebraicResult.Identity(LEFT)
  private val IdentR = AlgebraicResult.Identity(RIGHT)
  private val IdentB = AlgebraicResult.Identity(BOTH)

  /** THE CASE ORACLE.  Exactly one of the four events fires per algebraic decision, and the one that
   *  fires names the object the caller will reuse — so `AlgebraEmpty + AlgebraIdentityLeft +
   *  AlgebraIdentityRight + AlgebraBespoke` is the number of decisions the run made, and the identity
   *  counts are the number of whole subspaces accepted without traversal.  `Identity(BOTH)` is
   *  reported as LEFT because `pick` hands back the left object. */
  private def rEmpty: AlgebraicResult =
    effort(EffortEvent.AlgebraEmpty); AlgebraicResult.Empty
  private def rIdent(mask: Int): AlgebraicResult =
    effort(EffortEvent.SubtrieAcceptedByPointer)
    if (mask & LEFT) != 0 then
      effort(EffortEvent.AlgebraIdentityLeft)
      if mask == BOTH then IdentB else IdentL
    else
      effort(EffortEvent.AlgebraIdentityRight)
      IdentR
  private def rBespoke(t: ITrie): AlgebraicResult =
    effort(EffortEvent.AlgebraBespoke); AlgebraicResult.Bespoke(t)

  /** Materialize a result against the arguments it is relative to.  `Identity` resolves to the
   *  argument OBJECT (left preferred when both bits are set), keeping sharing exact. */
  private[morkl] def pick(r: AlgebraicResult, a: ITrie, b: ITrie): ITrie = r match
    case AlgebraicResult.Empty => empty
    case AlgebraicResult.Identity(m) => if (m & LEFT) != 0 then a else b
    case AlgebraicResult.Bespoke(t) => t

  // ---- children-map merges -----------------------------------------------------------------------
  // The Patricia forms (Tuning.patriciaOps, the default) are the pointer-preserving simultaneous
  // descents in IntTrieOps.  The fallback forms are per-key folds kept so `-Dmorkl.patriciaOps=false`
  // still MEANS something; they preserve the LEFT map by pointer (so the asymptotically important
  // "accepted the whole left subspace" case survives in both modes) but do not detect the RIGHT bit.

  private def mergeUnion(x: IntMap[ITrie], y: IntMap[ITrie]): IntMap[ITrie] =
    if Tuning.patriciaOps then IntTrieOps.unionTries(x, y)
    else
      var ch = x
      y.foreach { case (k, yc) =>
        effort(EffortEvent.PatriciaEntry)
        x.get(k) match
          case None => ch = ch.updated(k, yc)
          case Some(xc) => val u = union(xc, yc); if !(u eq xc) then ch = ch.updated(k, u) }
      ch

  private def mergeIntersect(x: IntMap[ITrie], y: IntMap[ITrie]): IntMap[ITrie] =
    if Tuning.patriciaOps then IntTrieOps.intersectTries(x, y)
    else
      var ch = IntMap.empty[ITrie]
      var kept = 0
      var allLeft = true
      x.foreach { case (k, xc) =>
        effort(EffortEvent.PatriciaEntry)
        y.get(k) match
          case None => allLeft = false
          case Some(yc) =>
            val r = intersection(xc, yc)
            if r.isEmpty then allLeft = false
            else { if !(r eq xc) then allLeft = false; ch = ch.updated(k, r); kept += 1 } }
      if allLeft && kept == x.size then x else ch

  private def mergeDiff(x: IntMap[ITrie], y: IntMap[ITrie]): IntMap[ITrie] =
    if Tuning.patriciaOps then IntTrieOps.diffTries(x, y)
    else
      var ch = x
      y.foreach { case (k, yc) =>
        effort(EffortEvent.PatriciaEntry)
        x.get(k).foreach { xc =>
          val r = subtraction(xc, yc)
          if r.isEmpty then ch = ch - k else if !(r eq xc) then ch = ch.updated(k, r) } }
      ch

  private def mergeRestrict(x: IntMap[ITrie], p: IntMap[ITrie]): IntMap[ITrie] =
    if Tuning.patriciaOps then IntTrieOps.restrictTries(x, p)
    else
      var ch = IntMap.empty[ITrie]
      var kept = 0
      var allLeft = true
      x.foreach { case (k, xc) =>
        effort(EffortEvent.PatriciaEntry)
        p.get(k) match
          case None => allLeft = false
          case Some(pc) =>
            val r = restriction(xc, pc)
            if r.isEmpty then allLeft = false
            else { if !(r eq xc) then allLeft = false; ch = ch.updated(k, r); kept += 1 } }
      if allLeft && kept == x.size then x else ch

  private def mergeRaff(x: IntMap[ITrie], y: IntMap[ITrie]): IntMap[ITrie] =
    if Tuning.patriciaOps then IntTrieOps.raffTries(x, y)
    else
      var ch = x
      y.foreach { case (k, yc) =>
        effort(EffortEvent.PatriciaEntry)
        x.get(k).foreach { xc =>
          val r = raffination(xc, yc)
          if r.isEmpty then ch = ch - k else if !(r eq xc) then ch = ch.updated(k, r) } }
      ch

  // ---- ring of sets ------------------------------------------------------------------------------
  // Each op is a thin wrapper over its `...R` form, which reports the algebraic case; the `R` forms
  // recurse on themselves (through the children-map merges) so identity/emptiness propagates
  // bottom-up: a node whose children all come back by pointer, and whose terminal is unaffected, is
  // itself `Identity` — the whole subtree is reused with zero allocation.

  def union(a: ITrie, b: ITrie): ITrie = pick(unionR(a, b), a, b)
  def unionR(a: ITrie, b: ITrie): AlgebraicResult =
    effort(EffortEvent.TrieNodeVisit)
    if a eq b then { effort(EffortEvent.ReusedSubtrie); if a.isEmpty then rEmpty else rIdent(BOTH) }
    else if b.isEmpty then (if a.isEmpty then rEmpty else rIdent(LEFT))
    else if a.isEmpty then rIdent(RIGHT)
    else
      val term = a.terminal || b.terminal
      val ch = mergeUnion(a.children, b.children)
      val l = (ch eq a.children) && term == a.terminal
      val r = (ch eq b.children) && term == b.terminal
      if l then rIdent(if r then BOTH else LEFT)
      else if r then rIdent(RIGHT)
      else rBespoke(node(term, ch))

  def intersection(a: ITrie, b: ITrie): ITrie = pick(intersectionR(a, b), a, b)
  def intersectionR(a: ITrie, b: ITrie): AlgebraicResult =
    effort(EffortEvent.TrieNodeVisit)
    if a eq b then { effort(EffortEvent.ReusedSubtrie); if a.isEmpty then rEmpty else rIdent(BOTH) }
    else if a.isEmpty || b.isEmpty then rEmpty
    else
      val term = a.terminal && b.terminal
      val ch = mergeIntersect(a.children, b.children)
      if ch.isEmpty && !term then rEmpty
      else
        val l = (ch eq a.children) && term == a.terminal
        val r = (ch eq b.children) && term == b.terminal
        if l then rIdent(if r then BOTH else LEFT)
        else if r then rIdent(RIGHT)
        else rBespoke(node(term, ch))

  def subtraction(a: ITrie, b: ITrie): ITrie = pick(subtractionR(a, b), a, b)
  def subtractionR(a: ITrie, b: ITrie): AlgebraicResult =
    effort(EffortEvent.TrieNodeVisit)
    if a eq b then { effort(EffortEvent.ReusedSubtrie); rEmpty }
    else if a.isEmpty then rEmpty
    else if b.isEmpty then rIdent(LEFT)
    else
      val term = a.terminal && !b.terminal
      val ch = mergeDiff(a.children, b.children)
      if ch.isEmpty && !term then rEmpty
      else if (ch eq a.children) && term == a.terminal then rIdent(LEFT)
      else rBespoke(node(term, ch))

  /** restriction `x <| prefixes`: keep the x-paths that start with some path in `prefixes` (keeping
   *  the prefix).  Walk x guided by the prefixes trie; when a prefix ENDS (`prefixes.terminal`) the
   *  entire x-subtree below is kept — by pointer, in constant time, whatever its size.  That is the
   *  central operation of this backend: restriction by `{ε}` is O(1) and restriction by one present
   *  prefix of length `d` is Θ(d), independent of the millions of nodes below the matched prefix. */
  def restriction(x: ITrie, prefixes: ITrie): ITrie = pick(restrictionR(x, prefixes), x, prefixes)
  def restrictionR(x: ITrie, prefixes: ITrie): AlgebraicResult =
    effort(EffortEvent.TrieNodeVisit)
    if x eq prefixes then { effort(EffortEvent.ReusedSubtrie); if x.isEmpty then rEmpty else rIdent(BOTH) }
    else if x.isEmpty || prefixes.isEmpty then rEmpty
    else if prefixes.terminal then rIdent(LEFT)        // ε prefixes everything: ALL of x, by pointer
    else
      val ch = mergeRestrict(x.children, prefixes.children)
      if ch.isEmpty then rEmpty                        // a path shorter than the prefix does not start with it
      else
        val l = (ch eq x.children) && !x.terminal      // ε ∈ x has no prefix here (ε ∉ prefixes)
        val r = ch eq prefixes.children                // result terminal (false) == prefixes.terminal
        if l then rIdent(if r then BOTH else LEFT)
        else if r then rIdent(RIGHT)
        else rBespoke(node(false, ch))

  /** raffination `x \| y == x ∖ (x <| y)`: drop every x-path that extends some y-prefix.  FUSED into
   *  a single traversal of the y-guided part of x — the defining
   *  formula walks x twice and materialises the intermediate restriction, which is pure waste when
   *  the answer is `x` itself or `∅`. */
  def raffination(x: ITrie, y: ITrie): ITrie = pick(raffinationR(x, y), x, y)
  def raffinationR(x: ITrie, y: ITrie): AlgebraicResult =
    effort(EffortEvent.TrieNodeVisit)
    if x.isEmpty then rEmpty
    else if x eq y then { effort(EffortEvent.ReusedSubtrie); rEmpty }  // every path prefixes itself
    else if y.isEmpty then rIdent(LEFT)
    else if y.terminal then rEmpty                     // ε prefixes everything: all of x dropped
    else
      val term = x.terminal                            // ε survives: ε ∉ y here
      val ch = mergeRaff(x.children, y.children)
      if ch.isEmpty && !term then rEmpty
      else if ch eq x.children then rIdent(LEFT)
      else rBespoke(node(term, ch))

  /** composition (concatenation product) `{p ++ q : p ∈ a, q ∈ b}`: graft `b` at every terminal of
   *  `a`.  THE GRAFT FRONTIER is `a`'s NODES, not its terminals: the
   *  same `b` object is shared at every graft, but the spine above each graft is rebuilt, so a single
   *  depth-`d` path with ONE terminal still allocates `d` nodes.  The two identities below are what
   *  make the degenerate cases constant time: `a·{ε} == a` and `{ε}·b == b`. */
  def composition(a: ITrie, b: ITrie): ITrie = pick(compositionR(a, b), a, b)
  def compositionR(a: ITrie, b: ITrie): AlgebraicResult =
    effort(EffortEvent.TrieNodeVisit)
    if a.isEmpty || b.isEmpty then rEmpty
    else if b.terminal && b.children.isEmpty then      // a · {ε} == a
      if a.terminal && a.children.isEmpty then rIdent(BOTH) else rIdent(LEFT)
    else if a.terminal && a.children.isEmpty then rIdent(RIGHT)   // {ε} · b == b, CONSTANT TIME
    else
      val mapped = node(false, a.children.transform((_, ac) => composition(ac, b)))
      rBespoke(if a.terminal then union(mapped, b) else mapped)

  // ---- n-ary join-all / meet-all (the asymptotically interesting ones) --------------------------

  /** The non-empty inputs, DEDUPLICATED BY IDENTITY.  Both `joinAll` and `meetAll` are idempotent, so
   *  a repeated operand object is free — and under iteration/fixpoint the same tail-trie is handed in
   *  many times.  Linear identity scan while the operand list is short, an `IdentityHashMap` past
   *  that, so dedup is O(k) rather than O(k²) on a wide loop. */
  /** does `ts` hold an EMPTY operand?  `meetAll`'s pre-scan, counted operand by operand: it
   *  short-circuits on the first empty input (which annihilates the meet), so what it costs is how far
   *  it got and not `k`. */
  private def anyEmptyOperand(ts: IterableOnce[ITrie]): Boolean =
    var n = 0
    var found = false
    val it = ts.iterator
    while it.hasNext && !found do { found = it.next().isEmpty; n += 1 }
    effortN(EffortEvent.NaryOperandProbe, n.toLong)
    found

  private def liveDistinct(ts: IterableOnce[ITrie], dropEmpty: Boolean): mutable.ArrayBuffer[ITrie] =
    // SIZED, not `empty`: `ArrayBuffer.empty` allocates a 16-slot array, and almost every call here has
    // two or three operands — with the scratch storage now counted (EffortEvent.NaryScratchSlot) that
    // constant was the single largest `alloc` term of a small `joinAll`
    val buf = new mutable.ArrayBuffer[ITrie](4)
    var seen: java.util.IdentityHashMap[ITrie, ITrie] = null
    var pr = 0                                         // operand probes, emitted once at the end
    val it = ts.iterator
    while it.hasNext do
      val t = it.next()
      if !dropEmpty || t.nonEmpty then
        var dup = false
        if seen != null then { pr += 1; dup = seen.put(t, t) != null }
        else
          var i = 0
          while i < buf.length && !dup do { if buf(i) eq t then dup = true; i += 1 }
          pr += i
        if dup then effort(EffortEvent.ReusedSubtrie)
        else
          buf += t
          if seen == null && buf.length > 24 then
            seen = new java.util.IdentityHashMap[ITrie, ITrie]()
            effortN(EffortEvent.NaryScratchSlot, 2L * (buf.length + 1))
            buf.foreach(x => seen.put(x, x))
            pr += buf.length
    effortN(EffortEvent.NaryOperandProbe, pr.toLong)
    // THE BUFFER'S OWN STORAGE: 4 slots at construction and, once it has doubled to hold `k` elements,
    // fewer than `4k` slots over the whole doubling series
    effortN(EffortEvent.NaryScratchSlot, math.max(4L, 4L * buf.length))
    buf

  /** join-all: the union of MANY tries in ONE simultaneous pass.
   *
   *  The children step is [[IntTrieOps.joinAllTries]], a simultaneous descent over all `k` children
   *  maps.  It keeps the property the balanced pairwise fold cannot express — a key present in exactly
   *  one input has that input's whole subtrie placed BY POINTER, so `k` head-disjoint tries allocate
   *  one node in total instead of `k-1` — and it no longer pays for that with a linear pass over the
   *  operands' keys.
   *
   *  THAT LINEAR PASS WAS A REAL ASYMPTOTIC DEFECT, not a constant.  The previous implementation
   *  grouped every child of every operand into a `LongMap` of buffers and rebuilt the result map key by
   *  key, i.e. `Θ(Σᵢ fan(mᵢ))` unconditionally — while the pairwise Patricia union it was introduced to
   *  beat answers the decisive wide case in `O(1)`, joining two non-interleaving key ranges at the top
   *  without descending either.  A `TailsUnion` over two 1024-head groups therefore cost 2048 entry
   *  visits where the merge is constant.  Both wins are now in one place: `k == 1` is a pointer,
   *  `k == 2` is the proven pairwise descent, and `k > 2` descends the union of the Patricia trees.
   *
   *  With `-Dmorkl.patriciaOps=false` the group-by-key form below still runs, so the flag keeps
   *  meaning something and the two are directly comparable. */
  def joinAll(ts: IterableOnce[ITrie]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    val live = liveDistinct(ts, dropEmpty = true)
    if live.isEmpty then empty
    else if live.length == 1 then { effort(EffortEvent.SubtrieAcceptedByPointer); live(0) }
    else if live.length == 2 then union(live(0), live(1))
    else
      var term = false
      var i = 0
      while i < live.length do { if live(i).terminal then term = true; i += 1 }
      effortN(EffortEvent.NaryOperandProbe, live.length.toLong)      // the terminal-flag scan
      val ch =
        if Tuning.patriciaOps then
          val maps = new Array[IntMap[ITrie]](live.length)
          effortN(EffortEvent.NaryScratchSlot, live.length.toLong)
          i = 0
          while i < live.length do { maps(i) = live(i).children; i += 1 }
          effortN(EffortEvent.NaryOperandProbe, live.length.toLong)
          IntTrieOps.joinAllTries(maps)
        else
          val groups = mutable.LongMap.empty[mutable.ArrayBuffer[ITrie]]
          i = 0
          while i < live.length do
            live(i).children.foreach { case (k, c) =>
              effort(EffortEvent.PatriciaEntry)
              groups.getOrElseUpdate(k.toLong, mutable.ArrayBuffer.empty) += c }
            i += 1
          var m = IntMap.empty[ITrie]
          groups.foreach { case (k, cs) => m = m.updated(k.toInt, joinAll(cs)) }
          m
      // THE WHOLE JOIN IS ONE OPERAND: its children map came back by pointer and its terminal flag
      // already dominates.  Concluding it here is what lets an absorbed group cost zero allocation.
      var res: ITrie = null
      i = 0
      while i < live.length && (res eq null) do
        if (ch eq live(i).children) && live(i).terminal == term then res = live(i)
        i += 1
      effortN(EffortEvent.NaryOperandProbe, i.toLong)                // the result-identity search
      if res ne null then { effort(EffortEvent.SubtrieAcceptedByPointer); res } else node(term, ch)

  /** meet-all: the intersection of MANY tries.
   *
   *  The children step is [[IntTrieOps.meetAllTries]], a simultaneous descent over all `k` children
   *  maps.  It keeps the property that makes an n-ary meet worth having — the descent follows the
   *  SMALLEST BRANCH AT EVERY LEVEL, so one small operand prunes the others wherever it is missing a
   *  key, which a pairwise fold cannot do because it walks the first two operands' shared structure in
   *  full before the third one is consulted.
   *
   *  WHAT IT FIXES.  The previous children step realised "smallest at every level" by iterating the
   *  smallest node's keys and probing the other `k-1` maps for each — `Θ(fan)` probes, so a meet of two
   *  1024-head nodes whose key ranges do not interleave cost 1024 probes where a Patricia prefix
   *  comparison rejects the pair outright.  Bounding the work by the smallest FAN is not the same as
   *  bounding it by the smallest FRONTIER, and only the frontier is what the descent sees.
   *
   *  The degenerate rounds survive: any empty input annihilates in `O(1)`, one distinct input is
   *  returned by pointer, and a branch with no heads settles from the terminal flags alone.  With
   *  `-Dmorkl.patriciaOps=false` the probe loop below still runs, so the flag keeps meaning something
   *  and the two are directly comparable. */
  def meetAll(ts: scala.collection.Seq[ITrie]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if ts.isEmpty then empty
    else if anyEmptyOperand(ts) then { effort(EffortEvent.SubtrieRejectedByPointer); empty }
    else
      val live = liveDistinct(ts, dropEmpty = false)
      if live.length == 1 then { effort(EffortEvent.SubtrieAcceptedByPointer); live(0) }
      else if live.length == 2 then intersection(live(0), live(1))
      else
        var ti = 0
        while ti < live.length && live(ti).terminal do ti += 1
        val term = ti == live.length
        effortN(EffortEvent.NaryOperandProbe, math.min(ti + 1, live.length).toLong)
        val ch =
          if Tuning.patriciaOps then
            val maps = new Array[IntMap[ITrie]](live.length)
            effortN(EffortEvent.NaryScratchSlot, live.length.toLong)
            var i = 0
            while i < live.length do { maps(i) = live(i).children; i += 1 }
            effortN(EffortEvent.NaryOperandProbe, live.length.toLong)
            IntTrieOps.meetAllTries(maps)
          else
            // the per-key probe loop: iterate the smallest fan, abandon a key on the first input that
            // lacks it.  Correct, and Θ(fan) where the Patricia descent is Θ(frontier).
            var si = 0
            var i = 1
            while i < live.length do
              if live(i).children.size < live(si).children.size then si = i
              i += 1
            val smallest = live(si)
            var m = IntMap.empty[ITrie]
            smallest.children.foreach { case (k, sc) =>
              val cs = mutable.ArrayBuffer.empty[ITrie]
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
                val r = meetAll(cs)
                if r.nonEmpty then m = m.updated(k, r) }
            m
        if ch.isEmpty && !term then empty
        else
          // THE WHOLE MEET IS ONE OPERAND: every other operand contains it, so it is returned by
          // pointer and nothing above this node is rebuilt either.
          var res: ITrie = null
          var i = 0
          while i < live.length && (res eq null) do
            if (ch eq live(i).children) && live(i).terminal == term then res = live(i)
            i += 1
          effortN(EffortEvent.NaryOperandProbe, i.toLong)             // the result-identity search
          if res ne null then { effort(EffortEvent.SubtrieAcceptedByPointer); res } else node(term, ch)

  // ---- prefix operations --------------------------------------------------------------------------

  def wrap(ids: List[Int], s: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if s.isEmpty then empty else ids.foldRight(s)((id, acc) => node(false, IntMap.singleton(id, acc)))
  def unwrap(s: ITrie, ids: List[Int]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    ids match
      case Nil => s
      case h :: t => s.children.get(h).map(unwrap(_, t)).getOrElse(empty)

  /** TailsUnion: drop one head and union the tails = join-all of the child subtries.  ONE head is the
   *  identity — that child subtrie IS the answer, returned by pointer. */
  def tailsUnion(s: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if s.children.isEmpty then empty
    else if s.children.size == 1 then { effort(EffortEvent.SubtrieAcceptedByPointer); s.children.valuesIterator.next() }
    else joinAll(s.children.valuesIterator)
  /** TailsIntersection: tails common to every head = meet-all of the child subtries.  Zero heads is
   *  `∅` and one head is that child, both without touching it. */
  def tailsIntersection(s: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if s.children.isEmpty then empty
    else if s.children.size == 1 then { effort(EffortEvent.SubtrieAcceptedByPointer); s.children.valuesIterator.next() }
    else meetAll(s.children.valuesIterator.toSeq)
  def head(s: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    node(false, s.children.foldLeft(IntMap.empty[ITrie])((m, kv) => m.updated(kv._1, epsilon)))

  /** a left fold for the same reason as [[fromSpaceValue]] */
  def fromPaths(ps: IterableOnce[PathValue]): ITrie = ps.iterator.foldLeft(empty)((t, p) => union(t, singletonP(p)))

  /** All non-empty postfixes of every path (suffix closure), STRUCTURALLY — no path materialization.
   *  Identity: S(t) = (t minus its ε) ∪ ⋃_k S(child_k): the first union is every suffix starting at
   *  position 0 (the non-empty paths themselves), the second every suffix starting deeper.  The union
   *  is the n-ary `joinAll`, not a left fold over the children. */
  def suffixClosure(t: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if t.children.isEmpty then empty
    else
      val parts = mutable.ArrayBuffer.empty[ITrie]
      parts += node(false, t.children)
      t.children.foreach { case (_, c) => parts += suffixClosure(c) }
      joinAll(parts)

  // ---- ordered selection --------------------------------------------------------------------------

  /** Canonical child order (by un-interned [[PathItem]], the order `pathValueOrdering` induces) plus
   *  the running terminal offsets, for [[range]]'s order-statistic slice.  `out(i)` is the `i`-th key
   *  and `out(k + i)` is the number of this node's terminals that PRECEDE child `i`, so child `i`
   *  occupies the index window `[out(k+i), out(k+i+1))` of the node's ordered terminal list.
   *
   *  A BOUNDED identity-keyed memo rather than a field on `ITrie`: `Range` is a rare operator and a
   *  per-node field would grow every trie in the process.  The cap keeps the memo from retaining
   *  arbitrarily many nodes; dropping an entry only costs a re-sort. */
  private val orderMemo: java.util.Map[ITrie, Array[Int]] =
    java.util.Collections.synchronizedMap(new java.util.IdentityHashMap[ITrie, Array[Int]]())
  private def ordered(n: ITrie): Array[Int] =
    val hit = orderMemo.get(n)
    if hit != null then hit
    else
      val ks = n.children.keysIterator.toArray.sortBy(Interner.unintern)
      val k = ks.length
      val out = new Array[Int](2 * k)
      var i = 0
      var acc = if n.terminal then 1 else 0
      while i < k do
        out(i) = ks(i)
        out(k + i) = acc
        acc += n.children(ks(i)).count
        i += 1
      if orderMemo.size > 8192 then orderMemo.clear()
      orderMemo.put(n, out)
      out

  /** the first child index whose terminal window ENDS after `lo` — a binary search on the cached
   *  offsets, so the children entirely before the window are never even looked at */
  private def firstAfter(ord: Array[Int], k: Int, lo: Int): Int =
    if lo <= 0 then 0
    else
      var a = 0
      var b = k - 1
      while a < b do
        val mid = (a + b) >>> 1
        if ord(k + mid + 1) <= lo then a = mid + 1 else b = mid
      a

  /** ORDER-STATISTIC SLICE.  `[lo, hi)` are indices into `n`'s own
   *  canonical terminal list.  A child entirely inside the window is ACCEPTED WHOLE by pointer; a
   *  child entirely outside is REJECTED without being visited; only genuinely partial children are
   *  descended, and only they and the two cut frontiers are rebuilt.  The predecessor enumerated the
   *  window path-by-path and re-`union`ed each one into the result. */
  private def slice(n: ITrie, lo: Int, hi: Int): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if hi <= lo then empty
    else if lo <= 0 && hi >= n.count then { effort(EffortEvent.SubtrieAcceptedByPointer); n }
    else
      val ord = ordered(n)
      val k = ord.length >>> 1
      val term = n.terminal && lo <= 0
      var i = firstAfter(ord, k, lo)
      if i > 0 then effortN(EffortEvent.SubtrieRejectedByPointer, i.toLong)
      var ch = IntMap.empty[ITrie]
      while i < k && ord(k + i) < hi do
        val base = ord(k + i)
        val c = n.children(ord(i))
        val r = slice(c, lo - base, hi - base)
        if r.nonEmpty then ch = ch.updated(ord(i), r)
        i += 1
      if i < k then effortN(EffortEvent.SubtrieRejectedByPointer, (k - i).toLong)
      if ch.isEmpty && !term then empty else node(term, ch)

  /** Native ordered slice `[start, end)` in canonical (`String`) order — NO path materialization.
   *  A FULL window is the identity and costs O(1): the cached [[ITrie.count]] answers the window
   *  test without a walk, and the operand is returned by pointer. */
  def range(t: ITrie, start: Int, end: Int): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    val size = t.count
    val (lo, hi) = RangeBounds.normalize(size, start, end)
    if hi <= lo then empty
    else if lo == 0 && hi == size then { effort(EffortEvent.SubtrieAcceptedByPointer); t }
    else slice(t, lo, hi)

  // ---- convergence ---------------------------------------------------------------------------------

  /** THE FIXPOINT CONVERGENCE TEST.
   *
   *  `nxt == cur` was a full structural `==` walk every round, uninstrumented.  This walks only the
   *  EQUALITY FRONTIER: pointer identity settles a whole subtrie (the common case, because every
   *  operation above propagates identity, so an unchanged branch of an iterate is the SAME object),
   *  the terminal flag and the child-map arity reject in O(1), and an already-computed terminal count
   *  rejects without forcing one.  Each node actually compared counts one
   *  [[EffortEvent.EqualityFrontierVisit]] — accounted separately from `touch` on purpose: it is real
   *  executor work, but folding it into a calibrated component would silently change what every
   *  existing `touch` bound is being compared against (that re-attribution belongs to the review
   *  6, in the cost model). */
  def equalT(a: ITrie, b: ITrie): Boolean =
    effort(EffortEvent.EqualityFrontierVisit)
    if a eq b then { effort(EffortEvent.ReusedSubtrie); true }
    else if a.terminal != b.terminal then false
    else if a.children eq b.children then true
    else
      val ka = a.countIfKnown
      val kb = b.countIfKnown
      if ka >= 0 && kb >= 0 && ka != kb then false
      else a.children.size == b.children.size &&
           a.children.forall { case (k, ac) => b.children.get(k) match
             case Some(bc) => equalT(ac, bc)
             case None => false }

/** Direct evaluator over the interned IntMap-trie.  Mirrors [[evalT]] but on [[ITrie]]; path
 *  constants are interned once (at singleton/wrap construction) and the set operations only
 *  combine interned ints — no [[PathItem]] is touched during evaluation.  Grounded host
 *  functions cross the SpaceValue boundary (and re-intern their outputs there). */
private val iLiteralCache: java.util.Map[SpaceValue, ITrie] =
  java.util.Collections.synchronizedMap(new java.util.IdentityHashMap[SpaceValue, ITrie]())
def iLiteral(sv: SpaceValue): ITrie =
  val hit = iLiteralCache.get(sv); if hit != null then hit else { val t = ITrie.fromSpaceValue(sv); iLiteralCache.put(sv, t); t }

/** The op-graph stores Literal/Constant payloads as serialized STRINGS; a graph executor that
 *  re-decodes (base64 + parse + intern) on every node execution is necessarily slower than `evalI`,
 *  which holds live interned objects.  These process-wide, string-keyed caches decode each distinct
 *  constant exactly once, so `execT` does a single O(1) lookup per node thereafter — the reason
 *  `exec` had no business being slower than `eval`.  Keys are the (stable) serialized strings. */
private val iLiteralStrCache = new java.util.concurrent.ConcurrentHashMap[String, ITrie]()
def iLiteralStr(constant: String): ITrie =
  iLiteralStrCache.computeIfAbsent(constant, c => ITrie.fromSpaceValue(LiteralStore.resolve(c)))
private val iConstStrCache = new java.util.concurrent.ConcurrentHashMap[String, List[Int]]()
def internConstStr(constant: String): List[Int] =
  iConstStrCache.computeIfAbsent(constant, c => Interner.internPath(LiteralCodec.decodeConst(c).items))

/** The three caches' occupancies, for [[GlobalState.probe]].  They are declared `private` at file
 *  scope, so the accessor has to live here; it exists because all three are APPEND-ONLY FOR THE LIFE
 *  OF THE JVM and are therefore candidate explanations for a counted column that moves when another
 *  suite runs first (see GlobalState.scala's header and build.sbt's `testGrouping`).  Reading them
 *  costs one `size` each and mutates nothing. */
def iCacheSizes: (Int, Int, Int) = (iLiteralCache.size, iLiteralStrCache.size, iConstStrCache.size)

def pathItemsI(x: Path)(using pc: PathContext, ic: Map[SpaceMention, ITrie],
                        rc: PartialFunction[RoutinePtr, Routine]): List[Int] =
  effort(EffortEvent.TriePathDispatch)                     // one Path subterm, `Deref` included
  x match
    case Path.Deref(pr) => Interner.internPath(pc.resolve(pr).items)
    case Path.Constant(pi) => Interner.internPath(pi.items)
    case Path.Concat(l, r) => pathItemsI(l) ++ pathItemsI(r)
    case Path.GroundedPP(p, f) => Interner.internPath(f(PathValue(Interner.uninternPath(pathItemsI(p)))).items)
    case Path.GroundedSP(sp, f) => Interner.internPath(f(evalI(sp).toSpaceValue).items)

def evalI(s: Space)(using pc: PathContext = PathContextMap(Map.empty),
                    ic: Map[SpaceMention, ITrie] = Map.empty,
                    rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): ITrie =
  inline def P(x: Path): PathValue = PathValue(Interner.uninternPath(pathItemsI(x)))
  effort(EffortEvent.TrieDispatch)                         // one Space node visited by evalI
  s match
    case Space.Empty => ITrie.empty
    case Space.Mention(v) => ic.getOrElse(v, ITrie.empty)
    case Space.Singleton(p) => ITrie.singleton(pathItemsI(p))
    case Space.Literal(sv) => iLiteral(sv)
    case Space.Union(a, b) => ITrie.union(evalI(a), evalI(b))
    // eager (no subterm short-circuit): both operands are always evaluated, matching the dataflow
    // op-graph executor (execT) so the two are a fair comparison.  The ITrie ops keep their own
    // internal empty fast-paths, so an empty operand is still cheap.
    case Space.Intersection(a, b) => ITrie.intersection(evalI(a), evalI(b))
    case Space.Subtraction(a, b) => ITrie.subtraction(evalI(a), evalI(b))
    case Space.Restriction(a, b) => ITrie.restriction(evalI(a), evalI(b))
    case Space.Raffination(a, b) => ITrie.raffination(evalI(a), evalI(b))
    case Space.Composition(a, b) => ITrie.composition(evalI(a), evalI(b))
    case Space.Wrap(src, p) => ITrie.wrap(pathItemsI(p), evalI(src))
    case Space.Unwrap(src, p) => ITrie.unwrap(evalI(src), pathItemsI(p))
    case Space.TailsUnion(src) => ITrie.tailsUnion(evalI(src))
    case Space.TailsIntersection(src) => ITrie.tailsIntersection(evalI(src))
    case Space.Range(x, lo, hi) => ITrie.range(evalI(x), lo, hi)  // native ordered trie-slice (no path round-trip)
    case Space.GroundedPS(p, f) => ITrie.fromSpaceValue(f(P(p)))
    case Space.GroundedSS(sp, f) => ITrie.fromSpaceValue(f(evalI(sp).toSpaceValue))
    case Space.Iteration(src, symbol, rest, body) =>
      val t = evalI(src)
      // n-ary join over the head groups: one simultaneous pass, and a head whose body result shares
      // no key with the others contributes its subtrie by pointer
      ITrie.joinAll(t.children.iterator.map { case (k, sub) =>
        effort(EffortEvent.LoopBodyEntry)                   // one head-group body entry
        evalI(body)(using pc.grown(Map(symbol -> PathValue(Interner.unintern(k) :: Nil))), ic.updated(rest, sub), rc)
      }.toSeq)
    case Space.Fixpoint(init, rec, body) =>
      var cur = evalI(init)
      var stop = false
      while !stop do
        effort(EffortEvent.FixpointRound)                   // counts the terminating round too
        // `X |-> X u F(X)`, not `F` — MORKL.scala's `eval` Fixpoint arm and
        // terminating/fixpoint_is_lfp.smt2 (O1) carry the argument.
        val nxt = ITrie.union(cur, evalI(body)(using pc, ic.updated(rec, cur), rc))
        // identity-preserving ops make pointer equality the common convergence signal; `equalT`
        // checks it FIRST and then walks only the equality frontier
        if ITrie.equalT(nxt, cur) then stop = true else cur = nxt
      cur
    case Space.Fold(src, initial, acc, symbol, rest, body, update) =>
      val t = evalI(src)
      var accv = PathValue(Interner.uninternPath(pathItemsI(initial)))
      var out = ITrie.empty
      for (k, sub) <- t.children.iterator.toSeq.sortBy((kk, _) => kk) do
        effort(EffortEvent.LoopBodyEntry)
        val pctx = pc.grown(Map(acc -> accv, symbol -> PathValue(Interner.unintern(k) :: Nil)))
        val ictx = ic.updated(rest, sub)
        out = ITrie.union(out, evalI(body)(using pctx, ictx, rc))
        accv = PathValue(Interner.uninternPath(pathItemsI(update)(using pctx, ictx, rc)))
      out
    case Space.Call(rp, refs, mentions) =>
      effort(EffortEvent.CallEntry)                         // one routine call entered
      val refvs = refs.map(P)
      val mentionvs = mentions.map(m => evalI(m))
      val Routine(_, refns, mentionns, body) = rc(rp)
      val pctx = PathContextMap(Map.from(refns.iterator zip refvs.iterator))
      val ictx = Map.from(mentionns.iterator zip mentionvs.iterator)
      body match
        case Space.Union(l, Space.Call(`rp`, `refs`, `mentions`))
          if (refs.iterator zip refvs.iterator).forall((p, pv) => pv == PathValue(Interner.uninternPath(pathItemsI(p)(using pctx, ictx, rc)))) &&
             (mentions.iterator zip mentionvs.iterator).forall((m, tv) => ITrie.equalT(tv, evalI(m)(using pctx, ictx, rc))) =>
          evalI(l)(using pctx, ictx, rc)
        case _ => evalI(body)(using pctx, ictx, rc)
