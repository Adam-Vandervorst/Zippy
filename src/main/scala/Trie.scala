package morkl

import scala.collection.immutable.TreeMap
import scala.collection.mutable

/** A persistent path-trie: the trie-native representation of a MORKL space (a set of paths).
 *
 *  The reference [[SpaceValue]] backs a space by `Set[List[PathItem]]` — generic but
 *  sub-optimal, because every MORKL operation is really a structural operation on a trie.
 *  This structure makes those operations native: union/intersection/subtraction are recursive
 *  merges, composition grafts (with structural sharing), wrap/unwrap/restriction walk a spine,
 *  and `iter` reads each child's tail-trie directly instead of re-grouping a flat set.
 *
 *  A node carries `terminal` (does a path END here, i.e. is the empty path present at this
 *  node) and `children` keyed by [[PathItem]] in its natural (`String`) order.  Tries
 *  are immutable and structurally shared; smart construction keeps them canonical (no empty
 *  subtries), so `==` is exact set-equality and node identity enables cheap sharing.
 */
final case class Trie(terminal: Boolean, children: TreeMap[PathItem, Trie]):
  def isEmpty: Boolean = !terminal && children.isEmpty
  def nonEmpty: Boolean = !isEmpty
  /** CACHED TERMINAL COUNT — computed at most once per node object, read in O(1) after.
   *
   *  Same device as [[ITrie.count]] and for the same reason: [[Trie.range]]'s window test and its
   *  order-statistic slice both need the terminal count of a subtrie, and recomputing it by a full
   *  recursive walk at every query made a FULL-window `Range` — the identity — proportional to the
   *  operand.  A plain non-volatile `int`: the write is idempotent and `int` writes do not tear, so a
   *  benign race can only recompute. */
  private var szc: Int = -1
  /** number of paths (terminals) in the set — O(1) once computed */
  def size: Int =
    var s = szc
    if s < 0 then
      s = (if terminal then 1 else 0) + children.valuesIterator.map(_.size).sum
      szc = s
    s
  /** number of trie nodes (a structural-size measure) */
  def nodeCount: Int = 1 + children.valuesIterator.map(_.nodeCount).sum
  def toSpaceValue: SpaceValue = SpaceValue(Trie.toPaths(this))
  def show: String = toSpaceValue.show
  /** number of DISTINCT length-`n` prefixes present (paths of length >= n collapsed to their
   *  first `n` items).  O(nodes above depth n); used e.g. to count n-queens solutions whose
   *  residual paths carry a decorating tail. */
  def prefixCount(n: Int): Int =
    if n == 0 then (if nonEmpty then 1 else 0)
    else children.valuesIterator.map(_.prefixCount(n - 1)).sum

object Trie:
  val empty: Trie = Trie(false, TreeMap.empty)
  /** the singleton set {ε} containing just the empty path */
  val epsilon: Trie = Trie(true, TreeMap.empty)

  def singleton(items: List[PathItem]): Trie = items.foldRight(epsilon)((it, acc) => Trie(false, TreeMap(it -> acc)))
  def singleton(p: PathValue): Trie = singleton(p.items)

  /** All non-empty postfixes of every path, STRUCTURALLY (no path materialization):
   *  S(t) = (t minus its ε) ∪ ⋃_k S(child_k). */
  def suffixClosure(t: Trie): Trie =
    if t.children.isEmpty then empty
    else t.children.foldLeft(Trie(false, t.children): Trie) { case (acc, (_, c)) => union(acc, suffixClosure(c)) }
  /** ORDER-STATISTIC SLICE `[start, end)` in canonical order — no path materialization.
   *
   *  `TreeMap` iterates its children in `String` order, which IS the canonical order
   *  `pathValueOrdering` induces, so — unlike `ITrie`, which has to memoise a canonical order over its
   *  interned integer keys — the offsets can be accumulated on the fly.  A child whose terminal window
   *  lies entirely inside `[lo, hi)` is accepted WHOLE by pointer; a child entirely before or after is
   *  skipped by reading its cached [[Trie.size]] without descending it; only genuinely partial children
   *  are visited, and only they and the two cut frontiers are rebuilt.
   *
   *  This replaces the DEGENERACY documented here previously: a full recursive `size` walk before the
   *  identity check (now O(1) through the cached count) and a window rebuilt path by path through
   *  `singleton` + `union`, which cost `Θ(window · depth)` allocations and re-merged every emitted path
   *  into the accumulator.  `ITrie.range` (IntTrie.scala) is the same algorithm on the interned
   *  representation. */
  def range(t: Trie, start: Int, end: Int): Trie =
    val size = t.size
    val (lo, hi) = RangeBounds.normalize(size, start, end)
    if hi <= lo then empty
    else if lo == 0 && hi == size then t
    else slice(t, lo, hi)

  /** `[lo, hi)` are indices into `n`'s own canonical terminal list */
  private def slice(n: Trie, lo: Int, hi: Int): Trie =
    if hi <= lo then empty
    else if lo <= 0 && hi >= n.size then n                       // whole subtrie, by pointer
    else
      val term = n.terminal && lo <= 0
      var acc = if n.terminal then 1 else 0
      var out = TreeMap.empty[PathItem, Trie]
      val it = n.children.iterator
      while it.hasNext && acc < hi do
        val (k, c) = it.next()
        val cs = c.size
        if acc + cs > lo then                                    // else: entirely before the window
          val r = slice(c, lo - acc, hi - acc)
          if r.nonEmpty then out = out.updated(k, r)
        acc += cs
      if out.isEmpty && !term then empty else Trie(term, out)

  def fromPaths(ps: IterableOnce[PathValue]): Trie =
    ps.iterator.foldLeft(empty)((t, p) => union(t, singleton(p)))
  def fromSpaceValue(sv: SpaceValue): Trie = fromPaths(sv.paths)

  def toPaths(t: Trie): Set[PathValue] =
    val out = Set.newBuilder[PathValue]
    def go(n: Trie, acc: List[PathItem]): Unit =
      if n.terminal then out += PathValue(acc.reverse)
      for (k, c) <- n.children do go(c, k :: acc)
    go(t, Nil); out.result()

  /** paths in the canonical (PathItem-order) lexicographic order; prefixes precede extensions */
  def pathsInOrder(t: Trie): Iterator[PathValue] =
    def go(n: Trie, acc: List[PathItem]): Iterator[PathValue] =
      (if n.terminal then Iterator.single(PathValue(acc.reverse)) else Iterator.empty) ++
        n.children.iterator.flatMap((k, c) => go(c, k :: acc))
    go(t, Nil)

  // ---- algebraic results ------------------------------------------------------

  /** Per-node outcome of a set-algebraic operation, RELATIVE to its arguments — the set-only
   *  analogue of pathmap's `AlgebraicResult<V>` (ring.rs).  A space is a pure SET of paths (no
   *  attached values), so stronger laws hold and the ops below decide these cases at EVERY level
   *  of the trie:
   *
   *    - `Identity(mask)` — the result IS an argument (LEFT bit / RIGHT bit; both bits assert the
   *      arguments denote the same set).  The caller reuses the argument node unchanged: no
   *      allocation, no re-traversal, structural sharing preserved all the way up.
   *    - `Empty` — the result is the empty set; the parent prunes the key instead of storing an
   *      empty child.  Where both `Empty` and `Identity` hold (all arguments empty), `Empty`
   *      takes precedence — the ring.rs convention.
   *    - `Bespoke(t)` — the result genuinely mixes the arguments; a fresh node was built.
   *
   *  Case inventory (all set-equalities below are exact characterizations):
   *    union         Identity(L) ⟺ b ⊆ a;  Identity(R) ⟺ a ⊆ b;  both ⟺ a == b;
   *                  Empty ⟺ both arguments empty;  Bespoke: elements from both sides.
   *    intersection  Identity ⟺ that argument is contained in the other (necessarily the smaller
   *                  one);  Empty ⟺ disjoint (an empty argument is the degenerate case);
   *                  Bespoke: partial overlap.
   *    subtraction   Identity(L) ⟺ a ∩ b == ∅ ("right was empty" is the special case);
   *                  Empty ⟺ a ⊆ b (incl. a empty);  Bespoke: some but not all of a removed.
   *                  Result == right is NOT a case: a\b == b forces b ⊆ a\b, so b == ∅ and then
   *                  a\b == b needs a == ∅ — that is `Empty`.  (ring.rs's non-commutative rule:
   *                  never set the counter bit.)
   *    restriction   Identity(L) ⟺ every left path extends some right prefix (ε ∈ right is the
   *                  degenerate case: everything kept);  Identity(R) ⟺ the result equals right
   *                  as a set — every right path is matched by an EQUAL left path and no longer
   *                  ones;  Empty ⟺ either side empty, or no left path extends any right prefix;
   *                  Bespoke: some left paths kept, some dropped.
   *    raffination   (a \| b == a \ (a <| b), fused into ONE traversal — the definition re-walks
   *                  `a` twice)  Identity(L) ⟺ no left path extends a right prefix;  Empty ⟺
   *                  every left path does (ε ∈ right annihilates);  Bespoke otherwise.
   *    composition   Identity(L) ⟺ b == {ε};  Identity(R) ⟺ a == {ε};  Empty ⟺ either side
   *                  empty.  Exact: a finite non-empty set is never closed under appending a
   *                  non-ε path, so `a·b == a` cannot happen any other way.
   *
   *  Mask completeness: a SET bit is always true.  An UNSET bit is also exact — `Bespoke` really
   *  differs from both arguments — with ONE exception (mirroring ring.rs's allowance): when
   *  restriction short-circuits on ε ∈ right it returns `Identity(LEFT)` without checking whether
   *  left == right, so restriction's RIGHT bit is sound but may under-report.  Tests assert
   *  soundness everywhere and completeness for every other op/bit (see TrieAlgebra). */
  enum AlgebraicResult:
    case Empty
    case Identity(mask: Int)
    case Bespoke(t: Trie)

  object AlgebraicResult:
    inline val LEFT = 1
    inline val RIGHT = 2
    inline val BOTH = 3

  import AlgebraicResult.{LEFT, RIGHT, BOTH}
  private val IdentL = AlgebraicResult.Identity(LEFT)
  private val IdentR = AlgebraicResult.Identity(RIGHT)
  private val IdentB = AlgebraicResult.Identity(BOTH)

  /** Materialize a result against the arguments it is relative to.  `Identity` resolves to the
   *  argument OBJECT (left preferred when both bits are set), keeping sharing exact. */
  private def pick(r: AlgebraicResult, a: Trie, b: Trie): Trie = r match
    case AlgebraicResult.Empty => empty
    case AlgebraicResult.Identity(m) => if (m & LEFT) != 0 then a else b
    case AlgebraicResult.Bespoke(t) => t

  // ---- ring of sets ---------------------------------------------------------
  // Each op is a thin wrapper over its `...R` form, which reports the algebraic case; the `R`
  // forms recurse on themselves so identity/emptiness propagates bottom-up: a node whose children
  // all come back Identity(LEFT) (and whose terminal is unaffected) is itself Identity(LEFT) —
  // the whole subtree is reused with zero allocation.  Child updates are buffered so that the
  // no-change case never touches the TreeMap.

  def union(a: Trie, b: Trie): Trie = pick(unionR(a, b), a, b)
  def unionR(a: Trie, b: Trie): AlgebraicResult =
    if a eq b then (if a.isEmpty then AlgebraicResult.Empty else IdentB)
    else if b.isEmpty then (if a.isEmpty then AlgebraicResult.Empty else IdentL)
    else if a.isEmpty then IdentR
    else
      var allL = a.terminal || !b.terminal      // does b add ε?
      var allR = b.terminal || !a.terminal
      var overlap = 0
      var updates: List[(PathItem, Trie)] = Nil
      for (k, bc) <- b.children do
        a.children.get(k) match
          case None => allL = false; updates = (k -> bc) :: updates
          case Some(ac) =>
            overlap += 1
            unionR(ac, bc) match
              case AlgebraicResult.Identity(m) =>
                if (m & LEFT) == 0 then { allL = false; updates = (k -> bc) :: updates }
                if (m & RIGHT) == 0 then allR = false
              case AlgebraicResult.Bespoke(t) => allL = false; allR = false; updates = (k -> t) :: updates
              case AlgebraicResult.Empty => throw IllegalStateException("union of non-empty children is non-empty")
      if overlap < a.children.size then allR = false    // a has keys b lacks
      if allL then (if allR then IdentB else IdentL)
      else if allR then IdentR
      else
        var ch = a.children
        for (k, t) <- updates do ch = ch.updated(k, t)
        AlgebraicResult.Bespoke(Trie(a.terminal || b.terminal, ch))

  def intersection(a: Trie, b: Trie): Trie = pick(intersectionR(a, b), a, b)
  def intersectionR(a: Trie, b: Trie): AlgebraicResult =
    if a eq b then (if a.isEmpty then AlgebraicResult.Empty else IdentB)
    else if a.isEmpty || b.isEmpty then AlgebraicResult.Empty
    else
      val term = a.terminal && b.terminal
      var allL = a.terminal == term             // a loses ε?
      var allR = b.terminal == term
      val fromA = a.children.size <= b.children.size
      val (small, large) = if fromA then (a, b) else (b, a)
      var kept: List[(PathItem, Trie)] = Nil
      var keptN = 0
      for (k, sc) <- small.children do
        large.children.get(k) match
          case None => ()                       // key dropped; counted via keptN below
          case Some(lc) =>
            val (ac, bc) = if fromA then (sc, lc) else (lc, sc)
            intersectionR(ac, bc) match
              case AlgebraicResult.Empty => allL = false; allR = false
              case AlgebraicResult.Identity(m) =>
                if (m & LEFT) == 0 then allL = false
                if (m & RIGHT) == 0 then allR = false
                kept = (k -> (if (m & LEFT) != 0 then ac else bc)) :: kept; keptN += 1
              case AlgebraicResult.Bespoke(t) => allL = false; allR = false; kept = (k -> t) :: kept; keptN += 1
      if keptN < a.children.size then allL = false
      if keptN < b.children.size then allR = false
      if allL then (if allR then IdentB else IdentL)
      else if allR then IdentR
      else if keptN == 0 && !term then AlgebraicResult.Empty
      else AlgebraicResult.Bespoke(Trie(term, TreeMap.from(kept)))

  def subtraction(a: Trie, b: Trie): Trie = pick(subtractionR(a, b), a, b)
  def subtractionR(a: Trie, b: Trie): AlgebraicResult =
    if a eq b then AlgebraicResult.Empty
    else if a.isEmpty then AlgebraicResult.Empty
    else if b.isEmpty then IdentL
    else
      val term = a.terminal && !b.terminal
      var allL = term == a.terminal             // does b remove ε?
      var removals: List[PathItem] = Nil
      var updates: List[(PathItem, Trie)] = Nil
      for (k, bc) <- b.children do
        a.children.get(k) match
          case None => ()
          case Some(ac) =>
            subtractionR(ac, bc) match
              case AlgebraicResult.Empty => allL = false; removals = k :: removals
              case AlgebraicResult.Identity(_) => ()          // only LEFT is possible
              case AlgebraicResult.Bespoke(t) => allL = false; updates = (k -> t) :: updates
      if allL then IdentL
      else
        var ch = a.children
        for k <- removals do ch = ch - k
        for (k, t) <- updates do ch = ch.updated(k, t)
        if ch.isEmpty && !term then AlgebraicResult.Empty else AlgebraicResult.Bespoke(Trie(term, ch))

  // ---- n-ary join-all / meet-all (the asymptotically interesting ones) ------

  /** join-all: the union of MANY tries in one simultaneous pass.  Children are grouped by key
   *  across all inputs and unified once per key, so the cost is O(total nodes) rather than the
   *  O(k · |result|) of folding pairwise `union` (which re-merges the growing accumulator). */
  def joinAll(ts: IterableOnce[Trie]): Trie =
    val live = ts.iterator.filter(_.nonEmpty).toArray
    if live.isEmpty then empty
    else if live.length == 1 then live(0)
    else
      var term = false
      val groups = mutable.TreeMap.empty[PathItem, mutable.ArrayBuffer[Trie]]
      for t <- live do
        if t.terminal then term = true
        for (k, c) <- t.children do groups.getOrElseUpdate(k, mutable.ArrayBuffer.empty) += c
      var ch = TreeMap.empty[PathItem, Trie]
      for (k, cs) <- groups do ch = ch.updated(k, joinAll(cs))
      Trie(term, ch)

  /** meet-all: the intersection of MANY tries.  A key can survive only if present in EVERY
   *  input, so we iterate the keys of the SMALLEST branch and probe the others; recursion only
   *  descends surviving keys.  Cost is bounded by the smallest branch (× branch count × log),
   *  not by the largest — the non-trivial asymptotic that pairwise `reduce(intersection)`
   *  (bounded by the largest, re-scanning each step) does not achieve. */
  def meetAll(ts: Seq[Trie]): Trie =
    if ts.isEmpty then empty
    else if ts.length == 1 then ts.head
    else if ts.exists(_.isEmpty) then empty
    else
      val term = ts.forall(_.terminal)
      val smallest = ts.minBy(_.children.size)
      val others = ts.filter(_ ne smallest)
      var ch = TreeMap.empty[PathItem, Trie]
      for (k, sc) <- smallest.children do
        val cs = others.flatMap(_.children.get(k))
        if cs.length == others.length then
          val r = meetAll(sc +: cs)
          if r.nonEmpty then ch = ch.updated(k, r)
      Trie(term, ch)

  // ---- prefix operations ----------------------------------------------------

  /** prepend the concrete prefix `items` to every path (a spine ending in `s`) */
  def wrap(items: List[PathItem], s: Trie): Trie =
    if s.isEmpty then empty else items.foldRight(s)((it, acc) => Trie(false, TreeMap(it -> acc)))

  /** strip the known prefix `items`; paths not starting with it are dropped */
  def unwrap(s: Trie, items: List[PathItem]): Trie = items match
    case Nil => s
    case h :: t => s.children.get(h).map(unwrap(_, t)).getOrElse(empty)

  /** composition (concatenation product) {p ++ q : p ∈ a, q ∈ b}: graft b at every terminal of a.
   *
   *  THE GRAFT FRONTIER IS a's NODES, NOT ITS TERMINALS.  The previous claim here — "each graft
   *  reuses the SAME b, so O(#terminals of a) new nodes" — was wrong, and wrong in the direction that
   *  flatters the algorithm.  Sharing `b` is real: the same object is
   *  attached at every graft, so nothing proportional to `N(b)` is ever copied.  But the recursion
   *  rebuilds the SPINE above every graft, so a single depth-`d` path — which has exactly ONE
   *  terminal — allocates `d` fresh nodes.  The correct account is `Theta(N(a))` fresh nodes (every
   *  non-terminal node of `a` is rebuilt by the `children.map`, plus one `union` frontier at each
   *  terminal of `a` where `b` merges into the mapped children).
   *
   *  The degenerate cases are the ones that must not pay that: `a·{ε} == a` and `{ε}·b == b` are
   *  decided by [[compositionR]] before any traversal, in constant time, and `{ε}·b` in particular is
   *  the adversarial case for any size-only cost bound. */
  def composition(a: Trie, b: Trie): Trie = pick(compositionR(a, b), a, b)
  def compositionR(a: Trie, b: Trie): AlgebraicResult =
    if a.isEmpty || b.isEmpty then AlgebraicResult.Empty
    else if b.terminal && b.children.isEmpty then       // a · {ε} == a
      if a.terminal && a.children.isEmpty then IdentB else IdentL
    else if a.terminal && a.children.isEmpty then IdentR // {ε} · b == b
    else
      val mapped = Trie(false, a.children.map((k, ac) => k -> composition(ac, b)))
      AlgebraicResult.Bespoke(if a.terminal then union(mapped, b) else mapped)

  /** restriction x <| prefixes: keep x-paths that start with some path in `prefixes` (keeping
   *  the prefix).  Walk x guided by the prefixes trie; when a prefix ends (`pref.terminal`),
   *  keep the entire x-subtree below. */
  def restriction(x: Trie, prefixes: Trie): Trie = pick(restrictionR(x, prefixes), x, prefixes)
  def restrictionR(x: Trie, prefixes: Trie): AlgebraicResult =
    if x eq prefixes then (if x.isEmpty then AlgebraicResult.Empty else IdentB)  // every path prefixes itself
    else if x.isEmpty || prefixes.isEmpty then AlgebraicResult.Empty
    else if prefixes.terminal then IdentL               // ε prefixes everything: all of x kept
    else
      var allL = !x.terminal                            // ε ∈ x has no prefix here (ε ∉ prefixes)
      var allR = true                                   // result terminal (false) == prefixes.terminal
      var matched = 0
      var kept: List[(PathItem, Trie)] = Nil
      var keptN = 0
      for (k, xc) <- x.children do
        prefixes.children.get(k) match
          case None => allL = false                     // whole x-subtree dropped
          case Some(pc) =>
            matched += 1
            restrictionR(xc, pc) match
              case AlgebraicResult.Empty => allL = false; allR = false
              case AlgebraicResult.Identity(m) =>
                if (m & LEFT) == 0 then allL = false
                if (m & RIGHT) == 0 then allR = false
                kept = (k -> (if (m & LEFT) != 0 then xc else pc)) :: kept; keptN += 1
              case AlgebraicResult.Bespoke(t) => allL = false; allR = false; kept = (k -> t) :: kept; keptN += 1
      if matched < prefixes.children.size then allR = false  // some prefix served nothing at all
      if allL then (if allR then IdentB else IdentL)
      else if allR then IdentR
      else if keptN == 0 then AlgebraicResult.Empty     // nothing prefixed (both sides non-empty)
      else AlgebraicResult.Bespoke(Trie(false, TreeMap.from(kept)))  // a path shorter than the prefix does not start with it

  /** raffination x \| y == x \ (x <| y): drop every x-path that extends some y-prefix.  Fused
   *  into a single traversal of the y-guided part of x — the defining formula walks x twice
   *  (once to build the restriction, once to subtract it). */
  def raffination(x: Trie, y: Trie): Trie = pick(raffinationR(x, y), x, y)
  def raffinationR(x: Trie, y: Trie): AlgebraicResult =
    if x.isEmpty then AlgebraicResult.Empty
    else if x eq y then AlgebraicResult.Empty           // every path prefixes itself
    else if y.isEmpty then IdentL
    else if y.terminal then AlgebraicResult.Empty       // ε prefixes everything: all of x dropped
    else
      val term = x.terminal                             // ε survives: ε ∉ y here
      var allL = true
      var removals: List[PathItem] = Nil
      var updates: List[(PathItem, Trie)] = Nil
      for (k, yc) <- y.children do
        x.children.get(k) match
          case None => ()
          case Some(xc) =>
            raffinationR(xc, yc) match
              case AlgebraicResult.Empty => allL = false; removals = k :: removals
              case AlgebraicResult.Identity(_) => ()    // only LEFT is possible
              case AlgebraicResult.Bespoke(t) => allL = false; updates = (k -> t) :: updates
      if allL then IdentL
      else
        var ch = x.children
        for k <- removals do ch = ch - k
        for (k, t) <- updates do ch = ch.updated(k, t)
        if ch.isEmpty && !term then AlgebraicResult.Empty else AlgebraicResult.Bespoke(Trie(term, ch))

  /** TailsUnion: drop one head and union the tails = join-all of the child subtries. */
  def tailsUnion(s: Trie): Trie = joinAll(s.children.values)
  /** TailsIntersection: tails common to every head = meet-all of the child subtries. */
  def tailsIntersection(s: Trie): Trie = meetAll(s.children.values.toSeq)
  /** Head: the set of first items (each as a length-1 path). */
  def head(s: Trie): Trie = Trie(false, TreeMap.from(s.children.keysIterator.map(k => k -> epsilon)))

  // ---- ordered selection ----------------------------------------------------


/** A read zipper into a trie: a focus node plus the breadcrumb trail back to the root.  This is
 *  the imperative-execution view (cf. PathMap): `descend`/`ascend` are the loop primitives a
 *  RecursiveOpGraph-style backend uses to walk a space without materializing intermediates. */
final case class Zipper(focus: Trie, crumbs: List[Zipper.Crumb]):
  def isTerminal: Boolean = focus.terminal
  def childKeys: Iterable[PathItem] = focus.children.keys
  def descend(k: PathItem): Option[Zipper] =
    focus.children.get(k).map(c => Zipper(c, Zipper.Crumb(k, focus.terminal, focus.children) :: crumbs))
  def ascend: Option[Zipper] = crumbs match
    case Zipper.Crumb(k, pt, pch) :: rest => Some(Zipper(Trie(pt, pch.updated(k, focus)), rest))
    case Nil => None
  def root: Trie = ascend match { case Some(z) => z.root; case None => focus }
  def path: List[PathItem] = crumbs.reverseIterator.map(_.key).toList

object Zipper:
  final case class Crumb(key: PathItem, parentTerminal: Boolean, parentChildren: TreeMap[PathItem, Trie])
  def apply(t: Trie): Zipper = Zipper(t, Nil)

/** Direct evaluator over the optimized trie — the native counterpart of [[eval]].  It mirrors
 *  `eval`'s structure but every operation is a native trie op, and `iter` reads each child's
 *  tail-trie directly (no per-step regrouping of a flat set).  Grounded host functions and the
 *  rare residual/transform operators cross the [[SpaceValue]] boundary; everything else stays
 *  in the trie.  Space mentions resolve through a `Map[SpaceMention, Trie]` context. */
def pathItemsT(x: Path)(using pc: PathContext, tc: Map[SpaceMention, Trie],
                        rc: PartialFunction[RoutinePtr, Routine]): List[PathItem] = x match
  case Path.Deref(pr) => pc.resolve(pr).items
  case Path.Constant(pi) => pi.items
  case Path.Concat(l, r) => pathItemsT(l) ++ pathItemsT(r)
  case Path.GroundedPP(p, f) => f(PathValue(pathItemsT(p))).items
  case Path.GroundedSP(sp, f) => f(evalT(sp).toSpaceValue).items

/** Memoize Literal -> Trie by identity: literal tables (e.g. n-queens add/sub/upto) are stable
 *  `val`s accessed thousands of times; building their trie once amortizes the conversion. */
private val literalTrieCache: java.util.Map[SpaceValue, Trie] =
  java.util.Collections.synchronizedMap(new java.util.IdentityHashMap[SpaceValue, Trie]())
def literalTrie(sv: SpaceValue): Trie =
  val hit = literalTrieCache.get(sv)
  if hit != null then hit else { val t = Trie.fromSpaceValue(sv); literalTrieCache.put(sv, t); t }

def evalT(s: Space)(using pc: PathContext = PathContextMap(Map.empty),
                    tc: Map[SpaceMention, Trie] = Map.empty,
                    rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Trie =
  inline def P(x: Path): PathValue = PathValue(pathItemsT(x))
  s match
    case Space.Empty => Trie.empty
    case Space.Mention(v) => tc.getOrElse(v, Trie.empty)
    case Space.Singleton(p) => Trie.singleton(pathItemsT(p))
    case Space.Literal(sv) => literalTrie(sv)
    case Space.Union(a, b) => Trie.union(evalT(a), evalT(b))
    // short-circuit when the empty operand annihilates the op — avoids evaluating the (often
    // large) other operand of a guarded branch like `(\/(loc /\ b)) x bigExpr` whose guard is
    // empty for all-but-one case.  Sound: ∅ annihilates ∩/·/<|/\||/wrap/unwrap.
    // eager (no subterm short-circuit) — fair vs the dataflow op-graph; ops keep internal empty fast-paths.
    case Space.Intersection(a, b) => Trie.intersection(evalT(a), evalT(b))
    case Space.Subtraction(a, b) => Trie.subtraction(evalT(a), evalT(b))
    case Space.Restriction(a, b) => Trie.restriction(evalT(a), evalT(b))
    case Space.Raffination(a, b) => Trie.raffination(evalT(a), evalT(b))
    case Space.Composition(a, b) => Trie.composition(evalT(a), evalT(b))
    case Space.Wrap(src, p) => Trie.wrap(pathItemsT(p), evalT(src))
    case Space.Unwrap(src, p) => Trie.unwrap(evalT(src), pathItemsT(p))
    case Space.TailsUnion(src) => Trie.tailsUnion(evalT(src))
    case Space.TailsIntersection(src) => Trie.tailsIntersection(evalT(src))
    case Space.Range(x, lo, hi) => Trie.range(evalT(x), lo, hi)  // native ordered trie-slice (no path round-trip)
    case Space.GroundedPS(p, f) => Trie.fromSpaceValue(f(P(p)))
    case Space.GroundedSS(sp, f) => Trie.fromSpaceValue(f(evalT(sp).toSpaceValue))
    case Space.Iteration(src, symbol, rest, body) =>
      val t = evalT(src)
      // native: each child IS the tail-trie for its head — no regrouping of a flat set
      Trie.joinAll(t.children.toSeq.map { (h, sub) =>
        evalT(body)(using pc.grown(Map(symbol -> PathValue(h :: Nil))), tc.updated(rest, sub), rc)
      })
    case Space.Fixpoint(init, rec, body) =>
      var cur = evalT(init)
      var stop = false
      while !stop do
        // `X |-> X u F(X)`, not `F` — MORKL.scala's `eval` Fixpoint arm and
        // terminating/fixpoint_is_lfp.smt2 (O1) carry the argument.
        val nxt = Trie.union(cur, evalT(body)(using pc, tc.updated(rec, cur), rc))
        // identity-preserving ops make `eq` the common convergence signal — check it before
        // the structural comparison
        if (nxt eq cur) || nxt == cur then stop = true else cur = nxt
      cur
    case Space.Fold(src, initial, acc, symbol, rest, body, update) =>
      val t = evalT(src)
      var accv = PathValue(pathItemsT(initial))
      var out = Trie.empty
      for (h, sub) <- t.children.toSeq.sortBy((k, _) => k) do
        val pctx = pc.grown(Map(acc -> accv, symbol -> PathValue(h :: Nil)))
        val tctx = tc.updated(rest, sub)
        out = Trie.union(out, evalT(body)(using pctx, tctx, rc))
        accv = PathValue(pathItemsT(update)(using pctx, tctx, rc))
      out
    case Space.Call(rp, refs, mentions) =>
      val refvs = refs.map(P)
      val mentionvs = mentions.map(m => evalT(m))
      val Routine(_, refns, mentionns, body) = rc(rp)
      val pctx = PathContextMap(Map.from(refns.iterator zip refvs.iterator))
      val tctx = Map.from(mentionns.iterator zip mentionvs.iterator)
      body match
        // fixpoint stabilization: a tail-recursive `l \/ self(args)` whose args are unchanged
        case Space.Union(l, Space.Call(`rp`, `refs`, `mentions`))
          if (refs.iterator zip refvs.iterator).forall((p, pv) => pv == PathValue(pathItemsT(p)(using pctx, tctx, rc))) &&
             (mentions.iterator zip mentionvs.iterator).forall((m, tv) => tv == evalT(m)(using pctx, tctx, rc)) =>
          evalT(l)(using pctx, tctx, rc)
        case _ => evalT(body)(using pctx, tctx, rc)
