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
  /** number of paths (terminals) in the set */
  def size: Int = (if terminal then 1 else 0) + children.valuesIterator.map(_.size).sum
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

  /** Canonical node constructor: drops empty children so `isEmpty`/`==` stay exact. */
  def node(terminal: Boolean, children: TreeMap[PathItem, Trie]): Trie =
    val pruned = children.filter((_, c) => c.nonEmpty)
    Trie(terminal, pruned)

  def singleton(items: List[PathItem]): Trie = items.foldRight(epsilon)((it, acc) => Trie(false, TreeMap(it -> acc)))
  def singleton(p: PathValue): Trie = singleton(p.items)

  /** All non-empty postfixes of every path, STRUCTURALLY (no path materialization):
   *  S(t) = (t minus its ε) ∪ ⋃_k S(child_k). */
  def suffixClosure(t: Trie): Trie =
    if t.children.isEmpty then empty
    else t.children.foldLeft(Trie(false, t.children): Trie) { case (acc, (_, c)) => union(acc, suffixClosure(c)) }
  /** Native ordered slice `[start, end)` in canonical order — no path materialization.  The TreeMap
   *  children already iterate in `String` order, so we walk in order (prefixes before
   *  extensions), count terminals and emit only those in the window, stopping once it is filled. */
  def range(t: Trie, start: Int, end: Int): Trie =
    val size = t.size
    val (lo, hi) = RangeBounds.normalize(size, start, end)
    if hi <= lo then empty
    else if lo == 0 && hi == size then t
    else
      var idx = 0
      var out = empty
      def go(n: Trie, acc: List[PathItem]): Unit =
        if idx < hi then
          if n.terminal then { if idx >= lo then out = union(out, singleton(acc.reverse)); idx += 1 }
          if idx < hi then
            val it = n.children.iterator
            while it.hasNext && idx < hi do { val (k, c) = it.next(); go(c, k :: acc) }
      go(t, Nil)
      out

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

  // ---- ring of sets ---------------------------------------------------------

  def union(a: Trie, b: Trie): Trie =
    if a.isEmpty then b else if b.isEmpty then a
    else
      var ch = a.children
      for (k, bc) <- b.children do
        ch = ch.updatedWith(k) { case Some(ac) => Some(union(ac, bc)); case None => Some(bc) }
      Trie(a.terminal || b.terminal, ch)

  def intersection(a: Trie, b: Trie): Trie =
    if a.isEmpty || b.isEmpty then empty
    else
      val (small, large) = if a.children.size <= b.children.size then (a, b) else (b, a)
      var ch = TreeMap.empty[PathItem, Trie]
      for (k, sc) <- small.children; lc <- large.children.get(k) do
        val r = intersection(sc, lc); if r.nonEmpty then ch = ch.updated(k, r)
      Trie(a.terminal && b.terminal, ch)

  def subtraction(a: Trie, b: Trie): Trie =
    if a.isEmpty then empty else if b.isEmpty then a
    else
      var ch = a.children
      for (k, ac) <- a.children; bc <- b.children.get(k) do
        val r = subtraction(ac, bc)
        ch = if r.isEmpty then ch - k else ch.updated(k, r)
      Trie(a.terminal && !b.terminal, ch)

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

  /** composition (concatenation product) {p ++ q : p ∈ a, q ∈ b}: graft b at every terminal of
   *  a.  With persistent sharing, each graft reuses the SAME b — O(#terminals of a) new nodes. */
  def composition(a: Trie, b: Trie): Trie =
    if a.isEmpty || b.isEmpty then empty
    else
      val mapped = Trie(false, a.children.map((k, ac) => k -> composition(ac, b)))
      if a.terminal then union(mapped, b) else mapped

  /** restriction x <| prefixes: keep x-paths that start with some path in `prefixes` (keeping
   *  the prefix).  Walk x guided by the prefixes trie; when a prefix ends (`pref.terminal`),
   *  keep the entire x-subtree below. */
  def restriction(x: Trie, prefixes: Trie): Trie =
    if x.isEmpty || prefixes.isEmpty then empty
    else if prefixes.terminal then x
    else
      var ch = TreeMap.empty[PathItem, Trie]
      for (k, xc) <- x.children; pc <- prefixes.children.get(k) do
        val r = restriction(xc, pc); if r.nonEmpty then ch = ch.updated(k, r)
      Trie(false, ch) // a path shorter than the prefix does not start with it

  def raffination(x: Trie, y: Trie): Trie = subtraction(x, restriction(x, y))

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
      var acc = cur
      var stop = false
      while !stop do
        val nxt = evalT(body)(using pc, tc.updated(rec, cur), rc)
        if nxt == cur then stop = true else { acc = Trie.union(acc, nxt); cur = nxt }
      acc
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
