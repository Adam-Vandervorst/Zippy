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
 *  structural, O(n+m) `unionWith`/`intersectionWith` callbacks directly — they line up exactly
 *  with the algebra (union = merge-with-recursive-union, intersection = merge-with-recursive-
 *  intersection).  Evaluation over [[ITrie]] never touches a [[PathItem]]: it only combines
 *  interned ints; un-interning happens only at the [[toSpaceValue]] boundary. */
final case class ITrie(terminal: Boolean, children: IntMap[ITrie]):
  def isEmpty: Boolean = !terminal && children.isEmpty
  def nonEmpty: Boolean = !isEmpty
  // Every recursive walk below counts ONE EffortEvent.TrieNodeVisit per node it examines.  These are
  // the per-node descents review.md item 1 says were uncounted; `SpatialCost`'s `touch` component is
  // defined by them (plus EffortEvent.PatriciaVisit), which is what makes `touch` calibratable at all.
  def size: Int =
    effort(EffortEvent.TrieNodeVisit)
    (if terminal then 1 else 0) + children.valuesIterator.map(_.size).sum
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
  def fromSpaceValue(sv: SpaceValue): ITrie = sv.paths.foldLeft(empty)((t, p) => union(t, singletonP(p)))

  def toPaths(t: ITrie): Set[PathValue] =
    val out = Set.newBuilder[PathValue]
    def go(n: ITrie, acc: List[Int]): Unit =
      effort(EffortEvent.TrieNodeVisit)
      if n.terminal then out += PathValue(Interner.uninternPath(acc.reverse))
      n.children.foreach { case (k, c) => go(c, k :: acc) }
    go(t, Nil); out.result()

  private def prune(m: IntMap[ITrie]): IntMap[ITrie] =
    m.foldLeft(IntMap.empty[ITrie]) { case (acc, (k, v)) => if v.nonEmpty then acc.updated(k, v) else acc }

  // ---- ring of sets via IntMap callbacks ------------------------------------

  def union(a: ITrie, b: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if a.isEmpty then b else if b.isEmpty then a
    else if Tuning.patriciaOps then
      if a eq b then { effort(EffortEvent.ReusedSubtrie); a }
      else node(a.terminal || b.terminal, IntTrieOps.unionTries(a.children, b.children))
    else node(a.terminal || b.terminal, a.children.unionWith(b.children, (_, x, y) => union(x, y)))

  def intersection(a: ITrie, b: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if a.isEmpty || b.isEmpty then empty
    else if Tuning.patriciaOps then
      if a eq b then { effort(EffortEvent.ReusedSubtrie); a }
      else node(a.terminal && b.terminal, IntTrieOps.intersectTries(a.children, b.children))
    else node(a.terminal && b.terminal, prune(a.children.intersectionWith(b.children, (_, x, y) => intersection(x, y))))

  def subtraction(a: ITrie, b: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if a.isEmpty then empty else if b.isEmpty then a
    else if Tuning.patriciaOps then
      if a eq b then { effort(EffortEvent.ReusedSubtrie); empty }
      else node(a.terminal && !b.terminal, IntTrieOps.diffTries(a.children, b.children))
    else
      var ch = a.children
      b.children.foreach { case (k, bc) => a.children.get(k).foreach { ac =>
        val r = subtraction(ac, bc); ch = if r.isEmpty then ch - k else ch.updated(k, r) } }
      node(a.terminal && !b.terminal, ch)

  // ---- n-ary join-all / meet-all --------------------------------------------

  def joinAll(ts: IterableOnce[ITrie]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    val live = ts.iterator.filter(_.nonEmpty).toArray
    if live.isEmpty then empty else if live.length == 1 then live(0)
    else if Tuning.patriciaOps then
      // balanced pairwise merge over the native Patricia union (eq short-circuits shared sub-tries).
      // Avoids the boxed-Int HashMap + ArrayBuffer regrouping; halves the depth vs a left fold.
      def merge(lo: Int, hi: Int): ITrie =
        if hi - lo == 1 then live(lo) else { val mid = (lo + hi) >>> 1; union(merge(lo, mid), merge(mid, hi)) }
      merge(0, live.length)
    else
      var term = false
      val groups = mutable.HashMap.empty[Int, mutable.ArrayBuffer[ITrie]]
      for t <- live do
        if t.terminal then term = true
        t.children.foreach { case (k, c) => groups.getOrElseUpdate(k, mutable.ArrayBuffer.empty) += c }
      var ch = IntMap.empty[ITrie]
      for (k, cs) <- groups do ch = ch.updated(k, joinAll(cs))
      node(term, ch)

  def meetAll(ts: Seq[ITrie]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if ts.isEmpty then empty else if ts.length == 1 then ts.head else if ts.exists(_.isEmpty) then empty
    else if Tuning.patriciaOps then
      // smallest-first fold over the native Patricia intersection (simultaneous descent + eq
      // short-circuit on shared sub-tries — the common case for the tails of an iterated relation).
      ts.sortBy(_.children.size).reduceLeft(intersection)
    else
      val term = ts.forall(_.terminal)
      val smallest = ts.minBy(_.children.size)
      val others = ts.filter(_ ne smallest)
      var ch = IntMap.empty[ITrie]
      smallest.children.foreach { case (k, sc) =>
        val cs = others.flatMap(_.children.get(k))
        if cs.length == others.length then { val r = meetAll(sc +: cs); if r.nonEmpty then ch = ch.updated(k, r) } }
      node(term, ch)

  // ---- prefix operations ----------------------------------------------------

  def wrap(ids: List[Int], s: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if s.isEmpty then empty else ids.foldRight(s)((id, acc) => node(false, IntMap.singleton(id, acc)))
  def unwrap(s: ITrie, ids: List[Int]): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    ids match
      case Nil => s
      case h :: t => s.children.get(h).map(unwrap(_, t)).getOrElse(empty)

  def composition(a: ITrie, b: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if a.isEmpty || b.isEmpty then empty
    else
      val mapped = node(false, a.children.transform((_, ac) => composition(ac, b)))
      if a.terminal then union(mapped, b) else mapped

  def restriction(x: ITrie, prefixes: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if x.isEmpty || prefixes.isEmpty then empty
    else if prefixes.terminal then x
    else if Tuning.patriciaOps then node(false, IntTrieOps.restrictTries(x.children, prefixes.children))
    else
      var ch = IntMap.empty[ITrie]
      x.children.foreach { case (k, xc) => prefixes.children.get(k).foreach { pc =>
        val r = restriction(xc, pc); if r.nonEmpty then ch = ch.updated(k, r) } }
      node(false, ch)

  def raffination(x: ITrie, y: ITrie): ITrie = subtraction(x, restriction(x, y))
  def tailsUnion(s: ITrie): ITrie = joinAll(s.children.valuesIterator.toSeq)
  def tailsIntersection(s: ITrie): ITrie = meetAll(s.children.valuesIterator.toSeq)
  def head(s: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    node(false, s.children.foldLeft(IntMap.empty[ITrie])((m, kv) => m.updated(kv._1, epsilon)))

  def fromPaths(ps: IterableOnce[PathValue]): ITrie = ps.iterator.foldLeft(empty)((t, p) => union(t, singletonP(p)))

  /** All non-empty postfixes of every path (suffix closure), STRUCTURALLY — no path materialization.
   *  Identity: S(t) = (t minus its ε) ∪ ⋃_k S(child_k): the first union is every suffix starting at
   *  position 0 (the non-empty paths themselves), the second every suffix starting deeper. */
  def suffixClosure(t: ITrie): ITrie =
    effort(EffortEvent.TrieNodeVisit)
    if t.children.isEmpty then empty
    else t.children.foldLeft(node(false, t.children): ITrie) { case (acc, (_, c)) => union(acc, suffixClosure(c)) }
  /** Native ordered slice `[start, end)` in canonical (`String`) order — NO path
   *  materialization.  Walks the trie in canonical order (children sorted by their un-interned item;
   *  prefixes before extensions), counting terminals and emitting only those inside the window, and
   *  stops as soon as the window is filled.  The full-range slice is the identity (returns `t`). */
  def range(t: ITrie, start: Int, end: Int): ITrie =
    val size = t.size
    val (lo, hi) = RangeBounds.normalize(size, start, end)
    if hi <= lo then empty
    else if lo == 0 && hi == size then t
    else
      var idx = 0
      var out = empty
      def go(n: ITrie, acc: List[Int]): Unit =
        effort(EffortEvent.TrieNodeVisit)
        if idx < hi then
          if n.terminal then { if idx >= lo then out = union(out, singleton(acc.reverse)); idx += 1 }
          if idx < hi && n.children.nonEmpty then
            val keys = n.children.keysIterator.toArray.sortBy(Interner.unintern)
            var i = 0
            while i < keys.length && idx < hi do { go(n.children(keys(i)), keys(i) :: acc); i += 1 }
      go(t, Nil)
      out

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
      ITrie.joinAll(t.children.iterator.map { case (k, sub) =>
        effort(EffortEvent.LoopBodyEntry)                   // one head-group body entry
        evalI(body)(using pc.grown(Map(symbol -> PathValue(Interner.unintern(k) :: Nil))), ic.updated(rest, sub), rc)
      }.toSeq)
    case Space.Fixpoint(init, rec, body) =>
      var cur = evalI(init)
      var acc = cur
      var stop = false
      while !stop do
        effort(EffortEvent.FixpointRound)                   // counts the terminating round too
        val nxt = evalI(body)(using pc, ic.updated(rec, cur), rc)
        if nxt == cur then stop = true else { acc = ITrie.union(acc, nxt); cur = nxt }
      acc
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
             (mentions.iterator zip mentionvs.iterator).forall((m, tv) => tv == evalI(m)(using pctx, ictx, rc)) =>
          evalI(l)(using pctx, ictx, rc)
        case _ => evalI(body)(using pctx, ictx, rc)
