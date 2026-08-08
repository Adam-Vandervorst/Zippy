package morkl

import scala.collection.immutable.IntMap

/** SpaceZipper-based evaluation (a third paradigm beside the interpreters and the op-graph).
 *
 *  A [[SpaceZipper]] is a CURSOR at a focus in a — possibly purely VIRTUAL — interned-int trie.  The three
 *  fundamental movements are:
 *    - `terminal`   : is the focus path a complete member?
 *    - `children`   : the child sub-zippers keyed by interned item (the sub-zippers are UNFORCED)
 *    - `descend(k)` : the sub-zipper one item down (never materializes)
 *
 *  WHAT THEY COST.  The previous version of this comment claimed all three are "CONSTANT TIME IN THE
 *  SPACE SIZE ... they touch only the current node's branching".  The second half is the true claim and
 *  the first half does not follow from it — a node's branching is not a constant (review.md item 3):
 *
 *   - `descend(k)` IS cheap: one Patricia probe per zipper layer, and it allocates one virtual cursor
 *     per layer.  O(layers) probes, independent of the space below the focus.
 *   - `terminal` IS cheap: one boolean per layer.  `Prefix.terminal` short-circuits on
 *     `remaining.isEmpty` and never reaches its source; `RestrictionNode.terminal` is a literal `false`
 *     that reads neither operand.
 *   - `children` IS NOT constant time.  `Lit.children` runs `IntMap.transform` over the ENTIRE child
 *     map of the focus node and allocates one wrapper per entry; `Union`/`Intersection`/`Subtraction`/
 *     `Composition`/`RestrictionNode` run a whole `IntMap` `unionWith`/`intersectionWith`/`transform`
 *     over their operands' child maps, which can transform or merge an entire `IntMap`.  The cost is
 *     Θ(child-map entries at the focus) PER LAYER — bounded by the focus node's branching, never by the
 *     space size below it.  That last part is the property worth having, and it is what the comment
 *     should have said.  One [[EffortEvent.ZipperCursorRead]] is counted for a whole map operation, so
 *     SpatialDemand.scala carries the per-ENTRY oracle ([[ZipperDemandEvent]], review.md item 6).
 *
 *  Each space operation has a VIRTUAL zipper that composes its operands' cursors lazily, following the
 *  abstract trie spec — e.g. a Union's child-map is the IntMap union of its operands' child-maps, an
 *  Intersection's is their IntMap intersection.  So an entire routine's set algebra fuses into ONE
 *  zipper tree and ONE traversal, with no intermediate tries (deforestation).  You always lift a
 *  concrete trie into a zipper by `traversal` and drop a zipper back into a trie by `materialize`.
 *
 *  ASYMPTOTICS.  The old claim — "`materialize` visits each node of the logical result exactly once"
 *  and "costs O(sum of operand trie nodes visited)" — is also false, and it is false in the direction
 *  that matters: it is a LINEAR bound on an algorithm that is frequently O(depth) or O(1).  A `Lit`
 *  result is returned BY POINTER and NONE of its nodes are visited.  The real parameter is the number
 *  of FORCED NON-`Lit` CURSOR NODES, and it is decided TOP-DOWN by the outer consumer, not bottom-up by
 *  the operands: a union of two deep tries with disjoint root branches forces ONE node and reuses both
 *  child tries; `Prefix(p, X)` forces `|p| + 1` and reuses `X`'s children; a restriction by a length-`d`
 *  prefix forces `d` and returns the selected subtree wholesale; a composition at a terminal leaf grafts
 *  the existing right cursor.  SpatialDemand.scala computes that number from a demanded-prefix profile
 *  and a layer count, and `ZipperCost` (SpatialCost.scala) now CONSUMES it — but only partly, and the
 *  split is measured (`SpatialScaleCheck`, LIM-1/LIM-2): the demand region reaches `Touch`, whose
 *  prediction is correctly `[0,0]` against a counted 0 on every fused family, and it does NOT reach
 *  `Work`/`Alloc`, which are still the per-operator sum charged in proportion to each operand's
 *  `Meas.nodes` — so `(A ∪ B) ∩ C` with a fixed `C` is still priced as the full inner union (predicted
 *  slope 0.96-1.00 against a measured 0.00, worst error 2053x).  review.md item 3 is closed for one
 *  component and open for two.
 *
 *  Control-flow / positional ops (Iteration, Fold, Fixpoint, Range, residuals, Call, grounded) are NOT
 *  local trie ops; they are handled by a routine "call" that materializes via [[evalI]] and is re-lifted
 *  by `traversal` (what is materialized vs. fused can be chosen later; caching can be added later). */
sealed trait SpaceZipper:
  def terminal: Boolean
  def children: IntMap[SpaceZipper]
  def descend(k: Int): SpaceZipper

object SpaceZipper:
  /** The empty space as a zipper (no value at the focus, no children). */
  val empty: SpaceZipper = Lit(ITrie.empty)

  /** Lift a concrete trie into a zipper by traversal — O(1): the trie itself is the cursor. */
  def traversal(t: ITrie): SpaceZipper = Lit(t)

  /** Drop a zipper into a concrete trie by materialization.
   *
   *  THE COST PARAMETER IS THE NUMBER OF FORCED NON-`Lit` CURSOR NODES, and this DFS is where that set
   *  is generated: a `Lit` cursor is returned BY POINTER — an arbitrarily large trie handed back without
   *  visiting one node of it — so the recursion stops wherever the fused algebra has collapsed to a
   *  concrete cursor.  It is NOT true that every logical result node is visited once.
   *
   *  What the counted events mean here: one [[EffortEvent.ZipperMaterializeNode]] and one
   *  [[EffortEvent.FreshNode]] per FORCED node (never per result node), one
   *  [[ZipperDemandEvent.AcceptedLitSubtrie]] per whole subtrie taken by pointer, and one
   *  [[ZipperDemandEvent.MaterializeEntry]] per child-map entry this loop iterates and rebuilds — the
   *  iteration and the `IntMap.updated` chain that review.md item 6 says nothing counted. */
  def materialize(z: SpaceZipper): ITrie = z match
    case Lit(t) =>
      zdemand(ZipperDemandEvent.AcceptedLitSubtrie)           // whole subtrie by pointer, unvisited
      t                                                      // already concrete: no re-traversal
    case _ =>
      effort(EffortEvent.ZipperMaterializeNode)
      effort(EffortEvent.FreshNode)                          // exactly one fresh ITrie per FORCED node
      var ch = IntMap.empty[ITrie]
      z.children.foreach { (k, cz) =>
        zdemand(ZipperDemandEvent.MaterializeEntry)
        val c = materialize(cz); if c.nonEmpty then ch = ch.updated(k, c) }
      ITrie(z.terminal, ch)

  // ---- concrete: a cursor over a materialized trie -------------------------------------------------
  /** `terminal` and `descend` are per-layer constant work.  `children` is NOT: it rebuilds the focus
   *  node's ENTIRE child map (`IntMap.transform`) and allocates one wrapper per entry, which is why it
   *  emits one [[ZipperDemandEvent.LitTransformEntry]] per entry on top of the single
   *  [[EffortEvent.ZipperCursorRead]] the whole operation has always counted. */
  final case class Lit(t: ITrie) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); t.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      t.children.transform((_, c) => { zdemand(ZipperDemandEvent.LitTransformEntry); Lit(c) })
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); t.children.get(k) match { case Some(c) => Lit(c); case None => empty } }

  // ---- referential-identity short-circuit (O(1)): two cursors are the SAME space when they are the
  // same object, or both are concrete cursors over the same (reference-equal) trie.  This is a pure
  // pointer test — never a structural walk — so it preserves the constant-time movement guarantee. ----
  private def sameSpace(a: SpaceZipper, b: SpaceZipper): Boolean =
    (a eq b) || ((a, b) match { case (Lit(s), Lit(t)) => s eq t; case _ => false })
  /** Union smart constructor: x ∪ x = x — instant accept, no traversal of the shared branch. */
  def union(a: SpaceZipper, b: SpaceZipper): SpaceZipper =
    if sameSpace(a, b) then { effort(EffortEvent.ReusedSpace); a } else Union(a, b)
  /** Intersection smart constructor: x ∩ x = x — instant accept. */
  def intersection(a: SpaceZipper, b: SpaceZipper): SpaceZipper =
    if sameSpace(a, b) then { effort(EffortEvent.ReusedSpace); a } else Intersection(a, b)
  /** Subtraction smart constructor: x \ x = ∅ — instant prune of the whole shared branch. */
  def subtraction(a: SpaceZipper, b: SpaceZipper): SpaceZipper =
    if sameSpace(a, b) then { effort(EffortEvent.ReusedSpace); empty } else Subtraction(a, b)

  // ---- virtual zippers: one per local space operation, composing child cursors per the trie spec ----
  /** Union: value if EITHER has one; children = IntMap union, recursing into shared keys.  Shared (eq)
   *  sub-branches short-circuit through `union`, so a re-occurring branch is accepted, not re-descended. */
  // Every cursor query below counts ONE ZipperCursorRead.  A fused expression therefore counts one
  // read PER LAYER per visited node, which is exactly the work `ZipperCost` has to predict — and the
  // reason a Zipper cost cannot be the same formula as `execT`'s (review.md 2, fourth bullet).
  //
  // THAT ONE READ IS NOT THE WHOLE COST OF A `children` CALL (review.md item 6): the `IntMap` merge
  // below walks the entries of BOTH operand child maps, and a key present in only one side is handed
  // through UNCHANGED — so the fused layer survives only on the PAIRED keys and an unshared branch of a
  // concrete operand is accepted by pointer.  The per-entry counts are in ZipperDemandEvent.
  final case class Union(a: SpaceZipper, b: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); a.terminal || b.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      val ac = a.children; val bc = b.children
      zdemandMerge(ZipperDemandEvent.UnionMergeEntry, ac, bc)
      ac.unionWith(bc, (_, x, y) => { zdemand(ZipperDemandEvent.VirtualCursorAlloc); union(x, y) })
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); union(a.descend(k), b.descend(k)) }

  /** Intersection: value if BOTH have one; children = IntMap intersection (only items common to both).
   *  An unshared key is REJECTED WHOLE — neither side's branch is ever descended, which is what keeps an
   *  outer intersection proportional to its selective operand while the inner expression grows. */
  final case class Intersection(a: SpaceZipper, b: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); a.terminal && b.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      val ac = a.children; val bc = b.children
      zdemandMerge(ZipperDemandEvent.InterMergeEntry, ac, bc)
      ac.intersectionWith(bc, (_, x, y) => { zdemand(ZipperDemandEvent.VirtualCursorAlloc); intersection(x, y) })
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); intersection(a.descend(k), b.descend(k)) }

  /** Subtraction: a path is kept iff in `a` and not in `b`.  Keep a's items; subtract b where present.
   *  A shared (eq) sub-branch is instantly pruned to ∅ via `subtraction`, never re-descended.
   *
   *  A left key MISSING from the right keeps the LEFT CHILD CURSOR UNCHANGED (`case None => x`), so a
   *  left branch the right operand does not mention is accepted whole — by pointer when it is a `Lit`.
   *  The `transform` walks every left entry and probes the right map for it: two child-map entries of
   *  work per left entry, counted as [[ZipperDemandEvent.DiffScanEntry]]. */
  final case class Subtraction(a: SpaceZipper, b: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); a.terminal && !b.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      val bc = b.children
      val ac = a.children
      zdemandN(ZipperDemandEvent.DiffScanEntry, 2L * ac.size.toLong)   // transform + one probe per entry
      ac.transform { (k, x) =>
        bc.get(k) match
          case Some(y) => { zdemand(ZipperDemandEvent.VirtualCursorAlloc); subtraction(x, y) }
          case None => x
      }
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); subtraction(a.descend(k), b.descend(k)) }

  /** Composition (concatenation): a's children each composed with b; if a ends here, splice all of b.
   *
   *  THE GRAFT IS BY POINTER.  At a terminal focus the child map is merged with `b.children` — `b`'s OWN
   *  child cursors — so the right operand is attached, never copied per terminal.  A single deep left
   *  path therefore forces its own spine plus one focus node, and a LEFT EPSILON forces exactly one node
   *  and accepts all of `b`: not `N(a) · N(b)`, which is what `ZipperCost.compose` charges. */
  final case class Composition(a: SpaceZipper, b: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); a.terminal && b.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      val ac = a.children
      zdemandN(ZipperDemandEvent.CompMapEntry, ac.size.toLong)
      val mapped = ac.transform((_, x) => { zdemand(ZipperDemandEvent.VirtualCursorAlloc); Composition(x, b) })
      if a.terminal then
        val bc = b.children
        zdemandMerge(ZipperDemandEvent.CompGraftEntry, mapped, bc)
        mapped.unionWith(bc, (_, x, y) => { zdemand(ZipperDemandEvent.VirtualCursorAlloc); union(x, y) })
      else mapped
    def descend(k: Int) =
      effort(EffortEvent.ZipperCursorRead)
      val viaA = Composition(a.descend(k), b)
      if a.terminal then union(viaA, b.descend(k)) else viaA

  /** Wrap: prepend a (constant) prefix to a source.  While in the prefix, the only child is the next
   *  prefix item; once consumed, delegate to the source.
   *
   *  THE LAYER VANISHES AT THE FOCUS.  `case Nil => src.children` means the focus node's children ARE
   *  the source's own child cursors, so a `Prefix(p, X)` forces the `|p|`-node spine plus ONE focus node
   *  whose child map is copied, and then reuses every one of `X`'s children — not `|p| + 1 + N(X)`
   *  nodes, which is what `ZipperCost.wrap` charges. */
  final case class Prefix(remaining: List[Int], src: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); remaining.isEmpty && src.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      remaining match
        case Nil => src.children
        case h :: t =>
          zdemand(ZipperDemandEvent.PrefixSpineEntry)
          zdemand(ZipperDemandEvent.VirtualCursorAlloc)
          IntMap.singleton(h, Prefix(t, src))
    def descend(k: Int) =
      effort(EffortEvent.ZipperCursorRead)
      remaining match
        case Nil => src.descend(k)
        case h :: t => if k == h then Prefix(t, src) else empty

  /** Restriction: keep x-paths that have some `prefixes`-path as a prefix.  Once `prefixes` ends (a
   *  prefix matched) the whole x-subtree is kept; before that, descend only items common to both.
   *
   *  `restriction` RETURNS `x` ITSELF at a terminal prefix, so restriction by a length-`d` prefix forces
   *  the `d`-node matching frontier and hands the selected subtree back wholesale — by pointer when `x`
   *  is a `Lit` — and restriction by `{ε}` is one `terminal` read with no result node at all.  Note that
   *  `RestrictionNode.terminal` is a literal `false`: it reads neither operand and counts nothing. */
  def restriction(x: SpaceZipper, prefixes: SpaceZipper): SpaceZipper =
    if prefixes.terminal then x else RestrictionNode(x, prefixes)
  final case class RestrictionNode(x: SpaceZipper, prefixes: SpaceZipper) extends SpaceZipper:
    def terminal = false                                     // no prefix matched yet ⇒ x-value here is not kept
    def children =
      effort(EffortEvent.ZipperCursorRead)
      val xc = x.children; val pc = prefixes.children
      zdemandMerge(ZipperDemandEvent.RestrictMergeEntry, xc, pc)
      xc.intersectionWith(pc, (_, xk, pk) => { zdemand(ZipperDemandEvent.VirtualCursorAlloc); restriction(xk, pk) })
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); restriction(x.descend(k), prefixes.descend(k)) }

  /** Raffination: x \ restriction(x, y). */
  def raffination(x: SpaceZipper, y: SpaceZipper): SpaceZipper = Subtraction(x, restriction(x, y))

  /** TailsUnion: drop the first item of each path and union the tails = the union of all child cursors.
   *  `merged` is a lazy val, so the source's child map is read ONCE; the reduce then builds a chain of
   *  `heads - 1` fused `Union` layers, and every later query cascades through the whole chain. */
  final case class TailsUnion(src: SpaceZipper) extends SpaceZipper:
    private lazy val merged: SpaceZipper =
      val cs = src.children
      zdemandN(ZipperDemandEvent.TailsChainEntry, cs.size.toLong)
      zdemandN(ZipperDemandEvent.VirtualCursorAlloc, math.max(cs.size.toLong - 1L, 0L))
      if cs.isEmpty then empty else cs.valuesIterator.reduce(Union(_, _))
    def terminal = { effort(EffortEvent.ZipperCursorRead); merged.terminal }
    def children = { effort(EffortEvent.ZipperCursorRead); merged.children }
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); merged.descend(k) }

  /** TailsIntersection: group by head, intersect tails = the intersection of all PRESENT-head cursors.
   *  Unlike TailsUnion, an *empty* head poisons the intersection, so we must intersect only over heads
   *  that are actually present (non-empty) — which requires the head set.  We therefore materialize the
   *  source here (it inherently needs the present-head set) and reuse the trie-level meet-all. */
  final case class TailsIntersection(src: SpaceZipper) extends SpaceZipper:
    private lazy val merged: SpaceZipper = traversal(ITrie.tailsIntersection(materialize(src)))
    def terminal = { effort(EffortEvent.ZipperCursorRead); merged.terminal }
    def children = { effort(EffortEvent.ZipperCursorRead); merged.children }
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); merged.descend(k) }

  /** Unwrap: strip a (constant) prefix — pure navigation, O(|p|) descents; the resulting cursor IS the
   *  unwrap (no re-traversal, no materialization). */
  def unwrap(src: SpaceZipper, p: List[Int]): SpaceZipper = p.foldLeft(src)((z, k) => z.descend(k))

/** Lift a Space into a fused [[SpaceZipper]] tree.  The LOCAL set-algebra operators become virtual zippers
 *  (one fused traversal); control-flow / positional operators materialize via [[evalI]] (the "call"
 *  mechanism) and are re-lifted with `traversal`. */
def transpileZ(s: Space)(using pc: PathContext, ic: Map[SpaceMention, ITrie], rc: PartialFunction[RoutinePtr, Routine]): SpaceZipper =
  import SpaceZipper.*
  effort(EffortEvent.ZipperBuild)                            // one Space node lifted into a cursor
  s match
    case Space.Empty => SpaceZipper.empty
    case Space.Singleton(p) => traversal(ITrie.singleton(pathItemsI(p)))
    case Space.Literal(sv) => traversal(iLiteral(sv))
    case Space.Mention(m) => traversal(ic.getOrElse(m, ITrie.empty))
    case Space.Union(x, y) => union(transpileZ(x), transpileZ(y))
    case Space.Intersection(x, y) => intersection(transpileZ(x), transpileZ(y))
    case Space.Subtraction(x, y) => subtraction(transpileZ(x), transpileZ(y))
    case Space.Restriction(x, y) => restriction(transpileZ(x), transpileZ(y))
    case Space.Raffination(x, y) => raffination(transpileZ(x), transpileZ(y))
    case Space.Composition(x, y) => Composition(transpileZ(x), transpileZ(y))
    case Space.Wrap(src, p) => Prefix(pathItemsI(p), transpileZ(src))
    case Space.Unwrap(src, p) => unwrap(transpileZ(src), pathItemsI(p))
    case Space.TailsUnion(src) => TailsUnion(transpileZ(src))
    case Space.TailsIntersection(src) => TailsIntersection(transpileZ(src))
    // Range: fuse the source as a zipper, then take the native ordered trie-slice (no path round-trip,
    // no evalI re-evaluation of the source).  The slice is inherently count-based, so it materializes.
    case Space.Range(x, lo, hi) => effort(EffortEvent.TrieOpEntry); traversal(ITrie.range(materialize(transpileZ(x)), lo, hi))
    // Iteration stays on the evalI "call".  Two native forms were tried — a binary `Union` tree of the
    // per-head fused bodies, and a STREAMING n-ary `unionN` (joinAll shape) — and BOTH regress wide
    // sources ~33-40x (royal92 aunt, 3008 heads: ~82 ms vs evalI 2.5 ms).  The combiner is not the cost:
    // it is materializing 3008 per-head fused-algebra bodies node-by-node (the zipper's constant-factor
    // overhead) where evalI uses bulk Patricia ops with empty short-circuits.  With no OUTER operator to
    // prune the bodies, fusion cannot win, so evalI is strictly better here.  (A future win needs either
    // the byte/bit-trie under the symbols, or an outer-pruned Iteration — not a different union combiner.)
    // control-flow / positional / opaque: not local trie ops — a routine "call" materializes via evalI.
    // COUNTED: this is the boundary at which execZ stops being a fused zipper and becomes evalI, so a
    // Zipper cost report that does not expose it is mixing two different executables (review.md 2).
    case other => effort(EffortEvent.ZipperFallbackToEvalI); traversal(evalI(other))

/** SpaceZipper executor: materialize the fused zipper version of the program. */
def execZ(s: Space)(using pc: PathContext = PathContextMap(Map.empty),
                    ic: Map[SpaceMention, ITrie] = Map.empty,
                    rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): ITrie =
  SpaceZipper.materialize(transpileZ(s))
