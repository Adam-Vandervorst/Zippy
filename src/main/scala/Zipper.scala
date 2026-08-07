package morkl

import scala.collection.immutable.IntMap

/** SpaceZipper-based evaluation (a third paradigm beside the interpreters and the op-graph).
 *
 *  A [[SpaceZipper]] is a CURSOR at a focus in a — possibly purely VIRTUAL — interned-int trie.  The three
 *  fundamental movements are all CONSTANT TIME IN THE SPACE SIZE (they touch only the current node's
 *  branching, never re-descending a branch):
 *    - `terminal`   : is the focus path a complete member?
 *    - `children`   : the child sub-zippers keyed by interned item (UNFORCED — cheap wrappers)
 *    - `descend(k)` : the sub-zipper one item down (O(1) per zipper layer; never materializes)
 *
 *  Each space operation has a VIRTUAL zipper that composes its operands' cursors lazily, following the
 *  abstract trie spec — e.g. a Union's child-map is the IntMap union of its operands' child-maps, an
 *  Intersection's is their IntMap intersection.  So an entire routine's set algebra fuses into ONE
 *  zipper tree and ONE traversal: `materialize` is a single DFS that visits each node of the logical
 *  result exactly once, with no intermediate tries (deforestation).  You always lift a concrete trie
 *  into a zipper by `traversal` and drop a zipper back into a trie by `materialize`.
 *
 *  Asymptotics: a `materialize` of a fused expression costs O(sum of operand trie nodes visited) — the
 *  same as the corresponding ITrie ops — but performed in a single fused pass instead of building (and
 *  re-walking) an intermediate trie per operator.  Control-flow / positional ops (Iteration, Fold,
 *  Fixpoint, Range, residuals, Call, grounded) are NOT local trie ops; they are handled by a routine
 *  "call" that materializes via [[evalI]] and is re-lifted by `traversal` (what is materialized vs.
 *  fused can be chosen later; caching can be added later). */
sealed trait SpaceZipper:
  def terminal: Boolean
  def children: IntMap[SpaceZipper]
  def descend(k: Int): SpaceZipper

object SpaceZipper:
  /** The empty space as a zipper (no value at the focus, no children). */
  val empty: SpaceZipper = Lit(ITrie.empty)

  /** Lift a concrete trie into a zipper by traversal — O(1): the trie itself is the cursor. */
  def traversal(t: ITrie): SpaceZipper = Lit(t)

  /** Drop a zipper into a concrete trie by materialization — one DFS, each logical node visited once. */
  def materialize(z: SpaceZipper): ITrie = z match
    case Lit(t) => t                                         // already concrete: no re-traversal
    case _ =>
      effort(EffortEvent.ZipperMaterializeNode)
      effort(EffortEvent.FreshNode)                          // exactly one fresh ITrie per node
      var ch = IntMap.empty[ITrie]
      z.children.foreach { (k, cz) => val c = materialize(cz); if c.nonEmpty then ch = ch.updated(k, c) }
      ITrie(z.terminal, ch)

  // ---- concrete: a cursor over a materialized trie -------------------------------------------------
  final case class Lit(t: ITrie) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); t.terminal }
    def children = { effort(EffortEvent.ZipperCursorRead); t.children.transform((_, c) => Lit(c)) }
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
  final case class Union(a: SpaceZipper, b: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); a.terminal || b.terminal }
    def children = { effort(EffortEvent.ZipperCursorRead); a.children.unionWith(b.children, (_, x, y) => union(x, y)) }
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); union(a.descend(k), b.descend(k)) }

  /** Intersection: value if BOTH have one; children = IntMap intersection (only items common to both). */
  final case class Intersection(a: SpaceZipper, b: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); a.terminal && b.terminal }
    def children = { effort(EffortEvent.ZipperCursorRead); a.children.intersectionWith(b.children, (_, x, y) => intersection(x, y)) }
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); intersection(a.descend(k), b.descend(k)) }

  /** Subtraction: a path is kept iff in `a` and not in `b`.  Keep a's items; subtract b where present.
   *  A shared (eq) sub-branch is instantly pruned to ∅ via `subtraction`, never re-descended. */
  final case class Subtraction(a: SpaceZipper, b: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); a.terminal && !b.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      val bc = b.children
      a.children.transform((k, x) => bc.get(k) match { case Some(y) => subtraction(x, y); case None => x })
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); subtraction(a.descend(k), b.descend(k)) }

  /** Composition (concatenation): a's children each composed with b; if a ends here, splice all of b. */
  final case class Composition(a: SpaceZipper, b: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); a.terminal && b.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      val mapped = a.children.transform((_, x) => Composition(x, b))
      if a.terminal then mapped.unionWith(b.children, (_, x, y) => union(x, y)) else mapped
    def descend(k: Int) =
      effort(EffortEvent.ZipperCursorRead)
      val viaA = Composition(a.descend(k), b)
      if a.terminal then union(viaA, b.descend(k)) else viaA

  /** Wrap: prepend a (constant) prefix to a source.  While in the prefix, the only child is the next
   *  prefix item; once consumed, delegate to the source. */
  final case class Prefix(remaining: List[Int], src: SpaceZipper) extends SpaceZipper:
    def terminal = { effort(EffortEvent.ZipperCursorRead); remaining.isEmpty && src.terminal }
    def children =
      effort(EffortEvent.ZipperCursorRead)
      remaining match
        case Nil => src.children
        case h :: t => IntMap.singleton(h, Prefix(t, src))
    def descend(k: Int) =
      effort(EffortEvent.ZipperCursorRead)
      remaining match
        case Nil => src.descend(k)
        case h :: t => if k == h then Prefix(t, src) else empty

  /** Restriction: keep x-paths that have some `prefixes`-path as a prefix.  Once `prefixes` ends (a
   *  prefix matched) the whole x-subtree is kept; before that, descend only items common to both. */
  def restriction(x: SpaceZipper, prefixes: SpaceZipper): SpaceZipper =
    if prefixes.terminal then x else RestrictionNode(x, prefixes)
  final case class RestrictionNode(x: SpaceZipper, prefixes: SpaceZipper) extends SpaceZipper:
    def terminal = false                                     // no prefix matched yet ⇒ x-value here is not kept
    def children = { effort(EffortEvent.ZipperCursorRead); x.children.intersectionWith(prefixes.children, (_, xc, pc) => restriction(xc, pc)) }
    def descend(k: Int) = { effort(EffortEvent.ZipperCursorRead); restriction(x.descend(k), prefixes.descend(k)) }

  /** Raffination: x \ restriction(x, y). */
  def raffination(x: SpaceZipper, y: SpaceZipper): SpaceZipper = Subtraction(x, restriction(x, y))

  /** TailsUnion: drop the first item of each path and union the tails = the union of all child cursors. */
  final case class TailsUnion(src: SpaceZipper) extends SpaceZipper:
    private lazy val merged: SpaceZipper = { val cs = src.children; if cs.isEmpty then empty else cs.valuesIterator.reduce(Union(_, _)) }
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
