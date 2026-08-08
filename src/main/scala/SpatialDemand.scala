package morkl

import scala.collection.immutable.IntMap
import scala.collection.mutable.ArrayBuffer

/** ==============================================================================================
 *  ZIPPER DEMAND ANALYSIS  (review.md item 3, plus the zipper half of item 6)
 *
 *  WHY THIS FILE EXISTS.  `ZipperCost` (SpatialCost.scala) prices each subexpression of a fused
 *  zipper term independently and the traversal ADDS those prices.  That is the wrong semantics for a
 *  lazy fused cursor: a `SpaceZipper` evaluates nothing when it is built, and the OUTER CONSUMER
 *  decides which cursor prefixes are ever forced.  Summing local worst cases therefore charges work
 *  the program provably never does — `(A ∪ B) ∩ C` is charged the full inner union although
 *  `ZipperScaleBench` shows it staying proportional to a fixed `C`.
 *
 *  THE RIGHT PARAMETER.  Not operand nodes, not result nodes, not a sum of per-operator
 *  materialisations, but the number of **FORCED NON-`Lit` CURSOR NODES**: the prefixes at which
 *  `materialize` actually enters a virtual cursor.  Everything else in the answer arrives BY POINTER.
 *  Four quantities follow from that one set, and they are what [[DemandSummary]] reports:
 *
 *    forcedVirtual      — non-`Lit` cursor nodes forced   (= `ZipperMaterializeNode` = `FreshNode`)
 *    acceptedLit        — whole `Lit` subtries taken by pointer, never visited
 *    cursorMapEntries   — child-map ENTRIES the cursor `children` operations actually walk
 *    materializeEntries — child-map entries `materialize` itself iterates and `updated`s
 *
 *  HOW.  Top-down, over a DEMANDED-PREFIX PROFILE and a LAYER COUNT.  The analysis starts with the
 *  root prefix demanded (that is what `materialize` does) and pushes demand DOWNWARD one depth at a
 *  time.  At each depth it holds a frontier of (cursor shape, count) pairs; a step forces one layer
 *  stack, charges the child-map work of every layer in it, and produces the next frontier.  Demand
 *  STOPS at a shape that has collapsed to a `Lit` — that is the accept-by-pointer case, and it is why
 *  the four counterexamples in review.md item 3 come out right:
 *
 *   - a `Union` layer survives only on keys PRESENT IN BOTH operands (`IntMap.unionWith` hands an
 *     unshared key's value through unchanged), so two deep tries with disjoint root branches force
 *     ONE virtual node and accept both child tries whole;
 *   - a `Prefix` layer VANISHES once its prefix is consumed (`children` becomes `src.children`), so
 *     `Prefix(p, X)` forces `|p| + 1` nodes and then accepts `X`'s children;
 *   - `restriction(x, p)` RETURNS `x` as soon as `p` is terminal, so a length-`d` prefix forces `d`
 *     nodes and accepts the selected subtree wholesale;
 *   - `Composition.children` at a terminal `a` splices `b`'s OWN child cursors, so the right operand
 *     is grafted by pointer; a left epsilon forces one node and accepts all of `b`.
 *
 *  NO EVALUATION HAPPENS HERE.  The analysis consumes [[Layers]] (a per-depth structural profile) and
 *  [[Pairing]] (the relational sibling fact review.md item 2 asks for) and returns counts.  It never
 *  constructs a `SpaceZipper`, never calls `children`/`terminal`/`descend`, and never calls
 *  `eval`/`evalI`/`execZ`.  `Layers.ofTrie`/`Pairing.ofTries` are FACT EXTRACTORS for the calibration
 *  harness — the same role `Meas.exact` plays for sizes — and the analysis proper is a combinator over
 *  whatever facts it is handed.
 *
 *  EXACT VS UPPER BOUND.  Every COST count (forced nodes, cursor reads, child-map entries, virtual
 *  allocations) is an upper bound relative to the supplied facts, and all counts are EXACT when the
 *  facts settle every case distinction the executor makes.  `SpatialDemandCheck` asserts both halves:
 *  the bound on 389 random fused programs, and exact equality on the 227 of them whose facts are exact.
 *
 *  Getting the bound right needed BOTH ENDPOINTS of three judgements, which is the part a one-sided
 *  `min(N, N)` ceiling cannot express and where three real under-predictions were found:
 *
 *   - the PAIRED FRONTIER.  A fused layer survives on the paired keys (upper bound wanted), but a
 *     union-style merge returns `na + nb - paired` keys, so the surviving ARITY wants the LOWER bound.
 *     Assuming maximal overlap under-counted everything below it.
 *   - TERMINAL PREFIXES.  `restriction` accepting a subtree, and every `&&`/`||` short circuit in a
 *     `terminal` cascade, turn on whether a node is terminal.  `Layers` is a per-depth AGGREGATE, so
 *     `terms(d) >= 1` means "some node at this depth", never "this one" — [[SpatialDemand]] therefore
 *     carries `terminalCount` and `terminalCountLo` and uses whichever endpoint is sound at each site.
 *   - AN UNDECIDED SMART CONSTRUCTOR.  When the facts cannot say whether `restriction(x, p)` returned
 *     `x` or a `RestrictionNode`, NEITHER branch dominates (a `RestrictionNode` can have a smaller
 *     arity than the `x` it replaced, which makes an enclosing subtraction look cheaper), so both are
 *     carried and both are charged (`Cur.CBoth`).
 *
 *  Where a case split cannot be represented at all — a cross product of operand child shapes that would
 *  outgrow the shape budget — the run is marked `truncated` and STOPS CLAIMING TO BE A BOUND, rather
 *  than returning a number that is not one.
 *
 *  PART 1 of this file is the ORACLE (review.md item 6, zipper half): the per-child-map-ENTRY
 *  instrumentation the existing `EffortEvent` vocabulary is missing, in its own vocabulary and its own
 *  sink so that the four calibrated `EffortComponent`s and their gates are untouched.  PART 2 is the
 *  analysis.  They meet in `SpatialDemandCheck`, which predicts with PART 2 and measures with PART 1. */

// =================================================================================================
// PART 1 — THE ORACLE: per-child-map-ENTRY zipper instrumentation
// =================================================================================================

/** What a [[ZipperDemandEvent]] measures.  Deliberately NOT one of `EffortComponent`'s four: those
 *  are calibrated against `SpatialCost`, and folding a new growing quantity into `Work` would move
 *  every existing zipper containment/tightness number at once.  When `SpatialEvents.scala` is next
 *  open these map onto it as `MapEntries -> Work`, `VirtualAlloc -> Alloc`, `Accepted -> Explain`. */
enum ZipperDemandComponent:
  /** child-map entries an `IntMap` operation inside a cursor actually walks */
  case MapEntries
  /** entries `SpaceZipper.materialize` iterates and rebuilds */
  case MaterializeEntries
  /** whole `Lit` subtries returned by pointer without being visited */
  case Accepted
  /** virtual cursor objects allocated by a `children` combiner */
  case VirtualAlloc

/** One counted unit of ZIPPER child-map work.  Each case names the exact source site that emits it.
 *
 *  These are the counts review.md item 6 says the oracle misses: `Lit.children`,
 *  `Union/Intersection/Subtraction.children` run `IntMap.transform`/`unionWith`/`intersectionWith`
 *  while ONE `ZipperCursorRead` is counted for the WHOLE map operation, and `materialize` iterates and
 *  updates child maps and allocates virtual nodes with nothing counted at all. */
enum ZipperDemandEvent(val component: ZipperDemandComponent, val site: String):
  /** one entry of the `IntMap.transform` in `Lit.children` (which rebuilds the ENTIRE child map) */
  case LitTransformEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "Lit.children")
  /** one child-map entry walked by `Union.children`'s `IntMap.unionWith` (both operand maps) */
  case UnionMergeEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "Union.children")
  /** one child-map entry walked by `Intersection.children`'s `IntMap.intersectionWith` */
  case InterMergeEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "Intersection.children")
  /** one left child-map entry walked by `Subtraction.children` (`transform`, then a probe into `b`) */
  case DiffScanEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "Subtraction.children")
  /** one left child-map entry walked by `Composition.children`'s `transform` */
  case CompMapEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "Composition.children")
  /** one child-map entry walked by the graft `unionWith` at a terminal `Composition` focus */
  case CompGraftEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "Composition.children")
  /** the one-entry `IntMap.singleton` a `Prefix` spine layer builds */
  case PrefixSpineEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "Prefix.children")
  /** one child-map entry walked by `RestrictionNode.children`'s `intersectionWith` */
  case RestrictMergeEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "RestrictionNode.children")
  /** one child cursor folded into a `TailsUnion` merge chain */
  case TailsChainEntry extends ZipperDemandEvent(ZipperDemandComponent.MapEntries, "TailsUnion.merged")
  /** one child-map entry `materialize` iterates (and `updated`s when the child is non-empty) */
  case MaterializeEntry extends ZipperDemandEvent(ZipperDemandComponent.MaterializeEntries, "materialize")
  /** one whole `Lit` subtrie `materialize` returned BY POINTER, without visiting a single node of it */
  case AcceptedLitSubtrie extends ZipperDemandEvent(ZipperDemandComponent.Accepted, "materialize")
  /** ONE COMBINER INVOCATION inside a `children` map operation — i.e. one virtual cursor constructed
   *  (or, when a smart constructor's pointer test fires, deliberately NOT constructed: the invocation is
   *  still the unit of work, and `EffortEvent.ReusedSpace` is what records the short circuit).  `Lit`
   *  wrappers are counted by [[LitTransformEntry]] instead, one per transformed entry. */
  case VirtualCursorAlloc extends ZipperDemandEvent(ZipperDemandComponent.VirtualAlloc, "children")

object ZipperDemandEvent:
  def ofComponent(c: ZipperDemandComponent): Vector[ZipperDemandEvent] =
    values.iterator.filter(_.component == c).toVector

/** A counted vector of zipper child-map work. */
final case class ZipperCounts(counts: Map[ZipperDemandEvent, Long]):
  def apply(e: ZipperDemandEvent): Long = counts.getOrElse(e, 0L)
  def component(c: ZipperDemandComponent): Long =
    ZipperDemandEvent.ofComponent(c).foldLeft(0L)((n, e) => Ivl.add(n, apply(e)))
  def cursorMapEntries: Long = component(ZipperDemandComponent.MapEntries)
  def materializeEntries: Long = component(ZipperDemandComponent.MaterializeEntries)
  def acceptedLit: Long = component(ZipperDemandComponent.Accepted)
  /** virtual cursors allocated.  `Lit.children` allocates exactly one wrapper per transformed entry, so
   *  [[ZipperDemandEvent.LitTransformEntry]] IS that part of the count and is not hooked twice. */
  def virtualAlloc: Long =
    Ivl.add(component(ZipperDemandComponent.VirtualAlloc), apply(ZipperDemandEvent.LitTransformEntry))
  def nonZero: Vector[(ZipperDemandEvent, Long)] = counts.toVector.filter(_._2 != 0L).sortBy(_._1.ordinal)
  def show: String =
    s"cursorMapEntries=$cursorMapEntries materializeEntries=$materializeEntries " +
    s"acceptedLit=$acceptedLit virtualAlloc=$virtualAlloc"
  def showEvents: String = if nonZero.isEmpty then "(none)" else nonZero.map((e, n) => s"$e=$n").mkString(" ")

object ZipperCounts:
  val zero: ZipperCounts = ZipperCounts(Map.empty)

/** The sink.  Same shape and same guarantees as [[EffortSink]] — a plain static boolean plus a
 *  thread-local counter, so a hook compiles to one static load and a not-taken branch when no
 *  counting region is open.  It is SEPARATE from `EffortSink` on purpose: arming one must not perturb
 *  the other's numbers, and `SpatialEventsCheck`'s per-component gates keep reading exactly what they
 *  read before.  The disabled cost is MEASURED in `SpatialDemandCheck`, not asserted. */
object ZipperDemandSink:
  final class Counter:
    private val v = new Array[Long](ZipperDemandEvent.values.length)
    def add(e: ZipperDemandEvent, n: Long): Unit =
      val i = e.ordinal
      v(i) = Ivl.add(v(i), n)
    def snapshot: ZipperCounts =
      ZipperCounts(ZipperDemandEvent.values.iterator.map(e => e -> v(e.ordinal)).filter(_._2 != 0L).toMap)

  /** THE ARMED FLAG — see [[EffortSink.armed]]; `private[morkl]` because every hook site is in
   *  package `morkl` (Zipper.scala), unlike the trie hooks which must be visible from
   *  `scala.collection.immutable`. */
  private[morkl] var armed: Boolean = false
  private val active = new ThreadLocal[Counter]
  private var openRegions: Int = 0

  private[morkl] def record(e: ZipperDemandEvent, n: Long): Unit =
    val c = active.get
    if c != null then c.add(e, n)

  /** Run `body` with zipper counting on for THIS thread and return its counts. */
  def count[A](body: => A): (A, ZipperCounts) =
    val c = new Counter
    val prev = active.get
    active.set(c)
    synchronized { openRegions += 1; armed = true }
    try
      val a = body
      a -> c.snapshot
    finally
      if prev == null then active.remove() else active.set(prev)
      synchronized { openRegions -= 1; if openRegions == 0 then armed = false }

  def counts(body: => Any): ZipperCounts = count(body)._2

/** Emit one zipper child-map event. */
inline def zdemand(inline e: ZipperDemandEvent): Unit =
  if ZipperDemandSink.armed then ZipperDemandSink.record(e, 1L)

/** Emit `n` of one zipper child-map event.  `n` is an INLINE parameter, so an `IntMap.size` passed
 *  here is only computed when the sink is armed. */
inline def zdemandN(inline e: ZipperDemandEvent, inline n: Long): Unit =
  if ZipperDemandSink.armed then ZipperDemandSink.record(e, n)

/** Count the entries of the TWO child maps a Patricia merge walks (`unionWith`/`intersectionWith`).
 *  Both `size` calls are inside the guard, so a disarmed run does not pay for them. */
inline def zdemandMerge(inline e: ZipperDemandEvent, inline a: IntMap[?], inline b: IntMap[?]): Unit =
  if ZipperDemandSink.armed then ZipperDemandSink.record(e, a.size.toLong + b.size.toLong)

// =================================================================================================
// PART 2 — THE ANALYSIS
// =================================================================================================

/** THE PER-DEPTH STRUCTURAL PROFILE of one operand trie — the only thing the demand analysis knows
 *  about a concrete operand.
 *
 *  `nodesAt(d)` is `K_d`, the number of trie nodes at depth `d` (`K_0 = 1` for any non-empty trie);
 *  `termsAt(d)` counts the terminal ones; `maxArityAt(d)` is the largest branching of any node at
 *  depth `d`.  Child-map ENTRIES held by depth-`d` nodes are `K_{d+1}` by definition, which is why
 *  this one vector is enough to price every `children` operation in the zipper.
 *
 *  All three are UPPER bounds; `exact` says the caller knows them as values.  `size · len` (the
 *  `Meas.nodes` fallback) is exactly the information this replaces: a profile keeps the prefix
 *  sharing and the depth structure that a single product throws away. */
final case class Layers(nodesAt: Vector[Long], termsAt: Vector[Long], maxArityAt: Vector[Long],
                        exact: Boolean = true):
  def depth: Int = nodesAt.length - 1
  def nodes(d: Int): Long = if d >= 0 && d < nodesAt.length then nodesAt(d) else 0L
  def terms(d: Int): Long = if d >= 0 && d < termsAt.length then termsAt(d) else 0L
  def maxArity(d: Int): Long = if d >= 0 && d < maxArityAt.length then maxArityAt(d) else 0L
  /** child-map entries held by the depth-`d` layer, i.e. the nodes one level down */
  def entries(d: Int): Long = nodes(d + 1)
  def total: Long = nodesAt.foldLeft(0L)(Ivl.add)
  def isEmpty: Boolean = nodesAt.isEmpty
  def show: String = s"K=${nodesAt.mkString("[", ",", "]")} T=${termsAt.mkString("[", ",", "]")}" +
                     (if exact then "" else " (bound)")

object Layers:
  /** no node at all — `SpaceZipper.empty` is `Lit(ITrie.empty)`, one node with no children */
  val empty: Layers = Layers(Vector(1L), Vector(0L), Vector(0L))
  /** `{ε}` */
  val epsilon: Layers = Layers(Vector(1L), Vector(1L), Vector(0L))
  /** one path of `len` items: one node per depth, terminal only at the bottom */
  def path(len: Int): Layers =
    Layers(Vector.fill(len + 1)(1L),
           Vector.tabulate(len + 1)(d => if d == len then 1L else 0L),
           Vector.tabulate(len + 1)(d => if d == len then 0L else 1L))
  /** A FACT EXTRACTOR for the calibration harness: the exact profile of a concrete operand.
   *  Structural — it reads `terminal`/`children` fields and calls no `ITrie` algebra, so it emits no
   *  effort event and is not an evaluation. */
  def ofTrie(t: ITrie): Layers =
    val nodes = ArrayBuffer.empty[Long]; val terms = ArrayBuffer.empty[Long]; val ar = ArrayBuffer.empty[Long]
    var level: Vector[ITrie] = Vector(t)
    while level.nonEmpty do
      nodes += level.size.toLong
      terms += level.count(_.terminal).toLong
      ar += level.foldLeft(0L)((m, n) => math.max(m, n.children.size.toLong))
      level = level.flatMap(_.children.valuesIterator)
    Layers(nodes.toVector, terms.toVector, ar.toVector)

/** THE RELATIONAL SIBLING FACT for one binary node: how many prefixes at each depth carry a node in
 *  BOTH operands.  This is review.md item 2's "relational frontier" at the zipper level, and it is
 *  what turns `min(N(a), N(b))` into the actual control parameter: a `Union`/`Subtraction` layer only
 *  survives on a PAIRED key, an `Intersection`/`Restriction` only descends into one.
 *
 *  `pairedAt = None` falls back to the `min(K_d(a), K_d(b))` ceiling, which is sound and is all a
 *  unary size/shape domain can give.  `same` is the pointer-identity fact `SpaceZipper.sameSpace`
 *  tests: the smart constructors then return an operand (or `empty`) with no traversal at all. */
final case class Pairing(pairedAt: Option[Vector[Long]], same: Boolean = false, exact: Boolean = true):
  /** the paired frontier at relative depth `d`, never above either side's own arity */
  def paired(d: Int, arityA: Long, arityB: Long): Long =
    val ceiling = math.min(arityA, arityB)
    pairedAt match
      case Some(v) => math.min(if d >= 0 && d < v.length then v(d) else 0L, ceiling)
      case None => ceiling

object Pairing:
  /** no relational knowledge: the `min` ceiling */
  val unknown: Pairing = Pairing(None, false, false)
  /** the two operands are the SAME object (`sameSpace`) */
  val identical: Pairing = Pairing(None, true, true)
  /** the root branches are DISJOINT: the two operands pair at the root and nowhere below it */
  val disjointBelowRoot: Pairing = Pairing(Some(Vector(1L)))
  /** A FACT EXTRACTOR for the calibration harness: the exact paired frontier of two concrete
   *  operands.  A simultaneous structural descent — no algebra, no allocation of results. */
  def ofTries(a: ITrie, b: ITrie): Pairing =
    // POINTER IDENTITY IS A FACT, and it is the one `SpaceZipper.sameSpace` tests: two `Lit` cursors
    // over the same trie object make the smart constructors return an operand (or `∅`) with no
    // traversal at all.  Recording it here is what lets the analysis stay EXACT on `x ∪ x` / `x ∖ x`.
    if a eq b then return Pairing(None, same = true, exact = true)
    val out = ArrayBuffer.empty[Long]
    var level: Vector[(ITrie, ITrie)] = Vector((a, b))
    while level.nonEmpty do
      out += level.size.toLong
      level = level.flatMap { (x, y) =>
        x.children.iterator.flatMap((k, xc) => y.children.get(k).map(yc => (xc, yc))).toVector
      }
    Pairing(Some(out.toVector))

/** THE ZIPPER IR the analysis walks — one case per `SpaceZipper` constructor `transpileZ` can build.
 *
 *  `Lift` is a concrete cursor (`traversal`), which is also what a control-flow / positional subterm
 *  becomes: `transpileZ` materialises `Iteration`/`Fold`/`Fixpoint`/`Range`/`Call`/grounded terms
 *  through `evalI` and re-lifts the result, so from the zipper's point of view they are `Lit`s and
 *  their cost belongs to the TRIE model, not here (`Fallback` records the boundary so the two halves
 *  are never reported as one number). */
enum ZIR:
  case Lift(l: Layers)
  case Fallback(result: Layers)
  case Un(a: ZIR, b: ZIR, rel: Pairing = Pairing.unknown)
  case In(a: ZIR, b: ZIR, rel: Pairing = Pairing.unknown)
  case Diff(a: ZIR, b: ZIR, rel: Pairing = Pairing.unknown)
  case Comp(a: ZIR, b: ZIR)
  case Pre(plen: Int, src: ZIR)
  case Unw(src: ZIR, plen: Int)
  case Res(x: ZIR, prefixes: ZIR, rel: Pairing = Pairing.unknown)
  case Raff(x: ZIR, prefixes: ZIR, rel: Pairing = Pairing.unknown)
  case TailsU(src: ZIR)
  case TailsI(result: Layers)

/** WHAT THE DEMAND ANALYSIS RETURNS.
 *
 *  `forcedVirtual` is THE allocation parameter: `SpaceZipper.materialize` emits exactly one
 *  `ZipperMaterializeNode` and one `FreshNode` per forced non-`Lit` cursor node, and nothing else
 *  allocates a result node.  `acceptedLit` is its complement — the subtries that arrive by pointer.
 *  `demandedAt` is the demanded-prefix profile itself (forced + accepted per depth) and `layersAt` the
 *  layer count at each demanded depth, which is what makes a cursor read count meaningful.
 *
 *  `exact` means every count here IS the measurement, because the supplied facts settled every case
 *  distinction the executor makes.  Otherwise the COST counts (`forcedVirtual`/`freshNodes`,
 *  `cursorReads`, `cursorMapEntries + materializeEntries`, `virtualAlloc`) are upper bounds and
 *  `acceptedLit` is a diagnostic — an accept is good news, so its sound direction is the other one.
 *  `truncated` withdraws even the upper-bound claim: the walk hit a case split it could not represent.
 *  `fallbacks` counts the `evalI` boundaries in the term; the work BEYOND those boundaries is the trie
 *  model's to price and is deliberately not folded in here. */
final case class DemandSummary(forcedVirtual: Long, acceptedLit: Long,
                               cursorReads: Long, cursorMapEntries: Long, materializeEntries: Long,
                               virtualAlloc: Long,
                               demandedAt: Vector[Long], forcedAt: Vector[Long], layersAt: Vector[Long],
                               fallbacks: Long,
                               exact: Boolean, coarsened: Boolean, truncated: Boolean):
  /** fresh materialised `ITrie` nodes — the same set as [[forcedVirtual]], by construction */
  def freshNodes: Long = forcedVirtual
  def depth: Int = demandedAt.length
  def show: String =
    s"forcedVirtual=$forcedVirtual acceptedLit=$acceptedLit cursorReads=$cursorReads " +
    s"cursorMapEntries=$cursorMapEntries materializeEntries=$materializeEntries " +
    s"virtualAlloc=$virtualAlloc fallbacks=$fallbacks" +
    (if exact then " EXACT" else " (upper bound)") +
    (if coarsened then " COARSENED" else "") + (if truncated then " TRUNCATED" else "")
  def showProfile: String =
    s"demanded=${demandedAt.mkString("[", ",", "]")} forced=${forcedAt.mkString("[", ",", "]")} " +
    s"layers=${layersAt.mkString("[", ",", "]")}"

object DemandSummary:
  val zero: DemandSummary =
    DemandSummary(0, 0, 0, 0, 0, 0, Vector.empty, Vector.empty, Vector.empty, 0, true, false, false)

/** THE ANALYSIS.
 *
 *  One `analyze` call runs in a fresh [[SpatialDemand.Run]], so nothing about the walk is shared
 *  between calls or between threads. */
object SpatialDemand:

  /** the maximum result depth the top-down walk descends before declaring the answer truncated */
  val maxDepth: Int = 4096
  /** the maximum number of distinct cursor SHAPES kept on one frontier before the answer is truncated */
  val maxShapes: Int = 64
  /** the longest `TailsUnion` merge chain the analysis expands structurally */
  val maxChain: Int = 64

  // ---- the positioned cursor: a layer stack whose leaves carry their own depth -------------------

  /** A cursor SHAPE at one demanded frontier.  Every leaf carries its own depth into its own operand,
   *  because the fused operators do NOT all descend in lockstep: `Composition` restarts its right
   *  operand at the root at every terminal graft, and `Prefix` holds its source at the root while the
   *  prefix is being consumed. */
  private enum Cur:
    /** A concrete cursor over depth `d` of `l` — the ACCEPT-BY-POINTER case when it is the top.
     *
     *  `linear` says the demanded prefixes map INJECTIVELY onto this operand's nodes, which is true of
     *  every lockstep operator (the prefix `u` reads the operand's node at `u`, once) and FALSE of a
     *  `Composition`'s right operand: the same right cursor is re-read at EVERY terminal graft, so its
     *  child map is transformed once per graft and the `K_{d+1}` ceiling does not apply. */
    case CLit(l: Layers, d: Int, linear: Boolean = true)
    case CUn(a: Cur, b: Cur, rel: Pairing, k: Int)
    case CIn(a: Cur, b: Cur, rel: Pairing, k: Int)
    case CDiff(a: Cur, b: Cur, rel: Pairing, k: Int)
    /** `b` is the right cursor AT ITS OWN ROOT: the same object is grafted at every terminal of `a` */
    case CComp(a: Cur, b: Cur)
    case CPre(rem: Int, src: Cur)
    case CRes(x: Cur, p: Cur, rel: Pairing, k: Int)
    /** a virtual node that delegates every query to an inner cursor (`TailsUnion`/`TailsIntersection`) */
    case CDelegate(inner: Cur)
    /** THE UNDECIDED SMART CONSTRUCTOR.  `restriction(x, p)` returns `x` when `p` is terminal and a
     *  `RestrictionNode` otherwise; when the facts cannot settle which, BOTH shapes are carried and BOTH
     *  are charged.  Taking the "pessimistic" branch alone is NOT sound: a `RestrictionNode` can have a
     *  SMALLER arity than the `x` it would have been replaced by, which makes an enclosing subtraction
     *  look cheaper than it is (caught by the random soundness check, seed 46). */
    case CBoth(a: Cur, b: Cur)
  import Cur.*

  /** the number of virtual layers in a stack — 0 for a concrete cursor */
  private def layerCount(c: Cur): Long = c match
    case CLit(_, _, _) => 0L
    case CUn(a, b, _, _) => 1L + layerCount(a) + layerCount(b)
    case CIn(a, b, _, _) => 1L + layerCount(a) + layerCount(b)
    case CDiff(a, b, _, _) => 1L + layerCount(a) + layerCount(b)
    case CComp(a, b) => 1L + layerCount(a) + layerCount(b)
    case CPre(_, src) => 1L + layerCount(src)
    case CRes(x, p, _, _) => 1L + layerCount(x) + layerCount(p)
    case CDelegate(inner) => 1L + layerCount(inner)
    case CBoth(a, b) => math.max(layerCount(a), layerCount(b))

  /** are ALL facts in this stack exact?  This drives the ONE place where the upper and the lower bound
   *  disagree: accepting a restricted subtree needs a LOWER bound on terminal prefixes. */
  private def exactAll(c: Cur): Boolean = c match
    case CLit(l, _, _) => l.exact
    case CUn(a, b, r, _) => r.exact && exactAll(a) && exactAll(b)
    case CIn(a, b, r, _) => r.exact && exactAll(a) && exactAll(b)
    case CDiff(a, b, r, _) => r.exact && exactAll(a) && exactAll(b)
    case CComp(a, b) => exactAll(a) && exactAll(b)
    case CPre(_, src) => exactAll(src)
    case CRes(x, p, r, _) => r.exact && exactAll(x) && exactAll(p)
    case CDelegate(inner) => exactAll(inner)
    case CBoth(_, _) => false

  /** UPPER bound on how many of `n` demanded prefixes have `terminal = true` at this cursor.  A
   *  `Prefix` with items left and a `RestrictionNode` are structurally never terminal: the code returns
   *  a literal `false` without reading either operand. */
  private def terminalCount(c: Cur, n: Long): Long = c match
    case CLit(l, d, _) => math.min(n, l.terms(d))
    case CUn(a, b, _, _) => math.min(n, Ivl.add(terminalCount(a, n), terminalCount(b, n)))
    case CIn(a, b, _, _) => math.min(terminalCount(a, n), terminalCount(b, n))
    case CDiff(a, _, _, _) => terminalCount(a, n)
    case CComp(a, _) => math.min(terminalCount(a, n), n)
    case CPre(rem, src) => if rem > 0 then 0L else terminalCount(src, n)
    case CRes(_, _, _, _) => 0L
    case CDelegate(inner) => terminalCount(inner, n)
    case CBoth(a, b) => math.max(terminalCount(a, n), terminalCount(b, n))

  /** A LOWER bound on how many of `n` demanded prefixes are terminal here.
   *
   *  This is NOT `terminalCount` with the inequality flipped, and the difference is a real soundness
   *  trap: `Layers` is an AGGREGATE per depth, so `terms(d) >= 1` says "some depth-`d` node is terminal",
   *  never "THIS one is".  A cursor that arrived by `Unwrap`/`descend` sits at one specific node, and
   *  concluding it is terminal from the layer total made `restriction` accept a subtree the run really
   *  descended into (caught by the random soundness check, seed 165).  A depth-`d` node is PROVABLY
   *  terminal only when every node at that depth is. */
  private def terminalCountLo(c: Cur, n: Long): Long = c match
    case CLit(l, d, _) =>
      // `l.exact` is what rules out a cursor that arrived by `descend`: it may be sitting on NO node at
      // all (a missing key yields `SpaceZipper.empty`), in which case "every node at this depth is
      // terminal" says nothing about it.
      if l.exact && l.nodes(d) > 0L && l.terms(d) >= l.nodes(d) then math.min(n, l.nodes(d)) else 0L
    case CUn(a, b, _, _) => math.max(terminalCountLo(a, n), terminalCountLo(b, n))
    case CIn(a, b, _, _) => Ivl.relu(terminalCountLo(a, n) + terminalCountLo(b, n) - n)
    case CDiff(a, b, _, _) => Ivl.relu(terminalCountLo(a, n) - terminalCount(b, n))
    case CComp(a, b) => Ivl.relu(terminalCountLo(a, n) + terminalCountLo(b, n) - n)
    case CPre(rem, src) => if rem > 0 then 0L else terminalCountLo(src, n)
    case CRes(_, _, _, _) => 0L
    case CDelegate(inner) => terminalCountLo(inner, n)
    case CBoth(_, _) => 0L

  /** The `ZipperCursorRead`s the `terminal` query costs over `n` prefixes at this stack, honouring the
   *  `&&`/`||` SHORT CIRCUITS the code really has:
   *
   *   - `RestrictionNode.terminal` is a literal `false` — no hook, no operand read: 0.
   *   - `Prefix.terminal` short-circuits on `remaining.isEmpty` and never reaches its source while the
   *     prefix is unconsumed.
   *   - `Intersection`/`Subtraction`/`Composition` read the RIGHT operand only where the left one is
   *     terminal, so the right side is charged `terminalCount(left)` times, not `n`.
   *   - `Union` is `a.terminal || b.terminal`, so `b` is read where `a` is NOT terminal.  Bounding that
   *     by `n` needs no lower bound on terminals and stays an upper bound. */
  private def termReads(c: Cur, n: Long): Long = c match
    case CLit(_, _, _) => n
    // `a.terminal || b.terminal` reads `b` only where `a` is NOT terminal, which needs a LOWER bound on
    // a's terminals ([[terminalCountLo]]) — exact where the facts settle it, conceded as `n` otherwise.
    case CUn(a, b, _, _) => n + termReads(a, n) + termReads(b, n - terminalCountLo(a, n))
    case CIn(a, b, _, _) => n + termReads(a, n) + termReads(b, terminalCount(a, n))
    case CDiff(a, b, _, _) => n + termReads(a, n) + termReads(b, terminalCount(a, n))
    case CComp(a, b) => n + termReads(a, n) + termReads(b, terminalCount(a, n))
    case CPre(rem, src) => if rem > 0 then n else n + termReads(src, n)
    case CRes(_, _, _, _) => 0L
    case CDelegate(inner) => n + termReads(inner, n)
    case CBoth(a, b) => termReads(a, n) + termReads(b, n)

  /** `min(n · per, cap)` without overflowing */
  private def capMul(n: Long, per: Long, cap: Long): Long =
    if n <= 0L || per <= 0L || cap <= 0L then 0L
    else if n > cap || per > cap then cap
    else math.min(n * per, cap)

  private def kid(c: Cur, n: Long): Vector[(Cur, Long)] = if n <= 0L then Vector.empty else Vector((c, n))

  /** Mark a whole cursor stack as RE-READ AT MANY PREFIXES.  Applied to a `Composition`'s right operand,
   *  which is grafted at every terminal of the left one, so its `children` cost is paid per graft. */
  private def delinearize(c: Cur): Cur = c match
    case CLit(l, d, _) => CLit(l, d, false)
    case CUn(a, b, r, k) => CUn(delinearize(a), delinearize(b), r, k)
    case CIn(a, b, r, k) => CIn(delinearize(a), delinearize(b), r, k)
    case CDiff(a, b, r, k) => CDiff(delinearize(a), delinearize(b), r, k)
    case CComp(a, b) => CComp(delinearize(a), delinearize(b))
    case CPre(rem, src) => CPre(rem, delinearize(src))
    case CRes(x, p, r, k) => CRes(delinearize(x), delinearize(p), r, k)
    case CDelegate(i) => CDelegate(delinearize(i))
    case CBoth(a, b) => CBoth(delinearize(a), delinearize(b))

  /** The AGGREGATE cost of forcing `children` on `n` prefixes that share one cursor shape, plus the
   *  next frontier.  `kids` counts KEYS, and its counts sum to the arity of the child map the cursor
   *  returns — which is exactly what `materialize` then iterates and rebuilds. */
  private final case class Step(reads: Long, entries: Long, alloc: Long, kids: Vector[(Cur, Long)]):
    def arity: Long = kids.foldLeft(0L)((s, kv) => Ivl.add(s, kv._2))

  /** the cursor `transpileZ` builds, plus the work it does WHILE BUILDING it (the `restriction`
   *  terminal probe, `Unwrap`'s descents, `TailsUnion`'s source read) */
  private final case class Build(cur: Cur, reads: Long, entries: Long, alloc: Long, fallbacks: Long)

  // ---- one analysis run --------------------------------------------------------------------------

  private final class Run:
    var coarsened: Boolean = false
    var truncated: Boolean = false
    /** set by EVERY inexact fact the walk consumes.  `exactAll` on the final cursor is not enough: a
     *  smart constructor can drop a subterm from the cursor AFTER its facts have shaped the answer (a
     *  `TailsUnion` whose source turns out to have no children keeps no trace of the union below it),
     *  and a pointer-identity short circuit the facts did not record is an over-count, not an exact
     *  answer. */
    var inexact: Boolean = false
    def note(l: Layers): Layers = { if !l.exact then inexact = true; l }
    def note(r: Pairing): Pairing = { if !r.exact then inexact = true; r }

    /** Distribute a paired frontier of `shared` keys over the two operands' child shapes.
     *
     *  With ONE shape per side — the ordinary case, since every lockstep operator produces one — this is
     *  EXACT: `s` keys carry the fused shape and the remainders carry the operands' own shapes.
     *
     *  With several shapes per side the true assignment of the paired keys is unknown, and picking one
     *  assignment is NOT sound in either direction: a fused pair can be dearer than an unpaired shape
     *  (so dropping it under-counts) while a shape that survives unpaired can keep an enclosing layer
     *  alive (so dropping THAT under-counts too — this is what the random soundness check found at seed
     *  46, where a `RestrictionNode` right operand with no children made a subtraction look as if its
     *  layer had died).  So every combination is charged, and the run is marked `coarsened`. */
    def pairKids(ka: Vector[(Cur, Long)], kb: Vector[(Cur, Long)], sharedHi: Long, sharedLo: Long,
                 comb: (Cur, Cur) => Cur, keepA: Boolean, keepB: Boolean): Vector[(Cur, Long)] =
      if ka.isEmpty || kb.isEmpty || sharedHi <= 0L then
        (if keepA then ka else Vector.empty) ++ (if keepB then kb else Vector.empty)
      else if ka.length == 1 && kb.length == 1 then
        val (ca, na) = ka.head; val (cb, nb) = kb.head
        // BOTH DIRECTIONS OF THE PAIRED FRONTIER ARE NEEDED, which is the subtlety a single `min(N,N)`
        // ceiling cannot express: the FUSED shape count wants the UPPER bound on the overlap, while the
        // keys that survive UNPAIRED want the LOWER bound — a union-style merge returns `na + nb - shared`
        // keys, so assuming maximal overlap would UNDER-count the resulting arity (and with it every
        // count below).  With no relational fact the lower bound is 0 and both operands' children are
        // charged in full.
        val s = math.min(sharedHi, math.min(na, nb))
        val sl = math.min(sharedLo, math.min(na, nb))
        kid(comb(ca, cb), s) ++
          (if keepA && na - sl > 0L then Vector((ca, na - sl)) else Vector.empty) ++
          (if keepB && nb - sl > 0L then Vector((cb, nb - sl)) else Vector.empty)
      else if ka.length * kb.length > maxShapes then
        // The cross product would outgrow the shape budget.  There is no sound way to pick a subset
        // (see above), so the run is TRUNCATED: it stops claiming to be a bound rather than quietly
        // returning a number that is not one.
        truncated = true
        (if keepA then ka else Vector.empty) ++ (if keepB then kb else Vector.empty)
      else
        coarsened = true
        val paired = for (ca, na) <- ka; (cb, nb) <- kb
                     yield (comb(ca, cb), math.min(sharedHi, math.min(na, nb)))
        paired.filter(_._2 > 0L) ++
          (if keepA then ka else Vector.empty) ++ (if keepB then kb else Vector.empty)

    /** the LOWER endpoint of the paired frontier: the fact itself when it is exact, 0 otherwise */
    def sharedLoOf(rel: Pairing, shared: Long): Long = if rel.exact then shared else 0L

    def force(c: Cur, n: Long): Step = if truncated then Step(0, 0, 0, Vector.empty) else c match
      // `Lit.children` REBUILDS THE WHOLE CHILD MAP (`IntMap.transform`, one `Lit` per entry).  This is
      // the growing work review.md item 6 says one `ZipperCursorRead` was standing in for.
      case CLit(l, d, lin) =>
        val e = if lin then capMul(math.min(n, l.nodes(d)), l.maxArity(d), l.entries(d))
                else Ivl.mul(n, l.maxArity(d))
        Step(n, e, e, kid(CLit(l, d + 1, lin), e))  // one `children` read per prefix, even off the end

      // Union: `unionWith` walks BOTH child maps, and a key present in only ONE side keeps that side's
      // child cursor UNCHANGED — so the Union layer survives only on the PAIRED frontier and an
      // unshared branch of a concrete operand is accepted by pointer.
      case CUn(a, b, rel, k) =>
        val sa = force(a, n); val sb = force(b, n)
        val shared = rel.paired(k + 1, sa.arity, sb.arity)
        Step(n + sa.reads + sb.reads,
             Ivl.add(Ivl.add(sa.entries, sb.entries), Ivl.add(sa.arity, sb.arity)),
             Ivl.add(Ivl.add(sa.alloc, sb.alloc), shared),
             pairKids(sa.kids, sb.kids, shared, sharedLoOf(rel, shared),
                      (x, y) => CUn(x, y, rel, k + 1), true, true))

      // Intersection: only the paired frontier survives at all — an unshared branch is REJECTED whole.
      // This is what keeps an outer intersection proportional to its selective operand while the inner
      // union grows (ZipperScaleBench's (A ∪ B) ∩ C).
      case CIn(a, b, rel, k) =>
        val sa = force(a, n); val sb = force(b, n)
        val shared = rel.paired(k + 1, sa.arity, sb.arity)
        Step(n + sa.reads + sb.reads,
             Ivl.add(Ivl.add(sa.entries, sb.entries), Ivl.add(sa.arity, sb.arity)),
             Ivl.add(Ivl.add(sa.alloc, sb.alloc), shared),
             pairKids(sa.kids, sb.kids, shared, sharedLoOf(rel, shared),
                      (x, y) => CIn(x, y, rel, k + 1), false, false))

      // Subtraction: `a.children.transform` walks every left entry and probes `b`'s map for it (2 per
      // left entry).  A left key MISSING from the right keeps the left child cursor unchanged — the
      // "missing right branch returns the whole left subtree" identity.
      case CDiff(a, b, rel, k) =>
        val sa = force(a, n); val sb = force(b, n)
        val shared = rel.paired(k + 1, sa.arity, sb.arity)
        Step(n + sa.reads + sb.reads,
             Ivl.add(Ivl.add(sa.entries, sb.entries), Ivl.add(sa.arity, sa.arity)),
             Ivl.add(Ivl.add(sa.alloc, sb.alloc), shared),
             pairKids(sa.kids, sb.kids, shared, sharedLoOf(rel, shared),
                      (x, y) => CDiff(x, y, rel, k + 1), true, false))

      // Composition: one wrapper per left entry, and AT A TERMINAL LEFT FOCUS the right cursor's OWN
      // children are spliced in — the right operand is GRAFTED BY POINTER, not copied per terminal.
      // A left epsilon has no entries to map, so it forces one node and accepts all of `b`.
      case CComp(a, b) =>
        val sa = force(a, n)
        val t = terminalCount(a, n)
        // `children` itself asks `a.terminal`, which CASCADES through a's whole layer stack — not one
        // read.  Charging `n` here under-predicted the cursor reads of a composition over a fused left
        // operand (caught by the random soundness check).
        val aTerm = termReads(a, n)
        val viaA: Vector[(Cur, Long)] = sa.kids.map((c, m) => (CComp(c, b): Cur, m))
        if t <= 0L then
          Step(n + sa.reads + aTerm, Ivl.add(sa.entries, sa.arity), Ivl.add(sa.alloc, sa.arity), viaA)
        else
          val sb = force(b, t)
          // how many of `a`'s child keys collide with `b`'s root keys is a relational fact nobody
          // supplies for a composition, so the graft is an upper bound and the run says so
          val shared = math.min(sa.arity, sb.arity)
          if shared > 0L then inexact = true
          Step(n + sa.reads + aTerm + sb.reads,
               Ivl.add(Ivl.add(sa.entries, sa.arity), Ivl.add(sb.entries, Ivl.add(sa.arity, sb.arity))),
               Ivl.add(Ivl.add(sa.alloc, sa.arity), Ivl.add(sb.alloc, shared)),
               pairKids(viaA, sb.kids, shared, 0L, (x, y) => CUn(x, y, Pairing.unknown, 0), true, true))

      // Prefix: while items remain the child map is a ONE-ENTRY singleton, so the spine is |p| forced
      // nodes.  Once the prefix is consumed the layer VANISHES — `children` IS `src.children` — so the
      // focus node copies exactly one child map and everything below it is the source's own cursor.
      case CPre(rem, src) =>
        if rem > 0 then Step(n, n, n, kid(CPre(rem - 1, src), n))
        else { val s = force(src, n); Step(n + s.reads, s.entries, s.alloc, s.kids) }

      // Restriction: `intersectionWith` walks both maps, and `restriction(xc, pc)` RETURNS `xc` as soon
      // as the prefix side is terminal.  So the forced frontier is the paired NON-TERMINAL frontier and
      // the selected subtree is accepted wholesale.  With inexact facts we cannot LOWER-bound the
      // terminal prefixes, so we assume none and keep the forced count an upper bound.
      case CRes(x, p, rel, k) =>
        val sx = force(x, n); val sp = force(p, n)
        val shared = rel.paired(k + 1, sx.arity, sp.arity)
        // Keys whose PREFIX child is terminal accept the x-child wholesale.  BOTH endpoints of that
        // count are needed: the number of accepts is bounded ABOVE by `pTermHi` (that is what is
        // reported), while the number of surviving `RestrictionNode`s — the part that COSTS — is bounded
        // above by `shared - pTermLo`.  Where the facts settle it the two coincide and the answer is
        // exact; where they do not, both shapes are charged and neither branch is silently preferred.
        val pTermHi = sp.kids.foldLeft(0L)((s, kv) => Ivl.add(s, terminalCount(kv._1, kv._2)))
        val pTermLo = sp.kids.foldLeft(0L)((s, kv) => Ivl.add(s, terminalCountLo(kv._1, kv._2)))
        val tShared = math.min(shared, pTermHi)
        val resShared = shared - math.min(shared, pTermLo)
        if tShared > 0L && sx.kids.length > 1 then coarsened = true
        val accepted = if tShared > 0L then sx.kids.headOption.map((cx, _) => (cx, tShared)).toVector
                       else Vector.empty
        // the `restriction` combiner reads `prefixes.terminal` once per shared key, and that query
        // cascades through the prefix child's own layer stack
        val probeUnit = sp.kids.foldLeft(1L)((mx, kv) => math.max(mx, termReads(kv._1, 1L)))
        Step(n + sx.reads + sp.reads + Ivl.mul(shared, probeUnit),
             Ivl.add(Ivl.add(sx.entries, sp.entries), Ivl.add(sx.arity, sp.arity)),
             Ivl.add(Ivl.add(sx.alloc, sp.alloc), shared),
             accepted ++ pairKids(sx.kids, sp.kids, resShared, sharedLoOf(rel, resShared),
                                  (a2, b2) => CRes(a2, b2, rel, k + 1), false, false))

      // A delegating virtual node (`TailsUnion`, `TailsIntersection`): one forced node at the top, then
      // the inner cursor's children — the layer does not repeat below it.
      case CDelegate(inner) =>
        val s = force(inner, n)
        Step(n + s.reads, s.entries, s.alloc, s.kids)

      // both possible shapes are charged, and both kid sets go on the next frontier
      case CBoth(a, b) =>
        val sa = force(a, n); val sb = force(b, n)
        Step(sa.reads + sb.reads, Ivl.add(sa.entries, sb.entries), Ivl.add(sa.alloc, sb.alloc),
             sa.kids ++ sb.kids)

    def descend1(c: Cur): (Cur, Long, Long) = c match
      // A DESCENT MAY LAND NOWHERE: `Lit.descend` on a missing key returns `SpaceZipper.empty`, so the
      // per-depth profile no longer describes THIS cursor's node and its facts stop being exact.
      case CLit(l, d, lin) => (CLit(l.copy(exact = false), d + 1, lin), 1L, 0L)
      case CUn(a, b, rel, k) =>
        val (a2, ra, aa) = descend1(a); val (b2, rb, ab) = descend1(b)
        (CUn(a2, b2, rel, k + 1), 1L + ra + rb, 1L + aa + ab)
      case CIn(a, b, rel, k) =>
        val (a2, ra, aa) = descend1(a); val (b2, rb, ab) = descend1(b)
        (CIn(a2, b2, rel, k + 1), 1L + ra + rb, 1L + aa + ab)
      case CDiff(a, b, rel, k) =>
        val (a2, ra, aa) = descend1(a); val (b2, rb, ab) = descend1(b)
        (CDiff(a2, b2, rel, k + 1), 1L + ra + rb, 1L + aa + ab)
      // `Composition.descend` reads `a.terminal` (cascading), and where `a` may be terminal it unions in
      // `b.descend(k)` — so the cursor one item down is a fused Union, not another bare Composition
      case CComp(a, b) =>
        val (a2, ra, aa) = descend1(a)
        val own = 1L + ra + termReads(a, 1L)
        if terminalCount(a, 1L) <= 0L then (CComp(a2, b), own, 1L + aa)
        else
          val (b2, rb, ab) = descend1(b)
          (CUn(CComp(a2, b), b2, Pairing.unknown, 0), own + rb, 2L + aa + ab)
      case CPre(rem, src) =>
        if rem > 0 then (CPre(rem - 1, src), 1L, 0L) else { val (s, r, a) = descend1(src); (s, 1L + r, a) }
      case CRes(x, p, rel, k) =>
        val (x2, rx, ax) = descend1(x); val (p2, rp, ap) = descend1(p)
        (CRes(x2, p2, rel, k + 1), 1L + rx + rp + termReads(p2, 1L), 1L + ax + ap)
      case CDelegate(inner) => val (i2, r, a) = descend1(inner); (i2, 1L + r, a)
      case CBoth(a, b) =>
        val (a2, ra, aa) = descend1(a); val (b2, rb, ab) = descend1(b)
        (CBoth(a2, b2), ra + rb, aa + ab)

    def descend(c: Cur, times: Int): (Cur, Long, Long) =
      var cur = c; var reads = 0L; var alloc = 0L; var i = 0
      while i < times do
        val (c2, r, a) = descend1(cur)
        cur = c2; reads += r; alloc += a; i += 1
      (cur, reads, alloc)

    def join(c: Cur, a: Build, b: Build): Build =
      Build(c, a.reads + b.reads, a.entries + b.entries, a.alloc + b.alloc, a.fallbacks + b.fallbacks)

    def build(z: ZIR): Build = z match
      case ZIR.Lift(l) => Build(CLit(note(l), 0, true), 0, 0, 0, 0)
      // `transpileZ` materialises a control-flow / positional subterm through `evalI` and re-lifts the
      // RESULT, so the fused expression sees a `Lit`.  Its `evalI` cost belongs to the trie model; the
      // boundary is reported separately so the two halves are never one number (review.md item 3).
      case ZIR.Fallback(r) => Build(CLit(note(r), 0, true), 0, 0, 0, 1)
      case ZIR.Un(x, y, rel0) =>
        val rel = note(rel0)
        val bx = build(x); val by = build(y)
        if rel.same then join(bx.cur, bx, by) else join(CUn(bx.cur, by.cur, rel, 0), bx, by)
      case ZIR.In(x, y, rel0) =>
        val rel = note(rel0)
        val bx = build(x); val by = build(y)
        if rel.same then join(bx.cur, bx, by) else join(CIn(bx.cur, by.cur, rel, 0), bx, by)
      case ZIR.Diff(x, y, rel0) =>
        val rel = note(rel0)
        val bx = build(x); val by = build(y)
        // x ∖ x = ∅: the whole shared branch is pruned by a pointer test, with no traversal at all
        if rel.same then join(CLit(Layers.empty, 0, true), bx, by)
        else join(CDiff(bx.cur, by.cur, rel, 0), bx, by)
      case ZIR.Comp(x, y) =>
        val bx = build(x); val by = build(y)
        join(CComp(bx.cur, delinearize(by.cur)), bx, by)
      case ZIR.Pre(plen, s) => val b = build(s); b.copy(cur = CPre(plen, b.cur))
      case ZIR.Unw(s, plen) =>
        val b = build(s)
        if plen > 0 then inexact = true              // see `descend1`: the facts stop being per-node
        val (c, r, a) = descend(b.cur, plen)
        Build(c, b.reads + r, b.entries, b.alloc + a, b.fallbacks)
      case ZIR.Res(x, p, rel0) =>
        val rel = note(rel0)
        val bx = build(x); val bp = build(p)
        // `SpaceZipper.restriction` reads `prefixes.terminal` BEFORE building a node, and RETURNS `x`
        // when it is already terminal — restriction by `{ε}` costs one read and allocates nothing.
        val cur =
          if terminalCountLo(bp.cur, 1L) >= 1L then bx.cur                    // `{ε}`-style: x itself
          else if terminalCount(bp.cur, 1L) >= 1L then CBoth(bx.cur, CRes(bx.cur, bp.cur, rel, 0))
          else CRes(bx.cur, bp.cur, rel, 0)
        Build(cur, bx.reads + bp.reads + termReads(bp.cur, 1L), bx.entries + bp.entries,
              bx.alloc + bp.alloc, bx.fallbacks + bp.fallbacks)
      case ZIR.Raff(x, p, rel0) =>
        // `raffination(x, y) = Subtraction(x, restriction(x, y))` — the LEFT operand is lifted TWICE
        val rel = note(rel0)
        val bx = build(x); val br = build(ZIR.Res(x, p, rel))
        Build(CDiff(bx.cur, br.cur, Pairing.unknown, 0), bx.reads + br.reads, bx.entries + br.entries,
              bx.alloc + br.alloc, bx.fallbacks + br.fallbacks)
      case ZIR.TailsU(s) =>
        // `merged` is a lazy val: ONE source `children` read, then a chain of `arity - 1` fused Union
        // layers, so one query at the top cascades through the whole chain.
        val b = build(s)
        val st = force(b.cur, 1L)
        val parts = st.arity
        if parts > maxChain then truncated = true
        val shapes = st.kids.map(_._1)
        val chain =
          if parts <= 0L || shapes.isEmpty then CLit(Layers.empty, 0, true)
          else
            var acc: Cur = shapes.head
            var i = 1L
            while i < math.min(parts, maxChain.toLong) do
              acc = CUn(acc, shapes(((i % shapes.length.toLong).toInt)), Pairing.unknown, 0); i += 1
            acc
        // `st.entries` is the source's own `children` cost; the reduce then folds every one of the
        // `parts` child cursors (one `TailsChainEntry` each) and allocates `parts - 1` Union layers.
        Build(CDelegate(chain), b.reads + st.reads, Ivl.add(Ivl.add(b.entries, st.entries), parts),
              b.alloc + st.alloc + math.max(parts - 1L, 0L), b.fallbacks)
      case ZIR.TailsI(r0) =>
        val r = note(r0)
        // TailsIntersection MATERIALISES its source (it needs the present-head set) and re-lifts the
        // trie-level meet-all, so it is a fallback boundary with one delegating node on top of a `Lit`.
        Build(CDelegate(CLit(r, 0, true)), 0, 0, 0, 1)

    /** THE TOP-DOWN DRIVER.
     *
     *  The root prefix is demanded because that is exactly what `SpaceZipper.materialize` does; demand
     *  then flows only to the child keys each forced layer's `children` actually produces.  A frontier
     *  entry whose shape has collapsed to a concrete cursor is ACCEPTED and never descended — that is
     *  the accept-by-pointer case, and it is the whole difference from a summed local worst case. */
    def run(z: ZIR): DemandSummary =
      val b = build(z)
      var forced = 0L; var accepted = 0L
      var reads = b.reads; var entries = b.entries; var matEntries = 0L; var alloc = b.alloc
      val demandedAt = ArrayBuffer.empty[Long]; val forcedAt = ArrayBuffer.empty[Long]
      val layersAt = ArrayBuffer.empty[Long]
      var frontier: Vector[(Cur, Long)] = Vector((b.cur, 1L))
      var d = 0
      while frontier.nonEmpty && d < maxDepth && !truncated do
        demandedAt += frontier.foldLeft(0L)((s, kv) => Ivl.add(s, kv._2))
        var fHere = 0L; var lHere = 0L
        val next = ArrayBuffer.empty[(Cur, Long)]
        // an undecided smart constructor is expanded here, so a concrete branch is ACCEPTED and a
        // virtual branch is FORCED, and the answer bounds whichever one the run really took
        val expanded = frontier.flatMap {
          case (CBoth(a, b), n) => Vector((a, n), (b, n))
          case other => Vector(other)
        }
        for (c, n) <- expanded do
          c match
            case CLit(_, _, _) => accepted = Ivl.add(accepted, n)   // the whole subtrie arrives by pointer
            case _ =>
              forced = Ivl.add(forced, n); fHere = Ivl.add(fHere, n)
              lHere = math.max(lHere, layerCount(c))
              reads = Ivl.add(reads, termReads(c, n))
              val s = force(c, n)
              reads = Ivl.add(reads, s.reads)
              entries = Ivl.add(entries, s.entries)
              matEntries = Ivl.add(matEntries, s.arity)          // materialize iterates the child map
              alloc = Ivl.add(alloc, s.alloc)
              next ++= s.kids
        forcedAt += fHere; layersAt += lHere
        // merge equal shapes so the frontier stays a PROFILE rather than a path enumeration
        val merged = next.groupBy(_._1).iterator
          .map((c, vs) => (c, vs.foldLeft(0L)((s, kv) => Ivl.add(s, kv._2)))).toVector
        if merged.length > maxShapes then truncated = true
        frontier = merged
        d += 1
      if frontier.nonEmpty then truncated = true
      DemandSummary(forced, accepted, reads, entries, matEntries, alloc,
                    demandedAt.toVector, forcedAt.toVector, layersAt.toVector, b.fallbacks,
                    exactAll(b.cur) && !inexact && !coarsened && !truncated, coarsened, truncated)
  end Run

  /** Analyse a fused zipper term top-down. */
  def analyze(z: ZIR): DemandSummary = new Run().run(z)

  // ---- lifting a Space term into the IR ---------------------------------------------------------

  /** the subterms `transpileZ` does NOT fuse: it materialises them through `evalI` and re-lifts the
   *  result with `traversal`, so the fused expression sees a `Lit` and the boundary is counted */
  def isFallback(s: Space): Boolean = s match
    case Space.Iteration(_, _, _, _) | Space.Fold(_, _, _, _, _, _, _) | Space.Fixpoint(_, _, _) |
         Space.Call(_, _, _) | Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => true
    case _ => false

  /** Lift a `Space` into the zipper IR, mirroring `transpileZ` constructor for constructor.
   *
   *  APPLY THIS TO THE OPTIMIZED BODY (`Routine.optimized`), not the definitional one: a cost estimate
   *  should describe the program that actually runs.  `leaf` supplies the profile of each subterm
   *  `transpileZ` turns into a concrete cursor — `Mention`, `Literal`, `Singleton`, `Range`, and every
   *  control-flow term.  `rel` supplies the relational sibling fact for a binary node; the default
   *  `Pairing.unknown` is the plain `min(K_d, K_d)` ceiling. */
  def fromSpace(s: Space, leaf: Space => Layers,
                rel: (Space, Space) => Pairing = (_, _) => Pairing.unknown): ZIR =
    def go(x: Space): ZIR = x match
      case Space.Empty => ZIR.Lift(Layers.empty)
      case Space.Union(a, b) => ZIR.Un(go(a), go(b), rel(a, b))
      case Space.Intersection(a, b) => ZIR.In(go(a), go(b), rel(a, b))
      case Space.Subtraction(a, b) => ZIR.Diff(go(a), go(b), rel(a, b))
      case Space.Restriction(a, b) => ZIR.Res(go(a), go(b), rel(a, b))
      case Space.Raffination(a, b) => ZIR.Raff(go(a), go(b), rel(a, b))
      case Space.Composition(a, b) => ZIR.Comp(go(a), go(b))
      case Space.Wrap(src, p) => ZIR.Pre(pathLen(p), go(src))
      case Space.Unwrap(src, p) => ZIR.Unw(go(src), pathLen(p))
      case Space.TailsUnion(src) => ZIR.TailsU(go(src))
      case Space.TailsIntersection(_) => ZIR.TailsI(leaf(x))
      case other => if isFallback(other) then ZIR.Fallback(leaf(other)) else ZIR.Lift(leaf(other))
    go(s)

  /** the item length of a path when the SYNTAX gives one: a constant's items, or a `PathRef`'s declared
   *  `lengthHint`.  A `Deref` with no hint has no static length, so the caller must supply the profile
   *  through `leaf` instead of relying on this. */
  def pathLen(p: Path): Int = p match
    case Path.Constant(pv) => pv.items.length
    case Path.Deref(pr) => if pr.lengthHint >= 0 then pr.lengthHint else 0
    case Path.Concat(l, r) => pathLen(l) + pathLen(r)
    case _ => 0
end SpatialDemand
