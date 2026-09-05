package morkl

import scala.collection.immutable.{IntMap, IntMapView, ArraySeq}
import scala.collection.mutable
import scala.collection.mutable.Stack

/** ==================================================================================================
 *  THE OPERATIONAL RESOURCE SEMANTICS (tasks.md A1).
 *
 *  ==WHAT THIS FILE IS==
 *  ONE definition of what every backend and the counted oracle mean by "resource use".  It has three
 *  layers, and the layers are the artifacts A1 names:
 *
 *   1. [[EventKind]] — the backend-INDEPENDENT event algebra: node visits, operand probes,
 *      allocation, retained sharing, key comparisons, materialisation, rounds (plus the one hand-off
 *      kind the zipper needs).  Every counted `EffortEvent` has exactly one kind
 *      ([[EventKind.of]]), and a component (`Work`/`Alloc`/`Rounds`/`Touch`) is a set of kinds
 *      ([[EventKind.inclusion]]).  docs/SPATIAL_SEMANTICS.md records the unit, the inclusion rule and
 *      the sharing convention of each component.
 *   2. [[SemanticsProfile]] — the BACKEND PARAMETERS: which concrete event a kind is emitted as by
 *      which executable, what the representation is, and the one platform parameter the semantics
 *      does not define itself (the reference sort).  A backend difference is a different profile,
 *      never a different semantics.
 *   3. [[EventSemantics]] — the compositional EVENT SEMANTICS itself: for every certified `Space`
 *      constructor and every backend, the event multiset of one execution as a function of the
 *      operands' concrete structure (their paths, their trie shape, their Patricia child maps, and
 *      which operand OBJECTS are the same object).  It is stated as an independent interpreter:
 *      it computes the result AND the events by the rules below, it never reads the executors'
 *      hooks, and it is held to them differentially (`SpatialSemanticsCheck`: same event multiset,
 *      every constructor, every backend).
 *
 *  ==WHO IS THE COUNTED INTERPRETER==
 *  `SpatialEvents.scala`'s hooks inside `eval`/`evalI`/`execT`/`execZ` are the counted
 *  interpreter of this semantics — [[SpatialEvents.counted]] is the entry point — and this file is
 *  what they are counted AGAINST.  An executor whose hooks disagree with the semantics is a bug in
 *  one of the two, and the differential suite says which constructor and which event.  Nothing in
 *  the analysis (tasks.md A4) may derive a cost from anything but the rules in this file: the
 *  abstract transfers bound the STRUCTURAL QUANTITIES these rules count (paired prefix frontiers,
 *  live operands, Patricia shapes, forced cursor nodes), never a constant read off a benchmark.
 *
 *  ==THE N-ARY OPERAND DISCIPLINE (ordered live frontiers)==
 *  Every n-ary operation (`joinAll`/`meetAll`, hence `Iteration`, `TailsUnion`, `TailsIntersection`,
 *  and the Patricia `joinAllTries`/`meetAllTries` below them) is specified over its ORDERED LIVE
 *  FRONTIER: the operands in the order the executor sees them, an operand RETIRED when it is empty
 *  (`dropEmpty`, `stopOnNil`), REVISITED when the split hands it down unchanged (a map whose own
 *  branching bit is below the split bit is re-listed at the next level), ALIASED when two positions
 *  hold the same object (deduplicated by identity: one probe, one `SubtrieAcceptedByPointer`, no
 *  second traversal), and REUSED when the result IS an operand (returned by pointer, no allocation).
 *  Each of those is a rule below with its own event, not a fallback model.
 *
 *  ==SHARING CONVENTION==
 *  `Alloc` counts FRESH objects: a node is fresh when the rule builds it (`fresh`), and NOT fresh
 *  when the result is an operand object or a sub-object of one (identity cases, pointer accepts).
 *  Sharing is therefore observable as the difference between the nodes a result HAS and the nodes
 *  that were ALLOCATED to build it; the `RetainedShare` kind counts the decisions that made that
 *  difference.  The convention is the executors' (IntTrie.scala `node` is the one allocation site).
 *
 *  ==WHAT IS OUTSIDE==
 *  Grounded host functions (`GroundedPS/SS`, `GroundedPP/SP`) are applied, not specified: their
 *  cost is theirs.  `IntMap` node allocation, `Interner` probes and the `Range` key sort are the
 *  declared oracle gaps of SpatialEvents.scala (`OracleGap.declared`) and stay outside the counted
 *  unit here exactly as there; the one platform parameter the reference backend needs (its sort's
 *  comparison count) is a [[SemanticsProfile]] parameter, computed by running the platform sort with
 *  a counting comparator, and it is named as such rather than modelled.
 *  ================================================================================================== */

/** THE EVENT ALGEBRA.  Backend-independent kinds; every `EffortEvent` has exactly one. */
enum EventKind:
  /** a node of the program, the value, or the representation examined: dispatches, cursor reads,
   *  trie/Patricia descents, equality-frontier visits */
  case NodeVisit
  /** one operand of an n-ary operation examined by its per-call operand handling */
  case OperandProbe
  /** one fresh object: a path, a trie node, a frame, a scratch slot */
  case Alloc
  /** a whole sub-structure kept or dropped BY POINTER, or a result that IS an operand */
  case RetainedShare
  /** one item-against-item comparison */
  case KeyComparison
  /** one virtual cursor node forced into a concrete node */
  case Materialize
  /** one dynamic frame: a loop body, a fixpoint round, a call */
  case Round
  /** control handed from one executable to another (the zipper's `evalI` fallback) */
  case Handoff

object EventKind:
  import EffortEvent.*
  def of(e: EffortEvent): EventKind = e match
    case AstDispatch | PathDispatch | TrieDispatch | TriePathDispatch | GraphNodeDispatch |
         ZipperBuild | TrieOpEntry | ZipperCursorRead | TrieNodeVisit | PatriciaVisit |
         PatriciaEntry | EqualityFrontierVisit => NodeVisit
    case NaryOperandProbe => OperandProbe
    case PathItemComparison => KeyComparison
    case FreshPath | FreshTrieNode | FreshNode | GraphFrameAllocation | NaryScratchSlot => Alloc
    case ZipperMaterializeNode => Materialize
    case LoopBodyEntry | FixpointRound | CallEntry => Round
    case AlgebraEmpty | AlgebraIdentityLeft | AlgebraIdentityRight | AlgebraBespoke |
         SubtrieAcceptedByPointer | SubtrieRejectedByPointer | ReusedSpace | ReusedSubtrie => RetainedShare
    case ZipperFallbackToEvalI => Handoff

  /** THE INCLUSION RULE: which kinds a calibrated component sums.  `Explain` events are excluded by
   *  `EffortEvent.component`, so `Touch` is the two descent events and nothing else, exactly as
   *  `SpatialEvents.scala` states; the kind view here says WHY each event is where it is. */
  def inclusion(c: EffortComponent): Set[EventKind] = c match
    case EffortComponent.Work => Set(NodeVisit, OperandProbe, KeyComparison, Materialize)
    case EffortComponent.Alloc => Set(Alloc)
    case EffortComponent.Rounds => Set(Round)
    case EffortComponent.Touch => Set(NodeVisit)
    case EffortComponent.Explain => Set(RetainedShare, Handoff)

/** THE BACKEND PARAMETERS of the semantics: one profile per executable. */
final case class SemanticsProfile(backend: Backend,
                                  /** the event one visited program node is emitted as */
                                  dispatch: EffortEvent,
                                  /** the event one visited PATH subterm is emitted as */
                                  pathDispatch: Option[EffortEvent],
                                  /** the event one entry into the trie algebra from a slot is emitted as */
                                  opEntry: Option[EffortEvent],
                                  /** the representation the rules are stated over */
                                  repr: String,
                                  /** the one platform parameter (the reference sort), or none */
                                  platform: Option[String])

object SemanticsProfile:
  import EffortEvent.*
  val reference: SemanticsProfile = SemanticsProfile(Backend.Reference, AstDispatch, Some(PathDispatch), None,
    "Set[PathValue]: a path is a list of items; a space is a hash set of paths",
    Some("the platform sort's comparison count on the operand's iteration order (Range)"))
  val trie: SemanticsProfile = SemanticsProfile(Backend.Trie, TrieDispatch, Some(TriePathDispatch), None,
    "ITrie: interned Patricia child maps; pointer-preserving case-returning algebra", None)
  val graph: SemanticsProfile = SemanticsProfile(Backend.Graph, GraphNodeDispatch, None, Some(TrieOpEntry),
    "RecursiveOpGraph slots over ITrie; one frame per scope, reused across a loop's children", None)
  val zipper: SemanticsProfile = SemanticsProfile(Backend.Zipper, ZipperBuild, Some(TriePathDispatch), Some(TrieOpEntry),
    "SpaceZipper: virtual cursors over ITrie, materialised top-down; control flow handed to evalI", None)
  val all: Vector[SemanticsProfile] = Vector(reference, trie, graph, zipper)
  def of(b: Backend): SemanticsProfile = all.find(_.backend == b).get

/** the semantics' own tally.  An [[EffortSink.Counter]] — the same saturating counters the executors
 *  fill — but never installed as the active sink: the semantics computes, it is not measured. */
final class Tally:
  private val c = new EffortSink.Counter
  def add(e: EffortEvent): Unit = c.add(e, 1L)
  def add(e: EffortEvent, n: Long): Unit = c.add(e, n)
  def events: Events = c.snapshot

/** THE COUNTED INTERPRETER: the instrumented executors, run under one counting region.  This is the
 *  object the event semantics is held to.  `SpatialEvents.counted(b)(body)` is `EffortSink.count`
 *  with the backend named, so a caller cannot count one executable and label the result another. */
object SpatialEvents:
  final case class Counted[A](backend: Backend, value: A, events: Events)
  def counted[A](backend: Backend)(body: => A): Counted[A] =
    val (a, e) = EffortSink.count(body)
    Counted(backend, a, e)

// ==================================================================================================
// THE EVENT SEMANTICS
// ==================================================================================================
object EventSemantics:
  import EffortEvent.*

  /** THE PLATFORM PARAMETER: how many item comparisons the reference backend's `Range` sort performs
   *  on this operand sequence.  Computed by running the same library sort with a counting comparator
   *  that compares items exactly as `pathValueOrdering` does; it is a parameter, not a rule, because
   *  the number depends on the platform's sort algorithm and not on the language. */
  def platformSortComparisons(v: Vector[PathValue]): Long =
    var n = 0L
    given cnt: Ordering[PathValue] with
      def compare(a: PathValue, b: PathValue): Int =
        val ai = a.items.iterator; val bi = b.items.iterator
        while ai.hasNext && bi.hasNext do
          n += 1
          val c = ai.next().compareTo(bi.next())
          if c != 0 then return c
        Integer.compare(a.items.length, b.items.length)
    v.sorted(using cnt)
    n

  // ---- entry points, one per backend ---------------------------------------------------------------

  /** the reference backend (`eval`) */
  def reference(s: Space)(using pc: PathContext = PathContextMap(Map.empty), sc: SpaceContext = SpaceContextMap(Map.empty),
                          rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): (SpaceValue, Events) =
    val t = new Tally
    val r = new RefSpec(t, rc)
    val v = SpaceValue(r.recs(s, pc, sc))
    (v, t.events)

  /** the trie backend (`evalI`) */
  def trie(s: Space)(using pc: PathContext = PathContextMap(Map.empty), ic: Map[SpaceMention, ITrie] = Map.empty,
                     rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): (ITrie, Events) =
    val t = new Tally
    val sp = new TrieSpec(t)
    val v = sp.eval(s)(using pc, ic, rc)
    (v, t.events)

  /** the graph backend (`runGraphT` / `execT`) */
  def graph(g: RecursiveOpGraph, refs: Map[String, List[Int]] = Map.empty, mentions: Map[String, ITrie] = Map.empty,
            index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): (ITrie, Events) =
    val t = new Tally
    val sp = new GraphSpec(t, new TrieSpec(t))
    val v = sp.run(g, refs, mentions, index)
    (v, t.events)

  /** the zipper backend (`execZ`) */
  def zipper(s: Space)(using pc: PathContext = PathContextMap(Map.empty), ic: Map[SpaceMention, ITrie] = Map.empty,
                       rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): (ITrie, Events) =
    val t = new Tally
    val sp = new ZipperSpec(t, new TrieSpec(t))
    val v = sp.materialize(sp.transpile(s)(using pc, ic, rc))
    (v, t.events)

  // ================================================================================================
  // 1.  THE REFERENCE BACKEND — sets of paths
  // ================================================================================================

  /** `eval`'s rules.  A `Space` node costs one `AstDispatch`, a `Path` subterm one `PathDispatch`;
   *  every path the rule BUILDS is one `FreshPath` (a stored literal is returned, not built); a
   *  prefix test costs one `PathItemComparison` per item actually compared, in the operands'
   *  iteration order; a partial `Range` costs the platform sort.  Loops, rounds and calls are one
   *  `Round` each, the terminating fixpoint round included. */
  private final class RefSpec(t: Tally, rc: PartialFunction[RoutinePtr, Routine]):
    import Space.*

    def startsWith(x: List[PathItem], p: List[PathItem]): Boolean =
      var a = x; var b = p; var ok = true
      while ok && b.nonEmpty do
        if a.isEmpty then ok = false
        else
          t.add(PathItemComparison)
          if a.head != b.head then ok = false else { a = a.tail; b = b.tail }
      ok

    def recp(x: Path, pc: PathContext, sc: SpaceContext): List[PathItem] =
      t.add(PathDispatch)
      x match
        case Path.Deref(pr) => pc.resolve(pr).items
        case Path.Constant(pi) => pi.items
        case Path.Concat(l, r) => recp(l, pc, sc) ++ recp(r, pc, sc)
        case Path.GroundedPP(p, f) => f(PathValue(recp(p, pc, sc))).items
        case Path.GroundedSP(s, f) => f(SpaceValue(recs(s, pc, sc))).items

    def evalTop(s: Space, pc: PathContext, sc: SpaceContext): SpaceValue = SpaceValue(recs(s, pc, sc))

    def recs(x: Space, pc: PathContext, sc: SpaceContext): Set[PathValue] =
      t.add(AstDispatch)
      x match
        case Empty => Set()
        case Call(rp, refs, mentions) =>
          t.add(CallEntry)
          val refvs = refs.map(p => PathValue(recp(p, pc, sc)))
          val mentionvs = mentions.map(s => SpaceValue(recs(s, pc, sc)))
          val Routine(_, refns, mentionns, body) = rc(rp)
          val pctx = PathContextMap(Map.from(refns zip refvs))
          val sctx = SpaceContextMap(Map.from(mentionns zip mentionvs))
          body match
            case Union(l, Call(`rp`, `refs`, `mentions`)) =>
              if (refs zip refvs).forall((p, pv) => pv == evalTop(Singleton(p), pctx, sctx).paths.head) &&
                 (mentions zip mentionvs).forall((s, sv) => sv == evalTop(s, pctx, sctx))
              then evalTop(l, pctx, sctx).paths
              else evalTop(body, pctx, sctx).paths
            case _ => evalTop(body, pctx, sctx).paths
        case Mention(p) => sc.resolve(p).paths
        case Singleton(p) => t.add(FreshPath); Set(PathValue(recp(p, pc, sc)))
        case Literal(SpaceValue(ps)) => ps
        case Union(a, b) => recs(a, pc, sc) union recs(b, pc, sc)
        case Intersection(a, b) => recs(a, pc, sc) intersect recs(b, pc, sc)
        case Subtraction(a, b) => recs(a, pc, sc) removedAll recs(b, pc, sc)
        case Restriction(xe, pe) =>
          val prefixes = recs(pe, pc, sc)
          recs(xe, pc, sc).filter(v => prefixes.exists(p => startsWith(v.items, p.items)))
        case Composition(a, b) =>
          val ys = recs(b, pc, sc)
          for e1 <- recs(a, pc, sc); e2 <- ys yield { t.add(FreshPath); PathValue(e1.items ++ e2.items) }
        case Wrap(src, p) => recs(Composition(Singleton(p), src), pc, sc)
        case Unwrap(src, pe) =>
          val p = recp(pe, pc, sc)
          val s = recs(src, pc, sc)
          s.collect { case e if startsWith(e.items, p) => t.add(FreshPath); PathValue(e.items.drop(p.length)) }
        case TailsUnion(src) =>
          recs(src, pc, sc).collect { case PathValue(_ :: r) => t.add(FreshPath); PathValue(r) }
        case TailsIntersection(src) =>
          val groups = recs(src, pc, sc).collect { case PathValue(h :: tl) => t.add(FreshPath); h -> PathValue(tl) }.groupMap(_._1)(_._2)
          if groups.isEmpty then Set.empty else groups.valuesIterator.map(_.toSet).reduce(_ intersect _)
        case Iteration(src, symbol, rest, templates) =>
          val groups = recs(src, pc, sc).collect { case PathValue(h :: tail) =>
            t.add(FreshPath, 2L); PathValue(h :: Nil) -> PathValue(tail) }.groupMap(_._1)(_._2)
          Set.from(for (h, r) <- groups;
                       p <- { t.add(LoopBodyEntry)
                              evalTop(templates, pc.grown(Map(symbol -> h)), sc.grown(Map(rest -> SpaceValue(Set.from(r))))) }.paths
                   yield p)
        case Fixpoint(init, rec, body) =>
          var cur = recs(init, pc, sc)
          var stop = false
          while !stop do
            t.add(FixpointRound)
            val nxt = cur union evalTop(body, pc, sc.grown(Map(rec -> SpaceValue(cur)))).paths
            if nxt == cur then stop = true else cur = nxt
          cur
        case Fold(src, initial, acc, symbol, rest, templates, update) =>
          var accValue = PathValue(recp(initial, pc, sc))
          val groups = recs(src, pc, sc).collect { case PathValue(h :: tail) =>
            t.add(FreshPath, 2L); PathValue(h :: Nil) -> PathValue(tail) }.groupMap(_._1)(_._2)
          val out = Set.newBuilder[PathValue]
          for (h, r) <- groups.toSeq.sortBy(_._1.show) do
            t.add(LoopBodyEntry)
            val pctx = pc.grown(Map(acc -> accValue, symbol -> h))
            val sctx = sc.grown(Map(rest -> SpaceValue(Set.from(r))))
            out ++= evalTop(templates, pctx, sctx).paths
            accValue = PathValue(evalTop(Singleton(update), pctx, sctx).paths.head.items)
          out.result()
        case Raffination(xe, ye) => recs(Subtraction(xe, Restriction(xe, ye)), pc, sc)
        case GroundedPS(p, f) => f(PathValue(recp(p, pc, sc))).paths
        case GroundedSS(s, f) => f(SpaceValue(recs(s, pc, sc))).paths
        case Range(xe, lo, hi) =>
          val s = recs(xe, pc, sc)
          val (a, b) = RangeBounds.normalize(s.size, lo, hi)
          if b <= a then Set.empty
          else if a == 0 && b == s.size then s
          else
            val v = s.toVector
            t.add(PathItemComparison, platformSortComparisons(v))
            v.sorted(using pathValueOrdering).slice(a, b).toSet
  end RefSpec

  // ================================================================================================
  // 2.  THE TRIE REPRESENTATION — ITrie over Patricia child maps
  // ================================================================================================

  /** the per-node outcome of a ring operation relative to its operands, the semantics' twin of
   *  `ITrie.AlgebraicResult`: `Empty`, the LEFT or RIGHT operand by pointer, or a fresh node */
  private enum Res:
    case Empty
    case Left, Right
    case Bespoke(n: ITrie)

  /** `evalI`'s rules and the rules of the trie algebra beneath them.  Shared by the graph and zipper
   *  backends, whose representation is the same trie: only the dispatch and entry events differ. */
  private final class TrieSpec(t: Tally):
    import Space.*
    import IntMapView.Shape

    require(Tuning.patriciaOps, "the event semantics is stated over the Patricia algebra (-Dmorkl.patriciaOps=true)")

    /** the semantics' own literal memo — identity-keyed like `iLiteralCache`, so two `Literal` nodes
     *  over the same `SpaceValue` object share one trie, exactly as the executor's do */
    private val literals = new java.util.IdentityHashMap[SpaceValue, ITrie]()
    private val literalStrs = mutable.HashMap.empty[String, ITrie]

    // ---- the one allocation rule and the case events ---------------------------------------------
    private def fresh(term: Boolean, ch: IntMap[ITrie]): ITrie = { t.add(FreshTrieNode); ITrie(term, ch) }
    private def visit(): Unit = t.add(TrieNodeVisit)
    private def enter(): Unit = t.add(PatriciaVisit)
    private def entry(): Unit = t.add(PatriciaEntry)
    private def took(): Unit = t.add(SubtrieAcceptedByPointer)
    private def dropped(): Unit = t.add(SubtrieRejectedByPointer)
    private def probes(n: Long): Unit = t.add(NaryOperandProbe, n)
    private def scratch(n: Long): Unit = t.add(NaryScratchSlot, n)
    private def rEmpty(): Res = { t.add(AlgebraEmpty); Res.Empty }
    private def rLeft(): Res = { t.add(SubtrieAcceptedByPointer); t.add(AlgebraIdentityLeft); Res.Left }
    private def rRight(): Res = { t.add(SubtrieAcceptedByPointer); t.add(AlgebraIdentityRight); Res.Right }
    private def rBespoke(n: ITrie): Res = { t.add(AlgebraBespoke); Res.Bespoke(n) }
    private def pick(r: Res, a: ITrie, b: ITrie): ITrie = r match
      case Res.Empty => ITrie.empty
      case Res.Left => a
      case Res.Right => b
      case Res.Bespoke(n) => n

    // ---- paths -------------------------------------------------------------------------------------
    def pathItems(x: Path)(using pc: PathContext, ic: Map[SpaceMention, ITrie], rc: PartialFunction[RoutinePtr, Routine]): List[Int] =
      t.add(TriePathDispatch)
      x match
        case Path.Deref(pr) => Interner.internPath(pc.resolve(pr).items)
        case Path.Constant(pi) => Interner.internPath(pi.items)
        case Path.Concat(l, r) => pathItems(l) ++ pathItems(r)
        case Path.GroundedPP(p, f) => Interner.internPath(f(PathValue(Interner.uninternPath(pathItems(p)))).items)
        case Path.GroundedSP(sp, f) => Interner.internPath(f(toSpaceValue(eval(sp))).items)

    /** `ITrie.toPaths`: one visit per node */
    def toSpaceValue(tr: ITrie): SpaceValue =
      val out = Set.newBuilder[PathValue]
      def go(n: ITrie, acc: List[Int]): Unit =
        visit()
        if n.terminal then out += PathValue(Interner.uninternPath(acc.reverse))
        n.children.foreach { case (k, c) => go(c, k :: acc) }
      go(tr, Nil); SpaceValue(out.result())

    // ---- the cached terminal count ------------------------------------------------------------------
    /** `ITrie.count`: a walk over every node whose count is not yet memoised, one visit each; the memo
     *  is then set on the real node so the next query is one load.  The cache state is part of the
     *  machine state and the semantics reads it (`countIfKnown`) rather than assuming it. */
    def count(n: ITrie): Int =
      val known = n.countIfKnown
      if known >= 0 then known
      else
        visit()
        val s = (if n.terminal then 1 else 0) + n.children.valuesIterator.map(count).sum
        n.count                                  // memoise on the real node: its children are cached now
        s

    // ---- ring operations -----------------------------------------------------------------------------
    def union(a: ITrie, b: ITrie): ITrie = pick(unionR(a, b), a, b)
    def unionR(a: ITrie, b: ITrie): Res =
      visit()
      if a eq b then { t.add(ReusedSubtrie); if a.isEmpty then rEmpty() else rLeft() }
      else if b.isEmpty then (if a.isEmpty then rEmpty() else rLeft())
      else if a.isEmpty then rRight()
      else
        val term = a.terminal || b.terminal
        val ch = unionTries(a.children, b.children)
        val l = (ch eq a.children) && term == a.terminal
        val r = (ch eq b.children) && term == b.terminal
        if l then rLeft() else if r then rRight() else rBespoke(fresh(term, ch))

    def intersection(a: ITrie, b: ITrie): ITrie = pick(intersectionR(a, b), a, b)
    def intersectionR(a: ITrie, b: ITrie): Res =
      visit()
      if a eq b then { t.add(ReusedSubtrie); if a.isEmpty then rEmpty() else rLeft() }
      else if a.isEmpty || b.isEmpty then rEmpty()
      else
        val term = a.terminal && b.terminal
        val ch = intersectTries(a.children, b.children)
        if ch.isEmpty && !term then rEmpty()
        else
          val l = (ch eq a.children) && term == a.terminal
          val r = (ch eq b.children) && term == b.terminal
          if l then rLeft() else if r then rRight() else rBespoke(fresh(term, ch))

    def subtraction(a: ITrie, b: ITrie): ITrie = pick(subtractionR(a, b), a, b)
    def subtractionR(a: ITrie, b: ITrie): Res =
      visit()
      if a eq b then { t.add(ReusedSubtrie); rEmpty() }
      else if a.isEmpty then rEmpty()
      else if b.isEmpty then rLeft()
      else
        val term = a.terminal && !b.terminal
        val ch = diffTries(a.children, b.children)
        if ch.isEmpty && !term then rEmpty()
        else if (ch eq a.children) && term == a.terminal then rLeft()
        else rBespoke(fresh(term, ch))

    def restriction(x: ITrie, prefixes: ITrie): ITrie = pick(restrictionR(x, prefixes), x, prefixes)
    def restrictionR(x: ITrie, prefixes: ITrie): Res =
      visit()
      if x eq prefixes then { t.add(ReusedSubtrie); if x.isEmpty then rEmpty() else rLeft() }
      else if x.isEmpty || prefixes.isEmpty then rEmpty()
      else if prefixes.terminal then rLeft()
      else
        val ch = restrictTries(x.children, prefixes.children)
        if ch.isEmpty then rEmpty()
        else
          val l = (ch eq x.children) && !x.terminal
          val r = ch eq prefixes.children
          if l then rLeft() else if r then rRight() else rBespoke(fresh(false, ch))

    def raffination(x: ITrie, y: ITrie): ITrie = pick(raffinationR(x, y), x, y)
    def raffinationR(x: ITrie, y: ITrie): Res =
      visit()
      if x.isEmpty then rEmpty()
      else if x eq y then { t.add(ReusedSubtrie); rEmpty() }
      else if y.isEmpty then rLeft()
      else if y.terminal then rEmpty()
      else
        val term = x.terminal
        val ch = raffTries(x.children, y.children)
        if ch.isEmpty && !term then rEmpty()
        else if ch eq x.children then rLeft()
        else rBespoke(fresh(term, ch))

    def composition(a: ITrie, b: ITrie): ITrie = pick(compositionR(a, b), a, b)
    def compositionR(a: ITrie, b: ITrie): Res =
      visit()
      if a.isEmpty || b.isEmpty then rEmpty()
      else if b.terminal && b.children.isEmpty then rLeft()
      else if a.terminal && a.children.isEmpty then rRight()
      else
        val mapped = fresh(false, a.children.transform((_, ac) => composition(ac, b)))
        rBespoke(if a.terminal then union(mapped, b) else mapped)

    // ---- n-ary --------------------------------------------------------------------------------------
    private def anyEmptyOperand(ts: IterableOnce[ITrie]): Boolean =
      var n = 0; var found = false
      val it = ts.iterator
      while it.hasNext && !found do { found = it.next().isEmpty; n += 1 }
      probes(n.toLong)
      found

    private def liveDistinct(ts: IterableOnce[ITrie], dropEmpty: Boolean): mutable.ArrayBuffer[ITrie] =
      val buf = new mutable.ArrayBuffer[ITrie](4)
      var seen: java.util.IdentityHashMap[ITrie, ITrie] = null
      var pr = 0
      val it = ts.iterator
      while it.hasNext do
        val x = it.next()
        if !dropEmpty || x.nonEmpty then
          var dup = false
          if seen != null then { pr += 1; dup = seen.put(x, x) != null }
          else
            var i = 0
            while i < buf.length && !dup do { if buf(i) eq x then dup = true; i += 1 }
            pr += i
          if dup then t.add(ReusedSubtrie)
          else
            buf += x
            if seen == null && buf.length > 24 then
              seen = new java.util.IdentityHashMap[ITrie, ITrie]()
              scratch(2L * (buf.length + 1))
              buf.foreach(y => seen.put(y, y))
              pr += buf.length
      probes(pr.toLong)
      scratch(math.max(4L, 4L * buf.length))
      buf

    def joinAll(ts: IterableOnce[ITrie]): ITrie =
      visit()
      val live = liveDistinct(ts, dropEmpty = true)
      if live.isEmpty then ITrie.empty
      else if live.length == 1 then { took(); live(0) }
      else if live.length == 2 then union(live(0), live(1))
      else
        var term = false
        var i = 0
        while i < live.length do { if live(i).terminal then term = true; i += 1 }
        probes(live.length.toLong)
        val maps = new Array[IntMap[ITrie]](live.length)
        scratch(live.length.toLong)
        i = 0
        while i < live.length do { maps(i) = live(i).children; i += 1 }
        probes(live.length.toLong)
        val ch = joinAllTries(maps, maps.length)
        var res: ITrie = null
        i = 0
        while i < live.length && (res eq null) do
          if (ch eq live(i).children) && live(i).terminal == term then res = live(i)
          i += 1
        probes(i.toLong)
        if res ne null then { took(); res } else fresh(term, ch)

    def meetAll(ts: scala.collection.Seq[ITrie]): ITrie =
      visit()
      if ts.isEmpty then ITrie.empty
      else if anyEmptyOperand(ts) then { dropped(); ITrie.empty }
      else
        val live = liveDistinct(ts, dropEmpty = false)
        if live.length == 1 then { took(); live(0) }
        else if live.length == 2 then intersection(live(0), live(1))
        else
          var ti = 0
          while ti < live.length && live(ti).terminal do ti += 1
          val term = ti == live.length
          probes(math.min(ti + 1, live.length).toLong)
          val maps = new Array[IntMap[ITrie]](live.length)
          scratch(live.length.toLong)
          var i = 0
          while i < live.length do { maps(i) = live(i).children; i += 1 }
          probes(live.length.toLong)
          val ch = meetAllTries(maps, maps.length)
          if ch.isEmpty && !term then ITrie.empty
          else
            var res: ITrie = null
            i = 0
            while i < live.length && (res eq null) do
              if (ch eq live(i).children) && live(i).terminal == term then res = live(i)
              i += 1
            probes(i.toLong)
            if res ne null then { took(); res } else fresh(term, ch)

    // ---- prefix operations ----------------------------------------------------------------------------
    def singleton(ids: List[Int]): ITrie =
      visit()
      ids.foldRight(ITrie.epsilon)((id, acc) => fresh(false, IntMap.singleton(id, acc)))
    def fromSpaceValue(sv: SpaceValue): ITrie =
      sv.paths.foldLeft(ITrie.empty)((acc, p) => union(acc, singleton(Interner.internPath(p.items))))
    def wrap(ids: List[Int], s: ITrie): ITrie =
      visit()
      if s.isEmpty then ITrie.empty else ids.foldRight(s)((id, acc) => fresh(false, IntMap.singleton(id, acc)))
    def unwrap(s: ITrie, ids: List[Int]): ITrie =
      visit()
      ids match
        case Nil => s
        case h :: tl => s.children.get(h).map(unwrap(_, tl)).getOrElse(ITrie.empty)
    def tailsUnion(s: ITrie): ITrie =
      visit()
      if s.children.isEmpty then ITrie.empty
      else if s.children.size == 1 then { took(); s.children.valuesIterator.next() }
      else joinAll(s.children.valuesIterator)
    def tailsIntersection(s: ITrie): ITrie =
      visit()
      if s.children.isEmpty then ITrie.empty
      else if s.children.size == 1 then { took(); s.children.valuesIterator.next() }
      else meetAll(s.children.valuesIterator.toSeq)

    // ---- ordered selection ------------------------------------------------------------------------------
    /** `ITrie.ordered` without the memo: the memo only spares the (uncounted) key sort, and the child
     *  counts it forces are cached on the nodes themselves, so hit and miss emit the same events */
    private def ordered(n: ITrie): Array[Int] =
      val ks = n.children.keysIterator.toArray.sortBy(Interner.unintern)
      val k = ks.length
      val out = new Array[Int](2 * k)
      var i = 0
      var acc = if n.terminal then 1 else 0
      while i < k do
        out(i) = ks(i); out(k + i) = acc
        acc += count(n.children(ks(i)))
        i += 1
      out
    private def firstAfter(ord: Array[Int], k: Int, lo: Int): Int =
      if lo <= 0 then 0
      else
        var a = 0; var b = k - 1
        while a < b do
          val mid = (a + b) >>> 1
          if ord(k + mid + 1) <= lo then a = mid + 1 else b = mid
        a
    private def slice(n: ITrie, lo: Int, hi: Int): ITrie =
      visit()
      if hi <= lo then ITrie.empty
      else if lo <= 0 && hi >= count(n) then { took(); n }
      else
        val ord = ordered(n)
        val k = ord.length >>> 1
        val term = n.terminal && lo <= 0
        var i = firstAfter(ord, k, lo)
        if i > 0 then t.add(SubtrieRejectedByPointer, i.toLong)
        var ch = IntMap.empty[ITrie]
        while i < k && ord(k + i) < hi do
          val base = ord(k + i)
          val c = n.children(ord(i))
          val r = slice(c, lo - base, hi - base)
          if r.nonEmpty then ch = ch.updated(ord(i), r)
          i += 1
        if i < k then t.add(SubtrieRejectedByPointer, (k - i).toLong)
        if ch.isEmpty && !term then ITrie.empty else fresh(term, ch)
    def range(tr: ITrie, start: Int, end: Int): ITrie =
      visit()
      val size = count(tr)
      val (lo, hi) = RangeBounds.normalize(size, start, end)
      if hi <= lo then ITrie.empty
      else if lo == 0 && hi == size then { took(); tr }
      else slice(tr, lo, hi)

    // ---- convergence ---------------------------------------------------------------------------------------
    def equalT(a: ITrie, b: ITrie): Boolean =
      t.add(EqualityFrontierVisit)
      if a eq b then { t.add(ReusedSubtrie); true }
      else if a.terminal != b.terminal then false
      else if a.children eq b.children then true
      else
        val ka = a.countIfKnown; val kb = b.countIfKnown
        if ka >= 0 && kb >= 0 && ka != kb then false
        else a.children.size == b.children.size &&
             a.children.forall { case (k, ac) => b.children.get(k) match
               case Some(bc) => equalT(ac, bc)
               case None => false }

    // ---- the Patricia merges (IntTrieOps) ----------------------------------------------------------------------
    private val dedupScanMax = 24
    private def repKey(m: IntMap[ITrie]): Int = IntMapView.shape(m) match
      case Shape.Tip(k, _) => k
      case Shape.Bin(p, _, _, _) => p
      case _ => 0
    private def maskOf(m: IntMap[ITrie]): Int = IntMapView.shape(m) match
      case Shape.Bin(_, mm, _, _) => mm
      case _ => 0
    private def prefixOf(i: Int, m: Int): Int = i & (~(m - 1) ^ m)

    private def collectLive(ms: Array[IntMap[ITrie]], n: Int, live: Array[IntMap[ITrie]], stopOnNil: Boolean): Int =
      var k = 0; var i = 0; var pr = 0
      var seen: java.util.IdentityHashMap[IntMap[ITrie], IntMap[ITrie]] = null
      var annihilated = false
      while i < n && !annihilated do
        val m = ms(i)
        if m eq null then ()
        else if IntMapView.isNil(m) then { if stopOnNil then annihilated = true }
        else
          var dup = false
          if seen ne null then { pr += 1; dup = seen.put(m, m) ne null }
          else
            var j = 0
            while j < k && !dup do { if live(j) eq m then dup = true; j += 1 }
            pr += j
          if dup then took()
          else
            live(k) = m; k += 1
            if (seen eq null) && k > dedupScanMax then
              seen = new java.util.IdentityHashMap[IntMap[ITrie], IntMap[ITrie]](2 * k)
              scratch(2L * (k + 1))
              var j = 0
              while j < k do { seen.put(live(j), live(j)); j += 1 }
              pr += k
        i += 1
      probes(pr.toLong)
      if annihilated then -1 else k

    private def bin1(orig: IntMap[ITrie], p: Int, m: Int, l0: IntMap[ITrie], r0: IntMap[ITrie],
                     l: IntMap[ITrie], r: IntMap[ITrie]): IntMap[ITrie] =
      if (l eq l0) && (r eq r0) then orig else IntMapView.bin(p, m, l, r)
    private def binP(a: IntMap[ITrie], b: IntMap[ITrie], p: Int, m: Int,
                     l1: IntMap[ITrie], r1: IntMap[ITrie], l2: IntMap[ITrie], r2: IntMap[ITrie],
                     l: IntMap[ITrie], r: IntMap[ITrie]): IntMap[ITrie] =
      if (l eq l1) && (r eq r1) then a
      else if (l eq l2) && (r eq r2) then b
      else if IntMapView.isNil(l) then r
      else if IntMapView.isNil(r) then l
      else IntMapView.bin(p, m, l, r)
    private def binD(a: IntMap[ITrie], p: Int, m: Int, l0: IntMap[ITrie], r0: IntMap[ITrie],
                     l: IntMap[ITrie], r: IntMap[ITrie]): IntMap[ITrie] =
      if (l eq l0) && (r eq r0) then a
      else if IntMapView.isNil(l) then r
      else if IntMapView.isNil(r) then l
      else IntMapView.bin(p, m, l, r)

    private def insUnion(m: IntMap[ITrie], k: Int, v: ITrie, vLeft: Boolean): IntMap[ITrie] =
      entry()
      m.get(k) match
        case Some(w) =>
          val u = if vLeft then union(v, w) else union(w, v)
          if u eq w then m else m.updated(k, u)
        case None => took(); m.updated(k, v)

    def unionTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] =
      enter()
      if a eq b then a
      else IntMapView.shape(a) match
        case Shape.Nil => took(); b
        case Shape.Tip(k1, v1) => IntMapView.shape(b) match
          case Shape.Nil => took(); a
          case Shape.Tip(k2, v2) =>
            entry()
            if k1 == k2 then
              val u = union(v1, v2)
              if u eq v1 then a else if u eq v2 then b else IntMapView.tip(k1, u)
            else { took(); took(); IntMapView.join(k1, a, k2, b) }
          case _ => insUnion(b, k1, v1, true)
        case Shape.Bin(p1, m1, l1, r1) => IntMapView.shape(b) match
          case Shape.Nil => took(); a
          case Shape.Tip(k2, v2) => insUnion(a, k2, v2, false)
          case Shape.Bin(p2, m2, l2, r2) =>
            if IntMapView.shorter(m1, m2) then
              if !IntMapView.hasMatch(p2, p1, m1) then { took(); took(); IntMapView.join(p1, a, p2, b) }
              else if IntMapView.zero(p2, m1) then bin1(a, p1, m1, l1, r1, unionTries(l1, b), r1)
              else bin1(a, p1, m1, l1, r1, l1, unionTries(r1, b))
            else if IntMapView.shorter(m2, m1) then
              if !IntMapView.hasMatch(p1, p2, m2) then { took(); took(); IntMapView.join(p1, a, p2, b) }
              else if IntMapView.zero(p1, m2) then bin1(b, p2, m2, l2, r2, unionTries(a, l2), r2)
              else bin1(b, p2, m2, l2, r2, l2, unionTries(a, r2))
            else if p1 == p2 then
              val l = unionTries(l1, l2)
              val r = unionTries(r1, r2)
              if (l eq l1) && (r eq r1) then a
              else if (l eq l2) && (r eq r2) then b
              else IntMapView.bin(p1, m1, l, r)
            else { took(); took(); IntMapView.join(p1, a, p2, b) }

    def joinAllTries(ms: Array[IntMap[ITrie]], n: Int): IntMap[ITrie] =
      enter()
      val live = new Array[IntMap[ITrie]](n)
      scratch(n.toLong)
      val k = collectLive(ms, n, live, stopOnNil = false)
      var i = 0
      if k == 0 then IntMapView.empty
      else if k == 1 then { took(); live(0) }
      else if k == 2 then unionTries(live(0), live(1))
      else
        val rep = repKey(live(0))
        var acc = 0
        i = 0
        while i < k do { acc |= (repKey(live(i)) ^ rep) | maskOf(live(i)); i += 1 }
        probes(k.toLong)
        val br = java.lang.Integer.highestOneBit(acc)
        if br == 0 then
          val vs = new Array[ITrie](k)
          scratch(k.toLong)
          i = 0
          while i < k do { vs(i) = (IntMapView.shape(live(i)): @unchecked) match { case Shape.Tip(_, v) => v }; i += 1 }
          probes(k.toLong)
          val u = joinAll(ArraySeq.unsafeWrapArray(vs))
          var res: IntMap[ITrie] = null
          i = 0
          while i < k && (res eq null) do { if u eq vs(i) then res = live(i); i += 1 }
          probes(i.toLong)
          if res ne null then res else IntMapView.tip(rep, u)
        else
          val ls = new Array[IntMap[ITrie]](k)
          val rs = new Array[IntMap[ITrie]](k)
          scratch(2L * k)
          var nl = 0; var nr = 0
          i = 0
          while i < k do
            IntMapView.shape(live(i)) match
              case Shape.Bin(_, mm, l0, r0) if mm == br => ls(nl) = l0; nl += 1; rs(nr) = r0; nr += 1
              case _ =>
                val tt = live(i)
                if (repKey(tt) & br) == 0 then { ls(nl) = tt; nl += 1 } else { rs(nr) = tt; nr += 1 }
            i += 1
          probes(k.toLong)
          val l = joinAllTries(ls, nl)
          val r = joinAllTries(rs, nr)
          var res: IntMap[ITrie] = null
          i = 0
          while i < k && (res eq null) do
            IntMapView.shape(live(i)) match
              case Shape.Bin(_, mm, l0, r0) if mm == br && (l eq l0) && (r eq r0) => res = live(i)
              case _ => ()
            i += 1
          probes(i.toLong)
          if res ne null then res
          else if IntMapView.isNil(l) then r
          else if IntMapView.isNil(r) then l
          else IntMapView.bin(prefixOf(rep, br), br, l, r)

    def intersectTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] =
      enter()
      if a eq b then a
      else IntMapView.shape(a) match
        case Shape.Nil => dropped(); IntMapView.empty
        case Shape.Tip(k1, v1) => IntMapView.shape(b) match
          case Shape.Nil => dropped(); IntMapView.empty
          case Shape.Tip(k2, v2) =>
            entry()
            if k1 != k2 then { dropped(); dropped(); IntMapView.empty }
            else
              val r = intersection(v1, v2)
              if r.isEmpty then IntMapView.empty else if r eq v1 then a else if r eq v2 then b else IntMapView.tip(k1, r)
          case _ =>
            entry()
            b.get(k1) match
              case Some(w) =>
                val r = intersection(v1, w)
                if r.isEmpty then IntMapView.empty else if r eq v1 then a else IntMapView.tip(k1, r)
              case None => dropped(); IntMapView.empty
        case Shape.Bin(p1, m1, l1, r1) => IntMapView.shape(b) match
          case Shape.Nil => dropped(); IntMapView.empty
          case Shape.Tip(k2, w2) =>
            entry()
            a.get(k2) match
              case Some(v) =>
                val r = intersection(v, w2)
                if r.isEmpty then IntMapView.empty else if r eq w2 then b else IntMapView.tip(k2, r)
              case None => dropped(); IntMapView.empty
          case Shape.Bin(p2, m2, l2, r2) =>
            if IntMapView.shorter(m1, m2) then
              if !IntMapView.hasMatch(p2, p1, m1) then { dropped(); IntMapView.empty }
              else if IntMapView.zero(p2, m1) then { dropped(); intersectTries(l1, b) } else { dropped(); intersectTries(r1, b) }
            else if IntMapView.shorter(m2, m1) then
              if !IntMapView.hasMatch(p1, p2, m2) then { dropped(); IntMapView.empty }
              else if IntMapView.zero(p1, m2) then { dropped(); intersectTries(a, l2) } else { dropped(); intersectTries(a, r2) }
            else if p1 == p2 then
              binP(a, b, p1, m1, l1, r1, l2, r2, intersectTries(l1, l2), intersectTries(r1, r2))
            else { dropped(); dropped(); IntMapView.empty }

    def meetAllTries(ms: Array[IntMap[ITrie]], n: Int): IntMap[ITrie] =
      enter()
      val live = new Array[IntMap[ITrie]](n)
      scratch(n.toLong)
      val k = collectLive(ms, n, live, stopOnNil = true)
      var i = 0
      if k < 0 then { dropped(); IntMapView.empty }
      else if k == 0 then IntMapView.empty
      else if k == 1 then { took(); live(0) }
      else if k == 2 then intersectTries(live(0), live(1))
      else
        val rep = repKey(live(0))
        var acc = 0
        i = 0
        while i < k do { acc |= (repKey(live(i)) ^ rep) | maskOf(live(i)); i += 1 }
        probes(k.toLong)
        val br = java.lang.Integer.highestOneBit(acc)
        if br == 0 then
          val vs = new Array[ITrie](k)
          scratch(k.toLong)
          i = 0
          while i < k do { vs(i) = (IntMapView.shape(live(i)): @unchecked) match { case Shape.Tip(_, v) => v }; i += 1 }
          probes(k.toLong)
          val r = meetAll(ArraySeq.unsafeWrapArray(vs))
          if r.isEmpty then IntMapView.empty
          else
            var res: IntMap[ITrie] = null
            i = 0
            while i < k && (res eq null) do { if r eq vs(i) then res = live(i); i += 1 }
            probes(i.toLong)
            if res ne null then res else IntMapView.tip(rep, r)
        else
          val ls = new Array[IntMap[ITrie]](k)
          val rs = new Array[IntMap[ITrie]](k)
          scratch(2L * k)
          var nl = 0; var nr = 0
          var forcedL = false; var forcedR = false
          i = 0
          while i < k do
            IntMapView.shape(live(i)) match
              case Shape.Bin(_, mm, l0, r0) if mm == br => ls(nl) = l0; nl += 1; rs(nr) = r0; nr += 1
              case _ =>
                val tt = live(i)
                if (repKey(tt) & br) == 0 then { ls(nl) = tt; nl += 1; forcedL = true }
                else { rs(nr) = tt; nr += 1; forcedR = true }
            i += 1
          probes(k.toLong)
          if forcedL && forcedR then { dropped(); dropped(); IntMapView.empty }
          else if forcedL then { dropped(); meetAllTries(ls, nl) }
          else if forcedR then { dropped(); meetAllTries(rs, nr) }
          else
            val l = meetAllTries(ls, nl)
            val r = meetAllTries(rs, nr)
            var res: IntMap[ITrie] = null
            i = 0
            while i < k && (res eq null) do
              IntMapView.shape(live(i)) match
                case Shape.Bin(_, mm, l0, r0) if mm == br && (l eq l0) && (r eq r0) => res = live(i)
                case _ => ()
              i += 1
            probes(i.toLong)
            if res ne null then res
            else if IntMapView.isNil(l) then r
            else if IntMapView.isNil(r) then l
            else IntMapView.bin(prefixOf(rep, br), br, l, r)

    def restrictTries(x: IntMap[ITrie], p: IntMap[ITrie]): IntMap[ITrie] =
      enter()
      IntMapView.shape(x) match
        case Shape.Nil => dropped(); IntMapView.empty
        case Shape.Tip(k1, v1) => IntMapView.shape(p) match
          case Shape.Nil => dropped(); IntMapView.empty
          case Shape.Tip(k2, w2) =>
            entry()
            if k1 != k2 then { dropped(); dropped(); IntMapView.empty }
            else
              val r = restriction(v1, w2)
              if r.isEmpty then IntMapView.empty else if r eq v1 then x else if r eq w2 then p else IntMapView.tip(k1, r)
          case _ =>
            entry()
            p.get(k1) match
              case Some(w) =>
                val r = restriction(v1, w)
                if r.isEmpty then IntMapView.empty else if r eq v1 then x else IntMapView.tip(k1, r)
              case None => dropped(); IntMapView.empty
        case Shape.Bin(p1, m1, l1, r1) => IntMapView.shape(p) match
          case Shape.Nil => dropped(); IntMapView.empty
          case Shape.Tip(k2, w2) =>
            entry()
            x.get(k2) match
              case Some(v) =>
                val r = restriction(v, w2)
                if r.isEmpty then IntMapView.empty else if r eq w2 then p else IntMapView.tip(k2, r)
              case None => dropped(); IntMapView.empty
          case Shape.Bin(p2, m2, l2, r2) =>
            if IntMapView.shorter(m1, m2) then
              if !IntMapView.hasMatch(p2, p1, m1) then { dropped(); IntMapView.empty }
              else if IntMapView.zero(p2, m1) then { dropped(); restrictTries(l1, p) } else { dropped(); restrictTries(r1, p) }
            else if IntMapView.shorter(m2, m1) then
              if !IntMapView.hasMatch(p1, p2, m2) then { dropped(); IntMapView.empty }
              else if IntMapView.zero(p1, m2) then { dropped(); restrictTries(x, l2) } else { dropped(); restrictTries(x, r2) }
            else if p1 == p2 then
              binP(x, p, p1, m1, l1, r1, l2, r2, restrictTries(l1, l2), restrictTries(r1, r2))
            else { dropped(); dropped(); IntMapView.empty }

    def diffTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] =
      enter()
      if a eq b then IntMapView.empty
      else IntMapView.shape(a) match
        case Shape.Nil => IntMapView.empty
        case Shape.Tip(k1, v1) => IntMapView.shape(b) match
          case Shape.Nil => took(); a
          case _ =>
            entry()
            b.get(k1) match
              case Some(w) =>
                val r = subtraction(v1, w)
                if r.isEmpty then IntMapView.empty else if r eq v1 then a else IntMapView.tip(k1, r)
              case None => took(); a
        case Shape.Bin(p1, m1, l1, r1) => IntMapView.shape(b) match
          case Shape.Nil => took(); a
          case Shape.Tip(k2, w2) =>
            entry()
            a.get(k2) match
              case Some(v) =>
                val r = subtraction(v, w2)
                if r.isEmpty then a - k2 else if r eq v then a else a.updated(k2, r)
              case None => took(); a
          case Shape.Bin(p2, m2, l2, r2) =>
            if IntMapView.shorter(m1, m2) then
              if !IntMapView.hasMatch(p2, p1, m1) then { took(); a }
              else if IntMapView.zero(p2, m1) then binD(a, p1, m1, l1, r1, diffTries(l1, b), r1)
              else binD(a, p1, m1, l1, r1, l1, diffTries(r1, b))
            else if IntMapView.shorter(m2, m1) then
              if !IntMapView.hasMatch(p1, p2, m2) then { took(); a }
              else if IntMapView.zero(p1, m2) then { dropped(); diffTries(a, l2) } else { dropped(); diffTries(a, r2) }
            else if p1 == p2 then binD(a, p1, m1, l1, r1, diffTries(l1, l2), diffTries(r1, r2))
            else { took(); a }

    def raffTries(x: IntMap[ITrie], y: IntMap[ITrie]): IntMap[ITrie] =
      enter()
      if x eq y then IntMapView.empty
      else IntMapView.shape(x) match
        case Shape.Nil => IntMapView.empty
        case Shape.Tip(k1, v1) => IntMapView.shape(y) match
          case Shape.Nil => took(); x
          case _ =>
            entry()
            y.get(k1) match
              case Some(w) =>
                val r = raffination(v1, w)
                if r.isEmpty then IntMapView.empty else if r eq v1 then x else IntMapView.tip(k1, r)
              case None => took(); x
        case Shape.Bin(p1, m1, l1, r1) => IntMapView.shape(y) match
          case Shape.Nil => took(); x
          case Shape.Tip(k2, w2) =>
            entry()
            x.get(k2) match
              case Some(v) =>
                val r = raffination(v, w2)
                if r.isEmpty then x - k2 else if r eq v then x else x.updated(k2, r)
              case None => took(); x
          case Shape.Bin(p2, m2, l2, r2) =>
            if IntMapView.shorter(m1, m2) then
              if !IntMapView.hasMatch(p2, p1, m1) then { took(); x }
              else if IntMapView.zero(p2, m1) then binD(x, p1, m1, l1, r1, raffTries(l1, y), r1)
              else binD(x, p1, m1, l1, r1, l1, raffTries(r1, y))
            else if IntMapView.shorter(m2, m1) then
              if !IntMapView.hasMatch(p1, p2, m2) then { took(); x }
              else if IntMapView.zero(p1, m2) then { dropped(); raffTries(x, l2) } else { dropped(); raffTries(x, r2) }
            else if p1 == p2 then binD(x, p1, m1, l1, r1, raffTries(l1, l2), raffTries(r1, r2))
            else { took(); x }

    // ---- literals: the cache state is machine state ------------------------------------------------------
    def literal(sv: SpaceValue): ITrie =
      if iLiteralIsCached(sv) then iLiteral(sv)                 // warm: one lookup, nothing counted
      else
        val hit = literals.get(sv)
        if hit != null then hit
        else { val tr = fromSpaceValue(sv); literals.put(sv, tr); tr }
    def literalStr(constant: String): ITrie =
      if iLiteralStrIsCached(constant) then iLiteralStr(constant)
      else literalStrs.getOrElseUpdate(constant, fromSpaceValue(LiteralStore.resolve(constant)))

    // ---- evalI ----------------------------------------------------------------------------------------------
    def eval(s: Space)(using pc: PathContext, ic: Map[SpaceMention, ITrie], rc: PartialFunction[RoutinePtr, Routine]): ITrie =
      inline def P(x: Path): PathValue = PathValue(Interner.uninternPath(pathItems(x)))
      t.add(TrieDispatch)
      s match
        case Empty => ITrie.empty
        case Mention(v) => ic.getOrElse(v, ITrie.empty)
        case Singleton(p) => singleton(pathItems(p))
        case Literal(sv) => literal(sv)
        case Union(a, b) => union(eval(a), eval(b))
        case Intersection(a, b) => intersection(eval(a), eval(b))
        case Subtraction(a, b) => subtraction(eval(a), eval(b))
        case Restriction(a, b) => restriction(eval(a), eval(b))
        case Raffination(a, b) => raffination(eval(a), eval(b))
        case Composition(a, b) => composition(eval(a), eval(b))
        case Wrap(src, p) => val ids = pathItems(p); wrap(ids, eval(src))
        case Unwrap(src, p) => val tr = eval(src); unwrap(tr, pathItems(p))
        case TailsUnion(src) => tailsUnion(eval(src))
        case TailsIntersection(src) => tailsIntersection(eval(src))
        case Range(x, lo, hi) => range(eval(x), lo, hi)
        case GroundedPS(p, f) => fromSpaceValue(f(P(p)))
        case GroundedSS(sp, f) => fromSpaceValue(f(toSpaceValue(eval(sp))))
        case Iteration(src, symbol, rest, body) =>
          val tr = eval(src)
          joinAll(tr.children.iterator.map { case (k, sub) =>
            t.add(LoopBodyEntry)
            eval(body)(using pc.grown(Map(symbol -> PathValue(Interner.unintern(k) :: Nil))), ic.updated(rest, sub), rc)
          }.toSeq)
        case Fixpoint(init, rec, body) =>
          var cur = eval(init)
          var stop = false
          while !stop do
            t.add(FixpointRound)
            val nxt = union(cur, eval(body)(using pc, ic.updated(rec, cur), rc))
            if equalT(nxt, cur) then stop = true else cur = nxt
          cur
        case Fold(src, initial, acc, symbol, rest, body, update) =>
          val tr = eval(src)
          var accv = PathValue(Interner.uninternPath(pathItems(initial)))
          var out = ITrie.empty
          for (k, sub) <- tr.children.iterator.toSeq.sortBy((kk, _) => kk) do
            t.add(LoopBodyEntry)
            val pctx = pc.grown(Map(acc -> accv, symbol -> PathValue(Interner.unintern(k) :: Nil)))
            val ictx = ic.updated(rest, sub)
            out = union(out, eval(body)(using pctx, ictx, rc))
            accv = PathValue(Interner.uninternPath(pathItems(update)(using pctx, ictx, rc)))
          out
        case Call(rp, refs, mentions) =>
          t.add(CallEntry)
          val refvs = refs.map(P)
          val mentionvs = mentions.map(m => eval(m))
          val Routine(_, refns, mentionns, body) = rc(rp)
          val pctx = PathContextMap(Map.from(refns.iterator zip refvs.iterator))
          val ictx = Map.from(mentionns.iterator zip mentionvs.iterator)
          body match
            case Union(l, Call(`rp`, `refs`, `mentions`))
              if (refs.iterator zip refvs.iterator).forall((p, pv) => pv == PathValue(Interner.uninternPath(pathItems(p)(using pctx, ictx, rc)))) &&
                 (mentions.iterator zip mentionvs.iterator).forall((m, tv) => equalT(tv, eval(m)(using pctx, ictx, rc))) =>
              eval(l)(using pctx, ictx, rc)
            case _ => eval(body)(using pctx, ictx, rc)
  end TrieSpec

  // ================================================================================================
  // 3.  THE GRAPH BACKEND — op-graph slots over the trie representation
  // ================================================================================================

  /** `execT`'s rules: one `GraphNodeDispatch` per executed slot, one `TrieOpEntry` per SPACE slot,
   *  one frame per scope entered (a loop's frame is allocated once and reused across its children),
   *  the trie algebra beneath — with `execT`'s own empty-left short circuits, which skip the algebra
   *  entirely and therefore its visits. */
  private final class GraphSpec(t: Tally, trie: TrieSpec):
    def run(g: RecursiveOpGraph, refs: Map[String, List[Int]], mentions: Map[String, ITrie],
            index: PartialFunction[String, RecursiveOpGraph]): ITrie =
      t.add(GraphFrameAllocation)
      val frame = new Array[Any | Null](g.nodes.length)
      for (nl, i) <- g.nodes.iterator.zipWithIndex do nl match
        case Left(Node("ExtractPathRef", name, _, _)) => refs.get(name).foreach(frame(i) = _)
        case Left(Node("ExtractSpaceMention", name, _, _)) => mentions.get(name).foreach(frame(i) = _)
        case _ => ()
      val stack = Stack(frame)
      exec(g, stack, index)
      stack.top.last.asInstanceOf[ITrie]

    def exec(rog: RecursiveOpGraph, stack: Stack[Array[Any | Null]], index: PartialFunction[String, RecursiveOpGraph]): Unit =
      val l = rog.level
      var c = 0
      val s = stack.top
      inline def pos = (l, c)
      extension (p: (Int, Int)) inline def sget: ITrie = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[ITrie]
      extension (p: (Int, Int)) inline def pget: List[Int] = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[List[Int]]
      while c < rog.nodes.length do
        t.add(GraphNodeDispatch)
        rog.nodes(c) match
          case Left(Node(op, constant, kind, inputs)) => kind match
            case "path" => s(c) = (op match
              case "ExtractPathRef" => pos.pget
              case "Constant" => internConstStr(constant)
              case "Concat" => inputs(0).pget ++ inputs(1).pget)
            case "space" => t.add(TrieOpEntry); s(c) = (op match
              case "Empty" => ITrie.empty
              case "Call" =>
                t.add(CallEntry)
                t.add(GraphFrameAllocation)
                val code = index(constant)
                val cstack = Stack(new Array[Any | Null](code.nodes.length))
                for (arg, i) <- inputs.zipWithIndex do cstack.top(i) = stack(stack.length - 1 - arg._1)(arg._2)
                exec(code, cstack, index)
                cstack.top.last.asInstanceOf[ITrie]
              case "ExtractSpaceMention" => pos.sget
              case "Singleton" => trie.singleton(inputs(0).pget)
              case "Literal" => trie.literalStr(constant)
              case "Union" => trie.union(inputs(0).sget, inputs(1).sget)
              case "Intersection" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else trie.intersection(a, inputs(1).sget)
              case "Subtraction" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else trie.subtraction(a, inputs(1).sget)
              case "Restriction" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else trie.restriction(a, inputs(1).sget)
              case "Raffination" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else trie.raffination(a, inputs(1).sget)
              case "Composition" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else trie.composition(a, inputs(1).sget)
              case "Wrap" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else trie.wrap(inputs(1).pget, a)
              case "Unwrap" => val a = inputs(0).sget; if a.isEmpty then ITrie.empty else trie.unwrap(a, inputs(1).pget)
              case "TailsUnion" => trie.tailsUnion(inputs(0).sget)
              case "TailsIntersection" => trie.tailsIntersection(inputs(0).sget)
              case "Range" => val Array(lo, hi) = constant.split(",", 2).map(_.toInt); trie.range(inputs(0).sget, lo, hi)
              case other => throw IllegalStateException(s"event semantics: unsupported flat op $other"))
          case Right(sg: RecursiveOpGraph) =>
            sg.root.operation match
              case "Iteration" =>
                val src = sg.root.inputs(0).sget
                t.add(GraphFrameAllocation)
                val frame = new Array[Any | Null](sg.nodes.length)
                val last = sg.nodes.length - 1
                stack.push(frame)
                var acc = ITrie.empty
                src.children.foreach { case (k, sub) =>
                  t.add(LoopBodyEntry)
                  frame(0) = k :: Nil; frame(1) = sub
                  exec(sg, stack, index)
                  acc = trie.union(acc, frame(last).asInstanceOf[ITrie])
                }
                stack.pop()
                s(c) = acc
              case "Fixpoint" =>
                t.add(GraphFrameAllocation)
                val frame = new Array[Any | Null](sg.nodes.length)
                val last = sg.nodes.length - 1
                stack.push(frame)
                var cur = sg.root.inputs(0).sget
                var done = false
                while !done do
                  t.add(FixpointRound)
                  frame(0) = cur
                  exec(sg, stack, index)
                  val nxt = trie.union(cur, frame(last).asInstanceOf[ITrie])
                  if trie.equalT(nxt, cur) then done = true else cur = nxt
                stack.pop()
                s(c) = cur
              case other => throw IllegalStateException(s"event semantics: unsupported subgraph root $other")
        c += 1
  end GraphSpec

  // ================================================================================================
  // 4.  THE ZIPPER BACKEND — virtual cursors, materialised top-down
  // ================================================================================================

  /** `transpileZ`/`materialize`'s rules.  One `ZipperBuild` per `Space` node lifted into a cursor;
   *  one `ZipperCursorRead` per `terminal`/`children`/`descend` query on a cursor, cascading through
   *  every virtual layer at the focus (with the executor's short-circuit order); one
   *  `ZipperMaterializeNode` + `FreshNode` per FORCED non-literal cursor node and none for a literal
   *  returned by pointer; `ReusedSpace` when a smart constructor recognises the same space on both
   *  sides; the `evalI` fallback for every control-flow constructor, counted as one hand-off plus that
   *  executable's own events.  The lazily-forced chains (`TailsUnion`, `TailsIntersection`, a deferred
   *  descent) read their source once, on the first query. */
  private final class ZipperSpec(t: Tally, trie: TrieSpec):
    import Space.*

    sealed trait ZC
    final class ZLit(val tr: ITrie) extends ZC
    final class ZOpaque(val m: SpaceMention) extends ZC
    final class ZUnion(val a: ZC, val b: ZC) extends ZC
    final class ZInter(val a: ZC, val b: ZC) extends ZC
    final class ZSub(val a: ZC, val b: ZC) extends ZC
    final class ZComp(val a: ZC, val b: ZC) extends ZC
    final class ZPrefix(val remaining: List[Int], val src: ZC) extends ZC
    final class ZRestr(val x: ZC, val prefixes: ZC) extends ZC
    final class ZTailsU(val src: ZC) extends ZC { var merged: ZC | Null = null }
    final class ZTailsI(val src: ZC) extends ZC { var merged: ZC | Null = null }
    final class ZDescend(val src: ZC, val remaining: List[Int]) extends ZC { var target: ZC | Null = null }

    val empty: ZC = new ZLit(ITrie.empty)
    private def read(): Unit = t.add(ZipperCursorRead)
    private def cannot(m: SpaceMention): Nothing =
      throw IllegalStateException(s"opaque zipper source `${m.s}` cannot be materialised")

    private def sameSpace(a: ZC, b: ZC): Boolean =
      (a eq b) || ((a, b) match { case (x: ZLit, y: ZLit) => x.tr eq y.tr; case _ => false })
    def union(a: ZC, b: ZC): ZC = if sameSpace(a, b) then { t.add(ReusedSpace); a } else new ZUnion(a, b)
    def intersection(a: ZC, b: ZC): ZC = if sameSpace(a, b) then { t.add(ReusedSpace); a } else new ZInter(a, b)
    def subtraction(a: ZC, b: ZC): ZC = if sameSpace(a, b) then { t.add(ReusedSpace); empty } else new ZSub(a, b)
    def restriction(x: ZC, prefixes: ZC): ZC =
      if containsOpaque(prefixes) then new ZRestr(x, prefixes)
      else if terminal(prefixes) then x else new ZRestr(x, prefixes)
    def raffination(x: ZC, y: ZC): ZC = new ZSub(x, restriction(x, y))
    def unwrap(src: ZC, p: List[Int]): ZC =
      if p.isEmpty then src
      else if containsOpaque(src) then new ZDescend(src, p)
      else p.foldLeft(src)((z, k) => descend(z, k))

    def containsOpaque(z: ZC): Boolean = z match
      case _: ZOpaque => true
      case _: ZLit => false
      case u: ZUnion => containsOpaque(u.a) || containsOpaque(u.b)
      case u: ZInter => containsOpaque(u.a) || containsOpaque(u.b)
      case u: ZSub => containsOpaque(u.a) || containsOpaque(u.b)
      case u: ZComp => containsOpaque(u.a) || containsOpaque(u.b)
      case u: ZPrefix => containsOpaque(u.src)
      case u: ZRestr => containsOpaque(u.x) || containsOpaque(u.prefixes)
      case u: ZTailsU => containsOpaque(u.src)
      case u: ZTailsI => containsOpaque(u.src)
      case u: ZDescend => containsOpaque(u.src)

    private def mergedU(z: ZTailsU): ZC =
      if z.merged == null then
        val cs = children(z.src)
        z.merged = if cs.isEmpty then empty else cs.valuesIterator.reduce(new ZUnion(_, _))
      z.merged.nn
    private def mergedI(z: ZTailsI): ZC =
      if z.merged == null then z.merged = new ZLit(trie.tailsIntersection(materialize(z.src)))
      z.merged.nn
    private def target(z: ZDescend): ZC =
      if z.target == null then z.target = z.remaining.foldLeft(z.src)((c, k) => descend(c, k))
      z.target.nn

    def terminal(z: ZC): Boolean = z match
      case l: ZLit => read(); l.tr.terminal
      case o: ZOpaque => cannot(o.m)
      case u: ZUnion => read(); terminal(u.a) || terminal(u.b)
      case u: ZInter => read(); terminal(u.a) && terminal(u.b)
      case u: ZSub => read(); terminal(u.a) && !terminal(u.b)
      case u: ZComp => read(); terminal(u.a) && terminal(u.b)
      case u: ZPrefix => read(); u.remaining.isEmpty && terminal(u.src)
      case u: ZRestr => terminal(u.x) && terminal(u.prefixes)
      case u: ZTailsU => read(); terminal(mergedU(u))
      case u: ZTailsI => read(); terminal(mergedI(u))
      case u: ZDescend => terminal(target(u))

    def children(z: ZC): IntMap[ZC] = z match
      case l: ZLit => read(); l.tr.children.transform((_, c) => new ZLit(c))
      case o: ZOpaque => cannot(o.m)
      case u: ZUnion =>
        read()
        val ac = children(u.a); val bc = children(u.b)
        ac.unionWith(bc, (_, x, y) => union(x, y))
      case u: ZInter =>
        read()
        val ac = children(u.a); val bc = children(u.b)
        ac.intersectionWith(bc, (_, x, y) => intersection(x, y))
      case u: ZSub =>
        read()
        val bc = children(u.b)
        val ac = children(u.a)
        ac.transform { (k, x) => bc.get(k) match
          case Some(y) => subtraction(x, y)
          case None => x }
      case u: ZComp =>
        read()
        val ac = children(u.a)
        val mapped = ac.transform((_, x) => new ZComp(x, u.b))
        if terminal(u.a) then
          val bc = children(u.b)
          mapped.unionWith(bc, (_, x, y) => union(x, y))
        else mapped
      case u: ZPrefix =>
        read()
        u.remaining match
          case Nil => children(u.src)
          case h :: tl => IntMap.singleton(h, new ZPrefix(tl, u.src))
      case u: ZRestr =>
        read()
        val xc = children(u.x); val pc = children(u.prefixes)
        xc.intersectionWith(pc, (_, xk, pk) => restriction(xk, pk))
      case u: ZTailsU => read(); children(mergedU(u))
      case u: ZTailsI => read(); children(mergedI(u))
      case u: ZDescend => children(target(u))

    def descend(z: ZC, k: Int): ZC = z match
      case l: ZLit => read(); l.tr.children.get(k) match { case Some(c) => new ZLit(c); case None => empty }
      case o: ZOpaque => cannot(o.m)
      case u: ZUnion => read(); union(descend(u.a, k), descend(u.b, k))
      case u: ZInter => read(); intersection(descend(u.a, k), descend(u.b, k))
      case u: ZSub => read(); subtraction(descend(u.a, k), descend(u.b, k))
      case u: ZComp =>
        read()
        val viaA = new ZComp(descend(u.a, k), u.b)
        if terminal(u.a) then union(viaA, descend(u.b, k)) else viaA
      case u: ZPrefix =>
        read()
        u.remaining match
          case Nil => descend(u.src, k)
          case h :: tl => if k == h then new ZPrefix(tl, u.src) else empty
      case u: ZRestr => read(); restriction(descend(u.x, k), descend(u.prefixes, k))
      case u: ZTailsU => read(); descend(mergedU(u), k)
      case u: ZTailsI => read(); descend(mergedI(u), k)
      case u: ZDescend => descend(target(u), k)

    def materialize(z: ZC): ITrie = z match
      case l: ZLit => l.tr
      case _ =>
        t.add(ZipperMaterializeNode)
        t.add(FreshNode)
        var ch = IntMap.empty[ITrie]
        children(z).foreach { (k, cz) => val c = materialize(cz); if c.nonEmpty then ch = ch.updated(k, c) }
        ITrie(terminal(z), ch)

    def transpile(s: Space)(using pc: PathContext, ic: Map[SpaceMention, ITrie], rc: PartialFunction[RoutinePtr, Routine]): ZC =
      t.add(ZipperBuild)
      s match
        case Empty => empty
        case Singleton(p) => new ZLit(trie.singleton(trie.pathItems(p)))
        case Literal(sv) => new ZLit(trie.literal(sv))
        case Mention(m) => ic.get(m) match { case Some(tr) => new ZLit(tr); case None => new ZOpaque(m) }
        case Union(x, y) => union(transpile(x), transpile(y))
        case Intersection(x, y) => intersection(transpile(x), transpile(y))
        case Subtraction(x, y) => subtraction(transpile(x), transpile(y))
        case Restriction(x, y) => restriction(transpile(x), transpile(y))
        case Raffination(x, y) => raffination(transpile(x), transpile(y))
        case Composition(x, y) => new ZComp(transpile(x), transpile(y))
        case Wrap(src, p) => new ZPrefix(trie.pathItems(p), transpile(src))
        case Unwrap(src, p) => unwrap(transpile(src), trie.pathItems(p))
        case TailsUnion(src) => new ZTailsU(transpile(src))
        case TailsIntersection(src) => new ZTailsI(transpile(src))
        case Range(x, lo, hi) => t.add(TrieOpEntry); new ZLit(trie.range(materialize(transpile(x)), lo, hi))
        case other => t.add(ZipperFallbackToEvalI); new ZLit(trie.eval(other))
  end ZipperSpec
end EventSemantics
