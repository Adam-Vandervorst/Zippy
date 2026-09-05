package morkl

import scala.collection.immutable.SortedMap
import scala.collection.mutable
import Lower.LenBounds

/** ==================================================================================================
 *  RESOURCE BOUNDS BY ABSTRACT INTERPRETATION OF THE EVENT SEMANTICS (tasks.md A4).
 *
 *  ==THE ONE IDEA==
 *  A lower and an upper bound on every counted event are TWO ABSTRACTIONS OF THE SAME COUNTED
 *  EXECUTION.  `EventSemantics` (A1) says, rule for rule, what one execution costs as a function of
 *  the operands' concrete structure; [[CostSem]] runs the SAME rules over the two-tier domain (A3):
 *
 *    * on the EXACT tier the rule is re-run on the abstract value — a single-valued node IS the
 *      operand's structure, so every structure-determined event (dispatches, `TrieNodeVisit`,
 *      `FreshTrieNode`, cursor reads, loop entries, rounds, the ordered slice) is computed EXACTLY;
 *      the two things the structure does not determine are bounded: the Patricia layout of a child map
 *      (it depends on the interner's ids — bounded by the `2k-1` node envelope, docs/SPATIAL_SEMANTICS.md
 *      §6) and POINTER SHARING between structurally equal subtries (the executor shares exactly what it
 *      took by pointer; the arena hash-conses everything) — so every trie walk is run twice, once with
 *      sharing MAXIMAL (a lower bound on work and allocation) and once with sharing only where the alias
 *      channel PROVES it (an upper bound), and the interval is the pair;
 *    * on the SUMMARIZED tier the rule is bounded from the correlated facts: the relational frontier
 *      (`SpatialFrontier.binary`: paired prefixes, rebuilt nodes, accepts, Patricia envelope) for the
 *      ring operations, fan-out and fibres for the loops, the histogram for the products;
 *    * a choice node distributes: the hull over its alternatives.
 *
 *  LOWER BOUNDS COME ONLY FROM MUST FACTS, UPPER BOUNDS ONLY FROM MAY FACTS: a lower endpoint is the
 *  minimum over every alternative and the maximal-sharing walk; an upper endpoint the maximum over
 *  every alternative and the no-sharing walk.  There is no backend or constructor special case that
 *  bypasses this — every rule is one of the arms below and its derivation is recorded.
 *
 *  ==N-ARY, REST CHAINS, FIXPOINTS, CALLS==
 *  An n-ary union/intersection is priced from its ORDERED LIVE FRONTIER — the distinct live operands the
 *  domain proves ([[DomainFacts.distinctLive]]), the per-level probe/scratch rules of `joinAll`/`meetAll`
 *  and the union-of-keys envelope of the Patricia descent — never from a flattened operand count.  A
 *  rest chain (`Iteration` over the tails of an `Iteration` …) is priced per prefix level: each level's
 *  fan-out is the fibre the domain gives at that prefix, so a 16-cell board contributes ONE tile per
 *  cell and no `Shape.top` (the puzzle15 requirement — `SpatialDomainCheck` has the fibre law,
 *  `SpatialCostCheck` the priced chain).  A fixpoint is interpreted over the IR's accumulator/delta
 *  recurrence (A2): the exact tier runs the rounds; the summarized tier bounds them by the accumulator's
 *  growth, prices the body at the seed (must) and at the post-fixpoint (may), and adds the terminating
 *  empty-delta round and the equality frontier.  A `Call` is priced by binding the parameters to the
 *  arguments' abstract values and pricing the body (A5 makes this compositional; here a recursive call
 *  outside the IR's reach is `⊤` with a note, never a guess).
 *
 *  ==THE DERIVATION DAG==
 *  Every reported interval carries a [[Derivation]]: the rule, the input facts it read, the backend
 *  parameter, the widening (if any) and the resulting bounds, with the children's derivations below.
 *  [[Derivation.render]] is deterministic (no ids, no timing), so two runs of one analysis print the same
 *  certificate — `SpatialPipelineCheck` holds it to that.
 *
 *  ==CERTIFICATE COST== the domain's own work — arena nodes, alternatives, summaries, widenings — is
 *  reported in the certificate's `analysis` section (nodes minted, choices, widenings) so the resource
 *  dimensions the analysis itself consumed are visible beside the program's.
 *  ================================================================================================== */

// ==================================================================================================
// EVENT BOUNDS
// ==================================================================================================

/** per-event intervals; absent = [0, 0] */
final case class EventBounds(m: Map[EffortEvent, Ivl]):
  def apply(e: EffortEvent): Ivl = m.getOrElse(e, Ivl.zero)
  def +(o: EventBounds): EventBounds =
    EventBounds((m.keySet ++ o.m.keySet).iterator.map(e => e -> Ivl(Ivl.add(apply(e).lo, o(e).lo), Ivl.add(apply(e).hi, o(e).hi))).toMap)
  /** `k` executions of this: multiply by an interval */
  def scale(k: Ivl): EventBounds =
    EventBounds(m.view.mapValues(i => Ivl(Ivl.mul(i.lo, k.lo), Ivl.mul(i.hi, k.hi))).toMap)
  /** the hull of two alternatives */
  def hull(o: EventBounds): EventBounds =
    EventBounds((m.keySet ++ o.m.keySet).iterator.map(e => e -> Ivl(apply(e).lo min o(e).lo, apply(e).hi max o(e).hi)).toMap)
  def component(c: EffortComponent): Ivl =
    EffortEvent.ofComponent(c).foldLeft(Ivl.zero)((acc, e) => Ivl(Ivl.add(acc.lo, apply(e).lo), Ivl.add(acc.hi, apply(e).hi)))
  def contains(ev: Events): Boolean = EffortEvent.values.forall(e => e.component == EffortComponent.Explain || { val i = apply(e); i.lo <= ev(e) && ev(e) <= i.hi })
  def violations(ev: Events): Vector[String] =
    EffortEvent.values.toVector.filter(e => e.component != EffortComponent.Explain).flatMap { e =>
      val i = apply(e); if i.lo <= ev(e) && ev(e) <= i.hi then None else Some(s"$e counted=${ev(e)} predicted=${i.show}") }
  def show: String = m.toVector.filter(_._2.hi > 0).sortBy(_._1.ordinal).map((e, i) => s"$e=${i.show}").mkString(" ")
  def showComponents: String =
    EffortEvent.calibratedComponents.map(c => s"$c=${component(c).show}").mkString(" ")

object EventBounds:
  val zero: EventBounds = EventBounds(Map.empty)
  def one(e: EffortEvent): EventBounds = EventBounds(Map(e -> Ivl(1, 1)))
  def n(e: EffortEvent, k: Long): EventBounds = EventBounds(Map(e -> Ivl(k, k)))
  def ivl(e: EffortEvent, i: Ivl): EventBounds = EventBounds(Map(e -> i))
  def of(kv: (EffortEvent, Ivl)*): EventBounds = EventBounds(kv.toMap)
  def exact(ev: Events): EventBounds = EventBounds(ev.counts.map((e, n) => e -> Ivl(n, n)))
  def sum(xs: Iterable[EventBounds]): EventBounds = xs.foldLeft(zero)(_ + _)
  def hullOf(xs: Iterable[EventBounds]): EventBounds = xs.reduceOption(_ hull _).getOrElse(zero)

// ==================================================================================================
// THE DERIVATION DAG
// ==================================================================================================

final case class Derivation(rule: String, facts: Vector[String], backend: Backend, widening: Option[String],
                            result: EventBounds, children: Vector[Derivation]):
  /** deterministic rendering: rules, facts and bounds, indented; nothing volatile */
  def render(indent: Int = 0): String =
    val pad = "  " * indent
    val head = s"$pad$rule [${backend.slug}]" + widening.map(w => s"  WIDENED: $w").getOrElse("")
    val fs = facts.map(f => s"$pad  · $f")
    val res = s"$pad  ⇒ ${result.showComponents}"
    (head +: fs :+ res).mkString("\n") + (if children.isEmpty then "" else "\n" + children.map(_.render(indent + 1)).mkString("\n"))
  def widenings: Vector[String] = widening.toVector ++ children.flatMap(_.widenings)
  def size: Int = 1 + children.map(_.size).sum

/** THE REPORT of one analysis on one backend */
final case class CostReport(backend: Backend, phase: ExecutionPhase, bounds: EventBounds, value: Abs,
                            derivation: Derivation, domain: DomainCert, notes: Vector[String],
                            analysisNodes: Int,
                            /** A5: (reused, computed) routine summaries over this analysis */
                            summaries: (Int, Int) = (0, 0),
                            /** the abstract RESULT's cardinality interval (D3: held to the proved state-space maximum) */
                            valueSize: Ivl = Ivl.unknown):
  /** A6: the transfer rules this result depends on (registry ids of proofs/spatial/REGISTRY.tsv) */
  def dependencies: Vector[String] = SpatialTransfers.dependenciesOf(derivation)
  /** A6: CERTIFIED iff every rule the derivation used is PROVED or a stated premise in
   *  proofs/spatial/STATUS.tsv (written by the independent checker); false when the table is absent
   *  or any dependency is OPEN.  `certifiedModulo` lists the premises it rests on. */
  def certified: Boolean = SpatialTransfers.status.nonEmpty && dependencies.forall(d => SpatialTransfers.status.get(d).exists(v => v != "OPEN"))
  def certifiedModulo: Vector[String] =
    dependencies.flatMap(d => SpatialTransfers.status.get(d).filter(v => v == "CHECKED-PREMISE" || v.startsWith("PROVED-MODULO")).map(v => s"$d ($v)"))
  def component(c: EffortComponent): Ivl = bounds.component(c)
  def work: Ivl = component(EffortComponent.Work)
  def alloc: Ivl = component(EffortComponent.Alloc)
  def rounds: Ivl = component(EffortComponent.Rounds)
  def touch: Ivl = component(EffortComponent.Touch)
  /** every calibrated component finite */
  def finite: Boolean = EffortEvent.calibratedComponents.forall(c => component(c).hi < Ivl.INF)
  /** the largest calibrated endpoint */
  def magnitude: Long = EffortEvent.calibratedComponents.map(c => component(c).hi).max
  def contains(ev: Events): Boolean = bounds.contains(ev)
  def show: String =
    s"[${backend.slug}/${phase.toString.toLowerCase}] ${bounds.showComponents}\n  value ${value.show.take(160)}\n  ${domain.show.linesIterator.next()}" +
      (if notes.isEmpty then "" else notes.map("\n  ! " + _).mkString)

// ==================================================================================================
// THE ANALYSIS
// ==================================================================================================

/** the abstract environment: values for mentions, path abstractions for refs */
final case class PathAbs(value: Option[PathValue], len: Ivl):
  def show: String = value.map(_.show).getOrElse(s"?len${len.show}")
object PathAbs:
  def known(v: PathValue): PathAbs = PathAbs(Some(v), Ivl(v.items.length, v.items.length))
  def opaque(len: Ivl): PathAbs = PathAbs(None, len)
  val unknown: PathAbs = PathAbs(None, Ivl(0, Ivl.INF))

final case class AEnv(spaces: Map[SpaceMention, Abs] = Map.empty, paths: Map[PathRef, PathAbs] = Map.empty,
                      active: Set[RoutinePtr] = Set.empty)

final class CostSem(val backend: Backend, val domain: Domain, val routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                    val phase: ExecutionPhase = ExecutionPhase.Warm, val maxRounds: Int = 64,
                    /** the declared input mentions: the objects whose counts the warm run has memoised */
                    val declared: Set[SpaceMention] = Set.empty,
                    /** A5: the summary store, shared with the nested instances a backend's rules create */
                    val store: CostSem.SummaryStore = new CostSem.SummaryStore):
  import EffortEvent.*
  import Space.*
  private val notes = mutable.LinkedHashSet.empty[String]
  private def note(s: String): Unit = notes += s
  private val INF = Ivl.INF
  private def top: Ivl = Ivl(0, INF)
  private def pt(n: Long): Ivl = Ivl(n, n)
  private def add(a: Ivl, b: Ivl): Ivl = Ivl(Ivl.add(a.lo, b.lo), Ivl.add(a.hi, b.hi))
  private def mul(a: Ivl, b: Ivl): Ivl = Ivl(Ivl.mul(a.lo, b.lo), Ivl.mul(a.hi, b.hi))
  private def hullI(a: Ivl, b: Ivl): Ivl = Ivl(a.lo min b.lo, a.hi max b.hi)
  private def sat(x: Long): Long = if x < 0 then INF else x

  // ---- A5: PARAMETRIC ROUTINE SUMMARIES AND SIMULTANEOUS SCC SYSTEMS --------------------------------------
  /** a summary is keyed by the CANONICAL ROUTINE IDENTITY (the body alpha-normalised over positional
   *  parameters, with its arity) and the ABSTRACT INPUT (each argument's structural key, whether it is a
   *  declared input object, the alias classes among the arguments, the path arguments) — never by a
   *  residual integer.  Two calls with the same key have the same abstract result, the same per-invocation
   *  events and the same derivation, so the second reuses the first. */
  import CostSem.{SummaryKey, Summary}
  private def summaries: mutable.Map[SummaryKey, Summary] = store.summaries
  /** (reused, computed) summary counts over this analysis (shared with the nested backends' instances) */
  def summaryStats: (Int, Int) = (store.hits, store.misses)
  private def routineIdentity(d: Routine): Space = store.identities.getOrElseUpdate(d.name, {
    val renaming = d.mentions.zipWithIndex.map((m, i) => m -> (Mention(SpaceMention(s"#p$i")): Space)).toMap
    Matching.canon(Subst.apply(d.body, renaming))
  })
  private def aliasClasses(args: Vector[Abs]): Vector[Int] =
    args.indices.toVector.map(i => args.indices.find(j => DomainFacts.mustAlias(args(j), args(i))).getOrElse(i))
  private def isDeclared(a: Abs): Boolean = a.alias match { case Alias.Is(m) => declared(m); case _ => false }
  /** the positive recursive component a routine belongs to, as the IR's simultaneous system (A2), memoised
   *  per routine; `None` when the routine is not recursive or its component is not a finite system */
  private def sccSystem(r: RoutinePtr, refs: Vector[Path], ms: Vector[Space]): Option[(Lowered, EqSystem)] =
    store.sccOf.getOrElseUpdate(r, {
      try DeltaIR.lower(Call(r, refs, ms), routines) match
        case Verdict.Accepted(p) => p.systemOfRoutine(r).map(sys => (p, sys))
        case _ => None
      catch case scala.util.control.NonFatal(_) => None
    })

  // ---- values -----------------------------------------------------------------------------------------
  private def size(x: XNode): Ivl = domain.size(x)
  private def len(x: XNode): LenBounds = domain.len(x)
  private def lenI(x: XNode): Ivl = { val l = len(x); if l.isEmpty then Ivl.zero else Ivl(l.lo, if l.hi >= LenBounds.INF then INF else l.hi) }
  /** how many trie nodes a value has: exact on the exact tier, `SpatialFacts.trieNodes` on a summary */
  private def nodes(x: XNode): Ivl = x match
    case t: XTrie => t.children.values.foldLeft(pt(1))((acc, c) => add(acc, nodes(c)))
    case ch: XChoice => ch.alts.map(nodes).reduce(hullI)
    case s: XSumm =>
      // every path contributes at most its length in nodes, plus the root: a cap the shape-based count
      // loses past the depth cap
      val cap = Ivl.add(1, Ivl.mul(s.t.size.hi, if s.t.len.hi >= LenBounds.INF then INF else s.t.len.hi))
      val n = SpatialFacts.trieNodes(s.t).toOption.getOrElse(top)
      Ivl(n.lo, math.min(n.hi, cap))
  /** paths that are not ε */
  private def headed(x: XNode): Ivl =
    val s = size(x)
    // ε may / must be present: it is the one path with no head
    val (epsMay, epsMust) = x match
      case t: XTrie => (t.terminal, t.terminal)
      case ch: XChoice => (ch.alts.exists { case t: XTrie => t.terminal; case _ => true }, ch.alts.forall { case t: XTrie => t.terminal; case _ => false })
      case sm: XSumm => (sm.t.shape.eps.mayBe, sm.t.shape.eps.mustBe)
    Ivl(Ivl.relu(s.lo - (if epsMay then 1L else 0L)), if s.hi >= INF then INF else Ivl.relu(s.hi - (if epsMust then 1L else 0L)))
  private def pathLen(p: Path, env: AEnv): Ivl = p match
    case Path.Constant(v) => pt(v.items.length)
    case Path.Deref(r) => env.paths.get(r).map(_.len).getOrElse(if r.lengthHint >= 0 then pt(r.lengthHint) else top)
    case Path.Concat(l, r) => add(pathLen(l, env), pathLen(r, env))
    case _ => top
  private def pathValue(p: Path, env: AEnv): Option[PathValue] = p match
    case Path.Constant(v) => Some(v)
    case Path.Deref(r) => env.paths.get(r).flatMap(_.value)
    case Path.Concat(l, r) => for a <- pathValue(l, env); b <- pathValue(r, env) yield PathValue(a.items ++ b.items)
    case _ => None
  private def pathNodes(p: Path): Long = p match
    case Path.Concat(l, r) => 1L + pathNodes(l) + pathNodes(r)
    case _ => 1L

  // ---- the walks over exact tries: sharing maximal (lower) or proven only (upper) ---------------------
  /** the per-node case of a ring operation relative to its operands */
  private enum Res:
    case Empty, Left, Right
    case Fresh(n: XNode)
  private final class Walk(share: Boolean):
    /** one merge of two child maps with `m` and `n` keys, `paired` of them common: the Patricia envelope */
    def patricia(m: Long, n: Long, paired: Long): EventBounds =
      if m == 0 && n == 0 then EventBounds.one(PatriciaVisit)
      else
        // a simultaneous descent visits at most every node of both Patricia trees (2k-1 each); every
        // paired key costs one entry at the bottom (an exact Tip/Tip meeting) or one probe
        val hiVisits = sat((2 * m - 1).max(0) + (2 * n - 1).max(0)).max(1)
        val loVisits = 1L
        EventBounds.of(PatriciaVisit -> Ivl(loVisits, hiVisits), PatriciaEntry -> Ivl(0, paired.max(m min n)))
    def sameObj(a: XNode, b: XNode, alias: Boolean): Boolean = alias || (share && (a eq b))

    def union(a: XNode, b: XNode, alias: Boolean): (Res, EventBounds) =
      var ev = EventBounds.one(TrieNodeVisit)
      if sameObj(a, b, alias) then
        ev += EventBounds.one(ReusedSubtrie)
        if domain.mustEmpty(a) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty)) else (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
      else if domain.mustEmpty(b) then
        if domain.mustEmpty(a) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty)) else (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
      else if domain.mustEmpty(a) then (Res.Right, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityRight -> pt(1)))
      else (a, b) match
        case (x: XTrie, y: XTrie) if share && x.children == y.children && !x.children.isEmpty =>
          // the two nodes may share ONE child-map object: `unionTries` returns at once (`a eq b`)
          ev += EventBounds.one(PatriciaVisit)
          val term = x.terminal || y.terminal
          if term == x.terminal then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
          else if term == y.terminal then (Res.Right, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityRight -> pt(1)))
          else (Res.Fresh(domain.arena.trie(term, x.children, Cause.Op("union", Vector(a.id, b.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case (x: XTrie, y: XTrie) =>
          val keys = x.children.keySet ++ y.children.keySet
          var allLeft = true; var allRight = true
          val kids = mutable.ArrayBuffer.empty[(PathItem, XNode)]
          for k <- keys do (x.children.get(k), y.children.get(k)) match
            case (Some(c), Some(dd)) if share && (c eq dd) =>
              // equal children under maximal sharing: one shared Patricia subtree, never descended
              kids += k -> c
            case (Some(c), Some(dd)) =>
              val (r, e) = union(c, dd, false); ev += e
              val out = pick(r, c, dd)
              kids += k -> out
              if r != Res.Left && !(share && (out eq c)) then allLeft = false
              if r != Res.Right && !(share && (out eq dd)) then allRight = false
            case (Some(c), None) => kids += k -> c; allRight = false
            case (None, Some(dd)) => kids += k -> dd; allLeft = false
            case _ => ()
          val paired = (x.children.keySet intersect y.children.keySet).size.toLong
          ev += patricia(x.children.size, y.children.size, paired) +
            EventBounds.ivl(SubtrieAcceptedByPointer, Ivl(0, (keys.size - paired).toLong))
          val term = x.terminal || y.terminal
          if allLeft && term == x.terminal then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
          else if allRight && term == y.terminal then (Res.Right, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityRight -> pt(1)))
          else (Res.Fresh(domain.arena.trie(term, SortedMap.from(kids), Cause.Op("union", Vector(a.id, b.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case _ => throw IllegalStateException("walk over non-trie")

    def inter(a: XNode, b: XNode, alias: Boolean): (Res, EventBounds) =
      var ev = EventBounds.one(TrieNodeVisit)
      if sameObj(a, b, alias) then
        ev += EventBounds.one(ReusedSubtrie)
        if domain.mustEmpty(a) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty)) else (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
      else if domain.mustEmpty(a) || domain.mustEmpty(b) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
      else (a, b) match
        case (x: XTrie, y: XTrie) if share && x.children == y.children && !x.children.isEmpty =>
          // the two nodes may share ONE child-map object: `intersectTries` returns at once (`a eq b`)
          ev += EventBounds.one(PatriciaVisit)
          val term = x.terminal && y.terminal
          if term == x.terminal then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
          else if term == y.terminal then (Res.Right, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityRight -> pt(1)))
          else (Res.Fresh(domain.arena.trie(term, x.children, Cause.Op("inter", Vector(a.id, b.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case (x: XTrie, y: XTrie) =>
          val keys = x.children.keySet intersect y.children.keySet
          var allLeft = true; var allRight = keys.size == y.children.size
          if keys.size != x.children.size then allLeft = false
          val kids = mutable.ArrayBuffer.empty[(PathItem, XNode)]
          for k <- keys do
            val (c, dd) = (x.children(k), y.children(k))
            if share && (c eq dd) then kids += k -> c
            else
              val (r, e) = inter(c, dd, false); ev += e
              val out = pick(r, c, dd)
              if !domain.mustEmpty(out) then kids += k -> out else { allLeft = false; allRight = false }
              if r != Res.Left && !(share && (out eq c)) then allLeft = false
              if r != Res.Right && !(share && (out eq dd)) then allRight = false
          ev += patricia(x.children.size, y.children.size, keys.size.toLong) +
            EventBounds.ivl(SubtrieRejectedByPointer, Ivl(0, (x.children.size + y.children.size - 2 * keys.size).toLong.max(0)))
          val term = x.terminal && y.terminal
          if kids.isEmpty && !term then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
          else if allLeft && term == x.terminal then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
          else if allRight && term == y.terminal then (Res.Right, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityRight -> pt(1)))
          else (Res.Fresh(domain.arena.trie(term, SortedMap.from(kids), Cause.Op("inter", Vector(a.id, b.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case _ => throw IllegalStateException("walk over non-trie")

    def sub(a: XNode, b: XNode, alias: Boolean): (Res, EventBounds) =
      var ev = EventBounds.one(TrieNodeVisit)
      if sameObj(a, b, alias) then (Res.Empty, ev + EventBounds.of(ReusedSubtrie -> pt(1), AlgebraEmpty -> pt(1)))
      else if domain.mustEmpty(a) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
      else if domain.mustEmpty(b) then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
      else (a, b) match
        case (x: XTrie, y: XTrie) if share && x.children == y.children && !x.children.isEmpty =>
          // the two nodes may share ONE child-map object: `diffTries` returns at once (`a eq b`)
          ev += EventBounds.one(PatriciaVisit)
          val term = x.terminal && !y.terminal
          if !term then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
          else (Res.Fresh(domain.arena.trie(true, SortedMap.empty, Cause.Op("sub", Vector(a.id, b.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case (x: XTrie, y: XTrie) =>
          var allLeft = true
          val kids = mutable.ArrayBuffer.empty[(PathItem, XNode)]
          var paired = 0L
          for (k, c) <- x.children do y.children.get(k) match
            case Some(dd) if share && (c eq dd) => paired += 1; allLeft = false   // shared subtree: dropped whole
            case Some(dd) =>
              paired += 1
              val (r, e) = sub(c, dd, false); ev += e
              val out = pick(r, c, dd)
              if !domain.mustEmpty(out) then kids += k -> out else allLeft = false
              if r != Res.Left && !(share && (out eq c)) then allLeft = false
            case None => kids += k -> c
          ev += patricia(x.children.size, y.children.size, paired) +
            EventBounds.ivl(SubtrieAcceptedByPointer, Ivl(0, (x.children.size - paired).max(0)))
          val term = x.terminal && !y.terminal
          if kids.isEmpty && !term then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
          else if allLeft && term == x.terminal then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
          else (Res.Fresh(domain.arena.trie(term, SortedMap.from(kids), Cause.Op("sub", Vector(a.id, b.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case _ => throw IllegalStateException("walk over non-trie")

    def restrict(x0: XNode, p0: XNode, alias: Boolean): (Res, EventBounds) =
      var ev = EventBounds.one(TrieNodeVisit)
      if sameObj(x0, p0, alias) then
        ev += EventBounds.one(ReusedSubtrie)
        if domain.mustEmpty(x0) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty)) else (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
      else if domain.mustEmpty(x0) || domain.mustEmpty(p0) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
      else (x0, p0) match
        case (x: XTrie, p: XTrie) =>
          if p.terminal then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
          else
            val keys = x.children.keySet intersect p.children.keySet
            var allLeft = keys.size == x.children.size && !x.terminal
            var allRight = keys.size == p.children.size
            val kids = mutable.ArrayBuffer.empty[(PathItem, XNode)]
            for k <- keys do
              val (c, dd) = (x.children(k), p.children(k))
              val (r, e) = restrict(c, dd, false); ev += e
              val out = pick(r, c, dd)
              if !domain.mustEmpty(out) then kids += k -> out else { allLeft = false; allRight = false }
              if r != Res.Left && !(share && (out eq c)) then allLeft = false
              if r != Res.Right && !(share && (out eq dd)) then allRight = false
            ev += patricia(x.children.size, p.children.size, keys.size.toLong) +
              EventBounds.ivl(SubtrieRejectedByPointer, Ivl(0, (x.children.size + p.children.size - 2 * keys.size).toLong.max(0)))
            if kids.isEmpty then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
            else if allLeft then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
            else if allRight then (Res.Right, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityRight -> pt(1)))
            else (Res.Fresh(domain.arena.trie(false, SortedMap.from(kids), Cause.Op("restrict", Vector(x0.id, p0.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case _ => throw IllegalStateException("walk over non-trie")

    def raff(x0: XNode, y0: XNode, alias: Boolean): (Res, EventBounds) =
      var ev = EventBounds.one(TrieNodeVisit)
      if domain.mustEmpty(x0) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
      else if sameObj(x0, y0, alias) then (Res.Empty, ev + EventBounds.of(ReusedSubtrie -> pt(1), AlgebraEmpty -> pt(1)))
      else if domain.mustEmpty(y0) then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
      else (x0, y0) match
        case (x: XTrie, y: XTrie) if share && x.children == y.children && !x.children.isEmpty =>
          // the two nodes may share ONE child-map object: `raffTries` returns at once (`a eq b`)
          ev += EventBounds.one(PatriciaVisit)
          val term = x.terminal
          if !term then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
          else (Res.Fresh(domain.arena.trie(true, SortedMap.empty, Cause.Op("raff", Vector(x0.id, y0.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case (x: XTrie, y: XTrie) =>
          if y.terminal then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
          else
            var allLeft = true
            val kids = mutable.ArrayBuffer.empty[(PathItem, XNode)]
            var paired = 0L
            for (k, c) <- x.children do y.children.get(k) match
              case Some(dd) if share && (c eq dd) => paired += 1; allLeft = false   // shared subtree: dropped whole
              case Some(dd) =>
                paired += 1
                val (r, e) = raff(c, dd, false); ev += e
                val out = pick(r, c, dd)
                if !domain.mustEmpty(out) then kids += k -> out else allLeft = false
                if r != Res.Left && !(share && (out eq c)) then allLeft = false
              case None => kids += k -> c
            ev += patricia(x.children.size, y.children.size, paired) +
              EventBounds.ivl(SubtrieAcceptedByPointer, Ivl(0, (x.children.size - paired).max(0)))
            val term = x.terminal
            if kids.isEmpty && !term then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
            else if allLeft then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
            else (Res.Fresh(domain.arena.trie(term, SortedMap.from(kids), Cause.Op("raff", Vector(x0.id, y0.id)))), ev + EventBounds.of(AlgebraBespoke -> pt(1), FreshTrieNode -> pt(1)))
        case _ => throw IllegalStateException("walk over non-trie")

    def comp(a: XNode, b: XNode): (Res, EventBounds) =
      var ev = EventBounds.one(TrieNodeVisit)
      if domain.mustEmpty(a) || domain.mustEmpty(b) then (Res.Empty, ev + EventBounds.one(AlgebraEmpty))
      else (a, b) match
        case (x: XTrie, y: XTrie) =>
          if y.terminal && y.children.isEmpty then (Res.Left, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityLeft -> pt(1)))
          else if x.terminal && x.children.isEmpty then (Res.Right, ev + EventBounds.of(SubtrieAcceptedByPointer -> pt(1), AlgebraIdentityRight -> pt(1)))
          else
            val kids = mutable.ArrayBuffer.empty[(PathItem, XNode)]
            for (k, c) <- x.children do
              val (r, e) = comp(c, b); ev += e
              val out = pick(r, c, b)
              if !domain.mustEmpty(out) then kids += k -> out
            ev += EventBounds.one(FreshTrieNode)                       // the mapped node
            val mapped = domain.arena.trie(false, SortedMap.from(kids), Cause.Op("comp", Vector(a.id, b.id)))
            if x.terminal then
              val (r2, e2) = union(mapped, y, false); ev += e2
              (Res.Fresh(pick(r2, mapped, y)), ev + EventBounds.one(AlgebraBespoke))
            else (Res.Fresh(mapped), ev + EventBounds.one(AlgebraBespoke))
        case _ => throw IllegalStateException("walk over non-trie")

    def pick(r: Res, a: XNode, b: XNode): XNode = r match
      case Res.Empty => domain.arena.empty
      case Res.Left => a
      case Res.Right => b
      case Res.Fresh(n) => n

    /** `joinAll`/`meetAll` over exact operands: the ordered live frontier priced per level */
    def nary(ops: Vector[XNode], join: Boolean, aliasGroups: Vector[Int]): (XNode, EventBounds) =
      var ev = EventBounds.one(TrieNodeVisit)
      // liveDistinct: dedup by object — under `share`, structural equality; else by alias group
      val live = mutable.ArrayBuffer.empty[XNode]
      val seenGroups = mutable.ArrayBuffer.empty[Int]
      var probes = 0L
      var idx = 0
      if !join then
        // meetAll's empty pre-scan
        var i = 0; var found = false
        while i < ops.length && !found do { found = domain.mustEmpty(ops(i)); i += 1 }
        ev += EventBounds.n(NaryOperandProbe, i.toLong)
        if found then return (domain.arena.empty, ev + EventBounds.one(SubtrieRejectedByPointer))
      for o <- ops do
        if join && domain.mustEmpty(o) then ()
        else
          val dup = live.indices.exists(j => (share && (live(j) eq o)) || (aliasGroups(idx) >= 0 && seenGroups(j) == aliasGroups(idx)))
          val scanned = if live.length > 24 then 1L else (if dup then live.indices.indexWhere(j => (share && (live(j) eq o)) || (aliasGroups(idx) >= 0 && seenGroups(j) == aliasGroups(idx))) + 1L else live.length.toLong)
          probes += scanned
          if dup then ev += EventBounds.one(ReusedSubtrie)
          else
            live += o; seenGroups += aliasGroups(idx)
            if live.length == 25 then { ev += EventBounds.n(NaryScratchSlot, 2L * 26); probes += 25 }
        idx += 1
      ev += EventBounds.n(NaryOperandProbe, probes) + EventBounds.n(NaryScratchSlot, math.max(4L, 4L * live.length))
      if live.isEmpty then (domain.arena.empty, ev)
      else if live.length == 1 then (live(0), ev + EventBounds.one(SubtrieAcceptedByPointer))
      else if live.length == 2 then
        val (r, e) = if join then union(live(0), live(1), false) else inter(live(0), live(1), false)
        (pick(r, live(0), live(1)), ev + e)
      else
        // the n-ary descent over k live child maps: priced by the union-of-keys envelope, per level
        val k = live.length.toLong
        val tries = live.collect { case t: XTrie => t }
        val term = if join then tries.exists(_.terminal) else tries.forall(_.terminal)
        ev += EventBounds.n(NaryOperandProbe, if join then k else math.min(tries.indexWhere(!_.terminal) + 1L, k).max(1L)) +
          EventBounds.n(NaryScratchSlot, k) + EventBounds.n(NaryOperandProbe, k)
        // the result value: the exact fold
        val value = if join then live.reduce(domain.union) else live.reduce(domain.inter)
        val keyUnion = tries.flatMap(_.children.keySet).toSet.size.toLong
        val perLevelCalls = Ivl(1, sat(2 * keyUnion - 1).max(1))
        // every common prefix below the root is one more `joinAll`/`meetAll` on the children found
        // there, with its own `liveDistinct`: at most one per operand node below the roots
        val deeper = Ivl(0, tries.map(t => (nodes(t).hi - 1).max(0)).sum)
        val calls = add(perLevelCalls, deeper)
        val perCallProbes = Ivl(0, k * 3 + (if k > 24 then k else k * (k - 1) / 2))
        val perCallScratch = Ivl(k, 3 * k + (if k > 24 then 2 * (k + 1) else 0))
        ev += EventBounds.of(
          PatriciaVisit -> Ivl(1, sat(mul(calls, perLevelCalls).hi)),
          NaryOperandProbe -> mul(calls, perCallProbes),
          NaryScratchSlot -> mul(calls, perCallScratch),
          ReusedSubtrie -> Ivl(0, mul(calls, pt(k)).hi),
          AlgebraIdentityLeft -> Ivl(0, calls.hi), AlgebraIdentityRight -> Ivl(0, calls.hi), AlgebraBespoke -> Ivl(0, calls.hi), AlgebraEmpty -> Ivl(0, calls.hi),
          // below the child maps: the per-key groups are themselves n-ary joins/meets of the children
          TrieNodeVisit -> Ivl(0, sat(2 * tries.map(t => (nodes(t).hi - 1).max(0)).sum)),
          FreshTrieNode -> Ivl(0, sat(nodes(value).hi)),
          SubtrieAcceptedByPointer -> Ivl(0, add(calls, pt(keyUnion + 1)).hi),
          SubtrieRejectedByPointer -> Ivl(0, add(calls, pt(keyUnion + 1)).hi))
        (value, ev)
  end Walk
  private val walkLo = new Walk(share = true)
  private val walkHi = new Walk(share = false)

  /** run a trie-level operation on exact single-valued operands: the interval between the two walks */
  private def exactBinary(kind: String, a: Abs, b: Abs)(f: (Walk, XNode, XNode, Boolean) => (Res, EventBounds)): (Abs, EventBounds) =
    val alias = DomainFacts.mustAlias(a, b)
    val (rLo, eLo) = f(walkLo, a.node, b.node, alias)
    val (rHi, eHi) = f(walkHi, a.node, b.node, alias)
    val out = walkHi.pick(rHi, a.node, b.node)
    val al = rHi match
      case Res.Left => a.alias
      case Res.Right => b.alias
      case Res.Empty => Alias.Fresh
      case Res.Fresh(_) => Alias.Fresh
    (Abs(out, al), EventBounds((eLo.m.keySet ++ eHi.m.keySet).iterator.map(e => e -> Ivl(eLo(e).lo min eHi(e).lo, eLo(e).hi max eHi(e).hi)).toMap))

  // ---- ITrie.range on the exact tier: the count walk, then the order-statistic slice ----------------
  /** `cached`: the operand is an input object whose terminal counts a previous run memoised (warm) */
  private def rangeTrie(a: Abs, lo: Int, hi: Int, cached: Boolean): (Abs, EventBounds) =
    a.node match
      case t: XTrie if domain.exact(t) =>
        var ev = EventBounds.one(TrieNodeVisit)
        val n = size(t).lo
        // `t.count`: every node whose count is not memoised is visited once; a fresh result shares its
        // input children by pointer, so at least the root and at most every node
        // the shared `ITrie.empty`/`ITrie.epsilon` constants are counted once per process; the zipper's
        // materialisation may hand `range` a FRESH empty node instead
        // (a terminal-only node is NOT `ITrie.epsilon`: the algebra builds it fresh with `node(true, ∅)`)
        val constant = t.children.isEmpty && !t.terminal && backend != Backend.Zipper
        ev += EventBounds.ivl(TrieNodeVisit, if cached || constant then Ivl.zero else Ivl(0, nodes(t).hi max 1))
        val (lo2, hi2) = RangeBounds.normalize(n.toInt, lo, hi)
        if hi2 <= lo2 then (domain.empty, ev)
        else if lo2 == 0 && hi2 == n then (a, ev + EventBounds.one(SubtrieAcceptedByPointer))
        else
          val (r, e) = sliceTrie(t, lo2, hi2, cached)
          (Abs(r, Alias.Fresh), ev + e)
      case ch: XChoice =>
        val rs = ch.alts.map(x => rangeTrie(Abs(x, a.alias), lo, hi, cached))
        (Abs(domain.arena.choice(rs.map(_._1.node), Cause.Op("range", Vector(a.node.id))), Alias.Unknown), EventBounds.hullOf(rs.map(_._2)))
      case _ if size(a.node).hi == 0 =>
        // a must-empty summarized operand: the entry visit, the (memoised or one-node) count, nothing sliced
        (domain.empty, EventBounds.ivl(TrieNodeVisit, Ivl(1, 2)))
      case _ =>
        val out = domain.rangeA(a, lo, hi)
        val n = nodes(a.node)
        val full = SpatialCost.rangeIsIdentity(lo, hi)
        val countWalk = if cached then Ivl.zero else Ivl(0, n.hi)
        val slice = if full then EventBounds.one(SubtrieAcceptedByPointer)
                    else EventBounds.of(TrieNodeVisit -> Ivl(0, add(n, nodes(out.node)).hi), FreshTrieNode -> Ivl(0, nodes(out.node).hi),
                                        SubtrieAcceptedByPointer -> Ivl(0, add(n, pt(1)).hi), SubtrieRejectedByPointer -> Ivl(0, n.hi))
        (out, EventBounds.ivl(TrieNodeVisit, add(pt(1), countWalk)) + slice)

  /** `ITrie.slice`, in canonical (string) order — the order does not depend on the interner */
  private def sliceTrie(n: XTrie, lo: Int, hi: Int, cached: Boolean): (XNode, EventBounds) =
    var ev = EventBounds.one(TrieNodeVisit)
    val cnt = size(n).lo
    if hi <= lo then (domain.arena.empty, ev)
    else if lo <= 0 && hi >= cnt then (n, ev + EventBounds.one(SubtrieAcceptedByPointer))
    else
      // `ordered(n)` reads every child's count: a walk over the uncached ones
      val kids = n.children.toVector
      if !cached then ev += EventBounds.ivl(TrieNodeVisit, Ivl(0, kids.map(k => nodes(k._2).hi).sum))
      val k = kids.length
      val offsets = new Array[Long](k + 1)
      var acc = if n.terminal then 1L else 0L
      for i <- 0 until k do { offsets(i) = acc; acc += size(kids(i)._2).lo }
      offsets(k) = acc
      val term = n.terminal && lo <= 0
      var i = if lo <= 0 then 0 else { var a = 0; var b = k - 1; while a < b do { val mid = (a + b) >>> 1; if offsets(mid + 1) <= lo then a = mid + 1 else b = mid }; a }
      if i > 0 then ev += EventBounds.n(SubtrieRejectedByPointer, i.toLong)
      val out = mutable.ArrayBuffer.empty[(PathItem, XNode)]
      while i < k && offsets(i) < hi do
        val base = offsets(i).toInt
        val (c, e) = sliceTrie(kids(i)._2.asInstanceOf[XTrie], lo - base, hi - base, cached)
        ev += e
        if !domain.mustEmpty(c) then out += kids(i)._1 -> c
        i += 1
      if i < k then ev += EventBounds.n(SubtrieRejectedByPointer, (k - i).toLong)
      if out.isEmpty && !term then (domain.arena.empty, ev)
      else (domain.arena.trie(term, SortedMap.from(out), Cause.Op("range", Vector(n.id))), ev + EventBounds.one(FreshTrieNode))

  // ---- the frontier for summarized operands ------------------------------------------------------------------
  private def frontierEvents(op: FrontierOp, a: Abs, b: Abs): EventBounds =
    val f = SpatialFrontier.binary(op, domain.summary(a.node), domain.summary(b.node), DomainFacts.mustAlias(a, b), FrontierConfig.interned)
    // the MUST side of the frontier holds only when the two operands share no sub-object — two distinct
    // INPUTS (independently materialised); a result shares its inputs' children by pointer and `eq` then
    // skips paired prefixes the frontier counts
    val independent = (a.alias, b.alias) match
      case (Alias.Is(m), Alias.Is(n)) => m != n
      case _ => false
    val q = if f.isFallback then Ivl(1, add(nodes(a.node), nodes(b.node)).hi)
            else Ivl(if independent then f.depth.pairedTotal.lo max 1 else 1, f.depth.pairedTotal.hi max 1)
    val fresh = if f.isFallback then Ivl(0, add(nodes(a.node), nodes(b.node)).hi) else Ivl(0, f.rebuilt.hi)
    val pat = if f.isFallback then Ivl(0, sat(2 * add(nodes(a.node), nodes(b.node)).hi)) else Ivl(0, f.patricia.hi max q.hi)
    EventBounds.of(TrieNodeVisit -> q, FreshTrieNode -> fresh, PatriciaVisit -> pat,
                   PatriciaEntry -> Ivl(0, pat.hi), SubtrieAcceptedByPointer -> Ivl(0, add(q, pat).hi),
                   SubtrieRejectedByPointer -> Ivl(0, add(q, pat).hi), AlgebraBespoke -> Ivl(0, q.hi),
                   AlgebraIdentityLeft -> Ivl(0, q.hi), AlgebraIdentityRight -> Ivl(0, q.hi), AlgebraEmpty -> Ivl(0, q.hi), ReusedSubtrie -> Ivl(0, q.hi))

  private def isExactTrie(x: XNode): Boolean = x match
    case t: XTrie => domain.exact(t)
    case _ => false

  /** a binary trie operation, over the tiers */
  private def trieBinary(kind: String, op: FrontierOp, a: Abs, b: Abs, dom: (XNode, XNode) => XNode)
                        (walk: (Walk, XNode, XNode, Boolean) => (Res, EventBounds)): (Abs, EventBounds, Vector[String]) =
    if isExactTrie(a.node) && isExactTrie(b.node) then
      val (r, e) = exactBinary(kind, a, b)(walk)
      (r, e, Vector(s"exact operands: the algebra's own recursion, sharing ∈ [maximal, proven]; Patricia by the 2k-1 envelope"))
    else
      (a.node, b.node) match
        case (_: XChoice, _) | (_, _: XChoice) if !a.node.isInstanceOf[XSumm] && !b.node.isInstanceOf[XSumm] =>
          val as = a.node match { case ch: XChoice => ch.alts; case n => Vector(n) }
          val bs = b.node match { case ch: XChoice => ch.alts; case n => Vector(n) }
          if as.length.toLong * bs.length <= domain.budget.alternatives && as.forall(isExactTrie) && bs.forall(isExactTrie) then
            val rs = for x <- as; y <- bs yield exactBinary(kind, Abs(x, a.alias), Abs(y, b.alias))(walk)
            val value = domain.arena.choice(rs.map(_._1.node), Cause.Op(kind, Vector(a.node.id, b.node.id)))
            (Abs(value, Alias.Unknown), EventBounds.hullOf(rs.map(_._2)), Vector(s"${rs.length} alternative pairs, hull"))
          else
            val value = dom(a.node, b.node)
            (Abs(value, Alias.Unknown), frontierEvents(op, a, b), Vector("alternatives past the budget: the relational frontier over the summaries"))
        case _ =>
          val value = dom(a.node, b.node)
          val al = if value eq a.node then a.alias else if value eq b.node then b.alias else Alias.Unknown
          (Abs(value, al), frontierEvents(op, a, b), Vector(s"summarized operand: SpatialFrontier.binary(${op.show}) — paired prefixes |Q|, rebuilt, Patricia envelope"))

  // ---- literal / singleton construction on the trie backends --------------------------------------------------
  private def singletonTrie(l: Ivl): EventBounds =
    EventBounds.of(TrieNodeVisit -> pt(1), FreshTrieNode -> l)
  private def coldLiteral(v: Abs): EventBounds =
    // fromSpaceValue: a left fold of unions of singletons — one singleton per path plus a union each
    val n = size(v.node); val l = lenI(v.node)
    val per = add(l, pt(2))                                   // the singleton's nodes plus the union's fresh root
    val hi = add(mul(n, per), pt(1)).hi
    EventBounds.of(TrieNodeVisit -> Ivl(n.lo, hi), FreshTrieNode -> Ivl(0, hi), PatriciaVisit -> Ivl(0, sat(2 * hi)), PatriciaEntry -> Ivl(0, sat(2 * hi)),
                   AlgebraBespoke -> Ivl(0, hi), AlgebraIdentityLeft -> Ivl(0, hi), AlgebraIdentityRight -> Ivl(0, hi), AlgebraEmpty -> Ivl(0, n.hi),
                   SubtrieAcceptedByPointer -> Ivl(0, hi), SubtrieRejectedByPointer -> Ivl(0, hi), ReusedSubtrie -> Ivl(0, hi))

  // ==============================================================================================
  // THE INTERPRETER
  // ==============================================================================================
  private def D(rule: String, facts: Vector[String], ev: EventBounds, kids: Vector[Derivation], widening: Option[String] = None): Derivation =
    Derivation(rule, facts, backend, widening, ev, kids)

  private def dispatch: EventBounds = backend match
    case Backend.Reference => EventBounds.one(AstDispatch)
    case Backend.Trie => EventBounds.one(TrieDispatch)
    case Backend.Graph => EventBounds.of(GraphNodeDispatch -> pt(1), TrieOpEntry -> pt(1))
    case Backend.Zipper => EventBounds.one(ZipperBuild)
  private def pathDispatch(p: Path): EventBounds = backend match
    case Backend.Reference => EventBounds.n(PathDispatch, pathNodes(p))
    case Backend.Trie | Backend.Zipper => EventBounds.n(TriePathDispatch, pathNodes(p))
    case Backend.Graph => EventBounds.n(GraphNodeDispatch, pathNodes(p) - (if p.isInstanceOf[Path.Deref] then 1 else 0))

  /** ANALYSE a term: its abstract value, its event bounds, its derivation */
  def analyze(s: Space, env: AEnv): (Abs, EventBounds, Derivation) = backend match
    case Backend.Zipper => zipper(s, env)
    case _ => go(s, env)

  private def go(s: Space, env: AEnv): (Abs, EventBounds, Derivation) =
    val ref = backend == Backend.Reference
    s match
      case Empty => (domain.empty, dispatch, D("Empty", Vector.empty, dispatch, Vector.empty))
      case Mention(m) =>
        val v0 = env.spaces.getOrElse(m, { note(s"input ${m.s} undeclared: ⊤"); Abs(domain.arena.summ(SpatialType.top, Cause.Input(m)), Alias.Is(m)) })
        val v = if Mutation.active("drop-alias") then v0.copy(alias = Alias.Fresh) else v0   // E1 mutation site
        (v, dispatch, D(s"Mention ${m.s}", Vector(s"value ${v.show.take(80)}"), dispatch, Vector.empty))
      case Literal(v) =>
        val a = domain.literal(v)
        val ev = dispatch + (if !ref && phase == ExecutionPhase.Cold then coldLiteral(a) else EventBounds.zero)
        (a, ev, D("Literal", Vector(s"|v|=${v.paths.size}", s"phase $phase"), ev, Vector.empty))
      case Singleton(p) =>
        val l = pathLen(p, env)
        val value = pathValue(p, env) match
          case Some(v) => Abs(domain.alpha(SpaceValue(Set(v)), Cause.Op("singleton", Vector.empty)), Alias.Fresh)
          case None => Abs(domain.arena.summ(SpatialType(Shape.oneUnknownPath(LenBounds(l.lo, if l.hi >= INF then LenBounds.INF else l.hi)), SpaceType.boundedExact(LenBounds(l.lo, if l.hi >= INF then LenBounds.INF else l.hi), 1L)), Cause.Op("singleton", Vector.empty)), Alias.Fresh)
        val ev = dispatch + pathDispatch(p) + (if ref then EventBounds.one(FreshPath) else singletonTrie(l))
        (value, ev, D("Singleton", Vector(s"path ${pathValue(p, env).map(_.show).getOrElse("?")} len ${l.show}"), ev, Vector.empty))
      case Union(x, y) => binaryOp("Union", FrontierOp.Union, x, y, env, domain.unionA, (w, a, b, al) => w.union(a, b, al))
      case Intersection(x, y) => binaryOp("Intersection", FrontierOp.Intersection, x, y, env, domain.interA, (w, a, b, al) => w.inter(a, b, al))
      case Subtraction(x, y) => binaryOp("Subtraction", FrontierOp.Subtraction, x, y, env, domain.subA, (w, a, b, al) => w.sub(a, b, al))
      case Restriction(x, y) =>
        if ref then
          val (a, ea, da) = go(x, env); val (b, eb, db) = go(y, env)
          val out = domain.restrictA(a, b)
          val cmp = restrictionComparisons(a, b)
          val ev = dispatch + ea + eb + cmp
          (out, ev, D("Restriction/eval", Vector(s"comparisons ${cmp(PathItemComparison).show}"), ev, Vector(da, db)))
        else binaryOp("Restriction", FrontierOp.Restriction, x, y, env, domain.restrictA, (w, a, b, al) => w.restrict(a, b, al))
      case Raffination(x, y) =>
        if ref then
          // eval desugars to Subtraction(x, Restriction(x, y)): x is evaluated TWICE
          val (a, ea, da) = go(x, env); val (b, eb, db) = go(y, env)
          val out = domain.raffA(a, b)
          val ev = dispatch + EventBounds.n(AstDispatch, 2) + ea + ea + eb + restrictionComparisons(a, b)
          (out, ev, D("Raffination/eval", Vector("desugared: x evaluated twice"), ev, Vector(da, db)))
        else binaryOp("Raffination", FrontierOp.Raffination, x, y, env, domain.raffA, (w, a, b, al) => w.raff(a, b, al))
      case Composition(x, y) =>
        val (a, ea, da) = go(x, env); val (b, eb, db) = go(y, env)
        if ref then
          val out = domain.compA(a, b)
          val fresh = mul(size(a.node), size(b.node))
          val ev = dispatch + ea + eb + EventBounds.ivl(FreshPath, fresh)
          (out, ev, D("Composition/eval", Vector(s"|x|·|y| = ${fresh.show}"), ev, Vector(da, db)))
        else
          val (out, e, facts) =
            if isExactTrie(a.node) && isExactTrie(b.node) then
              val (r, e2) = exactBinary("comp", a, b)((w, p, q, _) => w.comp(p, q))
              (r, e2, Vector("exact composition: graft frontier = the left operand's nodes"))
            else
              val value = domain.compA(a, b)
              val na = nodes(a.node); val nb = nodes(b.node)
              val e2 = EventBounds.of(TrieNodeVisit -> Ivl(1, add(na, mul(size(a.node), nb)).hi), FreshTrieNode -> Ivl(0, add(na, mul(size(a.node), nb)).hi),
                                      PatriciaVisit -> Ivl(0, sat(2 * mul(size(a.node), nb).hi)), AlgebraBespoke -> Ivl(0, na.hi), AlgebraIdentityLeft -> Ivl(0, na.hi), AlgebraIdentityRight -> Ivl(0, na.hi), AlgebraEmpty -> Ivl(0, na.hi), SubtrieAcceptedByPointer -> Ivl(0, add(na, mul(size(a.node), nb)).hi))
              (value, e2, Vector("summarized composition: nodes(x) + |x|·nodes(y) envelope", s"|x| ${size(a.node).show} nodes(x) ${na.show}; |y| ${size(b.node).show} nodes(y) ${nb.show}; |x·y| ${size(value.node).show}"))
          val ev = dispatch + ea + eb + e
          (out, ev, D("Composition", facts, ev, Vector(da, db)))
      case Wrap(src, p) =>
        val (a, ea, da) = go(src, env)
        val l = pathLen(p, env)
        val out = pathValue(p, env) match
          case Some(v) => domain.wrapA(v.items, a)
          case None => Abs(domain.arena.summ(SpatialTyping.infer(Space.Wrap(Mention(SpaceMention("#w")), p), SpatialTyping.Env(spaces = Map(SpaceMention("#w") -> domain.summary(a.node)), opaque = Map.empty)), Cause.Op("wrap", Vector(a.node.id))), Alias.Fresh)
        val ev = dispatch + ea +
          (if ref then EventBounds.n(AstDispatch, 2) + pathDispatch(p) + EventBounds.one(FreshPath) + EventBounds.ivl(FreshPath, size(a.node))
           else pathDispatch(p) + EventBounds.one(TrieNodeVisit) + (if domain.mustEmpty(a.node) then EventBounds.zero else EventBounds.ivl(FreshTrieNode, if domain.mayEmpty(a.node) then Ivl(0, l.hi) else l)))
        (out, ev, D("Wrap", Vector(s"prefix len ${l.show}"), ev, Vector(da)))
      case Unwrap(src, p) =>
        val (a, ea, da) = go(src, env)
        val l = pathLen(p, env)
        val out = pathValue(p, env) match
          case Some(v) => domain.unwrapA(a, v.items)
          case None =>
            val inferred = domain.arena.summ(SpatialTyping.infer(Space.Unwrap(Mention(SpaceMention("#u")), p), SpatialTyping.Env(spaces = Map(SpaceMention("#u") -> domain.summary(a.node)))), Cause.Op("unwrap", Vector(a.node.id)))
            Abs(unwrapUnknown(a.node, l, inferred), Alias.Unknown)
        val ev = dispatch + ea + pathDispatch(p) +
          (if ref then EventBounds.ivl(FreshPath, size(out.node)) + unwrapComparisons(a.node, pathValue(p, env), l)
           else
             // one visit per level descended plus the entry; the descent stops at a missing key
             val levels = pathValue(p, env) match
               case Some(v) => descended(a.node, v.items)
               case None => Ivl(0, l.hi)
             EventBounds.ivl(TrieNodeVisit, add(pt(1), levels)))
        (out, ev, D("Unwrap", Vector(s"prefix len ${l.show}", s"result size ${size(out.node).show}"), ev, Vector(da)))
      case TailsUnion(src) =>
        val (a, ea, da) = go(src, env)
        val out = domain.tailsUnionA(a)
        val ev = dispatch + ea + (if ref then EventBounds.ivl(FreshPath, headed(a.node)) else naryOverChildren(a, join = true, out))
        (out, ev, D("TailsUnion", Vector(s"fan-out ${DomainFacts.fanOut(domain, a.node).show}"), ev, Vector(da)))
      case TailsIntersection(src) =>
        val (a, ea, da) = go(src, env)
        val out = domain.tailsInterA(a)
        val ev = dispatch + ea + (if ref then EventBounds.ivl(FreshPath, headed(a.node)) else naryOverChildren(a, join = false, out))
        (out, ev, D("TailsIntersection", Vector(s"fan-out ${DomainFacts.fanOut(domain, a.node).show}"), ev, Vector(da)))
      case Range(x, lo0, hi0) =>
        val (lo, hi) = if Mutation.active("reverse-range") then (hi0, lo0) else (lo0, hi0)   // E1 mutation site
        val (a, ea, da) = go(x, env)
        val out = domain.rangeA(a, lo, hi)
        val n = size(a.node)
        val full = SpatialCost.rangeIsIdentity(lo, hi)
        if ref then
          val cmp = if full then Ivl.zero else sortComparisons(a.node, lo, hi)
          val ev = dispatch + ea + EventBounds.ivl(PathItemComparison, cmp)
          (out, ev, D("Range/eval", Vector(s"|x| ${n.show}", if full then "full window: identity" else s"window ($lo,$hi)"), ev, Vector(da)))
        else
          // only a DECLARED input's object has its count memoised by the warm run; a binder's tails or a
          // result returned by pointer is rebuilt per run
          val cached = (a.alias match { case Alias.Is(m) => declared(m); case _ => false }) && phase == ExecutionPhase.Warm
          val (out2, e) = rangeTrie(a, lo, hi, cached)
          val ev = dispatch + ea + e
          (out2, ev, D("Range", Vector(s"|x| ${n.show}", if cached then "count memoised (input object, warm)" else "count walk", s"window ($lo,$hi)"), ev, Vector(da)))
      case Iteration(src, sym, rest, body) => iteration(src, sym, rest, body, env)
      case Fixpoint(init, rec, body) => fixpoint(init, rec, body, env)
      case Call(r, refs, ms) => call(r, refs, ms, env)
      case Fold(src, initial, acc, sym, rest, body, upd) =>
        val (a, ea, da) = go(src, env)
        val k = DomainFacts.fanOut(domain, a.node)
        val restV = Abs(domain.arena.summ(domain.summary(domain.tailsUnion(a.node)), Cause.Op("fold-rest", Vector(a.node.id))), Alias.Is(rest))
        val env2 = env.copy(spaces = env.spaces + (rest -> restV), paths = env.paths + (sym -> PathAbs.opaque(pt(1))) + (acc -> PathAbs.unknown))
        val (bv, eb, db) = go(body, env2)
        val out = Abs(domain.arena.summ(SpatialRecursion.weaken(domain.summary(bv.node)), Cause.Op("fold", Vector(a.node.id))), Alias.Fresh)
        val ev = dispatch + ea + EventBounds.ivl(LoopBodyEntry, k) + eb.scale(k) +
          (if ref then EventBounds.ivl(FreshPath, mul(pt(2), headed(a.node))) + pathDispatch(initial) + (EventBounds.n(AstDispatch, 1) + pathDispatch(upd)).scale(k) else pathDispatch(initial) + pathDispatch(upd).scale(k))
        note("Fold is outside the certified fragment; its value is weakened to a summary and its accumulator is unknown")
        (out, ev, D("Fold", Vector(s"groups ${k.show}", "outside the certified fragment"), ev, Vector(da, db)))
      case GroundedPS(p, _) =>
        val ev = dispatch + pathDispatch(p)
        note("a grounded host function: its result is ⊤ and its own cost is not counted")
        (Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Fresh), ev, D("GroundedPS", Vector("host function: ⊤"), ev, Vector.empty))
      case GroundedSS(x, _) =>
        val (_, ea, da) = go(x, env)
        val ev = dispatch + ea
        note("a grounded host function: its result is ⊤ and its own cost is not counted")
        (Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Fresh), ev, D("GroundedSS", Vector("host function: ⊤"), ev, Vector(da)))

  private def binaryOp(name: String, op: FrontierOp, x: Space, y: Space, env: AEnv, dom: (Abs, Abs) => Abs,
                       walk: (Walk, XNode, XNode, Boolean) => (Res, EventBounds)): (Abs, EventBounds, Derivation) =
    val (a, ea, da) = go(x, env); val (b, eb, db) = go(y, env)
    if backend == Backend.Reference then
      val out = dom(a, b)
      val ev = dispatch + ea + eb
      (out, ev, D(s"$name/eval", Vector.empty, ev, Vector(da, db)))
    else if backend == Backend.Graph && name != "Union" && domain.mustEmpty(a.node) then
      // execT's empty-left short circuit: the algebra is not entered
      val ev = dispatch + ea + eb
      (domain.empty, ev, D(s"$name/execT-empty-left", Vector("left operand provably empty: no algebra entry"), ev, Vector(da, db)))
    else
      val (out, e, facts) = trieBinary(name.toLowerCase, op, a, b, (p, q) => dom(Abs(p, a.alias), Abs(q, b.alias)).node)(walk)
      // execT's empty-left short circuit MAY fire: the algebra's lower endpoints drop to 0
      val mayShortCircuit = backend == Backend.Graph && name != "Union" && domain.mayEmpty(a.node)
      val e2 = if mayShortCircuit then EventBounds(e.m.view.mapValues(i => Ivl(0, i.hi)).toMap) else e
      val ev = dispatch + ea + eb + e2
      val al = if DomainFacts.mustAlias(a, b) then (if out.node eq a.node then a.alias else out.alias) else out.alias
      (Abs(out.node, al), ev, D(name, facts :+ s"must-alias ${DomainFacts.mustAlias(a, b)}", ev, Vector(da, db)))

  /** the descended levels of an unwrap: exact on a trie, bounded otherwise */
  private def descended(x: XNode, items: List[PathItem]): Ivl = x match
    case t: XTrie => items match
      case Nil => Ivl.zero
      case k :: rest => t.children.get(k) match
        case Some(c) => add(pt(1), descended(c, rest))
        case None => Ivl.zero
    case ch: XChoice => ch.alts.map(descended(_, items)).reduce(hullI)
    case s: XSumm => Ivl(0, items.length.toLong)

  /** `Restriction` on the reference backend: item comparisons of the `exists`-guarded prefix test */
  private def restrictionComparisons(x: Abs, p: Abs): EventBounds =
    (domain.enumerate(x.node), domain.enumerate(p.node)) match
      case (Some(xs), Some(ps)) if xs.length * ps.length <= 64 =>
        val bounds = for xv <- xs; pv <- ps yield
          var lo = 0L; var hi = 0L
          for e <- xv.paths do
            val costs = pv.paths.toVector.map { q =>
              var i = 0; var stop = false
              while !stop && i < q.items.length do
                if i >= e.items.length then stop = true
                else { i += 1; if e.items(i - 1) != q.items(i - 1) then stop = true }
              (i.toLong, q.items.length <= e.items.length && e.items.startsWith(q.items)) }
            val total = costs.map(_._1).sum
            if costs.exists(_._2) then { lo += costs.filter(_._2).map(_._1).min; hi += total } else { lo += total; hi += total }
          Ivl(lo, hi)
        EventBounds.ivl(PathItemComparison, bounds.reduce(hullI))
      case _ =>
        EventBounds.ivl(PathItemComparison, Ivl(0, mul(mul(size(x.node), size(p.node)), lenI(p.node)).hi))

  /** `Unwrap` on the reference backend: `startsWith(e, p)` compares items until a mismatch or the end of `p` */
  private def unwrapComparisons(x: XNode, p: Option[PathValue], plen: Ivl): EventBounds =
    (domain.enumerate(x), p) match
      case (Some(vs), Some(pv)) if vs.length <= 64 =>
        def c(e: PathValue): Long =
          var i = 0; var stop = false
          while !stop && i < pv.items.length do
            if i >= e.items.length then stop = true
            else { i += 1; if e.items(i - 1) != pv.items(i - 1) then stop = true }
          i.toLong
        EventBounds.ivl(PathItemComparison, vs.map(v => pt(v.paths.toVector.map(c).sum)).reduce(hullI))
      case _ => EventBounds.ivl(PathItemComparison, Ivl(0, mul(size(x), plen).hi))

  /** the platform sort's item comparisons on `n` paths: at least `n-1` pair comparisons of ≥1 item,
   *  at most `n⌈log₂n⌉` pair comparisons of at most `maxlen+1` items */
  private def sortComparisons(x: XNode, lo: Int, hi: Int): Ivl =
    val n = size(x); val l = lenI(x)
    def lg(k: Long): Long = if k <= 1 then 0 else 64 - java.lang.Long.numberOfLeadingZeros(k - 1)
    // the window is decided by the concrete size: on an exact size the identity case is decided here;
    // a comparison of ε against anything costs no item comparison, so the lower bound is 0
    val sorts = if n.lo == n.hi then { val (a, b) = RangeBounds.normalize(n.lo.toInt, lo, hi); !(b <= a || (a == 0 && b == n.lo)) } else true
    if !sorts then Ivl.zero
    else Ivl(0, if n.hi >= INF then INF else Ivl.mul(Ivl.mul(n.hi, lg(n.hi)), Ivl.add(l.hi, 1)))

  /** THE N-ARY ENVELOPE FOR SUMMARIZED OPERANDS: `k` live operands (the fan-out), a key union of at
   *  most `keys` at every level, a result of `res` nodes.  `liveDistinct` costs up to `k(k-1)/2` probes
   *  and `4k` slots at the root; the descent makes at most `2·keys-1` calls, each with `3k` probes plus a
   *  dedup of `k(k-1)/2` (or `k` past the threshold), `3k` split/live slots and `2(k+1)` map slots. */
  private def narySummBounds(k: Ivl, keys: Ivl, res: Ivl): EventBounds =
    // no operands: `joinAll`/`meetAll` over an empty sequence — one visit, the sized buffer
    if k.hi == 0 then return EventBounds.of(TrieNodeVisit -> Ivl(1, 1), NaryScratchSlot -> Ivl(0, 4))
    val kh = k.hi
    val dedup = if kh >= INF then INF else if kh > 24 then kh else kh * (kh - 1) / 2
    val calls = if keys.hi >= INF then INF else sat(2 * keys.hi - 1).max(1)
    val perCallProbes = sat(Ivl.add(Ivl.mul(3, kh), dedup))
    val perCallScratch = sat(Ivl.add(Ivl.mul(5, kh), 2))
    EventBounds.of(
      TrieNodeVisit -> Ivl(1, sat(Ivl.add(1, Ivl.add(calls, res.hi)))),
      NaryOperandProbe -> Ivl(0, sat(Ivl.add(Ivl.add(dedup, kh), Ivl.mul(calls, perCallProbes)))),
      NaryScratchSlot -> Ivl(0, sat(Ivl.add(Ivl.mul(4, kh), Ivl.mul(calls, perCallScratch)))),
      PatriciaVisit -> Ivl(0, calls), PatriciaEntry -> Ivl(0, calls),
      FreshTrieNode -> Ivl(0, res.hi), SubtrieAcceptedByPointer -> Ivl(0, sat(Ivl.add(calls, kh))),
      SubtrieRejectedByPointer -> Ivl(0, sat(Ivl.add(calls, kh))), ReusedSubtrie -> Ivl(0, kh),
      AlgebraBespoke -> Ivl(0, res.hi), AlgebraIdentityLeft -> Ivl(0, res.hi), AlgebraIdentityRight -> Ivl(0, res.hi), AlgebraEmpty -> Ivl(0, res.hi))

  /** `TailsUnion`/`TailsIntersection` on the trie backends: the n-ary operation over the children */
  private def naryOverChildren(a: Abs, join: Boolean, out: Abs): EventBounds =
    a.node match
      case t: XTrie if domain.exact(t) =>
        val kids = t.children.values.toVector
        val base = EventBounds.one(TrieNodeVisit)
        if kids.isEmpty then base
        else if kids.length == 1 then base + EventBounds.one(SubtrieAcceptedByPointer)
        else
          val groups = kids.indices.toVector.map(_ => -1)     // children of one input are distinct objects
          val (_, lo) = walkLo.nary(kids, join, groups)
          val (_, hi) = walkHi.nary(kids, join, groups)
          base + EventBounds((lo.m.keySet ++ hi.m.keySet).iterator.map(e => e -> Ivl(lo(e).lo min hi(e).lo, lo(e).hi max hi(e).hi)).toMap)
      case _ =>
        narySummBounds(DomainFacts.fanOut(domain, a.node), nodes(a.node), nodes(out.node))

  // ---- loops ----------------------------------------------------------------------------------------------------
  private def iteration(src: Space, sym: PathRef, rest: SpaceMention, body: Space, env: AEnv): (Abs, EventBounds, Derivation) =
    val ref = backend == Backend.Reference
    val (a, ea, da) = go(src, env)
    a.node match
      case t: XTrie if domain.exact(t) =>
        // one body per head, the tails exact; the result is the n-ary join of the per-head results
        val heads = t.children.toVector
        var ev = dispatch + ea
        val kids = mutable.ArrayBuffer.empty[Derivation]
        val results = mutable.ArrayBuffer.empty[Abs]
        for (h, tails) <- heads do
          ev += EventBounds.one(LoopBodyEntry)
          // the tail set of THIS head is one object; a different head's tails are a different object
          val env2 = env.copy(spaces = env.spaces + (rest -> Abs(tails, Alias.Is(SpaceMention(s"${rest.s}#$h")))), paths = env.paths + (sym -> PathAbs.known(PathValue(List(h)))))
          val (bv, eb, db) = go(body, env2)
          ev += eb; kids += db; results += bv
        if ref then
          ev += EventBounds.n(FreshPath, 2L * headed(t).lo)
          val value = results.foldLeft(domain.empty)((acc, r) => Abs(domain.union(acc.node, r.node), Alias.Fresh))
          (value, ev, D("Iteration/eval", Vector(s"${heads.length} heads, exact"), ev, da +: kids.toVector))
        else if results.forall(r => isExactTrie(r.node)) then
          val (vLo, eLo) = walkLo.nary(results.map(_.node).toVector, true, results.indices.toVector.map(_ => -1))
          val (_, eHi) = walkHi.nary(results.map(_.node).toVector, true, results.indices.toVector.map(_ => -1))
          ev += EventBounds((eLo.m.keySet ++ eHi.m.keySet).iterator.map(e => e -> Ivl(eLo(e).lo min eHi(e).lo, eLo(e).hi max eHi(e).hi)).toMap)
          (Abs(vLo, Alias.Fresh), ev, D("Iteration", Vector(s"${heads.length} heads, exact; joinAll over the per-head results"), ev, da +: kids.toVector))
        else
          // a body result is not exact: the n-ary join over the per-head results is bounded from the summaries
          val value = results.foldLeft(domain.empty)((acc, r) => Abs(domain.union(acc.node, r.node), Alias.Fresh))
          val k = pt(results.length.toLong)
          val bodyNodes = results.map(r => nodes(r.node)).reduceOption((x, y) => add(x, y)).getOrElse(Ivl.zero)
          ev += narySummBounds(k, bodyNodes, bodyNodes)
          (value, ev, D("Iteration", Vector(s"${heads.length} heads, exact; a body result is summarized: n-ary join bounded"), ev, da +: kids.toVector))
      case _ =>
        // summarized source: the body once, under the summarized fibre, times the fan-out
        val k = DomainFacts.fanOut(domain, a.node)
        // the UNION of all tails bounds every group from above; its WEAKENING (no must fact) is what a
        // group can be at its smallest — upper endpoints from the first, lower endpoints from the second
        // the fibre at this prefix: the LUB over the heads of what one head's tails can be
        val fibreT = domain.summary(domain.fibreLub(a.node))
        val fibre = domain.arena.summ(fibreT, Cause.Op("fibre", Vector(a.node.id)))
        val fibreLo = domain.arena.summ(SpatialRecursion.weaken(fibreT), Cause.Op("fibre-weak", Vector(a.node.id)))
        // ONE body analysis under the WEAKENED fibre.  Weakening drops must facts and keeps may facts, so
        // the run's lower endpoints hold for every group (no group must do more than the weakest can) and
        // its upper endpoints are those of a superset of every group's values — sound on both sides.  A
        // second run under the strong fibre would tighten only hi where a must fact short-circuits an
        // operation, and it doubles the work at every nesting level (2^16 body analyses on puzzle15).
        val env2 = env.copy(spaces = env.spaces + (rest -> Abs(fibreLo, Alias.Is(rest))), paths = env.paths + (sym -> PathAbs.opaque(pt(1))))
        val (bv, eb, db) = go(body, env2)
        val _ = fibre
        // the loop's value: the k-fold union of the body's summary (bounded ⊤ past 64 groups) — the body
        // was analysed once above, so no second inference of the nested term is needed (re-inferring the
        // whole nest at every level made puzzle15's 16-level nest quadratic in inference, minutes per run)
        val bodyT = SpatialRecursion.weaken(domain.summary(bv.node))
        val accT =
          if k.hi >= INF || k.hi > 64 then SpatialType(Shape.top, SpaceType.bounded(bodyT.len, Ivl.mul(k.hi, bodyT.size.hi)))
          else if k.hi == 0 then SpatialType.empty
          else
            val ms = (0 until k.hi.toInt).map(i => SpaceMention(s"#g$i"))
            SpatialType.reduce(SpatialTyping.infer(ms.map(m => Mention(m): Space).reduce(Union(_, _)), SpatialTyping.Env(spaces = ms.map(_ -> bodyT).toMap)))
        val value = Abs(domain.arena.summ(if k.lo == 0 then SpatialRecursion.weaken(accT) else accT, Cause.Op("iteration", Vector(a.node.id))), Alias.Fresh)
        val perHead = EventBounds.one(LoopBodyEntry) + eb
        var ev = dispatch + ea + perHead.scale(k)
        if ref then ev += EventBounds.ivl(FreshPath, mul(pt(2), headed(a.node)))
        else ev += narySummBounds(k, mul(k, nodes(bv.node)), mul(k, nodes(bv.node)))
        (value, ev, D("Iteration/summarized", Vector(s"fan-out ${k.show} (the fibre at this prefix)", s"body priced once under the summarized tails"), ev, Vector(da, db)))

  /** UNWRAP BY AN UNKNOWN PREFIX of length in `l`: the result is contained in `tails^k(x)` for the prefix's
   *  length k — whatever the items are, the paths that start with SOME k-item prefix are a subset of
   *  the k-fold tails.  The summarized `Unwrap` transfer alone, not knowing the items, sums the fibres of
   *  every possible head at each level (16 heads → 16^k paths for a one-path source); the meet with the
   *  tails bound keeps the source's own cardinality. */
  private def unwrapUnknown(x: XNode, l: Ivl, inferred: XNode): XNode =
    val maxLen = lenI(x).hi
    if l.lo >= INF || (l.hi >= INF && maxLen >= INF) then inferred
    else
      val hi = math.min(l.hi, maxLen)
      if hi < l.lo then domain.arena.empty
      else
        var acc: Option[XNode] = None
        var t = x
        var k = 0L
        while k <= hi do
          if k >= l.lo then acc = Some(acc.map(domain.join(_, t)).getOrElse(t))
          t = domain.fibreLub(t)                               // one head's tails, whichever head the prefix names
          k += 1
        acc match
          case Some(b) => domain.meet(inferred, b).getOrElse(domain.arena.empty)
          case None => inferred

  private def fixpoint(init: Space, rec: SpaceMention, body: Space, env: AEnv): (Abs, EventBounds, Derivation) =
    val ref = backend == Backend.Reference
    val (i0, ei, di) = go(init, env)
    // the IR premise: the body must be positive in the recursion variable
    // (with the routine table: a Call in the body is positive in its argument when the callee is)
    val rt: Variance.RoutineTable = Variance.routineTable(routines, callees(body).filter(routines.isDefinedAt)).get
    if !Variance.of(body, rec, rt).monotone then
      note(s"Fixpoint over ${rec.s} is not positive in its recursion variable: ⊤")
      val top = Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Fresh)
      val ev = dispatch + ei + EventBounds.of(FixpointRound -> Ivl(1, INF), AstDispatch -> Ivl(0, INF), TrieDispatch -> Ivl(0, INF), TrieNodeVisit -> Ivl(0, INF),
                                              FreshTrieNode -> Ivl(0, INF), FreshPath -> Ivl(0, INF), LoopBodyEntry -> Ivl(0, INF), CallEntry -> Ivl(0, INF),
                                              ZipperBuild -> Ivl(0, INF), ZipperCursorRead -> Ivl(0, INF), GraphNodeDispatch -> Ivl(0, INF), TrieOpEntry -> Ivl(0, INF),
                                              PatriciaVisit -> Ivl(0, INF), PathDispatch -> Ivl(0, INF), TriePathDispatch -> Ivl(0, INF), EqualityFrontierVisit -> Ivl(0, INF))
      return (top, ev, D("Fixpoint/non-positive", Vector("rejected by the variance analysis: ⊤"), ev, Vector(di)))
    var cur = i0
    // the first round always runs in full; later rounds are certain only while the iteration is exact
    var evLo = dispatch + ei
    var evHi = dispatch + ei
    val kids = mutable.ArrayBuffer[Derivation](di)
    var n = 0
    var stable = false
    var exactSoFar = true
    var widenedReason: Option[String] = None
    def roundEvents(cur: Abs): (Abs, EventBounds, Derivation) =
      val env2 = env.copy(spaces = env.spaces + (rec -> Abs(cur.node, Alias.Is(rec))))
      val (bv, eb, db) = go(body, env2)
      val (nxt, eu) =
        if ref then (Abs(domain.union(cur.node, bv.node), Alias.Fresh), EventBounds.zero)
        else if isExactTrie(cur.node) && isExactTrie(bv.node) then
          val (r, e) = exactBinary("union", Abs(cur.node, Alias.Is(rec)), bv)((w, a, b, al) => w.union(a, b, al))
          (r, e + EventBounds.ivl(EqualityFrontierVisit, Ivl(1, nodes(r.node).hi)) + EventBounds.ivl(ReusedSubtrie, Ivl(0, nodes(r.node).hi)))
        else
          (Abs(domain.union(cur.node, bv.node), Alias.Fresh), frontierEvents(FrontierOp.Union, Abs(cur.node, Alias.Is(rec)), bv) + EventBounds.ivl(EqualityFrontierVisit, Ivl(1, add(nodes(cur.node), nodes(bv.node)).hi)))
      (nxt, EventBounds.one(FixpointRound) + eb + eu, db)
    while !stable && n < maxRounds do
      n += 1
      val (nxt, er, db) = roundEvents(cur)
      kids += db
      val exactRound = domain.exact(nxt.node) && domain.exact(cur.node)
      if exactSoFar && exactRound then
        evLo += er; evHi += er
        if nxt.node eq cur.node then stable = true else cur = nxt
      else
        exactSoFar = false
        if n == 1 then evLo += er        // the first round is certain whatever the tier
        evHi += er
        val w = domain.widen(cur.node, nxt.node)
        if domain.leq(nxt.node, cur.node) then stable = true
        else cur = Abs(w, Alias.Fresh)
        if w.isInstanceOf[XSumm] then widenedReason = Some("iteration-widening")
    if !stable then
      note(s"Fixpoint over ${rec.s}: no post-fixpoint within $maxRounds abstract rounds — rounds unbounded")
      evHi += EventBounds.ivl(FixpointRound, Ivl(0, INF))
    else if !exactSoFar then
      // the abstract iteration stabilised at a summary: the concrete rounds are bounded by the growth,
      // and every further round costs at most one body at the post-fixpoint
      val extra = Ivl(0, if size(cur.node).hi >= INF then INF else sat(size(cur.node).hi - size(i0.node).lo + 1))
      val (_, er, _) = roundEvents(cur)
      evHi += EventBounds(er.m.view.mapValues(i => Ivl(0, i.hi)).toMap).scale(extra)
    val ev = EventBounds((evLo.m.keySet ++ evHi.m.keySet).iterator.map(e => e -> Ivl(evLo(e).lo min evHi(e).lo, evHi(e).hi max evLo(e).hi)).toMap)
    val facts = Vector(s"$n abstract rounds", if exactSoFar then "exact iteration: rounds decided" else "summarized: the first round is certain, further rounds bounded by growth")
    (Abs(cur.node, Alias.Fresh), ev, D("Fixpoint", facts, ev, kids.toVector, widenedReason))

  private def call(r: RoutinePtr, refs: Vector[Path], ms: Vector[Space], env: AEnv): (Abs, EventBounds, Derivation) =
    var ev = dispatch + EventBounds.one(CallEntry) + (if backend == Backend.Graph then EventBounds.one(GraphFrameAllocation) else EventBounds.zero)
    val kids = mutable.ArrayBuffer.empty[Derivation]
    val argVals = ms.map { m => val (v, e, d) = go(m, env); ev += e; kids += d; v }
    val refVals = refs.map { p => ev += pathDispatch(p); PathAbs(pathValue(p, env), pathLen(p, env)) }
    def top(why: String): (Abs, EventBounds, Derivation) =
      note(s"call to ${r.s}: $why — ⊤")
      val t = Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Fresh)
      val e2 = EventBounds.of(CallEntry -> Ivl(1, INF), AstDispatch -> Ivl(0, INF), TrieDispatch -> Ivl(0, INF), TrieNodeVisit -> Ivl(0, INF), FreshTrieNode -> Ivl(0, INF), FreshPath -> Ivl(0, INF), LoopBodyEntry -> Ivl(0, INF), FixpointRound -> Ivl(0, INF), ZipperBuild -> Ivl(0, INF), ZipperCursorRead -> Ivl(0, INF), GraphNodeDispatch -> Ivl(0, INF), TrieOpEntry -> Ivl(0, INF))
      (t, ev + e2, D(s"Call ${r.s}/⊤", Vector(why), ev + e2, kids.toVector))
    if !routines.isDefinedAt(r) then return top("unknown routine")
    if Mutation.active("erase-calls") then return top("erased by the E1 mutation")   // E1 mutation site
    val d = routines(r)
    val env2 = AEnv(spaces = d.mentions.zip(argVals).toMap, paths = d.refs.zip(refVals).toMap, active = env.active + r)
    // A5: a POSITIVE PASSTHROUGH RECURSIVE COMPONENT is the IR's simultaneous system — analysed as one
    // abstract least post-fixpoint over all of its equations, never re-discovered per call
    if !env.active(r) then sccSystem(r, refs, ms) match
      case Some((p, sys)) => return system(r, d, p, sys, argVals, refVals, env, ev, kids)
      case None => ()
    d.body match
      case Union(l, Call(`r`, refs2, ms2)) if refs2 == refs && ms2 == ms =>
        // THE STABILISED-ARGUMENT RULE of eval/evalI: the arguments are re-evaluated in the callee's
        // environment; equal arguments stop the recursion at `l`, otherwise `l ∪ r(new args)` is
        // evaluated.  On the exact tier the arguments are values and the recursion is run to its
        // stationary point; a summarized argument makes the stationary point undecidable (⊤).
        def unionOf(x: Abs, y: Abs): (Abs, EventBounds) =
          if backend == Backend.Reference then (Abs(domain.union(x.node, y.node), Alias.Fresh), EventBounds.zero)
          else if isExactTrie(x.node) && isExactTrie(y.node) then exactBinary("union", x, y)((w, a, b, al) => w.union(a, b, al))
          else (Abs(domain.union(x.node, y.node), Alias.Fresh), frontierEvents(FrontierOp.Union, x, y))
        var undecidable: Option[String] = None
        def level(curEnv: AEnv, depth: Int): (Abs, EventBounds) =
          if depth > maxRounds then { undecidable = Some(s"recursion deeper than $maxRounds levels"); return (domain.empty, EventBounds.zero) }
          var ev2 = EventBounds.zero
          // the check: every ref re-evaluated (eval: `eval(Singleton(p))`; evalI: `pathItemsI`) …
          var same = true
          for p <- refs2 do
            ev2 += (if backend == Backend.Reference then EventBounds.of(AstDispatch -> pt(1), FreshPath -> pt(1)) else EventBounds.zero) + pathDispatch(p)
            val v = pathValue(p, curEnv)
            val prev = curEnv.paths.get(d.refs(refs2.indexOf(p))).flatMap(_.value)
            if v.isEmpty || prev.isEmpty then { undecidable = Some("a path argument is not a value"); return (domain.empty, ev2) }
            if v != prev then same = false
          // … then every mention re-evaluated and compared (`equalT` on evalI), stopping at the first inequality
          val argAbs = mutable.ArrayBuffer.empty[Abs]
          var i = 0
          while same && i < ms2.length do
            val (mv, em, dm) = go(ms2(i), curEnv); kids += dm
            ev2 += em
            val prev = curEnv.spaces(d.mentions(i))
            if !(isExactTrie(mv.node) && isExactTrie(prev.node)) then { undecidable = Some("a space argument is summarized"); return (domain.empty, ev2) }
            if backend != Backend.Reference then ev2 += EventBounds.ivl(EqualityFrontierVisit, Ivl(1, nodes(mv.node).hi)) + (if mv.node eq prev.node then EventBounds.one(ReusedSubtrie) else EventBounds.zero)
            if !(mv.node eq prev.node) then same = false
            argAbs += mv
            i += 1
          if same then
            val (lv, el, dl) = go(l, curEnv); kids += dl
            (lv, ev2 + el)
          else
            // `l ∪ r(args)`: the Union node, `l`, the Call node (entry, args, refs), the deeper level, the union
            val (lv, el, dl) = go(l, curEnv); kids += dl
            ev2 += el + dispatch + dispatch + EventBounds.one(CallEntry) + (if backend == Backend.Graph then EventBounds.one(GraphFrameAllocation) else EventBounds.zero)
            for p <- refs2 do ev2 += pathDispatch(p)
            val fullArgs = ms2.indices.map { j => val (mv, em, dm) = go(ms2(j), curEnv); ev2 += em; kids += dm; mv }
            val nextEnv = AEnv(spaces = d.mentions.zip(fullArgs).toMap, paths = curEnv.paths, active = curEnv.active)
            val (dv, ed) = level(nextEnv, depth + 1)
            if undecidable.isDefined then return (domain.empty, ev2 + ed)
            val (uv, eu) = unionOf(lv, dv)
            (uv, ev2 + ed + eu)
        val (v, e) = level(env2, 1)
        undecidable match
          case Some(why) if why == "a space argument is summarized" =>
            summarizedStationary(r, d, l, refs2, ms2, argVals, refVals, env2, ev, kids).getOrElse(top(why))
          case Some(why) => top(why)
          case None => (v.copy(alias = Alias.Fresh), ev + e, D(s"Call ${r.s}/stationary", Vector("run to a stationary argument tuple"), ev + e, kids.toVector))
      case _ =>
        if env.active(r) then return top("recursive beyond the IR")
        // A5: THE PARAMETRIC SUMMARY at this abstract input — computed once per (canonical routine,
        // abstract input) and reused; the result's relation to the arguments (by pointer to one of them,
        // or a fresh object) is carried across the call boundary so correlations survive composition
        val key = SummaryKey(routineIdentity(d), (d.refs.length, d.mentions.length), argVals.map(_.node.key), argVals.map(isDeclared),
                             aliasClasses(argVals), refVals.map(p => (p.value, p.len)), phase)
        summaries.get(key) match
          case Some(sm) =>
            store.hits += 1
            val out = Abs(sm.value, sm.aliasArg.map(i => argVals(i).alias).getOrElse(Alias.Fresh))
            val e = ev + sm.events
            (out, e, D(s"Call ${r.s}/summary", Vector("summary REUSED: same canonical routine, same abstract input",
                                                        s"per-invocation ${sm.events.showComponents}"), e, kids.toVector :+ sm.derivation))
          case None =>
            store.misses += 1
            val (bv, eb, db) = go(d.body, env2)
            val aliasArg = argVals.indexWhere(a => a.alias == bv.alias && a.alias.isInstanceOf[Alias.Is]) match { case -1 => None; case i => Some(i) }
            summaries(key) = Summary(bv.node, aliasArg, eb, db)
            val out = Abs(bv.node, aliasArg.map(i => argVals(i).alias).getOrElse(Alias.Fresh))
            val e = ev + eb
            (out, e, D(s"Call ${r.s}", Vector(s"${ms.length} space args, ${refs.length} path args", "summary COMPUTED for this abstract input",
                                                s"per-invocation ${eb.showComponents}" + aliasArg.map(i => s"; result is argument $i by pointer").getOrElse("")), e, kids.toVector :+ db))

  /** THE STABILISED-ARGUMENT RECURSION WITH SUMMARIZED ARGUMENTS.  Equality of the argument tuple is not
   *  decidable on summaries, but the DEPTH of the recursion is bounded when the arguments have the
   *  semi-naive shape: every parameter is PASSTHROUGH (`p`), an EXTENSIVE ACCUMULATOR (`p ∪ X`), or a
   *  DRIVER whose expression is must-empty once every driver is empty (and the accumulators' `X` parts
   *  too).  Then each non-stationary level grows some accumulator (a level that grows none has all
   *  drivers empty: the tuple repeats within two more levels), so the levels are at most the
   *  accumulators' growth to their abstract post-fixpoint plus three.  Every level's events are bounded
   *  by the level priced at the post-fixpoint; the first level's check is certain.  `None` when the shape
   *  does not apply (the caller reports ⊤). */
  private def summarizedStationary(r: RoutinePtr, d: Routine, l: Space, refs2: Vector[Path], ms2: Vector[Space], argVals: Vector[Abs],
                                   refVals: Vector[PathAbs], env0: AEnv, ev: EventBounds, kids: mutable.ArrayBuffer[Derivation]): Option[(Abs, EventBounds, Derivation)] =
    val params = d.mentions
    enum Role { case Pass, Ext, Driver }
    val roles = ms2.zipWithIndex.map { (m, i) => m match
      case Mention(p) if p == params(i) => Role.Pass
      case Union(Mention(p), _) if p == params(i) => Role.Ext
      case Union(_, Mention(p)) if p == params(i) => Role.Ext
      case _ => Role.Driver }
    if !roles.contains(Role.Ext) then return None
    // the abstract iteration of the tuple to a post-fixpoint
    var cur = params.zip(argVals).toMap
    var n = 0
    var stable = false
    var widened: Option[String] = None
    val values = mutable.ArrayBuffer.empty[XNode]
    while !stable && n < maxRounds do
      n += 1
      val envK = env0.copy(spaces = env0.spaces ++ cur)
      val (lv, _, _) = go(l, envK); values += lv.node
      val nxt = params.zip(ms2).map { (p, m) => val (mv, _, _) = go(m, envK); p -> mv }.toMap
      if params.forall(p => domain.leq(nxt(p).node, cur(p).node)) then stable = true
      else
        cur = params.map(p => p -> Abs(domain.widen(cur(p).node, nxt(p).node), Alias.Fresh)).toMap
        if cur.values.exists(_.node.isInstanceOf[XSumm]) then widened = Some("iteration-widening")
    if !stable then return None
    val envP = env0.copy(spaces = env0.spaces ++ cur)
    // the vanishing test: drivers at exact ∅ (and accumulators at the post-fixpoint) make every driver and
    // every accumulator's increment must-empty
    val envZ = envP.copy(spaces = envP.spaces ++ params.zip(roles).collect { case (p, Role.Driver) => p -> domain.empty })
    val vanish = ms2.zipWithIndex.forall { (m, i) => roles(i) match
      case Role.Pass => true
      case Role.Driver => domain.mustEmpty(go(m, envZ)._1.node)
      case Role.Ext => m match
        case Union(Mention(p), x) if p == params(i) => domain.mustEmpty(go(x, envZ)._1.node)
        case Union(x, Mention(p)) if p == params(i) => domain.mustEmpty(go(x, envZ)._1.node)
        case _ => false }
    if !vanish then return None
    val growth = params.zip(roles).collect { case (p, Role.Ext) =>
      val hi = size(cur(p).node).hi; val lo = size(argVals(params.indexOf(p)).node).lo
      if hi >= INF then INF else (hi - lo).max(0) }.foldLeft(0L)((a, b) => Ivl.add(a, b))
    if growth >= INF then return None
    val levels = Ivl(1, growth + 3)
    // one level at the post-fixpoint: the check (refs, every mention), `l`, the call node and its arguments
    var perLevel = EventBounds.zero
    val lk = mutable.ArrayBuffer.empty[Derivation]
    for p <- refs2 do perLevel += (if backend == Backend.Reference then EventBounds.of(AstDispatch -> pt(1), FreshPath -> pt(1)) else EventBounds.zero) + pathDispatch(p)
    for m <- ms2 do { val (mv, em, dm) = go(m, envP); perLevel += em; lk += dm; if backend != Backend.Reference then perLevel += EventBounds.ivl(EqualityFrontierVisit, Ivl(0, nodes(mv.node).hi)) }
    val (lv, el, dl) = go(l, envP); perLevel += el; lk += dl
    perLevel += dispatch + dispatch + EventBounds.one(CallEntry) + (if backend == Backend.Graph then EventBounds.one(GraphFrameAllocation) else EventBounds.zero)
    for m <- ms2 do { val (_, em, _) = go(m, envP); perLevel += em }
    for p <- refs2 do perLevel += pathDispatch(p)
    // the union of `l` with the deeper result at every non-final level, on the trie backends
    val unionEv = if backend == Backend.Reference then EventBounds.zero else frontierEvents(FrontierOp.Union, lv, lv)
    val hiLevel = EventBounds((perLevel.m.keySet ++ unionEv.m.keySet).iterator.map(e => e -> Ivl(0, Ivl.add(perLevel(e).hi, unionEv(e).hi))).toMap)
    // the first level's CHECK is certain: its refs and its first mention, then `l`
    var lo1 = EventBounds.zero
    for p <- refs2 do lo1 += (if backend == Backend.Reference then EventBounds.of(AstDispatch -> pt(1), FreshPath -> pt(1)) else EventBounds.zero) + pathDispatch(p)
    ms2.headOption.foreach { m => val (_, em, _) = go(m, env0.copy(spaces = env0.spaces ++ params.zip(argVals))); lo1 += EventBounds(em.m.view.mapValues(i => Ivl(i.lo, i.lo)).toMap) }
    lo1 += EventBounds(el.m.view.mapValues(i => Ivl(i.lo, i.lo)).toMap)
    val total = EventBounds((lo1.m.keySet ++ hiLevel.m.keySet).iterator.map(e => e -> Ivl(lo1(e).lo, Ivl.mul(levels.hi, hiLevel(e).hi))).toMap)
    val value = Abs(values.foldLeft(lv.node)((acc, v) => domain.join(acc, v)), Alias.Fresh)
    val facts = Vector(
      s"summarized arguments: roles ${roles.zip(params).map((ro, p) => s"${p.s}:${ro.toString.toLowerCase}").mkString(", ")}",
      s"abstract post-fixpoint of the argument tuple after $n rounds; accumulator growth ≤ $growth",
      s"levels ∈ ${levels.show}: each non-stationary level grows an accumulator, the drivers vanish within two more",
      "every level priced at the post-fixpoint (upper), the first level's check certain (lower)")
    val dn = D(s"Call ${r.s}/stationary-summarized", facts, ev + total, kids.toVector ++ lk, widened)
    Some((value, ev + total, dn))

  /** A5: A RECURSIVE COMPONENT AS THE IR'S SIMULTANEOUS SYSTEM.  `DeltaIR.Exec.solve` iterates every
   *  equation of the SCC together from its init under the frozen parameters until the delta is empty:
   *  round 0 evaluates the inits, every later round evaluates every body once (the terminating
   *  empty-delta round included).  The abstract iteration mirrors that round for round on the exact tier;
   *  past it the first round is certain and the rest are bounded by the growth of the accumulator, with
   *  the widening recorded.  No executor runs such a component natively — `eval`'s Call rule diverges on
   *  it — so the pricing is the IR solver's schedule with this backend's body rules. */
  private def system(r: RoutinePtr, d: Routine, p: Lowered, sys: EqSystem, argVals: Vector[Abs], refVals: Vector[PathAbs],
                     env: AEnv, ev0: EventBounds, kids: mutable.ArrayBuffer[Derivation]): (Abs, EventBounds, Derivation) =
    val vars = sys.vars
    val frozenEnv = AEnv(spaces = d.mentions.zip(argVals).toMap, paths = d.refs.zip(refVals).toMap, active = env.active ++ sys.routines.keySet)
    var cur: Map[SpaceMention, Abs] = Map.empty
    var evLo = EventBounds.zero
    var evHi = EventBounds.zero
    val roundKids = mutable.ArrayBuffer.empty[Derivation]
    for e <- sys.eqs do
      val (iv, ie, id) = go(e.init, frozenEnv); evLo += ie; evHi += ie; roundKids += id
      cur = cur.updated(e.v, iv)
    def round(cur: Map[SpaceMention, Abs]): (Map[SpaceMention, Abs], EventBounds, Vector[Derivation]) =
      var er = EventBounds.zero
      val ds = mutable.ArrayBuffer.empty[Derivation]
      val env2 = frozenEnv.copy(spaces = frozenEnv.spaces ++ cur.map((v, a) => v -> Abs(a.node, Alias.Is(v))))
      val nxt = sys.eqs.map { e =>
        val (bv, eb, db) = go(e.body, env2); er += eb; ds += db
        // the accumulator: `A ∪ F(A)` — a Set union under the IR's reference solver, no trie events
        e.v -> Abs(domain.union(cur(e.v).node, bv.node), Alias.Fresh)
      }.toMap
      (nxt, er, ds.toVector)
    var n = 0
    var stable = false
    var exactSoFar = true
    var widened: Option[String] = None
    while !stable && n < maxRounds do
      n += 1
      val (nxt, er, ds) = round(cur); roundKids ++= ds
      val exactRound = vars.forall(v => domain.exact(nxt(v).node) && domain.exact(cur(v).node))
      if exactSoFar && exactRound then
        evLo += er; evHi += er
        if vars.forall(v => nxt(v).node eq cur(v).node) then stable = true else cur = nxt
      else
        exactSoFar = false
        if n == 1 then evLo += er
        evHi += er
        if vars.forall(v => domain.leq(nxt(v).node, cur(v).node)) then stable = true
        else
          cur = vars.map(v => v -> Abs(domain.widen(cur(v).node, nxt(v).node), Alias.Fresh)).toMap
          if cur.values.exists(_.node.isInstanceOf[XSumm]) then widened = Some("iteration-widening")
    if !stable then
      note(s"system of ${sys.routines.keys.map(_.s).mkString(",")}: no post-fixpoint within $maxRounds abstract rounds — rounds unbounded")
      evHi = EventBounds(evHi.m.view.mapValues(i => Ivl(i.lo, INF)).toMap)
    else if !exactSoFar then
      val growth = vars.map(v => if size(cur(v).node).hi >= INF then INF else size(cur(v).node).hi).max
      val extra = Ivl(0, if growth >= INF then INF else growth + 1)
      val (_, er, _) = round(cur)
      evHi += EventBounds(er.m.view.mapValues(i => Ivl(0, i.hi)).toMap).scale(extra)
    val evSys = EventBounds((evLo.m.keySet ++ evHi.m.keySet).iterator.map(e => e -> Ivl(evLo(e).lo min evHi(e).lo, evHi(e).hi max evLo(e).hi)).toMap)
    val sysNode = D("System", Vector(s"positive SCC {${sys.routines.keys.map(_.s).toVector.sorted.mkString(",")}}: ${vars.length} simultaneous equations (stratum ${sys.stratum})",
                                     s"$n abstract rounds after the init round",
                                     if exactSoFar then "exact iteration: rounds decided" else "summarized: the first round is certain, further rounds bounded by the accumulator's growth",
                                     "schedule: the IR solver's naive rounds (DeltaIR.Exec.solve); premises: " + p.premises.theorems.mkString(", ")),
                    evSys, roundKids.toVector, widened)
    val ev = ev0 + evSys
    val out = cur(sys.routines(r))
    (Abs(out.node, Alias.Fresh), ev, D(s"Call ${r.s}/system", Vector(s"answered by the component's system, projected on ${sys.routines(r).s}"), ev, kids.toVector :+ sysNode, widened))

  // ---- the zipper backend -----------------------------------------------------------------------------------
  /** the cursor shell over abstract literals.  `obj` is the OBJECT CLASS of a literal cursor's trie:
   *  two literals with the same class are the same trie object (the same input mention, the same
   *  literal value, a full-window range of the same operand); `-1` is a fresh object of this run. */
  private sealed trait ZX
  private final case class ZLitX(v: Abs, obj: Int) extends ZX
  private final case class ZUnionX(a: ZX, b: ZX) extends ZX
  private final case class ZInterX(a: ZX, b: ZX) extends ZX
  private final case class ZSubX(a: ZX, b: ZX) extends ZX
  private final case class ZCompX(a: ZX, b: ZX) extends ZX
  private final case class ZPrefixX(remaining: List[PathItem], src: ZX) extends ZX
  private final case class ZRestrX(x: ZX, p: ZX) extends ZX
  private final class ZTailsUX(val src: ZX) extends ZX { var merged: ZX | Null = null }
  private final class ZTailsIX(val src: ZX) extends ZX { var merged: ZX | Null = null }

  /** THE CURSOR WALK: `SpaceZipper`'s query semantics over exact abstract literals, read for read.
   *  `share` decides identity BELOW the literal roots (sub-cursors of different objects that are
   *  structurally equal may or may not be the same trie object): maximal sharing is the lower bound on
   *  reads and materialised nodes, proven-only sharing the upper bound.  Root identity is exact. */
  private final class ZipperWalk(share: Boolean, env: AEnv, kids: mutable.ArrayBuffer[Derivation]):
    var ev: EventBounds = EventBounds.zero
    private var freshObj = -2
    private def fresh(): Int = { freshObj -= 1; freshObj }
    private val childObjs = mutable.HashMap.empty[(Int, PathItem), Int]
    private def childObj(parent: Int, k: PathItem): Int =
      if parent == -1 || parent <= -2 then fresh() else childObjs.getOrElseUpdate((parent, k), { freshObj -= 1; freshObj })
    private val mentionObj = mutable.HashMap.empty[SpaceMention, Int]
    private val literalObj = new java.util.IdentityHashMap[SpaceValue, Integer]()
    private var nextObj = 0
    def objOfMention(m: SpaceMention): Int = mentionObj.getOrElseUpdate(m, { nextObj += 1; nextObj })
    def objOfLiteral(v: SpaceValue): Int =
      val hit = literalObj.get(v)
      if hit != null then hit.intValue else { nextObj += 1; literalObj.put(v, nextObj); nextObj }
    private def read(): Unit = ev += EventBounds.one(ZipperCursorRead)
    private def exactTrie(z: ZX): Boolean = z match
      case ZLitX(v, _) => isExactTrie(v.node)
      case _ => true
    def allExact(z: ZX): Boolean = z match
      case l: ZLitX => exactTrie(l)
      case ZUnionX(a, b) => allExact(a) && allExact(b)
      case ZInterX(a, b) => allExact(a) && allExact(b)
      case ZSubX(a, b) => allExact(a) && allExact(b)
      case ZCompX(a, b) => allExact(a) && allExact(b)
      case ZPrefixX(_, src) => allExact(src)
      case ZRestrX(x, p) => allExact(x) && allExact(p)
      case t: ZTailsUX => allExact(t.src)
      case t: ZTailsIX => allExact(t.src)
    /** the executor's `sameSpace` is a POINTER test on the underlying tries.  Which subtries are the same
     *  object is not visible to the analysis (a builder may share structurally equal subtries — the
     *  E1 adversarial family found `tails(k)` reusing one `{ε}` leaf under two heads), so the MAXIMAL-
     *  sharing walk (`share`, the lower bound) treats structurally equal exact tries as the same object
     *  and the no-sharing walk (the upper bound) treats only the same declared object as the same. */
    def sameSpace(a: ZX, b: ZX): Boolean =
      (a eq b) || ((a, b) match
        case (ZLitX(x, o1), ZLitX(y, o2)) =>
          (o1 > 0 && o1 == o2) ||
          (share && isExactTrie(x.node) && isExactTrie(y.node) && ((x.node eq y.node) || (domain.leq(x.node, y.node) && domain.leq(y.node, x.node))))
        case _ => false)
    def union(a: ZX, b: ZX): ZX = if sameSpace(a, b) then { ev += EventBounds.one(ReusedSpace); a } else ZUnionX(a, b)
    def intersection(a: ZX, b: ZX): ZX = if sameSpace(a, b) then { ev += EventBounds.one(ReusedSpace); a } else ZInterX(a, b)
    def subtraction(a: ZX, b: ZX): ZX = if sameSpace(a, b) then { ev += EventBounds.one(ReusedSpace); ZLitX(domain.empty, -1) } else ZSubX(a, b)
    def restriction(x: ZX, p: ZX): ZX = if terminal(p) then x else ZRestrX(x, p)
    def trieOf(z: ZX): XTrie = z match
      case ZLitX(v, _) => v.node match
        case t: XTrie if domain.exact(t) => t
        case _ => throw ZipperWalk.NotExact
      case _ => throw IllegalStateException("not a literal")
    private def mergedU(z: ZTailsUX): ZX =
      if z.merged == null then
        val cs = children(z.src)
        z.merged = if cs.isEmpty then ZLitX(domain.empty, -1) else cs.values.reduce(ZUnionX(_, _))
      z.merged.nn
    private def mergedI(z: ZTailsIX): ZX =
      if z.merged == null then
        val sv = materialize(z.src)
        val (out, e) = naryChildren(sv, join = false)
        ev += e
        z.merged = ZLitX(out, -1)
      z.merged.nn
    /** `tailsIntersection`/`tailsUnion` on a materialised trie, priced by the trie walks */
    private def naryChildren(v: Abs, join: Boolean): (Abs, EventBounds) =
      v.node match
        case t: XTrie if domain.exact(t) =>
          val kids0 = t.children.values.toVector
          val base = EventBounds.one(TrieNodeVisit)
          if kids0.isEmpty then (domain.empty, base)
          else if kids0.length == 1 then (Abs(kids0.head, Alias.Unknown), base + EventBounds.one(SubtrieAcceptedByPointer))
          else
            val groups = kids0.indices.toVector.map(_ => -1)
            val (r, e) = (if share then walkLo else walkHi).nary(kids0, join, groups)
            (Abs(r, Alias.Fresh), base + e)
        case _ =>
          val out = if join then domain.tailsUnionA(v) else domain.tailsInterA(v)
          (out, naryOverChildren(v, join, out))
    def terminal(z: ZX): Boolean = z match
      case l: ZLitX => read(); trieOf(l).terminal
      case ZUnionX(a, b) => read(); terminal(a) || terminal(b)
      case ZInterX(a, b) => read(); terminal(a) && terminal(b)
      case ZSubX(a, b) => read(); terminal(a) && !terminal(b)
      case ZCompX(a, b) => read(); terminal(a) && terminal(b)
      case ZPrefixX(rem, src) => read(); rem.isEmpty && terminal(src)
      case ZRestrX(x, p) => terminal(x) && terminal(p)
      case t: ZTailsUX => read(); terminal(mergedU(t))
      case t: ZTailsIX => read(); terminal(mergedI(t))
    def children(z: ZX): SortedMap[PathItem, ZX] = z match
      case l @ ZLitX(v, o) => read(); trieOf(l).children.map((k, c) => k -> (ZLitX(Abs(c, Alias.Unknown), childObj(o, k)): ZX))
      case ZUnionX(a, b) =>
        read()
        val ac = children(a); val bc = children(b)
        SortedMap.from((ac.keySet ++ bc.keySet).iterator.map(k => k -> ((ac.get(k), bc.get(k)) match
          case (Some(x), Some(y)) => union(x, y)
          case (Some(x), None) => x
          case (None, Some(y)) => y
          case _ => ZLitX(domain.empty, -1))))
      case ZInterX(a, b) =>
        read()
        val ac = children(a); val bc = children(b)
        SortedMap.from((ac.keySet intersect bc.keySet).iterator.map(k => k -> intersection(ac(k), bc(k))))
      case ZSubX(a, b) =>
        read()
        val bc = children(b); val ac = children(a)
        ac.map((k, x) => k -> (bc.get(k) match { case Some(y) => subtraction(x, y); case None => x }))
      case ZCompX(a, b) =>
        read()
        val ac = children(a)
        val mapped = ac.map((k, x) => k -> (ZCompX(x, b): ZX))
        if terminal(a) then
          val bc = children(b)
          SortedMap.from((mapped.keySet ++ bc.keySet).iterator.map(k => k -> ((mapped.get(k), bc.get(k)) match
            case (Some(x), Some(y)) => union(x, y)
            case (Some(x), None) => x
            case (None, Some(y)) => y
            case _ => ZLitX(domain.empty, -1))))
        else mapped
      case ZPrefixX(rem, src) =>
        read()
        rem match
          case Nil => children(src)
          case h :: tl => SortedMap(h -> ZPrefixX(tl, src))
      case ZRestrX(x, p) =>
        read()
        val xc = children(x); val pc = children(p)
        SortedMap.from((xc.keySet intersect pc.keySet).iterator.map(k => k -> restriction(xc(k), pc(k))))
      case t: ZTailsUX => read(); children(mergedU(t))
      case t: ZTailsIX => read(); children(mergedI(t))
    def descend(z: ZX, k: PathItem): ZX = z match
      case l @ ZLitX(v, o) => read(); trieOf(l).children.get(k) match { case Some(c) => ZLitX(Abs(c, Alias.Unknown), childObj(o, k)); case None => ZLitX(domain.empty, -1) }
      case ZUnionX(a, b) => read(); union(descend(a, k), descend(b, k))
      case ZInterX(a, b) => read(); intersection(descend(a, k), descend(b, k))
      case ZSubX(a, b) => read(); subtraction(descend(a, k), descend(b, k))
      case ZCompX(a, b) =>
        read()
        val viaA = ZCompX(descend(a, k), b)
        if terminal(a) then union(viaA, descend(b, k)) else viaA
      case ZPrefixX(rem, src) =>
        read()
        rem match
          case Nil => descend(src, k)
          case h :: tl => if h == k then ZPrefixX(tl, src) else ZLitX(domain.empty, -1)
      case ZRestrX(x, p) => read(); restriction(descend(x, k), descend(p, k))
      case t: ZTailsUX => read(); descend(mergedU(t), k)
      case t: ZTailsIX => read(); descend(mergedI(t), k)
    def materialize(z: ZX): Abs = z match
      case ZLitX(v, _) => v
      case _ =>
        ev += EventBounds.one(ZipperMaterializeNode) + EventBounds.one(FreshNode)
        val kids0 = children(z).iterator.map((k, cz) => k -> materialize(cz)).filterNot((_, c) => domain.mustEmpty(c.node)).map((k, c) => k -> c.node).toVector
        val term = terminal(z)
        Abs(domain.arena.trie(term, SortedMap.from(kids0), Cause.Op("materialize", Vector.empty)), Alias.Fresh)
    /** `transpileZ`, exactly: one build per node, the smart constructors, the fallback to evalI */
    def transpile(x: Space): ZX =
      ev += EventBounds.one(ZipperBuild)
      x match
        case Empty => ZLitX(domain.empty, objOfLiteral(SpaceValue(Set.empty)))
        case Singleton(p) =>
          val l = pathLen(p, env)
          ev += pathDispatch(p) + singletonTrie(l)
          pathValue(p, env) match
            case Some(v) => ZLitX(Abs(domain.alpha(SpaceValue(Set(v)), Cause.Op("singleton", Vector.empty)), Alias.Fresh), -1)
            case None => ZLitX(Abs(domain.arena.summ(SpatialType(Shape.oneUnknownPath(LenBounds(l.lo, if l.hi >= INF then LenBounds.INF else l.hi)), SpaceType.boundedExact(LenBounds(l.lo, if l.hi >= INF then LenBounds.INF else l.hi), 1L)), Cause.Op("singleton", Vector.empty)), Alias.Fresh), -1)
        case Literal(v) =>
          val a = domain.literal(v)
          if phase == ExecutionPhase.Cold then ev += coldLiteral(a)
          ZLitX(a, if v.paths.isEmpty then objOfLiteral(SpaceValue(Set.empty)) else objOfLiteral(v))
        case Mention(m) =>
          val v = env.spaces.getOrElse(m, Abs(domain.arena.summ(SpatialType.top, Cause.Input(m)), Alias.Is(m)))
          ZLitX(v, if domain.mustEmpty(v.node) then objOfLiteral(SpaceValue(Set.empty)) else objOfMention(m))
        case Union(a, b) => union(transpile(a), transpile(b))
        case Intersection(a, b) => intersection(transpile(a), transpile(b))
        case Subtraction(a, b) => subtraction(transpile(a), transpile(b))
        case Restriction(a, b) => restriction(transpile(a), transpile(b))
        case Raffination(a, b) => val x1 = transpile(a); ZSubX(x1, restriction(x1, transpile(b)))
        case Composition(a, b) => ZCompX(transpile(a), transpile(b))
        case Wrap(src, p) =>
          val items = pathValue(p, env)
          ev += pathDispatch(p)
          val z = transpile(src)
          items match
            case Some(v) => ZPrefixX(v.items, z)
            case None => fallbackLit(x)
        case Unwrap(src, p) =>
          val z = transpile(src)
          ev += pathDispatch(p)
          pathValue(p, env) match
            case Some(v) => if v.items.isEmpty then z else v.items.foldLeft(z)((c, k) => descend(c, k))
            case None => fallbackLit(x)
        case TailsUnion(src) => new ZTailsUX(transpile(src))
        case TailsIntersection(src) => new ZTailsIX(transpile(src))
        case Range(y, lo, hi) =>
          val z = transpile(y)
          ev += EventBounds.one(TrieOpEntry)
          val v = materialize(z)
          // an input literal's count is memoised by the warm run; anything materialised is fresh
          val cached = z match { case ZLitX(_, o) => o > 0 && phase == ExecutionPhase.Warm; case _ => false }
          val (rng, e) = rangeTrie(v, lo, hi, cached)
          ev += e
          if rng.node eq v.node then (z match { case l: ZLitX => l; case _ => ZLitX(v, -1) }) else ZLitX(rng, -1)
        case other => fallbackLit(other)
    def fallbackLit(x: Space): ZX =
      ev += EventBounds.one(ZipperFallbackToEvalI)
      val trie = new CostSem(Backend.Trie, domain, routines, phase, maxRounds, declared, store)
      val (v, e, d) = trie.go(x, env); ev += e; kids += d
      for n <- trie.notesOut do note(n)
      ZLitX(v, -1)
  end ZipperWalk
  private object ZipperWalk:
    /** a cursor query reached a summarized literal: the exact walk does not apply */
    object NotExact extends RuntimeException("not an exact shell", null, false, false)

  /** coarse bounds for a shell with SUMMARIZED literals: forced nodes by the frontier envelopes,
   *  reads by the layer count */
  private def zipperCoarse(s: Space, env: AEnv): (Abs, EventBounds, Derivation) =
    val trie = new CostSem(Backend.Trie, domain, routines, phase, maxRounds, declared, store)
    val (v, e, d) = trie.go(s, env)
    // every trie-algebra node visit becomes at most a forced cursor node; every forced node reads each
    // layer at most twice (children + terminal); the shell is at most the term's size
    def termSize(x: Space): Long = 1L + SizeZ3.children(x).map(termSize).sum
    // the cursor tree can be twice the term (Raffination duplicates its left operand); every query
    // reads at most every cursor node once, and a forced node makes at most two queries plus one per
    // smart-constructor terminal test
    val shell = 2L * termSize(s) + 2
    val visits = e(TrieNodeVisit).hi
    val forced = Ivl(0, sat(visits + nodes(v.node).hi + 1))
    val ev = EventBounds.of(ZipperBuild -> Ivl(1, shell), ZipperCursorRead -> Ivl(0, sat(Ivl.mul(Ivl.add(forced.hi, 1), 4 * shell))),
                            ZipperMaterializeNode -> forced, FreshNode -> forced, ZipperFallbackToEvalI -> Ivl(0, shell), ReusedSpace -> Ivl(0, shell),
                            TrieOpEntry -> Ivl(0, shell)) +
      EventBounds(e.m.filterNot((k, _) => k == TrieDispatch).view.mapValues(i => Ivl(0, i.hi)).toMap) + EventBounds.ivl(TrieDispatch, Ivl(0, e(TrieDispatch).hi))
    for n <- trie.notesOut do note(n)
    note("zipper over summarized operands: coarse envelope (forced nodes ≤ trie visits, reads ≤ 2·layers per forced node)")
    (v, ev, D("execZ/coarse", Vector("summarized literal in the shell"), ev, Vector(d)))

  private def zipper(s: Space, env: AEnv): (Abs, EventBounds, Derivation) =
    val kidsLo = mutable.ArrayBuffer.empty[Derivation]
    val lo = new ZipperWalk(share = true, env, kidsLo)
    val vLo =
      try
        val rootLo = lo.transpile(s)
        if !lo.allExact(rootLo) then return zipperCoarse(s, env)
        lo.materialize(rootLo)
      catch case ZipperWalk.NotExact => return zipperCoarse(s, env)
    val kidsHi = mutable.ArrayBuffer.empty[Derivation]
    val hi = new ZipperWalk(share = false, env, kidsHi)
    try hi.materialize(hi.transpile(s))
    catch case ZipperWalk.NotExact => return zipperCoarse(s, env)
    val ev = EventBounds((lo.ev.m.keySet ++ hi.ev.m.keySet).iterator.map(e => e -> Ivl(lo.ev(e).lo min hi.ev(e).lo, lo.ev(e).hi max hi.ev(e).hi)).toMap)
    (vLo, ev, D("execZ", Vector("exact shell: the cursor algebra read for read, sharing ∈ [maximal, proven]"), ev, kidsLo.toVector))

  def notesOut: Vector[String] = notes.toVector
end CostSem

// ==================================================================================================
// THE ENTRY POINTS
// ==================================================================================================
/** A6: THE TRANSFER REGISTRY AS THE ANALYSIS SEES IT.  `proofs/spatial/STATUS.tsv` is written by the
 *  independent checker (`proofs/spatial/check_transfers.py`) from `proofs/spatial/REGISTRY.tsv`; a
 *  derivation's rules map to the registry rows they rest on, and a result is certified only when every
 *  one of them is discharged.  Nothing here is trusted from a comment: an absent table certifies nothing. */
object SpatialTransfers:
  lazy val status: Map[String, String] =
    val f = java.nio.file.Paths.get("proofs/spatial/STATUS.tsv")
    if !java.nio.file.Files.isRegularFile(f) then Map.empty
    else
      scala.io.Source.fromFile(f.toFile).getLines().filter(l => l.nonEmpty && !l.startsWith("#")).map { l =>
        val cols = l.split("\t"); cols(0) -> cols.last.trim
      }.toMap
  /** the registry rows one derivation rule rests on */
  def rulesOf(rule: String, facts: Vector[String], widening: Option[String]): Vector[String] =
    val base = Vector("A6-IVL", "A6-ORDER", "A6-MUSTMAY", "A6-IVL-IMPL", "A6-EVENTS", "A6-BACKENDS")
    val op = rule.takeWhile(c => c != '/' && c != ' ')
    val exact = facts.exists(_.startsWith("exact operands"))
    val summ = facts.exists(_.startsWith("summarized operand"))
    val own = op match
      case "Union" => Vector(if summ then "A6-SUMM" else "A6-EXACT-UNION", "A6-EXACT-UNION-SAME", "A6-PATRICIA")
      case "Intersection" => Vector(if summ then "A6-SUMM" else "A6-EXACT-INTER", "A6-EXACT-INTER-SAME", "A6-PATRICIA")
      case "Subtraction" => Vector(if summ then "A6-SUMM" else "A6-EXACT-SUB", "A6-EXACT-SUB-SAME", "A6-PATRICIA")
      case "Restriction" => Vector(if summ then "A6-SUMM" else "A6-EXACT-RESTRICT", "A6-PATRICIA")
      case "Raffination" => Vector(if summ then "A6-SUMM" else "A6-EXACT-RAFF", "A6-PATRICIA")
      case "Composition" => Vector(if summ then "A6-SUMM" else "A6-EXACT-COMP")
      case "Wrap" => Vector("A6-EXACT-WRAP")
      case "Unwrap" => Vector("A6-EXACT-UNWRAP")
      case "TailsUnion" => Vector("A6-EXACT-TAILS-UNION", "A6-PATRICIA")
      case "TailsIntersection" => Vector("A6-EXACT-TAILS-INTER", "A6-PATRICIA")
      case "Range" => Vector("A6-RANGE", "A6-EXACT-RANGE")
      case "Fixpoint" | "System" => Vector("A6-WIDEN", "A6-BUDGET")
      case "Iteration" => if facts.exists(_.contains("summarized")) then Vector("A6-SUMM") else Vector.empty
      case _ => Vector.empty
    val w = if widening.isDefined then Vector("A6-WIDEN", "A6-SUMM") else Vector.empty
    val _ = exact
    (base ++ own ++ w).distinct
  def dependenciesOf(d: Derivation): Vector[String] =
    val acc = mutable.LinkedHashSet.empty[String]
    def go(x: Derivation): Unit = { acc ++= rulesOf(x.rule, x.facts, x.widening); x.children.foreach(go) }
    go(d)
    acc.toVector.sorted

object CostSem:
  /** A5: the summary key — TOP-LEVEL on purpose: an inner case class's equality includes its owning
   *  analysis instance, and the backends' nested instances must share one cache */
  final case class SummaryKey(routine: Space, arity: (Int, Int), args: Vector[XNode.Key], declaredArgs: Vector[Boolean],
                              aliasClasses: Vector[Int], refs: Vector[(Option[PathValue], Ivl)], phase: ExecutionPhase)
  /** a routine's summary at one abstract input: the result (by pointer to argument `aliasArg` when it is
   *  one), the PER-INVOCATION events of the body, and the derivation — the certificate node */
  final case class Summary(value: XNode, aliasArg: Option[Int], events: EventBounds, derivation: Derivation)
  /** A5: the parametric summaries, canonical routine identities and SCC systems of one analysis */
  final class SummaryStore:
    val summaries = mutable.HashMap.empty[SummaryKey, Summary]
    var hits = 0
    var misses = 0
    val identities = mutable.HashMap.empty[RoutinePtr, Space]
    val sccOf = mutable.HashMap.empty[RoutinePtr, Option[(Lowered, EqSystem)]]

  /** declared inputs: exact values where the caller has them, summaries otherwise */
  final case class Inputs(values: Map[SpaceMention, SpaceValue] = Map.empty,
                          summaries: Map[SpaceMention, SpatialType] = Map.empty,
                          paths: Map[PathRef, PathValue] = Map.empty,
                          pathLens: Map[PathRef, LenBounds] = Map.empty):
    def env(d: Domain): AEnv =
      val vs = values.map((m, v) => m -> d.input(m, v)) ++ summaries.filterNot((m, _) => values.contains(m)).map((m, t) => m -> d.inputSummary(m, t))
      val ps = paths.map((r, v) => r -> PathAbs.known(v)) ++ pathLens.filterNot((r, _) => paths.contains(r)).map((r, k) => r -> PathAbs.opaque(Ivl(k.lo, if k.hi >= LenBounds.INF then Ivl.INF else k.hi)))
      AEnv(vs, ps)

  def analyze(s: Space, inputs: Inputs, backend: Backend, routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
              phase: ExecutionPhase = ExecutionPhase.Warm, budget: DomainBudget = DomainBudget()): CostReport =
    val d = new Domain(budget)
    val sem = new CostSem(backend, d, routines, phase, declared = inputs.values.keySet ++ inputs.summaries.keySet)
    val (v, ev, der) = sem.analyze(s, inputs.env(d))
    CostReport(backend, phase, Mutation.bounds(ev), v, der, d.certificate, sem.notesOut, d.arena.size, sem.summaryStats, d.size(v.node))   // E1 mutation site

  def analyzeAll(s: Space, inputs: Inputs, routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                 phase: ExecutionPhase = ExecutionPhase.Warm): Map[Backend, CostReport] =
    Backend.values.iterator.map(b => b -> analyze(s, inputs, b, routines, phase)).toMap

  /** the GRAPH backend on an operation graph: `execT`'s slots, frames and short circuits over the same
   *  trie rules.  Analysed on the op-graph the pipeline lowers to, not on the `Space`. */
  def analyzeGraph(g: RecursiveOpGraph, inputs: Inputs, index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty,
                   phase: ExecutionPhase = ExecutionPhase.Warm, budget: DomainBudget = DomainBudget()): CostReport =
    val d = new Domain(budget)
    val sem = new GraphSem(d, phase, index, inputs.values.keySet ++ inputs.summaries.keySet)
    val (v, ev, der) = sem.run(g, inputs.env(d))
    CostReport(Backend.Graph, phase, Mutation.bounds(ev), v, der, d.certificate, sem.notesOut, d.arena.size, sem.summaryStats, d.size(v.node))

/** `execT` over an operation graph, abstractly: the same trie rules, the graph's own dispatch/frame
 *  rules, and its empty-left short circuits */
final class GraphSem(domain: Domain, phase: ExecutionPhase, index: PartialFunction[String, RecursiveOpGraph], declared: Set[SpaceMention] = Set.empty):
  import EffortEvent.*
  private val trie = new CostSem(Backend.Graph, domain, PartialFunction.empty, phase, declared = declared)
  private val notes = mutable.LinkedHashSet.empty[String]
  def notesOut: Vector[String] = notes.toVector
  def summaryStats: (Int, Int) = trie.summaryStats
  /** the callee graphs being executed: a re-entry is a recursion the graph executor cannot bound */
  private val activeCalls = mutable.HashSet.empty[String]
  private def pt(n: Long): Ivl = Ivl(n, n)
  private def sat(x: Long): Long = if x < 0 then Ivl.INF else x

  def run(g: RecursiveOpGraph, env0: AEnv): (Abs, EventBounds, Derivation) =
    var ev = EventBounds.one(GraphFrameAllocation)
    val frame = new Array[Any | Null](g.nodes.length)
    for (nl, i) <- g.nodes.iterator.zipWithIndex do nl match
      case Left(Node("ExtractPathRef", name, _, _)) => env0.paths.find(_._1.s == name).foreach((_, v) => frame(i) = v)
      case Left(Node("ExtractSpaceMention", name, _, _)) => env0.spaces.find(_._1.s == name).foreach((_, v) => frame(i) = v)
      case _ => ()
    val stack = mutable.Stack(frame)
    val kids = mutable.ArrayBuffer.empty[Derivation]
    ev += exec(g, stack, kids)
    val out = stack.top.last match
      case v: Abs => v
      case _ => Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Fresh)
    (out, ev, Derivation("execT graph", Vector(s"${g.nodes.length} slots"), Backend.Graph, None, ev, kids.toVector))

  private def exec(rog: RecursiveOpGraph, stack: mutable.Stack[Array[Any | Null]], kids: mutable.ArrayBuffer[Derivation]): EventBounds =
    var ev = EventBounds.zero
    val l = rog.level
    val s = stack.top
    def sget(p: (Int, Int)): Abs = stack(stack.length - 1 - p._1)(p._2) match
      case v: Abs => v
      case _ => Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Unknown)
    def pget(p: (Int, Int)): PathAbs = stack(stack.length - 1 - p._1)(p._2) match
      case v: PathAbs => v
      case _ => PathAbs.unknown
    var c = 0
    while c < rog.nodes.length do
      ev += EventBounds.one(GraphNodeDispatch)
      rog.nodes(c) match
        case Left(Node(op, constant, kind, inputs)) => kind match
          case "path" => s(c) = op match
            case "ExtractPathRef" => pget((l, c))
            case "Constant" => PathAbs.known(LiteralCodec.decodeConst(constant))
            case "Concat" =>
              val (a, b) = (pget(inputs(0)), pget(inputs(1)))
              PathAbs(for x <- a.value; y <- b.value yield PathValue(x.items ++ y.items), Ivl(Ivl.add(a.len.lo, b.len.lo), Ivl.add(a.len.hi, b.len.hi)))
          case "space" =>
            ev += EventBounds.one(TrieOpEntry)
            /** execT's EMPTY-LEFT SHORT CIRCUIT: every operation but Union returns ∅ without running when
             *  its left operand is empty — a MAY-empty left operand therefore carries no certain event */
            def shortCircuit(a: Abs, e: EventBounds, v: Abs): (Abs, EventBounds) =
              if domain.mayEmpty(a.node) && !domain.mustEmpty(a.node) then
                (Abs(domain.join(v.node, domain.empty.node), Alias.Fresh), EventBounds(e.m.view.mapValues(i => Ivl(0, i.hi)).toMap))
              else (v, e)
            def bin(name: String, mk: (Space, Space) => Space): Abs =
              val (a, b) = (sget(inputs(0)), sget(inputs(1)))
              if name != "Union" && domain.mustEmpty(a.node) then domain.empty
              else
                val env = AEnv(Map(SpaceMention("#l") -> a, SpaceMention("#r") -> b))
                val (v0, e0, d) = trie.analyze(mk(Space.Mention(SpaceMention("#l")), Space.Mention(SpaceMention("#r"))), env)
                val (v, e) = if name == "Union" then (v0, e0) else shortCircuit(a, e0, v0)
                // the term's own three dispatches are the graph's slots, already counted
                ev += EventBounds(e.m.filterNot((k, _) => k == GraphNodeDispatch || k == TrieOpEntry)); kids += d
                v
            def un(mk: Space => Space): Abs =
              val a = sget(inputs(0))
              val env = AEnv(Map(SpaceMention("#l") -> a))
              val (v, e, d) = trie.analyze(mk(Space.Mention(SpaceMention("#l"))), env)
              ev += EventBounds(e.m.filterNot((k, _) => k == GraphNodeDispatch || k == TrieOpEntry)); kids += d
              v
            s(c) = op match
              case "Empty" => domain.empty
              case "Call" =>
                ev += EventBounds.one(CallEntry) + EventBounds.one(GraphFrameAllocation)
                if !index.isDefinedAt(constant) || activeCalls(constant) then
                  notes += (if activeCalls(constant) then s"call to $constant: recursive on the operation graph (execT has no stationary-argument rule) — ⊤"
                            else s"call to $constant: no graph in the index — ⊤")
                  ev += EventBounds.of(GraphNodeDispatch -> Ivl(0, Ivl.INF), TrieOpEntry -> Ivl(0, Ivl.INF), TrieNodeVisit -> Ivl(0, Ivl.INF), FreshTrieNode -> Ivl(0, Ivl.INF),
                                       LoopBodyEntry -> Ivl(0, Ivl.INF), FixpointRound -> Ivl(0, Ivl.INF), CallEntry -> Ivl(0, Ivl.INF), GraphFrameAllocation -> Ivl(0, Ivl.INF),
                                       PatriciaVisit -> Ivl(0, Ivl.INF), NaryOperandProbe -> Ivl(0, Ivl.INF), NaryScratchSlot -> Ivl(0, Ivl.INF))
                  Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Fresh)
                else
                  val code = index(constant)
                  val cframe = new Array[Any | Null](code.nodes.length)
                  for (arg, i) <- inputs.zipWithIndex do cframe(i) = stack(stack.length - 1 - arg._1)(arg._2)
                  val cstack = mutable.Stack(cframe)
                  activeCalls += constant
                  try ev += exec(code, cstack, kids)
                  finally activeCalls -= constant
                  cstack.top.last match { case v: Abs => v; case _ => Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Fresh) }
              case "ExtractSpaceMention" => sget((l, c))
              case "Singleton" =>
                val p = pget(inputs(0))
                ev += EventBounds.of(TrieNodeVisit -> pt(1), FreshTrieNode -> p.len)
                p.value match
                  case Some(v) => Abs(domain.alpha(SpaceValue(Set(v))), Alias.Fresh)
                  case None => Abs(domain.arena.summ(SpatialType(Shape.oneUnknownPath(LenBounds(p.len.lo, if p.len.hi >= Ivl.INF then LenBounds.INF else p.len.hi)), SpaceType.boundedExact(LenBounds(p.len.lo, if p.len.hi >= Ivl.INF then LenBounds.INF else p.len.hi), 1L)), Cause.Literal), Alias.Fresh)
              case "Literal" => domain.literal(LiteralStore.resolve(constant))
              case "Union" => bin("Union", Space.Union.apply)
              case "Intersection" => bin("Intersection", Space.Intersection.apply)
              case "Subtraction" => bin("Subtraction", Space.Subtraction.apply)
              case "Restriction" => bin("Restriction", Space.Restriction.apply)
              case "Raffination" => bin("Raffination", Space.Raffination.apply)
              case "Composition" => bin("Composition", Space.Composition.apply)
              case "Wrap" =>
                val (a, p) = (sget(inputs(0)), pget(inputs(1)))
                if domain.mustEmpty(a.node) then domain.empty
                else
                  ev += EventBounds.of(TrieNodeVisit -> (if domain.mayEmpty(a.node) then Ivl(0, 1) else pt(1)), FreshTrieNode -> (if domain.mayEmpty(a.node) then Ivl(0, p.len.hi) else p.len))
                  p.value match
                    case Some(v) => domain.wrapA(v.items, a)
                    case None => Abs(domain.arena.summ(SpatialTyping.infer(Space.Wrap(Space.Mention(SpaceMention("#w")), Path.Constant(PathValue(List.fill(p.len.lo.toInt.max(0))("?")))), SpatialTyping.Env(spaces = Map(SpaceMention("#w") -> domain.summary(a.node)))), Cause.Literal), Alias.Fresh)
              case "Unwrap" =>
                val (a, p) = (sget(inputs(0)), pget(inputs(1)))
                if domain.mustEmpty(a.node) then domain.empty
                else
                  p.value match
                    case Some(v) =>
                      val env = AEnv(Map(SpaceMention("#l") -> a))
                      val (out0, e0, d) = trie.analyze(Space.Unwrap(Space.Mention(SpaceMention("#l")), Path.Constant(v)), env)
                      val (out, e) = shortCircuit(a, e0, out0)
                      ev += EventBounds(e.m.filterNot((k, _) => k == GraphNodeDispatch || k == TrieOpEntry)); kids += d
                      out
                    case None =>
                      ev += EventBounds.ivl(TrieNodeVisit, Ivl(if domain.mayEmpty(a.node) then 0 else 1, Ivl.add(1, p.len.hi)))
                      // contained in the k-fold tails for the prefix's length k (see CostSem.unwrapUnknown)
                      val maxLen = { val ln = domain.len(a.node); if ln.isEmpty then 0L else if ln.hi >= LenBounds.INF then Ivl.INF else ln.hi }
                      if p.len.lo >= Ivl.INF || (p.len.hi >= Ivl.INF && maxLen >= Ivl.INF) then Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Unknown)
                      else
                        val hi = math.min(p.len.hi, maxLen)
                        var acc: Option[XNode] = None; var t = a.node; var k = 0L
                        while k <= hi do { if k >= p.len.lo then acc = Some(acc.map(domain.join(_, t)).getOrElse(t)); t = domain.fibreLub(t); k += 1 }
                        Abs(acc.getOrElse(domain.arena.empty), Alias.Unknown)
              case "TailsUnion" => un(Space.TailsUnion.apply)
              case "TailsIntersection" => un(Space.TailsIntersection.apply)
              case "Range" => val Array(lo, hi) = constant.split(",", 2).map(_.toInt); un(x => Space.Range(x, lo, hi))
              case other => notes += s"unsupported graph op $other"; Abs(domain.arena.summ(SpatialType.top, Cause.Literal), Alias.Fresh)
        case Right(sg: RecursiveOpGraph) =>
          sg.root.operation match
            case "Iteration" =>
              val src = sget(sg.root.inputs(0))
              ev += EventBounds.one(GraphFrameAllocation)
              val frame = new Array[Any | Null](sg.nodes.length)
              val last = sg.nodes.length - 1
              stack.push(frame)
              src.node match
                case t: XTrie if domain.exact(t) =>
                  var acc = domain.empty
                  for (k, sub) <- t.children do
                    ev += EventBounds.one(LoopBodyEntry)
                    frame(0) = PathAbs.known(PathValue(List(k))); frame(1) = Abs(sub, Alias.Is(SpaceMention(s"${sg.root.constant}#rest#$k")))
                    ev += exec(sg, stack, kids)
                    val body = frame(last) match { case v: Abs => v; case _ => domain.empty }
                    val env = AEnv(Map(SpaceMention("#l") -> acc, SpaceMention("#r") -> body))
                    val (v, e, d) = trie.analyze(Space.Union(Space.Mention(SpaceMention("#l")), Space.Mention(SpaceMention("#r"))), env)
                    ev += EventBounds(e.m.filterNot((kk, _) => kk == GraphNodeDispatch || kk == TrieOpEntry)); kids += d
                    acc = v
                  s(c) = acc
                case _ =>
                  val k = DomainFacts.fanOut(domain, src.node)
                  val fibreT = domain.summary(domain.fibreLub(src.node))
                  // ONE body run under the WEAKENED fibre: sound lower AND upper endpoints (see CostSem.iteration)
                  frame(0) = PathAbs.opaque(pt(1)); frame(1) = Abs(domain.arena.summ(SpatialRecursion.weaken(fibreT), Cause.Literal), Alias.Unknown)
                  val e1 = exec(sg, stack, kids)
                  val body = frame(last) match { case v: Abs => v; case _ => domain.empty }
                  ev += (EventBounds.one(LoopBodyEntry) + e1).scale(k)
                  val bodyT = SpatialRecursion.weaken(domain.summary(body.node))
                  val accT =
                    if k.hi >= Ivl.INF || k.hi > 64 then SpatialType(Shape.top, SpaceType.bounded(bodyT.len, Ivl.mul(k.hi, bodyT.size.hi)))
                    else
                      val ms = (0 until k.hi.toInt.max(1)).map(i => SpaceMention(s"#g$i"))
                      SpatialType.reduce(SpatialTyping.infer(ms.map(m => Space.Mention(m): Space).reduce(Space.Union(_, _)), SpatialTyping.Env(spaces = ms.map(_ -> bodyT).toMap)))
                  val acc = Abs(domain.arena.summ(SpatialRecursion.weaken(accT), Cause.Literal), Alias.Fresh)
                  val bn = trieNodes(body.node)
                  val kb = Ivl(Ivl.mul(k.lo, bn.lo), Ivl.mul(k.hi, bn.hi))
                  ev += EventBounds.of(TrieNodeVisit -> Ivl(0, sat(Ivl.add(k.hi, kb.hi))), FreshTrieNode -> Ivl(0, kb.hi), PatriciaVisit -> Ivl(0, sat(Ivl.mul(2, kb.hi))),
                                       PatriciaEntry -> Ivl(0, sat(Ivl.mul(2, kb.hi))), SubtrieAcceptedByPointer -> Ivl(0, sat(Ivl.add(k.hi, kb.hi))), SubtrieRejectedByPointer -> Ivl(0, sat(Ivl.add(k.hi, kb.hi))),
                                       ReusedSubtrie -> Ivl(0, k.hi), AlgebraBespoke -> Ivl(0, kb.hi), AlgebraIdentityLeft -> Ivl(0, kb.hi), AlgebraIdentityRight -> Ivl(0, kb.hi), AlgebraEmpty -> Ivl(0, kb.hi))
                  s(c) = acc
              stack.pop()
            case "Fixpoint" =>
              ev += EventBounds.one(GraphFrameAllocation)
              val frame = new Array[Any | Null](sg.nodes.length)
              val last = sg.nodes.length - 1
              stack.push(frame)
              var cur = sget(sg.root.inputs(0))
              var done = false
              var n = 0
              var exactSoFar = true
              var evLo = EventBounds.zero; var evHi = EventBounds.zero
              def round(cur: Abs): (Abs, EventBounds) =
                var er = EventBounds.one(FixpointRound)
                frame(0) = Abs(cur.node, Alias.Is(SpaceMention(sg.root.constant)))
                er += exec(sg, stack, kids)
                val step = frame(last) match { case v: Abs => v; case _ => domain.empty }
                val env = AEnv(Map(SpaceMention("#l") -> Abs(cur.node, Alias.Is(SpaceMention(sg.root.constant))), SpaceMention("#r") -> step))
                val (nxt, e, d) = trie.analyze(Space.Union(Space.Mention(SpaceMention("#l")), Space.Mention(SpaceMention("#r"))), env)
                er += EventBounds(e.m.filterNot((kk, _) => kk == GraphNodeDispatch || kk == TrieOpEntry)) + EventBounds.ivl(EqualityFrontierVisit, Ivl(1, trieNodes(nxt.node).hi)); kids += d
                (nxt, er)
              while !done && n < 64 do
                n += 1
                val (nxt, er) = round(cur)
                if exactSoFar && domain.exact(nxt.node) && domain.exact(cur.node) then
                  evLo += er; evHi += er
                  if nxt.node eq cur.node then done = true else cur = nxt
                else
                  exactSoFar = false
                  if n == 1 then evLo += er
                  evHi += er
                  val w = domain.widen(cur.node, nxt.node)
                  if domain.leq(nxt.node, cur.node) then done = true else cur = Abs(w, Alias.Fresh)
              if !done then { notes += "graph fixpoint: no post-fixpoint within 64 abstract rounds"; evHi += EventBounds.ivl(FixpointRound, Ivl(0, Ivl.INF)) }
              else if !exactSoFar then
                val extra = Ivl(0, if domain.size(cur.node).hi >= Ivl.INF then Ivl.INF else (domain.size(cur.node).hi + 1).max(0))
                val (_, er) = round(cur)
                evHi += EventBounds(er.m.view.mapValues(i => Ivl(0, i.hi)).toMap).scale(extra)
              ev += EventBounds((evLo.m.keySet ++ evHi.m.keySet).iterator.map(e => e -> Ivl(evLo(e).lo min evHi(e).lo, evHi(e).hi max evLo(e).hi)).toMap)
              stack.pop()
              s(c) = cur
            case other => notes += s"unsupported subgraph $other"
      c += 1
    ev
  private def trieNodes(x: XNode): Ivl = x match
    case t: XTrie => t.children.values.foldLeft(pt(1))((acc, c) => Ivl(Ivl.add(acc.lo, trieNodes(c).lo), Ivl.add(acc.hi, trieNodes(c).hi)))
    case ch: XChoice => ch.alts.map(trieNodes).reduce((a, b) => Ivl(a.lo min b.lo, a.hi max b.hi))
    case s: XSumm =>
      val cap = Ivl.add(1, Ivl.mul(s.t.size.hi, if s.t.len.hi >= LenBounds.INF then Ivl.INF else s.t.len.hi))
      val n = SpatialFacts.trieNodes(s.t).toOption.getOrElse(Ivl(0, Ivl.INF))
      Ivl(n.lo, math.min(n.hi, cap))
