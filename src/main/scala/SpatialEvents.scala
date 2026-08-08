package morkl

/** ==============================================================================================
 *  EFFORT EVENTS — the "actual steps" oracle review.md finding 2 says the effort model is missing.
 *
 *  THE PROBLEM.  `SpatialCost` predicts `work`/`alloc`/`rounds`/`touch`, but until now nothing in
 *  the tree DEFINED those units operationally, so "is the prediction close?" was unanswerable and
 *  the only empirical evidence was a Spearman rank check against wall-clock time on 16 programs.
 *  Wall time validates an ordering; it cannot validate a component.
 *
 *  WHAT THIS FILE IS.  A closed vocabulary of source-level events, each with (a) at least one
 *  emitting site in a real executor and (b) exactly one cost component it belongs to.  A cost model
 *  is then calibratable: evaluate its symbolic components at the concrete input sizes, count the
 *  matching events for a real run, and report containment (`lower <= actual <= upper`) and slack
 *  (`upper / actual`).
 *
 *  INSTRUMENTATION IS NOT ANALYSIS.  Counting events while an executor runs is measurement of a
 *  RUN.  The analysis never calls an executor: `SpatialCost` has no `eval`/`evalI`/`exec*` call, and
 *  the calibration harness lives in the test suite, where executors are legitimate ground truth.
 *
 *  THE DISABLED PATH.  `effort` is an `inline def` guarding a call behind one load of a static
 *  non-final boolean.  When no counting region is open the branch is never taken and nothing else
 *  runs.  That claim is MEASURED, not asserted, in `SpatialEventsCheck`
 *  ("the disarmed sink's cost is measured, not asserted"), both per hook in a tight loop and at
 *  executor level with the hook count of the workload in hand.
 *
 *  WHAT IS COUNTED NOW, AND WHAT IS STILL NOT (review.md item 1).  The three gaps the previous
 *  revision admitted — `evalI` node dispatches, `ITrie`/`IntTrieOps` per-node descent, and trie-node
 *  allocation — are CLOSED: IntTrie.scala and IntTrieOps.scala carry hooks
 *  ([[EffortEvent.TrieDispatch]], [[EffortEvent.TriePathDispatch]], [[EffortEvent.TrieNodeVisit]],
 *  [[EffortEvent.PatriciaVisit]], [[EffortEvent.FreshTrieNode]], [[EffortEvent.ReusedSubtrie]], and
 *  `evalI`'s own [[EffortEvent.LoopBodyEntry]]/[[EffortEvent.FixpointRound]]/[[EffortEvent.CallEntry]]).
 *  All FOUR backends therefore have counted runs, and `touch` — previously an oracle-free component —
 *  is a CALIBRATED component on the three trie-shaped backends.
 *
 *  FOUR GAPS REMAIN, all named and all bounded:
 *
 *   1. `scala.collection.immutable.Set`/`Map` internals behind the REFERENCE evaluator (`eval` over
 *      `Set[PathValue]`) — hash probes, bucket copies.  A `Set` union of two 1000-element sets counts
 *      ONE `AstDispatch` and nothing else.  `eval` performs no `ITrie` work at all, so the reference
 *      backend's `touch` component has NO ORACLE.  That is declared IN THE MODEL
 *      (`CostModel.touchNoOracle`), it is the ONLY named exclusion from the tightness gate, and
 *      `SpatialEventsCheck` asserts the exclusion list is exactly that one entry so it cannot grow
 *      silently.  Synthesising an "actual" count from operand sizes would make the numbers look
 *      better and mean nothing, so it is not done.
 *   2. `IntMap` (Patricia) NODE ALLOCATION inside the standard library — `updated`, `updateWith`,
 *      `- k`, `IntMapUtils.join`.  [[EffortEvent.FreshTrieNode]] counts `ITrie` nodes, not the
 *      `IntMap` spines that hold their children.  The gap is bounded, not open-ended: every `IntMap`
 *      node lives on the child map of exactly one `ITrie` node and a Patricia tree over `k` keys has
 *      at most `2k-1` nodes, so `IntMap` allocation is at most `2 x (child edges) <= 2 x` the counted
 *      `FreshTrieNode` total in the same operation — the same order, with a constant this file
 *      states rather than hides.  The same `2k-1` fact is what makes the `touch` upper bounds in
 *      `SpatialCost` sound (see `TrieAlgebraCost.tPer`).
 *   3. The child-key sort inside `ITrie.range` uses the standard library's `sortBy`, so its
 *      comparisons are not counted.  The models keep the `log` factor anyway (it is real work), which
 *      shows up as slack on `Range` rather than as an unsound bound.  The gap SHRANK with the
 *      order-statistic slice: the sort now runs once per node the window actually cuts (and is
 *      memoised per node), not once per node of the operand, and a full window sorts nothing at all.
 *   4. `Interner.intern` PER PATH ITEM (IntTrie.scala).  `internPath` / `uninternPath` do one
 *      `ConcurrentHashMap` lookup and one cons cell per item of the path, and the only event on that
 *      route is ONE [[EffortEvent.TriePathDispatch]] for the whole `Path` subterm — so a length-`L`
 *      constant costs `L` map probes and is counted as 1.  review.md item 6, fourth bullet, names this
 *      and it is NOT closed.  The gap is bounded by the path-length channel the cost model already
 *      carries (`Lower.LenBounds`): it is at most `len(p)` per counted `TriePathDispatch`, i.e. a
 *      factor the model can name, not an unbounded one.  It is a `Work` gap only; `intern` allocates
 *      nothing per hit and performs no `ITrie` descent, so `Alloc` and `Touch` are unaffected.
 *      Closing it means one hook inside `Interner.intern`, which would move every hand-computed count
 *      in `SpatialEventsCheck` and every calibrated `Work` bound at once — hence it is declared here
 *      rather than done quietly.
 *
 *  WHAT THE CASE-RETURNING ALGEBRA ADDED (review.md items 1 and 2).  `ITrie`'s ring operations return
 *  `ITrie.AlgebraicResult`, so `evalI` — the executable `Backend.Trie` names — accepts and rejects
 *  whole subtries by pointer.  That control state is now counted: [[EffortEvent.AlgebraEmpty]],
 *  [[EffortEvent.AlgebraIdentityLeft]], [[EffortEvent.AlgebraIdentityRight]],
 *  [[EffortEvent.AlgebraBespoke]], [[EffortEvent.SubtrieAcceptedByPointer]],
 *  [[EffortEvent.SubtrieRejectedByPointer]], [[EffortEvent.PatriciaEntry]] and
 *  [[EffortEvent.EqualityFrontierVisit]].  All eight are `Explain`: they do not ADD work, they say
 *  which work was avoided, and a relational cost model (item 2) needs them as its oracle. */
enum EffortComponent:
  /** elementary steps the executor itself performs: node dispatches, cursor reads, item comparisons */
  case Work
  /** materialisation: a fresh path, a fresh `ITrie` node, a fresh executor frame */
  case Alloc
  /** dynamic frames: loop-body entries, fixpoint rounds, routine calls */
  case Rounds
  /** the per-node descent INSIDE the trie algebra: `ITrie`-level recursive entries and `IntMap`
   *  Patricia node visits.  Counted for the three trie-shaped executables; the reference evaluator
   *  performs none of it, which is why `ReferenceCost` declares `touchNoOracle`. */
  case Touch
  /** counted for EXPLANATION only — never summed into a calibrated component (it would double-count) */
  case Explain

/** One counted unit of executor effort.  Every case names its emitting executable(s); a case with no
 *  emitter is not allowed to exist (review.md finding 6 on `Fact.PrefixAbsent`: a public promise
 *  nothing ever produces is worse than no promise). */
enum EffortEvent(val component: EffortComponent, val emitter: String):
  // ---- node dispatches -------------------------------------------------------------------------
  /** one `Space` node visited by `eval.recs` (MORKL.scala) */
  case AstDispatch extends EffortEvent(EffortComponent.Work, "eval")
  /** one `Path` node visited by `eval.recp` (MORKL.scala) */
  case PathDispatch extends EffortEvent(EffortComponent.Work, "eval")
  /** one `Space` node visited by `evalI` (IntTrie.scala) — the trie interpreter's own dispatch */
  case TrieDispatch extends EffortEvent(EffortComponent.Work, "evalI")
  /** one `Path` subterm visited by `pathItemsI` (IntTrie.scala) */
  case TriePathDispatch extends EffortEvent(EffortComponent.Work, "evalI")
  /** one operation-graph slot executed by `execT` (GraphExec.scala) */
  case GraphNodeDispatch extends EffortEvent(EffortComponent.Work, "execT")
  /** one `Space` node lifted into a zipper by `transpileZ` (Zipper.scala) */
  case ZipperBuild extends EffortEvent(EffortComponent.Work, "execZ")

  // ---- comparisons -----------------------------------------------------------------------------
  /** one PathItem-vs-PathItem comparison: a `pathValueOrdering` step (the `Range` sort) or one item
   *  of a prefix test (`Restriction`, `Unwrap`) */
  case PathItemComparison extends EffortEvent(EffortComponent.Work, "eval")

  // ---- trie / cursor reads ---------------------------------------------------------------------
  /** one entry into an `ITrie` algebra operation FROM AN EXECUTOR SLOT.  `execT` emits it per space
   *  slot and `transpileZ` per `Range`; `evalI` does NOT (its per-node [[TrieDispatch]] already
   *  covers the node), which is why `TrieCostModel.opEntry` is 0 and `GraphCost.opEntry` is 1. */
  case TrieOpEntry extends EffortEvent(EffortComponent.Work, "execT,execZ")
  /** one `terminal` / `children` / `descend` query on a (possibly virtual) zipper cursor */
  case ZipperCursorRead extends EffortEvent(EffortComponent.Work, "execZ")
  /** one non-`Lit` node visited by `SpaceZipper.materialize` */
  case ZipperMaterializeNode extends EffortEvent(EffortComponent.Work, "execZ")

  // ---- the descent inside the trie algebra (IntTrie.scala / IntTrieOps.scala) -------------------
  /** one recursive `ITrie`-level entry: a node examined by `union`/`intersection`/`subtraction`/
   *  `restriction`/`composition`/`unwrap`/`wrap`/`joinAll`/`meetAll`/`suffixClosure`/`head`, or one
   *  node walked by `size`/`nodeCount`/`prefixCount`/`toPaths`/`range`. */
  case TrieNodeVisit extends EffortEvent(EffortComponent.Touch, "evalI,execT,execZ")
  /** one recursive entry into an `IntTrieOps` Patricia descent (`unionTries`/`intersectTries`/
   *  `diffTries`/`restrictTries`/`raffTries`) — the simultaneous two-sided walk the algebra is built on */
  case PatriciaVisit extends EffortEvent(EffortComponent.Touch, "evalI,execT,execZ")

  // ---- allocation ------------------------------------------------------------------------------
  /** one fresh `PathValue` built into a result by `eval` */
  case FreshPath extends EffortEvent(EffortComponent.Alloc, "eval")
  /** one fresh `ITrie` node allocated by the `ITrie` algebra itself (IntTrie.scala).  Disjoint from
   *  [[FreshNode]]: `SpaceZipper.materialize` builds its nodes in Zipper.scala, not here. */
  case FreshTrieNode extends EffortEvent(EffortComponent.Alloc, "evalI,execT,execZ")
  /** one fresh `ITrie` node allocated by `SpaceZipper.materialize` */
  case FreshNode extends EffortEvent(EffortComponent.Alloc, "execZ")
  /** one `Array[Any | Null]` executor frame allocated by `execT` */
  case GraphFrameAllocation extends EffortEvent(EffortComponent.Alloc, "execT")

  // ---- dynamic frames --------------------------------------------------------------------------
  /** one iteration/fold head-group body entry */
  case LoopBodyEntry extends EffortEvent(EffortComponent.Rounds, "eval,evalI,execT")
  /** one fixpoint round, INCLUDING the terminating round that discovers the iterate is unchanged */
  case FixpointRound extends EffortEvent(EffortComponent.Rounds, "eval,evalI,execT")
  /** one routine call entered */
  case CallEntry extends EffortEvent(EffortComponent.Rounds, "eval,evalI,execT")

  // ---- the ALGEBRAIC RESULT CASE of the case-returning trie algebra (review.md items 1 and 2) ----
  // Explanatory by construction: these do not add work, they say WHICH work was avoided.  A cost
  // model cannot express "an entire left subspace was accepted by pointer" unless the oracle counts
  // it, and a `Meas`-only summary (size/len/heads/nodes plus `same`/`headDisjoint`) cannot express it
  // either.  Exactly ONE of the four `Algebra*` events fires per algebraic decision made by
  // `ITrie.{unionR,intersectionR,subtractionR,restrictionR,raffinationR,compositionR}`, and the one
  // that fires names the object the caller reuses — so their sum is the number of decisions, and
  // `AlgebraIdentityLeft + AlgebraIdentityRight` is the number of nodes reused whole.  `Identity(BOTH)`
  // is reported as LEFT, because that is the object `pick` hands back.
  /** the operation's result is the empty set at this node (disjointness, annihilation, full removal) */
  case AlgebraEmpty extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")
  /** the result IS the left argument node: containment / disjoint-subtraction / terminal-prefix
   *  restriction / `a·{ε}` — the whole left subspace is accepted by pointer, nothing is allocated */
  case AlgebraIdentityLeft extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")
  /** the result IS the right argument node: reverse containment, `{ε}·b` */
  case AlgebraIdentityRight extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")
  /** the result genuinely mixes the arguments and a fresh node was built */
  case AlgebraBespoke extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")
  /** a whole subtrie became part of the result WITHOUT being traversed: an `Identity` decision, a
   *  Patricia branch attached unchanged, an `n`-ary group with a single contributor, or a child of a
   *  `range` window that lies entirely inside it.  THE headline number of the optimal algebra. */
  case SubtrieAcceptedByPointer extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")
  /** a whole subtrie was discarded WITHOUT being traversed: a Patricia prefix mismatch (disjointness),
   *  a missing key in a `meetAll` round, or a `range` child entirely outside the window */
  case SubtrieRejectedByPointer extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")
  /** one single-key Patricia ENTRY operation performed by the algebra (`get`/`updated`/`- k`, or a
   *  `Tip` arm of a descent) — the per-entry work `PatriciaVisit` (per recursive descent) omits */
  case PatriciaEntry extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")
  /** one node compared by `ITrie.equalT` — the fixpoint convergence test's EQUALITY FRONTIER.
   *
   *  Accounted separately from `touch` DELIBERATELY.  It is real executor work (review.md item 6 is
   *  right that a structural `==` walk was uninstrumented), but folding it into a calibrated component
   *  would silently change what every existing `touch` bound in `SpatialCost` is compared against.
   *  Counting it here makes the frontier visible now; re-attributing it belongs with the cost-model
   *  work of item 6. */
  case EqualityFrontierVisit extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")

  // ---- explanatory -----------------------------------------------------------------------------
  /** an identity / pointer-equality short circuit was taken at the ZIPPER level (`x ∪ x`, `x ∖ x`) */
  case ReusedSpace extends EffortEvent(EffortComponent.Explain, "execZ")
  /** an `a eq b` short circuit fired inside the `ITrie` algebra (a shared sub-trie was accepted or
   *  pruned whole instead of being descended) */
  case ReusedSubtrie extends EffortEvent(EffortComponent.Explain, "evalI,execT,execZ")
  /** `transpileZ` gave up on fusion and materialised a subterm through `evalI` */
  case ZipperFallbackToEvalI extends EffortEvent(EffortComponent.Explain, "execZ")

object EffortEvent:
  /** the executables a hook may name — the closure test in `SpatialEventsCheck` checks against this */
  val executables: Vector[String] = Vector("eval", "evalI", "execT", "execZ")
  def ofComponent(c: EffortComponent): Vector[EffortEvent] = values.iterator.filter(_.component == c).toVector
  /** the components whose totals a cost model's prediction is compared against */
  val calibratedComponents: Vector[EffortComponent] =
    Vector(EffortComponent.Work, EffortComponent.Alloc, EffortComponent.Rounds, EffortComponent.Touch)

/** A counted event vector.  Absent keys are zero; addition is saturating (a corpus run cannot make
 *  a count wrap into a small number and silently claim a tight model). */
final case class Events(counts: Map[EffortEvent, Long]):
  def apply(e: EffortEvent): Long = counts.getOrElse(e, 0L)
  def component(c: EffortComponent): Long =
    EffortEvent.ofComponent(c).foldLeft(0L)((n, e) => Ivl.add(n, apply(e)))
  /** the four CALIBRATED projections (whispers §7, extended with `touch`) */
  def work: Long = component(EffortComponent.Work)
  def alloc: Long = component(EffortComponent.Alloc)
  def rounds: Long = component(EffortComponent.Rounds)
  def touch: Long = component(EffortComponent.Touch)
  def total: Long = Ivl.add(Ivl.add(Ivl.add(work, alloc), rounds), touch)
  def +(o: Events): Events =
    Events((counts.keySet ++ o.counts.keySet).iterator.map(e => e -> Ivl.add(apply(e), o.apply(e))).toMap)
  def nonZero: Vector[(EffortEvent, Long)] = counts.toVector.filter(_._2 != 0L).sortBy(_._1.ordinal)
  def show: String =
    if nonZero.isEmpty then "(no events)"
    else nonZero.map((e, n) => s"${e}=$n").mkString(" ")
  def showComponents: String = s"work=$work alloc=$alloc rounds=$rounds touch=$touch"

object Events:
  val zero: Events = Events(Map.empty)

/** A destination for events.  Only two implementations exist and neither is ever consulted by an
 *  analysis. */
trait EffortSink:
  def add(e: EffortEvent, n: Long): Unit

object EffortSink:
  /** A flat array of saturating counters.  Not thread-safe by design: it is bound to ONE thread by
   *  [[count]], so counting adds no synchronisation to an executor. */
  final class Counter extends EffortSink:
    private val v = new Array[Long](EffortEvent.values.length)
    def add(e: EffortEvent, n: Long): Unit =
      val i = e.ordinal
      v(i) = Ivl.add(v(i), n)
    def apply(e: EffortEvent): Long = v(e.ordinal)
    def snapshot: Events = Events(EffortEvent.values.iterator.map(e => e -> v(e.ordinal)).filter(_._2 != 0L).toMap)
    def clear(): Unit = java.util.Arrays.fill(v, 0L)

  /** THE ARMED FLAG.
   *
   *  A plain (non-final, non-volatile) static boolean.  A hook compiles to one static load plus a
   *  branch that is never taken while counting is off, and the JIT cannot fold it away only because
   *  the field is mutable — which is the entire cost.  It is deliberately NOT volatile: the counter
   *  itself is thread-local, so a thread that never opened a region simply has no counter and every
   *  `record` is a no-op there.  The overhead claim is measured in `SpatialEventsCheck`.
   *
   *  PUBLIC BY NECESSITY, not by design: `IntTrieOps` must live in `scala.collection.immutable` to
   *  see `IntMap`'s Patricia structure, and an `inline` hook expanded there cannot reach a
   *  `private[morkl]` field.  Only [[count]] may WRITE it. */
  var armed: Boolean = false
  private val active = new ThreadLocal[Counter]
  private var openRegions: Int = 0

  def isCounting: Boolean = armed && active.get != null

  /** public for the same reason as [[armed]] */
  def record(e: EffortEvent, n: Long): Unit =
    val c = active.get
    if c != null then c.add(e, n)

  /** Run `body` with counting on for THIS thread, and return its events.  Nesting is supported: the
   *  inner region's counter shadows the outer one (the outer therefore excludes the inner). */
  def count[A](body: => A): (A, Events) =
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

  /** Events only — for the common case where the result is already known/checked elsewhere. */
  def events(body: => Any): Events = count(body)._2

/** Counting helpers whose disabled path is EXACTLY the original library call. */
object Effort:
  /** `x.startsWith(p)`, counting one [[EffortEvent.PathItemComparison]] per item actually compared.
   *  When the sink is disarmed this is the untouched `List.startsWith`. */
  def startsWith(x: List[PathItem], p: List[PathItem]): Boolean =
    if !EffortSink.armed then x.startsWith(p)
    else
      var a = x
      var b = p
      var ok = true
      while ok && b.nonEmpty do
        if a.isEmpty then ok = false
        else
          EffortSink.record(EffortEvent.PathItemComparison, 1L)
          if a.head != b.head then ok = false else { a = a.tail; b = b.tail }
      ok

/** Emit one event.  Inline so the disabled path is a static load and a not-taken branch. */
inline def effort(inline e: EffortEvent): Unit =
  if EffortSink.armed then EffortSink.record(e, 1L)

/** Emit `n` of one event (for a bulk step that is genuinely `n` units). */
inline def effortN(inline e: EffortEvent, inline n: Long): Unit =
  if EffortSink.armed then EffortSink.record(e, n)

// ================================================================================================
// PHASES AND CALIBRATION
// ================================================================================================

/** COLD vs WARM.  The distinction is a property of the RUN, not of the symbolic expression
 *  (whispers §7): a cold run pays for construction/interning/compilation that a warm run finds
 *  cached.  Concretely in this tree:
 *
 *   - `iLiteral`/`iLiteralStr` build an `ITrie` from a `SpaceValue` on first sight and return the
 *     cached trie afterwards, so a warm `Literal` is a map lookup and not `|v|` insertions;
 *   - `eval(Literal(v))` returns the ALREADY STORED `Set` in both phases — the `|v|` construction
 *     cost belongs to whoever built the literal, not to the evaluator (review.md finding 2, first
 *     bullet);
 *   - `transpile` + `optimize` + `Interner` work happens once per program, not per execution. */
enum ExecutionPhase:
  case Cold, Warm

/** One measured execution: which executable, in which phase, and what it counted. */
final case class CountedRun(backend: String, phase: ExecutionPhase, events: Events):
  def show: String = f"$backend%-10s ${phase}%-4s ${events.showComponents}"

/** One (component, backend, phase) calibration point: the counted actual against the predicted
 *  interval.  `Double` endpoints because a symbolic prediction is evaluated numerically and may be
 *  `+inf`. */
final case class Calibration(label: String, component: EffortComponent,
                             actual: Long, lower: Double, upper: Double):
  def contains: Boolean = lower <= actual.toDouble + 1e-9 && actual.toDouble <= upper + 1e-9
  /** is the prediction FINITE?  An `Amount.Unbounded` contains trivially and says nothing. */
  def bounded: Boolean = !upper.isInfinite
  /** how many times larger the predicted upper is than the truth; `1.0` is exact.  Undefined (`inf`)
   *  when nothing was counted, which is why [[slack]] exists and is what the gate uses. */
  def upperSlack: Double =
    if actual == 0L then (if upper == 0.0 then 1.0 else Double.PositiveInfinity)
    else upper / actual.toDouble
  /** THE GATED SLACK: `(upper + 1) / (actual + 1)`.
   *
   *  Additively smoothed so it is finite whenever the prediction is, including the very common
   *  `actual = 0` rows (a program that allocates nothing, a term with no loop).  It agrees with
   *  [[upperSlack]] to within `1/actual`, never hides a large absolute over-prediction (`actual = 0,
   *  upper = 1000` still reports 1001), and is never larger than `upperSlack` when `actual >= 1`. */
  def slack: Double = (upper + 1.0) / (actual.toDouble + 1.0)
  /** how many times smaller the predicted lower is than the truth; `1.0` is exact */
  def lowerSlack: Double =
    if lower <= 0.0 then (if actual == 0L then 1.0 else Double.PositiveInfinity)
    else actual.toDouble / lower
  def show: String = f"$label%-28s ${component}%-6s actual=$actual%10d  in [$lower%.0f, $upper%.0f]  " +
    (if contains then "OK  " else "OUT ") + f"slack=${slack}%.2f"

object Calibration:
  /** the q-quantile of a non-empty sample, nearest-rank (infinities are kept, not dropped: an
   *  infinite slack is a real result about the model and must not be hidden) */
  def quantile(xs: Vector[Double], q: Double): Double =
    require(xs.nonEmpty && 0.0 <= q && q <= 1.0, s"quantile($q) of ${xs.length} samples")
    val sorted = xs.sorted
    sorted(math.round((sorted.size - 1) * q).toInt)

  def median(xs: Vector[Double]): Double = quantile(xs, 0.5)
  def p95(xs: Vector[Double]): Double = quantile(xs, 0.95)

  /** Aggregate a bag of calibration points into the table review.md asks for: containment rate plus
   *  median, p95 and WORST slack (the two the tightness gate reads), keyed by whatever `label` the
   *  caller grouped by.  `unbounded` and `zeroActual` are reported so a tight-looking row cannot be
   *  tight only because most of its predictions said nothing. */
  final case class Summary(key: String, n: Int, contained: Int, medianSlack: Double, p95Slack: Double,
                           worst: Double, unbounded: Int, zeroActual: Int):
    def containmentRate: Double = if n == 0 then 1.0 else contained.toDouble / n
    def show: String =
      f"$key%-34s n=$n%5d  contained=${100.0 * containmentRate}%5.1f%%  " +
      f"median=${fmt(medianSlack)}%9s  p95=${fmt(p95Slack)}%9s  worst=${fmt(worst)}%9s" +
      (if unbounded == 0 then "" else s"  UNBOUNDED=$unbounded") +
      (if zeroActual == 0 then "" else s"  actual=0 on $zeroActual")
    private def fmt(d: Double): String = if d.isInfinite then "inf" else f"$d%.2f"

  /** the gated summary: over [[Calibration.slack]] */
  def summarize(key: String, cs: Vector[Calibration]): Summary = summarize(key, cs, _.slack)

  /** the same over the RAW multiplicative slack, for rows where something was actually counted */
  def summarizeRaw(key: String, cs: Vector[Calibration]): Summary =
    summarize(key, cs.filter(_.actual > 0L), _.upperSlack)

  def summarize(key: String, cs: Vector[Calibration], f: Calibration => Double): Summary =
    if cs.isEmpty then Summary(key, 0, 0, 1.0, 1.0, 1.0, 0, 0)
    else
      val xs = cs.map(f)
      Summary(key, cs.length, cs.count(_.contains), median(xs), p95(xs), xs.max,
              cs.count(!_.bounded), cs.count(_.actual == 0L))

  /** Spearman rank correlation — kept, but DEMOTED to a secondary trend metric (review.md 2). */
  def spearman(xs: Vector[Double], ys: Vector[Double]): Double =
    require(xs.length == ys.length && xs.nonEmpty)
    def ranks(v: Vector[Double]): Vector[Double] =
      val order = v.indices.sortBy(v).toVector
      val r = Array.fill(v.length)(0.0)
      var i = 0
      while i < order.length do
        var j = i
        while j + 1 < order.length && v(order(j + 1)) == v(order(i)) do j += 1
        val avg = (i + j) / 2.0
        for k <- i to j do r(order(k)) = avg
        i = j + 1
      r.toVector
    val (rx, ry) = (ranks(xs), ranks(ys))
    val n = xs.length.toDouble
    val (mx, my) = (rx.sum / n, ry.sum / n)
    val cov = rx.zip(ry).map((a, b) => (a - mx) * (b - my)).sum
    val sx = math.sqrt(rx.map(a => (a - mx) * (a - mx)).sum)
    val sy = math.sqrt(ry.map(b => (b - my) * (b - my)).sum)
    if sx == 0.0 || sy == 0.0 then 0.0 else cov / (sx * sy)
end Calibration
