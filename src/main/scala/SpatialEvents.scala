package morkl

/** ==============================================================================================
 *  EFFORT EVENTS — the "actual steps" oracle review.md finding 2 says the effort model is missing.
 *
 *  THE PROBLEM.  `SpatialCost` predicts `work`/`alloc`/`rounds`, but until now nothing in the tree
 *  DEFINED those units operationally, so "is the prediction close?" was unanswerable and the only
 *  empirical evidence was a Spearman rank check against wall-clock time on 16 programs.  Wall time
 *  validates an ordering; it cannot validate a component.
 *
 *  WHAT THIS FILE IS.  A closed vocabulary of source-level events, each with (a) exactly one
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
 *  ("the disabled sink costs nothing measurable").
 *
 *  WHAT IS NOT COUNTED, and why it matters.  Three sources of real work are outside this
 *  vocabulary because their code is not instrumented:
 *
 *   1. `scala.collection.immutable.Set`/`Map` internals behind the reference evaluator — hash
 *      probes, bucket copies.  A `Set` union of two 1000-element sets therefore counts ONE
 *      `AstDispatch` and nothing else.  Whatever a model claims about element touches has no
 *      oracle; `Cost.touch` carries such claims and is explicitly excluded from calibration.
 *   2. `ITrie` / `IntTrieOps` node visits and node allocations (IntTrie.scala, IntTrieOps.scala).
 *      Executors call into them; the calls are counted ([[EffortEvent.TrieOpEntry]]) but the
 *      per-node descent inside them is not.
 *   3. `evalI` node dispatches (IntTrie.scala).
 *
 *  Those three gaps mean the Trie backend model is UNCALIBRATED and the Graph/Zipper models are
 *  calibrated on dispatch/frame/cursor/allocation events only.  Synthesising an "actual" count from
 *  operand sizes would make the numbers look better and mean nothing, so it is not done. */
enum EffortComponent:
  /** elementary steps the executor itself performs: node dispatches, cursor reads, item comparisons */
  case Work
  /** materialisation: a fresh path, a fresh trie node, a fresh executor frame */
  case Alloc
  /** dynamic frames: loop-body entries, fixpoint rounds, routine calls */
  case Rounds
  /** counted for EXPLANATION only — never summed into a calibrated component (it would double-count) */
  case Explain

/** One counted unit of executor effort.  Every case names its emitting executor; a case with no
 *  emitter is not allowed to exist (review.md finding 6 on `Fact.PrefixAbsent`: a public promise
 *  nothing ever produces is worse than no promise). */
enum EffortEvent(val component: EffortComponent, val emitter: String):
  // ---- node dispatches -------------------------------------------------------------------------
  /** one `Space` node visited by `eval.recs` (MORKL.scala) */
  case AstDispatch extends EffortEvent(EffortComponent.Work, "eval")
  /** one `Path` node visited by `eval.recp` (MORKL.scala) */
  case PathDispatch extends EffortEvent(EffortComponent.Work, "eval")
  /** one operation-graph slot executed by `execT` (GraphExec.scala) */
  case GraphNodeDispatch extends EffortEvent(EffortComponent.Work, "execT")
  /** one `Space` node lifted into a zipper by `transpileZ` (Zipper.scala) */
  case ZipperBuild extends EffortEvent(EffortComponent.Work, "execZ")

  // ---- comparisons -----------------------------------------------------------------------------
  /** one PathItem-vs-PathItem comparison: a `pathValueOrdering` step (the `Range` sort) or one item
   *  of a prefix test (`Restriction`, `Unwrap`) */
  case PathItemComparison extends EffortEvent(EffortComponent.Work, "eval")

  // ---- trie / cursor reads ---------------------------------------------------------------------
  /** one entry into an `ITrie` algebra operation from an executor (the descent INSIDE it is not
   *  counted — see the file header) */
  case TrieOpEntry extends EffortEvent(EffortComponent.Work, "execT,execZ")
  /** one `terminal` / `children` / `descend` query on a (possibly virtual) zipper cursor */
  case ZipperCursorRead extends EffortEvent(EffortComponent.Work, "execZ")
  /** one non-`Lit` node visited by `SpaceZipper.materialize` */
  case ZipperMaterializeNode extends EffortEvent(EffortComponent.Work, "execZ")

  // ---- allocation ------------------------------------------------------------------------------
  /** one fresh `PathValue` built into a result by `eval` */
  case FreshPath extends EffortEvent(EffortComponent.Alloc, "eval")
  /** one fresh `ITrie` node allocated by `SpaceZipper.materialize` */
  case FreshNode extends EffortEvent(EffortComponent.Alloc, "execZ")
  /** one `Array[Any | Null]` executor frame allocated by `execT` */
  case GraphFrameAllocation extends EffortEvent(EffortComponent.Alloc, "execT")

  // ---- dynamic frames --------------------------------------------------------------------------
  /** one iteration/fold head-group body entry */
  case LoopBodyEntry extends EffortEvent(EffortComponent.Rounds, "eval,execT")
  /** one fixpoint round, INCLUDING the terminating round that discovers the iterate is unchanged */
  case FixpointRound extends EffortEvent(EffortComponent.Rounds, "eval,execT")
  /** one routine call entered */
  case CallEntry extends EffortEvent(EffortComponent.Rounds, "eval,execT")

  // ---- explanatory -----------------------------------------------------------------------------
  /** an identity / pointer-equality short circuit was taken (`x ∪ x`, `x ∖ x`, an `eq` subtrie) */
  case ReusedSpace extends EffortEvent(EffortComponent.Explain, "execZ")
  /** `transpileZ` gave up on fusion and materialised a subterm through `evalI` */
  case ZipperFallbackToEvalI extends EffortEvent(EffortComponent.Explain, "execZ")

object EffortEvent:
  def ofComponent(c: EffortComponent): Vector[EffortEvent] = values.iterator.filter(_.component == c).toVector

/** A counted event vector.  Absent keys are zero; addition is saturating (a corpus run cannot make
 *  a count wrap into a small number and silently claim a tight model). */
final case class Events(counts: Map[EffortEvent, Long]):
  def apply(e: EffortEvent): Long = counts.getOrElse(e, 0L)
  def component(c: EffortComponent): Long =
    EffortEvent.ofComponent(c).foldLeft(0L)((n, e) => Ivl.add(n, apply(e)))
  /** the three CALIBRATED projections (whispers §7) */
  def work: Long = component(EffortComponent.Work)
  def alloc: Long = component(EffortComponent.Alloc)
  def rounds: Long = component(EffortComponent.Rounds)
  def total: Long = Ivl.add(Ivl.add(work, alloc), rounds)
  def +(o: Events): Events =
    Events((counts.keySet ++ o.counts.keySet).iterator.map(e => e -> Ivl.add(apply(e), o.apply(e))).toMap)
  def nonZero: Vector[(EffortEvent, Long)] = counts.toVector.filter(_._2 != 0L).sortBy(_._1.ordinal)
  def show: String =
    if nonZero.isEmpty then "(no events)"
    else nonZero.map((e, n) => s"${e}=$n").mkString(" ")
  def showComponents: String = s"work=$work alloc=$alloc rounds=$rounds"

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
   *  `record` is a no-op there.  The overhead claim is measured in `SpatialEventsCheck`. */
  private[morkl] var armed: Boolean = false
  private val active = new ThreadLocal[Counter]
  private var openRegions: Int = 0

  def isCounting: Boolean = armed && active.get != null

  private[morkl] def record(e: EffortEvent, n: Long): Unit =
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
  /** how many times larger the predicted upper is than the truth; `1.0` is exact */
  def upperSlack: Double =
    if actual == 0L then (if upper == 0.0 then 1.0 else Double.PositiveInfinity)
    else upper / actual.toDouble
  /** how many times smaller the predicted lower is than the truth; `1.0` is exact */
  def lowerSlack: Double =
    if lower <= 0.0 then (if actual == 0L then 1.0 else Double.PositiveInfinity)
    else actual.toDouble / lower
  def show: String = f"$label%-28s ${component}%-6s actual=$actual%10d  in [$lower%.0f, $upper%.0f]  " +
    (if contains then "OK  " else "OUT ") + f"slack=${upperSlack}%.2f"

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
   *  median and p95 upper slack, keyed by whatever `label` the caller grouped by. */
  final case class Summary(key: String, n: Int, contained: Int, medianSlack: Double, p95Slack: Double,
                           worst: Double):
    def containmentRate: Double = if n == 0 then 1.0 else contained.toDouble / n
    def show: String =
      f"$key%-34s n=$n%5d  contained=${100.0 * containmentRate}%5.1f%%  " +
      f"median slack=${fmt(medianSlack)}%9s  p95=${fmt(p95Slack)}%9s  worst=${fmt(worst)}%9s"
    private def fmt(d: Double): String = if d.isInfinite then "inf" else f"$d%.2f"

  def summarize(key: String, cs: Vector[Calibration]): Summary =
    if cs.isEmpty then Summary(key, 0, 0, 1.0, 1.0, 1.0)
    else
      val slacks = cs.map(_.upperSlack)
      Summary(key, cs.length, cs.count(_.contains), median(slacks), p95(slacks), slacks.max)

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
