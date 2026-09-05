package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==============================================================================================
 *  THE PRODUCT REQUIREMENTS FOR A COST ESTIMATE
 *
 *  ==WHAT WAS WRONG==
 *  The tightness gates in `SpatialEventsCheck` were SELF-DERIVED: every threshold was read off the
 *  measurement the suite printed and rounded up.  A gate built that way cannot fail for the reason a
 *  gate exists — it says "the number did not move", never "the number is usable".  The published
 *  consequence was a blessed 4,500,000x `Touch` slack and a 250,000x `Alloc` slack on the
 *  cornerstones, with n-queens at ~3,839x work / 213,465x allocation / 3.98Mx touch, and Puzzle and
 *  Datalog removed from the statistic altogether.  Those are failed answers.
 *
 *  ==WHAT REPLACES IT==
 *  Three PRODUCT requirements, declared here from what a consumer of the estimate needs, stratified by
 *  (backend, component) with per-operator ladders on top:
 *
 *   1. WIDTH  — `(upper + 1) / (lower + 1)`.  An interval a caller cannot act on is not an answer.
 *      `[0, inf]` is the degenerate case; `[0, 10^200]` (Puzzle's, today) is the same failure with a
 *      finite number in it.
 *   2. ERROR  — `(upper + 1) / (actual + 1)` against COUNTED events.  What "how many steps?" means.
 *   3. SLOPE  — `log2((C(2n) + 1) / (C(n) + 1))` over a geometric ladder, predicted against measured
 *      and against the DECLARED growth class of the family.  THIS IS THE IMPORTANT ONE (the user's
 *      first steer): an estimate may be off by a constant, but an estimate that is off by a GROWTH
 *      CLASS is a failure even when it "contains" the measurement.  A bound that is linear where the
 *      algorithm is `O(depth)` fails here and passes every containment test ever written.
 *
 *  ==WHY THESE NUMBERS==
 *  They are not measurements.  Each tier states the decision it has to support:
 *
 *   - [[Tier.Selection]] — an estimate that CHOOSES A BACKEND.  The four executables differ by
 *     1.3x-7x on the cornerstones of this repository (aunt: `eval` work 1265 against `evalI` 193, a
 *     6.5x gap; gol: 7970 against 3390, 2.4x).  An estimate whose error exceeds the gap it is being
 *     used to resolve cannot resolve it, so the error budget is 4x and the width budget 8x.
 *   - [[Tier.Budget]] — an estimate that answers "will this run inside my time/memory budget".  An
 *     order of magnitude is the outer edge of useful for that question: 10x error, 64x width.
 *   - [[Tier.GrowthClass]] — an estimate that only claims the SHAPE of the curve.  100x error is not
 *     a useful absolute number and this tier says so; what it still enforces at full strength is the
 *     slope.  Using it is a statement that this channel is a classifier, not a predictor.
 *
 *  The slope budget is 0.35 doublings in every tier, including the weakest.  Adjacent growth classes
 *  differ by at least ~0.5 of a doubling in this range (`n` vs `n log n` at n=512 is 0.11 per doubling,
 *  `n` vs `n^2` is 1.0), so 0.35 separates constant-or-depth from linear — which is the distinction the
 *  whole optimal-backend argument rests on — while tolerating the log factors that are genuinely there.
 *
 *  ==AND WHEN A CHANNEL CANNOT MEET ITS TIER (tasks.md, milestone M1)==
 *  The gate is SOUNDNESS: every counted rung inside its predicted interval, every endpoint finite and
 *  below [[ProductRequirement.Astronomical]].  A channel that is sound but wider than its tier is printed
 *  `NOT USEFUL` for that tier — "wide intervals are allowed at this milestone but are reported as not
 *  useful" — and nothing else: there is no ledger of named exceptions any more, because a ledger is what
 *  turned known failures into a passing build.  Tightening a channel to its tier is later milestones'
 *  work and is measured here, row by row, against the tiers declared below. */
object ProductRequirement:

  /** THE ABSOLUTE CEILING ON AN INTERVAL ENDPOINT, and it is not read off any measurement.
   *
   *  the requirement: "Replacing infinity with `8e55` is not meaningful progress.  A bound that cannot
   *  distinguish the real execution from tens of orders of magnitude more work is unusable ... and
   *  should fail the gate just as an infinite bound does."  So it does, and the number is a statement
   *  about MACHINES rather than about this repository:
   *
   *   - `alloc` counts fresh `ITrie`/`PathValue` nodes, each at least 16 bytes.  10^12 of them is
   *     16 TB of live allocation — no machine completes that, so a predicted `alloc` above it is not a
   *     capacity answer about anything executable.
   *   - `work`/`touch`/`rounds` count primitive steps.  At the ~1 ns/step this tree measures
   *     (`SpatialEventsCheck`'s disarmed-hook accounting), 10^12 steps is ~17 minutes and 10^13 is
   *     three hours; a bound above 10^12 cannot answer "will this finish" for any caller.
   *
   *  A bound above this ceiling is therefore the same failed result as `inf` with a number in it, and it
   *  is gated under the `magnitude` statistic on every channel that produces a numeric endpoint. */
  val Astronomical: Double = 1.0e12

  /** one requirement tier: the four budgets plus the decision they exist to support */
  final case class Tier(name: String, width: Double, error: Double, slopeExcess: Double,
                        magnitude: Double, why: String):
    def show: String =
      f"$name%-12s width<=$width%8.1f error<=$error%8.1f slope<=+$slopeExcess%.2f " +
      f"endpoint<=${if magnitude.isInfinite then "inf" else f"$magnitude%.0e"}%8s"
    /** the budget for one named statistic.  `error`/`error-p95` share the error budget and
     *  `width`/`width-p95` the width budget: a p95 is the SAME requirement measured over a sample where
     *  a single outlier program is not the claim, not a second, softer requirement.
     *
     *  `lower-*` shares the ERROR budget on purpose: `(actual + 1)/(lower + 1)` asks the same question
     *  of the lower endpoint that `error` asks of the upper one, and a channel whose lower endpoint is
     *  0 where the execution provably allocated or touched fails it by construction (the requirement: "no
     *  zero lower endpoint when a nonempty execution must allocate or touch").
     *
     *  `numeric` has a budget of ZERO ON EVERY TIER, [[NotGated]] included.  That is not a calibration
     *  of constants — it is the precondition for having an estimate at all, and the reference
     *  evaluator's exemption is from its CONSTANTS being a product, not from its answer existing.  A
     *  symbolic prediction on a closed, terminating cornerstone scores `inf` here and fails. */
    def budget(what: String): Double =
      if what.startsWith("numeric") then 0.0
      else if what.startsWith("width") then width
      else if what.startsWith("error") then error
      else if what.startsWith("lower") then error
      else if what.startsWith("magnitude") then magnitude
      else slopeExcess

  val Selection: Tier = Tier("selection", 8.0, 4.0, 0.35, Astronomical,
    "this channel decides which executable to run; the inter-backend gap on real programs is 1.3x-7x, " +
    "so an estimate with more error than that cannot resolve the choice it is used for")
  val Budget: Tier = Tier("budget", 64.0, 10.0, 0.35, Astronomical,
    "this channel answers 'does this fit in my time/memory budget'; one order of magnitude is the " +
    "outer edge of usable for capacity planning")
  val GrowthClass: Tier = Tier("growth-class", 1024.0, 100.0, 0.35, Astronomical,
    "this channel is a CLASSIFIER, not a predictor: its absolute value is not usable and this tier " +
    "says so out loud, but its SLOPE is held to the full budget")

  /** THE REFERENCE EVALUATOR IS NOT GATED (the user's second steer).  `eval` over `Set[PathValue]` is
   *  allowed to be slow, its constants are not a product, and its `touch` has no oracle at all
   *  (`CostModel.touchNoOracle`).  Its rows are PRINTED wherever they are measured — an ungated row is
   *  still published — but no threshold is asserted on them, because calibrating the reference
   *  evaluator's constants is the wrong place to spend the budget. */
  val NotGated: Tier = Tier("not-gated", Double.PositiveInfinity, Double.PositiveInfinity,
    Double.PositiveInfinity, Double.PositiveInfinity,
    "the reference evaluator is not a product: `eval` over Set[PathValue] is allowed to be slow, its " +
    "constants are not gated, and its `touch` component has no counted oracle (the Set internals carry " +
    "no hooks). The rows are published, not asserted — but see `Tier.budget`: the `numeric` requirement " +
    "still applies, because an ungated CONSTANT is not the same thing as no answer")

  /** ONE WORKLOAD CLASS — the review asks for "a declared maximum interval RATIO per component AND
   *  WORKLOAD CLASS", so the classes are declared here instead of being implicit in which suite happens
   *  to call the gate.  A class either carries the [[tiers]] ratios or says out loud that it does not,
   *  and every scope that publishes rows must be declared here. */
  final case class Workload(scope: String, gated: Boolean, why: String)

  val workloads: Vector[Workload] = Vector(
    Workload("operator", true,
      "one CLOSED one-operator program per row with its inputs declared exactly (|a| = 64, |b| = 16). " +
      "Every endpoint is a number and WIDTH needs no execution, so the ratio requirement applies at full " +
      "strength; ERROR and SLOPE need counted runs and ladders and are gated in the other two classes"),
    Workload("ladder", true,
      "one operator per family over a geometric ladder of DECLARED inputs, on `Routine.optimized`'s " +
      "body. This is the class the SLOPE requirement exists for, and the only one that can see a " +
      "growth-class error; the asymptotic half is measured past the crossover region"),
    Workload("cornerstone", true,
      "whole real programs on `Routine.optimized`'s body against counted runs of the optimal backends. " +
      "This is the class the numbers a caller would actually act on live in, so every statistic applies"),
    Workload("corpus", false,
      "DEFINITIONAL random terms from the fuzzer. Their SOUNDNESS (containment) is gated at 100% and " +
      "that is what a random corpus is the right instrument for; their tightness is not gated because " +
      "a definitional-form tightness number is the wrong question (the user's third steer: asymptotics " +
      "belong on the optimized program). NOTE WHAT THIS DOES NOT EXCUSE: the cornerstones below are the " +
      "same programs' OPTIMIZED bodies and they are gated on every statistic"))

  def workloadOf(scope: String): Option[Workload] = workloads.find(_.scope == scope)

  /** THE STRATIFICATION BY BACKEND AND COMPONENT.
   *
   *  `Rounds` is [[Selection]] everywhere: a loop frame / fixpoint round / call entry is a control-flow
   *  event the analysis can count exactly on a closed program, and it is measured exactly on all four
   *  cornerstones that terminate (`rounds actual=7 in [7,7]`).  There is no excuse for it to be loose.
   *
   *  `Work` is [[Selection]] on the three trie-shaped executables for the same reason — a node dispatch
   *  is one per AST node per visit and the analysis knows the AST.
   *
   *  `Alloc` and `Touch` are [[Budget]]: both are bounded through the frontier summary, which is exact
   *  where the shape is closed and a ceiling where it is not, so a factor is expected and an order of
   *  magnitude is not.  Neither is [[GrowthClass]] — demoting them to a classifier would be giving up
   *  on the numbers the optimal-backend argument is made of. */
  val tiers: Map[(String, EffortComponent), Tier] = Map(
    ("reference", EffortComponent.Work)   -> NotGated,
    ("reference", EffortComponent.Alloc)  -> NotGated,
    ("reference", EffortComponent.Rounds) -> NotGated,
    ("reference", EffortComponent.Touch)  -> NotGated,
    ("trie",   EffortComponent.Work)   -> Selection,
    ("trie",   EffortComponent.Alloc)  -> Budget,
    ("trie",   EffortComponent.Rounds) -> Selection,
    ("trie",   EffortComponent.Touch)  -> Budget,
    ("zipper", EffortComponent.Work)   -> Budget,
    ("zipper", EffortComponent.Alloc)  -> Budget,
    ("zipper", EffortComponent.Rounds) -> Selection,
    ("zipper", EffortComponent.Touch)  -> Budget,
    ("graph",  EffortComponent.Work)   -> Selection,
    ("graph",  EffortComponent.Alloc)  -> Budget,
    ("graph",  EffortComponent.Rounds) -> Selection,
    ("graph",  EffortComponent.Touch)  -> Budget)

  def tierOf(backend: String, comp: EffortComponent): Option[Tier] = tiers.get((backend, comp))


/** ONE GATE DECISION, so the caller can print the whole table and fail once at the end.
 *
 *  ledger entry that explains a red row — it is printed, it is never consulted by [[ok]], and it was
 *  called `limitation` while it still had a vote. */
final case class GateRow(scope: String, subject: String, backend: String, comp: EffortComponent,
                         what: String, measured: Double, tier: ProductRequirement.Tier):
  def permitted: Double = tier.budget(what)
  def key: String = s"$scope $subject $backend $comp $what".trim
  def ok: Boolean = measured <= permitted + 1e-9
  def show: String =
    f"$key%-70s ${GateRow.fmt(measured)}%12s <= ${GateRow.fmt(permitted)}%12s  " +
    f"${if ok then "OK" else "FAIL"}%-4s [${tier.name}]"

object GateRow:
  def fmt(d: Double): String =
    if d.isInfinite then "inf" else if math.abs(d) >= 1e6 then f"$d%.2e" else f"$d%.2f"

class SpatialScaleCheck extends FunSuite, CalibrationProbe:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  // ==============================================================================================
  // 1. SHAPE BUILDERS — the correlated shapes a random corpus never produces
  // ==============================================================================================

  def pv(items: String*): PathValue = PathValue(items.toList)
  val eps: SpaceValue = SpaceValue(Set(PathValue(Nil)))
  def spc(ps: IterableOnce[PathValue]): SpaceValue = SpaceValue(ps.iterator.toSet)

  /** `n` distinct leaves under a fixed prefix — the PREFIX CYLINDER whose selected subtree grows */
  def fan(n: Int, tag: String, pre: List[String] = Nil, from: Int = 0, step: Int = 1): SpaceValue =
    spc((0 until n).map(i => PathValue(pre :+ s"$tag${from + i * step}")))
  /** the fixed 6-item prefix the cylinder families select by */
  val cyl: List[String] = List("c0", "c1", "c2", "c3", "c4", "c5")
  /** `n` paths over a FIXED number of heads — the rest-chain source (`K_1 = heads`, `K_2 = n`) */
  def chain(n: Int, heads: Int, tag: String): SpaceValue =
    spc((0 until n).map(i => pv(s"$tag.k${i % heads}", s"$tag.v$i")))

  def sm(s: String): SpaceMention = SpaceMention(s)

  // ==============================================================================================
  // 2. THE HARNESS
  // ==============================================================================================

  /** one rung's inputs and the routine they feed */
  final case class Scenario(routine: Routine, spaces: Map[SpaceMention, SpaceValue],
                            paths: Map[PathRef, PathValue] = Map.empty,
                            rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty)

  /** A generator family: one operator, one declared growth class, one geometric ladder.
   *
   *  `declared` is the class the family CLAIMS, per component, for the optimal backends;
   *  `perBackend` overrides it where the backends genuinely differ — which is the whole point of the
   *  fixed-selective-consumer family, where `execZ` is flat and `evalI` is linear on the same term. */
  final case class Family(name: String, op: String, why: String,
                          build: Int => Scenario,
                          declared: Map[EffortComponent, Double] = Map.empty,
                          perBackend: Map[(String, EffortComponent), Double] = Map.empty,
                          graph: Boolean = true):
    def declaredFor(backend: String, comp: EffortComponent): Option[Double] =
      perBackend.get((backend, comp)).orElse(declared.get(comp))

  val flat: Map[EffortComponent, Double] =
    EffortEvent.calibratedComponents.map(_ -> 0.0).toMap
  def linearIn(cs: EffortComponent*): Map[EffortComponent, Double] =
    flat ++ cs.map(_ -> 1.0)

  /** THE GEOMETRIC LADDER — NINE rungs, EIGHT doublings, and the length is the point.
   *
   *  It was five rungs (64..1024), and the fourth product requirement is precisely that this was
   *  not enough: "matching empirical and predicted growth class AFTER the crossover region".  LIM-4
   *  records the crossover concretely — `SpatialFrontier`'s Patricia term is
   *  `min(2(fanL + fanR), 2*PatriciaBits*(gateFan + |A|))` with `PatriciaBits = 33`, so the
   *  OPERAND-INDEPENDENT branch cannot win until the growing fan passes ~33x the gating fan, and the
   *  five-rung ladder sat ENTIRELY INSIDE that region.  Inside it a `min` of a growing and a constant
   *  term IS growing, so a predicted slope of 0.93 against a measured 0.00 is not a growth-class error at
   *  all — and a five-rung statistic cannot tell that case from a genuinely linear bound.  That is a gate
   *  that cannot see the distinction the whole optimal-backend argument rests on.
   *
   *  So the ladder runs to 16384.  Cost of the extra four rungs, measured: the ladder test went from
   *  1.3 s to the number printed at the end of this suite — the rungs are geometric, so the top one
   *  dominates and it is still seconds, which is what makes the honest ladder affordable. */
  val ladder: Vector[Int] = Vector(64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384)

  /** THE FIRST RUNG PAST THE CROSSOVER REGION.  Rungs at or above this are the ASYMPTOTIC sample: the
   *  `slope-asym-*` statistics are computed over them alone, so "the predicted growth class matches the
   *  measured one" is asked where a growth class is a meaningful thing to ask about.
   *
   *  2048 is not read off this suite's output.  It comes from the crossover LIM-4 derives from the
   *  formula (`fan > 33 x gateFan`, with a gating fan of 1 prefix and a growing fan of `n` leaves, so the
   *  constant branch wins from `n` in the low thousands) and it is confirmed by the independent 11-rung
   *  probe recorded in build.log, where the predicted `touch` of every whole-subtree family is FLAT from
   *  1024 upward.  The crossover rungs are still measured and still gated on `width`/`error`/`magnitude`
   *  and on the whole-ladder `slope-vs-measured` — nothing is dropped from the sample, and the
   *  crossover-region slopes are printed on every channel line. */
  val asymptoticFrom: Int = 2048

  /** `log2((C(2n) + 1) / (C(n) + 1))` — the statistic, verbatim */
  def slope(cn: Double, c2n: Double): Double = math.log((c2n + 1.0) / (cn + 1.0)) / math.log(2.0)
  def slopes(xs: Vector[Double]): Vector[Double] =
    if xs.length < 2 then Vector(0.0) else xs.sliding(2).map(w => slope(w(0), w(1))).toVector
  def maxSlope(xs: Vector[Double]): Double = slopes(xs).max

  def annOf(s: Scenario): SpatialAnnotations =
    SpatialAnnotations(
      spaces = s.spaces.view.mapValues(SpatialType.of).toMap,
      paths = s.paths,
      pathLens = s.paths.view.mapValues(v => Lower.LenBounds(v.items.length.toLong, v.items.length.toLong)).toMap,
      routines = s.rc)

  /** THE OPTIMIZED FORM, and its cost on every backend.
   *
   *  `Routine.optimized` runs the spatial hook with NO input annotation, so the body it produces is
   *  valid for every input and is the SAME term at every rung — the ladder then varies only the inputs,
   *  which is what makes the slope a statement about input growth and not about optimizer luck.  The
   *  decorated analysis of that body is what the cost env consumes, so the prediction
   *  sees the law and spatial refinements instead of re-inferring per node. */
  /** THE OPTIMIZED BODY, PRICED BY THE A4 ANALYSIS with the rung's inputs declared exactly: the
   *  reference, trie and zipper rules on the term, the graph rules on the operation graph `execT` runs. */
  def optimizedAndPriced(s: Scenario): (Routine, Map[Backend, CostReport]) =
    given PartialFunction[RoutinePtr, Routine] = s.rc
    val opt = s.routine.optimized
    val inputs = CostSem.Inputs(values = s.spaces, paths = s.paths)
    val term = Vector(Backend.Reference, Backend.Trie, Backend.Zipper).map(b => b -> CostSem.analyze(opt.body, inputs, b, s.rc)).toMap
    val graph =
      try Some(Backend.Graph -> CostSem.analyzeGraph(morkl.optimize(transpile(opt)), inputs))
      catch case _: NotImplementedError | _: IllegalStateException | _: MatchError | _: RuntimeException => None
    (opt, term ++ graph)


  def measure(opt: Routine, s: Scenario): (Map[String, Events], Map[String, Double]) =
    val pc: PathContext = PathContextMap(s.paths)
    val ic: Map[SpaceMention, ITrie] = s.spaces.view.mapValues(ITrie.fromSpaceValue).toMap
    val rc = s.rc
    // warm: fill the `iLiteral` memo and let the JIT see the shapes once
    val warm = evalI(opt.body)(using pc, ic, rc)
    val (tv, te) = EffortSink.count(evalI(opt.body)(using pc, ic, rc))
    val (zv, ze) = EffortSink.count(execZ(opt.body)(using pc, ic, rc))
    assertEquals(zv.toSpaceValue, tv.toSpaceValue,
                 s"${opt.name.s}: execZ and evalI disagree on the optimized body")
    var events = Map("trie" -> te, "zipper" -> ze)
    var times = Map("trie" -> bestMs(evalI(opt.body)(using pc, ic, rc)),
                    "zipper" -> bestMs(execZ(opt.body)(using pc, ic, rc)))
    // `execT` opportunistically: some bodies have no operation-graph node
    graphRun(opt, s, ic) match
      case Some((gv, ge, ms)) =>
        assertEquals(gv.toSpaceValue, tv.toSpaceValue, s"${opt.name.s}: execT disagrees with evalI")
        events += "graph" -> ge
        times += "graph" -> ms
      case None => ()
    assert(warm.size >= 0)
    (events, times)

  def graphRun(opt: Routine, s: Scenario, ic: Map[SpaceMention, ITrie]): Option[(ITrie, Events, Double)] =
    try
      val g = morkl.optimize(transpile(opt))
      val refs = s.paths.map((k, v) => k.s -> Interner.internPath(v.items))
      val ments = ic.map((k, v) => k.s -> v)
      runGraphT(g, refs, ments)
      val (v, e) = EffortSink.count(runGraphT(g, refs, ments))
      Some((v, e, bestMs(runGraphT(g, refs, ments))))
    catch case _: NotImplementedError | _: IllegalStateException | _: MatchError | _: RuntimeException => None

  def bestMs(body: => Any): Double =
    var best = Double.MaxValue
    for _ <- 0 until 3 do
      val t0 = java.lang.System.nanoTime()
      var i = 0
      while i < 3 do { body; i += 1 }
      best = math.min(best, (java.lang.System.nanoTime() - t0) / 1e6 / 3.0)
    best

  /** one (family, backend, component) channel over the whole ladder */
  final case class Channel(family: String, op: String, backend: String, comp: EffortComponent,
                           ns: Vector[Int], actual: Vector[Double],
                           lower: Vector[Double], upper: Vector[Double],
                           declared: Option[Double]):
    def contained: Boolean =
      actual.indices.forall(i => lower(i) <= actual(i) + 1e-9 && actual(i) <= upper(i) + 1e-9)
    def width: Double = upper.indices.map(i => (upper(i) + 1.0) / (lower(i) + 1.0)).max
    def error: Double = upper.indices.map(i => (upper(i) + 1.0) / (actual(i) + 1.0)).max
    /** THE LOWER ENDPOINT AGAINST THE TRUTH, over the rungs where the execution DID something.
     *
     *  the second product requirement: "no zero lower endpoint when a nonempty execution must
     *  allocate or touch".  A rung whose counted value is 0 is not evidence that anything was forced, so
     *  it is not sampled; a rung that counted `k > 0` is, and a lower endpoint of 0 there scores `k + 1`.
     *  The evidence that the work was MANDATORY is the counted run — which is a test oracle, not an input
     *  to any bound: nothing in `SpatialCost` sees it. */
    def lowerError: Double =
      val did = actual.indices.filter(i => actual(i) > 0.0)
      if did.isEmpty then 1.0 else did.map(i => (actual(i) + 1.0) / (lower(i) + 1.0)).max
    /** the largest predicted endpoint anywhere on the ladder */
    def magnitude: Double = upper.max
    def measSlope: Double = maxSlope(actual)
    def predSlope: Double = maxSlope(upper)
    /** the rungs at or past [[asymptoticFrom]] — where a GROWTH CLASS is a meaningful claim */
    def asymIdx: Vector[Int] = ns.indices.filter(i => ns(i) >= asymptoticFrom).toVector
    def measSlopeAsym: Double = maxSlope(asymIdx.map(actual))
    def predSlopeAsym: Double = maxSlope(asymIdx.map(upper))
    /** the crossover region, printed as evidence beside the asymptotic claim */
    def crossIdx: Vector[Int] = ns.indices.filter(i => ns(i) < asymptoticFrom).toVector
    def predSlopeCross: Double = maxSlope(crossIdx.map(upper))
    def ratio: Double = (actual.last + 1.0) / (actual.head + 1.0)
    def predRatio: Double = (upper.last + 1.0) / (upper.head + 1.0)
    def show: String =
      f"  $backend%-8s $comp%-6s actual=${actual.map(_.toLong).mkString(",")}%-56s " +
      f"pred=${upper.map(fmt).mkString(",")}%-64s " +
      f"slope meas=${measSlope}%5.2f/${measSlopeAsym}%5.2f pred=${predSlope}%5.2f/${predSlopeAsym}%5.2f " +
      f"decl=${declared.map(d => f"$d%.2f").getOrElse("  - ")}%s  " +
      f"err=${error}%9.2f width=${width}%9.2f loErr=${lowerError}%9.2f"
    private def fmt(d: Double): String =
      if d.isInfinite then "inf" else if d >= 1e7 then f"$d%.1e" else d.toLong.toString

  // ==============================================================================================
  // 3. THE FAMILIES
  // ==============================================================================================

  def routine(name: String, ments: Vector[String], body: Space): Routine =
    Routine(RoutinePtr(name), Vector.empty, ments.map(sm), body)

  /** THE SIX CASES the review names, plus a linear control and three degenerate identities. */
  val families: Vector[Family] = Vector(

    // ---- PREFIX CYLINDER: restriction by ONE PRESENT PREFIX of fixed length 6.  The selected subtree
    //      doubles at every rung; `ITrie.restrictionR` returns `Identity(LEFT)` at the terminal prefix,
    //      so the cost is Θ(6) whatever is below it (IntTrie.scala:320-333).
    Family("restrict/prefix-cylinder", "restriction",
      "a terminal prefix accepts X_u by pointer: Θ(|prefix|), independent of the selected subtree",
      n => Scenario(routine("cyl", Vector("s0", "s1"), Space.Restriction(S"s0", S"s1")),
                    Map(sm("s0") -> spc(fan(n, "x", cyl).paths + pv("sib")),
                        sm("s1") -> spc(Set(PathValue(cyl))))),
      declared = flat),

    // ---- restriction by {ε}: the whole space, by pointer, in constant time
    Family("restrict/epsilon", "restriction",
      "ε prefixes everything, so restriction by {ε} is the identity with zero allocation",
      n => Scenario(routine("reps", Vector("s0", "s1"), Space.Restriction(S"s0", S"s1")),
                    Map(sm("s0") -> fan(n, "x", List("g")), sm("s1") -> eps)),
      declared = flat),

    // ---- DISJOINT deep union: non-overlapping branches are attached unchanged (one fresh root)
    Family("union/disjoint", "union",
      "head-disjoint branches are attached unchanged: ONE fresh node, whatever the operands' size",
      n => Scenario(routine("dju", Vector("s0", "s1"), Space.Union(S"s0", S"s1")),
                    Map(sm("s0") -> fan(n, "x", List("L", "d1")),
                        sm("s1") -> fan(16, "y", List("R", "d1")))),
      declared = flat),

    // ---- SUBSET union: the right operand is a subset of the left, so the union IS the left
    Family("union/subset", "union",
      "subset is an identity: the union returns the left operand and allocates nothing",
      n => Scenario(routine("sbu", Vector("s0", "s1"), Space.Union(S"s0", S"s1")),
                    Map(sm("s0") -> fan(n, "x", List("g")), sm("s1") -> fan(4, "x", List("g")))),
      declared = flat),

    // ---- SHARED SUBTRIE intersection: a contained operand is returned whole
    Family("inter/shared-subtrie", "intersection",
      "a contained operand is returned by pointer; the growing half is never descended",
      n => Scenario(routine("shi", Vector("s0", "s1"), Space.Intersection(S"s0", S"s1")),
                    Map(sm("s0") -> spc(fan(n, "x", List("g")).paths ++ fan(8, "y", List("h")).paths),
                        sm("s1") -> fan(8, "y", List("h")))),
      declared = flat),

    // ---- DISJOINT intersection: rejected at the head level without descent
    Family("inter/disjoint", "intersection",
      "disjoint branches are rejected without descent; the result is empty and nothing is built",
      n => Scenario(routine("dji", Vector("s0", "s1"), Space.Intersection(S"s0", S"s1")),
                    Map(sm("s0") -> fan(n, "x", List("L")), sm("s1") -> fan(8, "y", List("R")))),
      declared = flat),

    // ---- SELF SUBTRACTION: x ∖ x is empty by pointer identity (and the optimizer may remove it)
    Family("subtract/self", "subtraction",
      "x ∖ x is empty by pointer identity — and the ordinary rule list may remove the node outright",
      n => Scenario(routine("sst", Vector("s0"), Space.Subtraction(S"s0", S"s0")),
                    Map(sm("s0") -> fan(n, "x", List("g")))),
      declared = flat),

    // ---- ABSORPTION: (s0 ∪ (s0 ∩ s1)) = s0
    Family("absorption", "union/intersection",
      "absorption: the inner intersection is contained in the outer left operand, so the union is an " +
      "identity — an algebraic law the random corpus never generates",
      n => Scenario(routine("abs", Vector("s0", "s1"),
                            Space.Union(S"s0", Space.Intersection(S"s0", S"s1"))),
                    Map(sm("s0") -> fan(n, "x", List("g")), sm("s1") -> fan(8, "x", List("g")))),
      declared = flat),

    // ---- ε · B: constant time
    Family("compose/epsilon", "composition",
      "{ε}·B returns B by pointer: composition with a left epsilon is the adversarial case for any " +
      "N(a)*N(b) formula",
      n => Scenario(routine("ceps", Vector("s0", "s1"), Space.Composition(S"s1", S"s0")),
                    Map(sm("s0") -> fan(n, "x", List("g")), sm("s1") -> eps)),
      declared = flat),

    // ---- FULL RANGE: the identity
    Family("range/full", "range",
      "a full window is the identity: `sliceRange` and `ITrie.range` both return their input",
      n => Scenario(routine("rgf", Vector("s0"), Space.Range(S"s0", 0, 0)),
                    Map(sm("s0") -> fan(n, "x", List("g")))),
      declared = flat),

    // ---- FIXED SELECTIVE CONSUMER: (A ∪ B) ∩ C with C fixed.  THE per-backend split: `execZ` fuses
    //      and stays proportional to C; `evalI` materialises the union first and grows with it.
    Family("select/fixed-consumer", "intersection",
      "(A ∪ B) ∩ C with a FIXED C: the fused zipper stays proportional to C while the eager union " +
      "grows — ZipperScaleBench's own demonstration, now with the cost prediction asserted",
      // EVERY key of A is paired with a key of B (they differ only in the third item), so the eager
      // union really does descend n times — a top-level-disjoint pair would be joined by the Patricia
      // merge in O(1) and the family would prove nothing.
      n => Scenario(routine("sfc", Vector("s0", "s1", "s2"),
                            Space.Intersection(Space.Union(S"s0", S"s1"), S"s2")),
                    Map(sm("s0") -> spc((0 until n).map(i => pv("g", "a" + i, "u"))),
                        sm("s1") -> spc((0 until n).map(i => pv("g", "a" + i, "v"))),
                        sm("s2") -> spc((0 until 8).map(i => pv("g", "a" + i, "u"))))),
      declared = flat,
      perBackend = Map(("trie", EffortComponent.Touch) -> 1.0, ("trie", EffortComponent.Alloc) -> 1.0,
                       ("graph", EffortComponent.Touch) -> 1.0, ("graph", EffortComponent.Alloc) -> 1.0)),

    // ---- REST CHAIN: a two-level iterator nest over a fixed head count.  frames = Σ_d K_d = heads + n,
    //      so `Rounds` and `Work` are LINEAR by construction — the family that proves a flat result in
    //      the others is not an artefact of the harness.
    Family("rest-chain/nest", "iteration",
      "a rest-chained iterator nest: frame entries are Σ_d K_d, so rounds and work are LINEAR — the " +
      "control that makes the flat families meaningful",
      n => Scenario(routine("rch", Vector("s0"),
                            Space.Iteration(S"s0", PathRef("h").known(1), sm("t"),
                              Space.Iteration(Space.Mention(sm("t")), PathRef("g").known(1), sm("_"),
                                Space.Singleton(Path.Concat(Path.Deref(PathRef("h").known(1)),
                                                            Path.Deref(PathRef("g").known(1))))))),
                    Map(sm("s0") -> chain(n, 8, "rc"))),
      declared = linearIn(EffortComponent.Work, EffortComponent.Alloc,
                          EffortComponent.Rounds, EffortComponent.Touch)),

    // ---- LINEAR CONTROL: a union in which EVERY key is paired (the operands differ only in the third
    //      item), so the frontier IS the whole input, every node on it is rebuilt, and the honest answer
    //      is slope 1 in both `alloc` and `touch`.  This family is what makes a flat result elsewhere
    //      mean something: a harness that reported 0 everywhere would report 0 here too.
    Family("union/paired-keys", "union",
      "every key is paired, so the frontier IS the whole input and slope 1 is the CORRECT answer — a " +
      "model that reported constant here would be unsound, and a harness that could not see the " +
      "difference would make every flat family above meaningless",
      n => Scenario(routine("pku", Vector("s0", "s1"), Space.Union(S"s0", S"s1")),
                    Map(sm("s0") -> spc((0 until n).map(i => pv("g", "a" + i, "u"))),
                        sm("s1") -> spc((0 until n).map(i => pv("g", "a" + i, "v"))))),
      declared = linearIn(EffortComponent.Alloc, EffortComponent.Touch),
      // `execZ` enters NO `IntTrieOps` descent (its `touch` is 0 by construction), and its cursor reads
      // DO grow here because every key is forced — both facts are measured, so both are declared.
      perBackend = Map(("zipper", EffortComponent.Touch) -> 0.0,
                       ("zipper", EffortComponent.Work) -> 1.0)),

    // ---- KEY-DISJOINT union under a SHARED prefix: the union row, "non-overlapping
    //      branches are attached unchanged".  The Patricia merge attaches whole branches, so `alloc` is
    //      FLAT while `touch` is linear — a split between two components of the same operator that a
    //      size-only bound cannot express at all.
    Family("union/disjoint-keys", "union",
      "key-disjoint operands under a shared prefix: branches are attached unchanged, so ALLOC is flat " +
      "while TOUCH is linear — two different growth classes on one node",
      n => Scenario(routine("dku", Vector("s0", "s1"), Space.Union(S"s0", S"s1")),
                    Map(sm("s0") -> fan(n, "x", List("g"), from = 0, step = 2),
                        sm("s1") -> fan(n, "x", List("g"), from = 1, step = 2))),
      declared = linearIn(EffortComponent.Touch),
      perBackend = Map(("zipper", EffortComponent.Touch) -> 0.0)))

  // ==============================================================================================
  // 4. THE LADDER TEST
  // ==============================================================================================

  def runFamily(f: Family): (Vector[Channel], Vector[(Double, Double)]) =
    val ns = ladder
    var trend = Vector.empty[(Double, Double)]
    var optShown = false
    val comps = EffortEvent.calibratedComponents
    // component-indexed accumulation: backend -> comp -> Vector[(actual, lo, hi)]
    var acc = Map.empty[(String, EffortComponent), Vector[(Double, Double, Double)]]
    def d(x: Long): Double = if x >= Ivl.INF then Double.PositiveInfinity else x.toDouble
    for n <- ns do
      val sc = f.build(n)
      val (opt, priced) = optimizedAndPriced(sc)
      if !optShown then
        println(s"SCALE ${f.name}: OPTIMIZED body = ${opt.body.show.replace('\n', ' ').take(150)}")
        println(s"SCALE ${f.name}: ${priced(Backend.Trie).derivation.size} derivation nodes; ${priced(Backend.Trie).domain.show.linesIterator.next()}")
        optShown = true
      val (events, times) = measure(opt, sc)
      for (slug, ev) <- events do
        val backend = Backend.values.find(_.slug == slug).get
        for rep <- priced.get(backend) do
          for c <- comps do
            val i = rep.component(c)
            acc = acc.updated((slug, c), acc.getOrElse((slug, c), Vector.empty) :+ (ev.component(c).toDouble, d(i.lo), d(i.hi)))
          // the correlated trend: the predicted upper endpoints against measured wall time, over every rung
          val tot = comps.map(c => d(rep.component(c).hi)).sum
          if !tot.isInfinite then trend :+= (tot, times(slug))
    val chans = acc.toVector.sortBy((k, _) => (k._1, k._2.ordinal)).flatMap { case ((slug, c), rows) =>
      if rows.length != ns.length then None
      else Some(Channel(f.name, f.op, slug, c, ns, rows.map(_._1), rows.map(_._2), rows.map(_._3),
                        f.declaredFor(slug, c)))
    }
    (chans, trend)


  test("PRODUCT REQUIREMENTS: the tier table is total over the backends and components it gates") {
    // every (backend, component) an executable can produce must have a declared tier — a channel with
    // no requirement is a channel nobody promised anything about
    for b <- Backend.values; c <- EffortEvent.calibratedComponents do
      assert(ProductRequirement.tierOf(b.slug, c).isDefined,
             s"no product requirement declared for (${b.slug}, $c)")
    println("REQUIREMENT: " + ProductRequirement.Selection.show)
    println("REQUIREMENT:   " + ProductRequirement.Selection.why)
    println("REQUIREMENT: " + ProductRequirement.Budget.show)
    println("REQUIREMENT:   " + ProductRequirement.Budget.why)
    println("REQUIREMENT: " + ProductRequirement.GrowthClass.show)
    println("REQUIREMENT:   " + ProductRequirement.GrowthClass.why)
    println("REQUIREMENT: " + ProductRequirement.NotGated.show)
    println("REQUIREMENT:   " + ProductRequirement.NotGated.why)
    for ((b, c), t) <- ProductRequirement.tiers.toVector.sortBy((k, _) => (k._1, k._2.ordinal)) do
      println(f"REQUIREMENT: ${b}%-10s ${c}%-6s => ${t.name}")
    // THE WORKLOAD CLASSES — the review asks for a declared maximum ratio per component AND WORKLOAD
    // CLASS, so the classes are a table and every scope that publishes rows must appear in it.
    for w <- ProductRequirement.workloads do
      println(f"REQUIREMENT: workload ${w.scope}%-12s ${if w.gated then "RATIOS GATED" else "NOT GATED"}%-13s ${w.why}")
    assertEquals(ProductRequirement.workloads.map(_.scope).distinct.length,
                 ProductRequirement.workloads.length, "duplicate workload scope")
    assertEquals(ProductRequirement.workloads.count(_.gated), 3,
                 "exactly one workload class may opt out of the ratio requirements — the DEFINITIONAL " +
                 "random corpus, whose soundness is gated instead")
    // THE ABSOLUTE CEILING is uniform across the gated tiers: it is a statement about machines, not
    // about the decision a channel supports, so no tier may weaken it.
    for t <- Vector(ProductRequirement.Selection, ProductRequirement.Budget, ProductRequirement.GrowthClass) do
      assertEquals(t.magnitude, ProductRequirement.Astronomical,
                   s"${t.name} may not set its own endpoint ceiling")
    assertEquals(ProductRequirement.NotGated.budget("numeric"), 0.0,
                 "the `numeric` requirement applies to EVERY tier including the ungated reference " +
                 "evaluator: NotGated exempts its constants from a threshold, not its answer from existing")
    // the reference evaluator is the ONE backend that is not gated, and the reason is the user's steer
    val ungated = ProductRequirement.tiers.filter((_, t) => t == ProductRequirement.NotGated)
      .keys.map(_._1).toSet
    assertEquals(ungated, Set("reference"),
                 "exactly one backend may be ungated — the reference evaluator, whose constants are " +
                 "not a product and whose touch has no oracle")
  }

  test("SCALE LADDERS: counted executions inside the predicted intervals on the OPTIMIZED form; slopes and widths reported") {
    // THE GATE AT M1 (tasks.md): soundness — every counted rung inside its interval — finiteness and the
    // absolute ceiling are hard; the width/error/slope statistics are measured against the tiers and
    // REPORTED per channel ("wide intervals are allowed at this milestone but are reported as not
    // useful").  No ledger of excused rows exists: a row either meets its tier or is printed NOT USEFUL.
    var rows = Vector.empty[GateRow]
    var unsound = Vector.empty[String]
    var hard = Vector.empty[String]
    var trend = Vector.empty[(Double, Double)]
    var channels = 0
    println(s"SCALE: ladder = ${ladder.mkString(",")}; the ASYMPTOTIC sample is the rungs >= " +
            s"$asymptoticFrom (${ladder.filter(_ >= asymptoticFrom).mkString(",")}).  Every `slope` cell " +
            "reads whole-ladder/asymptotic.")
    for f <- families do
      println("=" * 132)
      println(s"SCALE ${f.name}  [operator: ${f.op}]")
      println(s"SCALE   ${f.why}")
      val (chans, tr) = runFamily(f)
      trend ++= tr
      for ch <- chans do
        channels += 1
        println("SCALE " + ch.show)
        val tier = ProductRequirement.tierOf(ch.backend, ch.comp).get
        if !ch.contained then
          unsound :+= s"${ch.family}/${ch.backend}/${ch.comp}: actual=${ch.actual.map(_.toLong).mkString(",")} " +
                      s"outside [${ch.lower.map(_.toLong).mkString(",")}, ${ch.upper.map(fmtD).mkString(",")}]"
        if ch.magnitude.isInfinite then hard :+= s"${ch.family}/${ch.backend}/${ch.comp}: INFINITE upper endpoint"
        else if ch.magnitude >= ProductRequirement.Astronomical then hard :+= f"${ch.family}/${ch.backend}/${ch.comp}: ASTRONOMICAL upper endpoint ${ch.magnitude}%.3e"
        def row(what: String, measured: Double) =
          rows :+= GateRow("ladder", ch.family, ch.backend, ch.comp, what, measured, tier)
        row("width", ch.width)
        row("error", ch.error)
        row("lower-error", ch.lowerError)
        row("magnitude", ch.magnitude)
        row("slope-vs-measured", ch.predSlope - ch.measSlope)
        row("slope-asym-vs-measured", ch.predSlopeAsym - ch.measSlopeAsym)
        for d <- ch.declared do
          row("slope-measured-vs-declared", ch.measSlope - d)
          row("slope-predicted-vs-declared", ch.predSlope - d)
          row("slope-asym-measured-vs-declared", ch.measSlopeAsym - d)
          row("slope-asym-predicted-vs-declared", ch.predSlopeAsym - d)
    println("=" * 132)
    // ---- THE USEFULNESS REPORT: every row against its tier, reported, not gated at M1 ----------------
    val gated = rows.filter(_.tier != ProductRequirement.NotGated)
    val notUseful = gated.filterNot(_.ok)
    println(s"SCALE: USEFULNESS — ${gated.length} gated rows over $channels channels; ${notUseful.length} NOT USEFUL for their tier (reported, not gated at M1)")
    for r <- notUseful.sortBy(_.key) do println("SCALE:   NOT USEFUL " + r.show)
    for (what, rs) <- gated.groupBy(_.what).toVector.sortBy(_._1) do
      println(f"SCALE:   $what%-34s ${rs.count(_.ok)}%4d / ${rs.length}%-4d rows meet their tier; worst ${GateRow.fmt(rs.map(_.measured).max)}")
    // ---- the correlated trend: predicted cost against measured wall time (reported) -----------------
    if trend.length >= 8 then
      val rho = Calibration.spearman(trend.map(_._1), trend.map(_._2))
      println(f"SCALE: Spearman(predicted total upper bound, measured wall time) = $rho%.3f over ${trend.length} " +
              "(family, rung, backend) points on the OPTIMIZED form")
    // ---- SOUNDNESS AND FINITENESS: the hard gate ------------------------------------------------------
    if unsound.nonEmpty then
      println(s"SCALE: UNSOUND — ${unsound.length} channel(s) have a counted value OUTSIDE the predicted interval:")
      unsound.foreach(u => println("SCALE:   " + u))
    assert(unsound.isEmpty, s"${unsound.length} channel(s) unsound on the optimized form:\n  ${unsound.take(20).mkString("\n  ")}")
    assert(hard.isEmpty, s"infinite or astronomical predictions on closed ladders:\n  ${hard.take(20).mkString("\n  ")}")
  }

  private def fmtD(d: Double): String = if d.isInfinite then "inf" else d.toLong.toString
end SpatialScaleCheck
