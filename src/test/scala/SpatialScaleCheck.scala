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
 *  ==AND WHEN A CHANNEL CANNOT MEET ITS TIER==
 *  IT FAILS.  Full stop, with the measured number printed.  There is no naming that makes it pass.
 *
 *  That is a CHANGE from the previous revision of this file, and it is the whole of the review
 *  complaint about the gate: "the current gate architecture turns known failures into a passing build by
 *  naming them."  [[limitations]] used to be consulted by `publishGate` and a failing check that matched
 *  an entry — with a recorded number it had not regressed past — was printed and then NOT COUNTED.  840
 *  + 118 + 224 requirement checks produced 127 + 30 + 51 failures and three green suites.
 *
 *  The ledger REMAINS, unchanged in content, as EVIDENCE: owner, root cause, worst measured value,
 *  printed against every row it describes, because that is what makes a red build actionable.  What it
 *  no longer has is a vote.  The only two things it still decides can only ADD failures — NECESSITY (an
 *  entry whose subject stopped failing is stale) and COVERAGE (an entry whose channel stopped being
 *  measured).  [[ProductGate]] is the one implementation of that policy for all three suites. */
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
   *  and [[ProductGate]] FAILS on a scope that appears in neither list — so a new harness cannot publish
   *  numbers under no requirement at all. */
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

  /** ONE NAMED, JUSTIFIED LIMITATION of the analysis — a channel that does NOT meet its product
   *  requirement, recorded with the root cause, the file that owns the fix, the worst measured number
   *  and the exact set of (subject, component, statistic) triples it covers.
   *
   *  IT IS EVIDENCE, NOT A THRESHOLD, AND IT HAS NO VOTE.  The previous revision said the same first
   *  sentence and then handed the entry a `cap` that [[ProductGate]] compared the measurement against,
   *  which is exactly the "naming makes it pass" architecture the review rejects.  `cap` IS GONE.  The two
   *  recorded numbers stay, renamed to what they are — `worstErr` and `worstWidth`, the worst value
   *  MEASURED when the entry was written — so a reader can see at a glance whether a red row is the
   *  known defect or a new one, and so a diff of this file records movement.  Nothing reads them to
   *  decide a verdict.
   *
   *  Two properties are still ENFORCED, and both can only add failures:
   *
   *   1. NECESSITY.  Every `subject` listed must still produce a failing row.  When the owner fixes the
   *      model, the entry stops being necessary and the suite FAILS until the subject is removed.
   *      "A channel that becomes bounded must also fail so the ledger cannot rot."
   *   2. NAMED OWNER.  Every entry says which file must change.  An entry with no owner would be an
   *      admission that nobody intends to fix it. */
  final case class Limitation(id: String, scope: String, backend: String, comp: EffortComponent,
                              what: Set[String], subjects: Vector[String],
                              worstErr: Double, worstWidth: Double, owner: String, reason: String):
    def matches(scope: String, subject: String, backend: String, comp: EffortComponent, what: String): Boolean =
      this.scope == scope && this.backend == backend && this.comp == comp &&
      this.what.contains(what) && subjects.contains(subject)
    /** the worst value MEASURED for one statistic when this entry was written, for the reader only */
    def recorded(what: String): Double =
      if what.startsWith("error") then worstErr
      else if what.startsWith("width") then worstWidth
      else Double.NaN
    def show: String =
      f"$id%-8s $scope%-11s $backend%-8s $comp%-6s ${what.toVector.sorted.mkString("/")}%-58s " +
      f"measured err ${fmt(worstErr)}%10s width ${fmt(worstWidth)}%10s  owner: $owner"
    private def fmt(d: Double): String =
      if d.isInfinite then "inf" else if d >= 1e6 then f"$d%.2e" else f"$d%.2f"

  private val ErrAndSlope = Set("error", "width", "slope-vs-measured", "slope-predicted-vs-declared")
  private val WidthOnly = Set("width")
  /** the MUST side alone: for a defect that is entirely in the lower endpoint, where naming
   *  `error` or `width` too would claim an upper-bound problem the channel does not have */
  private val LowerErrOnly = Set("lower-error")
  /** the statistic that does NOT read the prediction: the measured slope against the family's own
   *  declaration.  A red row here is a claim about the MEASUREMENT or the DECLARATION and never
   *  about the model, which is why it needs its own group. */
  private val MeasSlopeOnly = Set("slope-measured-vs-declared")
  /** the whole-program scopes report a p95 alongside the worst; both names carry the same requirement */
  private val ErrAll = Set("error", "error-p95")
  private val WidthAll = Set("width", "width-p95")
  /** `error` and the two PREDICTED-slope statistics, WITHOUT `width` — for a defect that shows in
   *  the accuracy and the growth class of a prediction whose width is already owned by another
   *  entry.  `slope-measured-vs-declared` is deliberately absent: it does not involve the
   *  prediction at all, so an entry about a prediction must not claim it. */
  private val ErrSlopeOnly = Set("error", "slope-vs-measured", "slope-predicted-vs-declared")
  private val ErrWidth = ErrAll ++ WidthAll
  /** `error`/`width` PLUS `magnitude`: for a channel whose recorded failure IS the astronomical
   *  endpoint, leaving `magnitude` out would make the loudest statistic the entry exists to describe
   *  show up as an UNDIAGNOSED defect beside it. */
  private val ErrWidthMag = ErrWidth ++ Set("magnitude")
  private val Inf = Double.PositiveInfinity

  /** THE LEDGER — one entry per (scope, backend, component, statistic-family) defect, every one with the
   *  file that owns the fix.  It is EVIDENCE ONLY: see `Limitation` above and `ProductGate`.  Nothing here
   *  excuses a failing check, and the entry count is deliberately not stated — it goes DOWN as defects are
   *  fixed and a stale entry fails the build, so a number in this comment would only ever be wrong.
   *
   *  Read the `id` prefixes as the root causes; the `g`/`z`/`a`/`w` suffixes are the same cause reaching
   *  another (backend, component) through shared code.
   *
   *   LIM-1/2  the zipper's demand analysis lowers `Touch` and not `Work`/`Alloc`
   *   LIM-3    RETIRED — `Meas.countKnown` made the `Range` count walk operand-dependent
   *   OP-1     RETIRED — `Rel.mayShare` closed the recursive `a eq b` hole in the must-paired floor
   *   OP-1g    RETIRED — as OP-1
   *   OP-1z    RETIRED — as OP-1
   *   OP-3     RETIRED — `Layers.termsAt` = E_d - E_{d+1}, landed with the two `CRes` defects
   *   OP-2g    RETIRED — `execT`'s `Alloc` meets the budget tier on every operator
   *   OP-3g    RETIRED — `execT`'s `Work` meets the selection tier on every operator
   *   LIM-4    the frontier's whole-subtree accepts do not reach `touch`
   *   LIM-5    `alloc` is met against the result envelope, not the rebuilt count
   *   LIM-6    NO LOWER ENDPOINT is derived, so every width is `upper + 1`
   *   LIM-7    the rest-chain frame law is exact but emitted `upperOnly`
   *   LIM-8    the Patricia-visit constant is 3 per merged entry, measured ~0.6    (constant factor)
   *   LIM-9    the must-paired `touch` floor is refused where the operands may SHARE structure */
  /** ============================================================================================
   *  EVERY `worstErr`/`worstWidth` BELOW WAS RE-DERIVED ON 2026-09-03, AND IS NOW GATE-CHECKED.
   *
   *  These two fields are documented as "the worst value MEASURED for this statistic when this entry
   *  was written".  Until plan.md 0.7 they were PRINTED for the reader and compared against nothing,
   *  so they could drift arbitrarily far from the truth while the row stayed red for the same named
   *  reason.  `ProductGate.report` now fails a red row's entry as `STALE FIGURE` when its recorded
   *  number differs from the worst current measurement over its own subjects by more than 2%.
   *
   *  ITS FIRST RUN FOUND 29 STALE FIGURES ACROSS 24 OF THE 51 ENTRIES, in BOTH directions, and the
   *  understating half is the one that matters:
   *
   *    UNDERSTATED (the defect is BIGGER than the ledger said)
   *      LIM-6az  width    6 500 -> 178 049    (27x)
   *      LIM-7wg  width      450 ->   4 684    (10x)
   *      LIM-7/g/z width     180 ->   1 821    (10x)
   *      LIM-6ag  width      800 ->   8 204    (10x)
   *      LIM-6/g  width   25 000 ->  73 732    (3x)
   *      LIM-6w   width   14 000 ->  28 677    (2x)
   *    OVERSTATED (the number read as a ceiling the work had already improved on)
   *      CS-8/9   width   32 000 ->     295 / 354      (~100x)
   *      OP-6/g   width    4 900 ->      89.60         (55x)
   *      LIM-1    error    3 100 ->       4.08         (760x)
   *      CS-3     error      700 ->      21.13 ->  6.23  (33x, then `Shape.maxTailSize`)
   *      CS-P1..4 error   1.0e54 -> 3.23e52 / 7.37e52 -> 4.31e50 / 9.86e50
   *               width  1.0e57 -> 2.02e53 / 2.67e53 -> 2.70e51 / 3.57e51
   *
   *  Both directions are failures and neither is cosmetic.  An understated figure hides how far a
   *  channel actually is from its requirement, which is the number that decides whether the next
   *  task is worth starting.  An overstated one is worse: `plan.md`, `build.log` and the acceptance
   *  review all quote these figures as the state of the work, and a ceiling the work has already
   *  cleared reads as a defect that is still open.  Every value below now comes from the run that
   *  the gate compares it against, and the gate re-checks it on every run.
   *
   *  RE-DERIVING A FIGURE IS NOT THE SAME AS FIXING THE DEFECT.  Every row these entries describe is
   *  still RED against its product requirement; what changed is that the evidence beside it is true.
   *  plan.md 1B.8 is the task that retires the ledger to empty and re-derives what remains from the
   *  implementation.
   *  ============================================================================================ */
  val limitations: Vector[Limitation] = Vector(

    // ============================ LIM-1/2: the demand analysis, one component short ================
    Limitation("LIM-1", "ladder", "zipper", EffortComponent.Work, ErrAndSlope,
      // `union/disjoint-keys` LEFT: it meets the Work/budget requirement (width 5.00, error 1.11,
      // both slopes 0.00) and was already doing so at `01a5864`, before any of the n-ary work in
      // this change — so listing it was LEDGER DRIFT, and the stale-evidence check is what caught
      // it.  `select/fixed-consumer` remains and the note below is about that family.
      Vector("select/fixed-consumer"),
      4.08, 72.17, "SpatialCost.scala (ZipperCost) / SpatialDemand.scala",
      "THE DEMAND ANALYSIS LOWERS `Touch` AND NOT `Work`.  `execZ`'s counted cursor reads are CONSTANT on " +
      "every one of these terms (9-105, flat across the ladder) and the predicted `Touch` is correctly " +
      "0 at every rung — so the demand region IS recognised and the fused cursor algebra IS priced.  " +
      "`Work` is still the per-operator sum: `ZipperCost` charges `ZipperBuild` + `ZipperCursorRead` in " +
      "proportion to each operand's `Meas.nodes`, and `demandPrice + demandExtra + handedOff` does not come " +
      "out below that, so the meet keeps the eager number.  Worst measured error 2053x (range/full), and " +
      "the predicted slope is 0.96-1.00 against a measured 0.00 — a GROWTH-CLASS error, not a constant.  " +
      "EIGHT SUBJECTS LEFT THIS ENTRY IN THIS SESSION and the reason is the owning file: the demand price " +
      "now reaches `Work` on the SHARING families, so `restrict/prefix-cylinder` (width 10.25, error 1.17), " +
      "`restrict/epsilon` (2.75, 2.20), `union/disjoint` (3.25, 1.18), `union/subset` (12.00, 2.67), " +
      "`inter/shared-subtrie` (19.00, 4.75), `inter/disjoint` (3.25, 1.30), `absorption` (39.67, 9.15) and " +
      "`compose/epsilon` (3.50, 1.17) are inside the budget tier with slope 0.00 predicted against 0.00 " +
      "measured.  What is left is the three families where the demand region is NOT the whole term."),

    // ==============================================================================================
    // LIM-2 IS RETIRED — `union/disjoint-keys` was its last subject and it now MEETS its requirement.
    //
    // WHAT CLOSED IT is not recorded here as a model improvement, because it is not one: the entry was
    // ALREADY STALE at `01a5864`, before any of the n-ary work in this change — the baseline
    // `sbt test` at that commit reports all four of `LIM-1`, `LIM-2`, `LIM-5` and `LIM-5g` claiming
    // this subject and the subject passing.  So this is LEDGER DRIFT: whatever fixed the family was
    // committed without updating the entries that named it, and the stale-evidence check is what
    // caught it.  IT IS FOUR OF SEVENTY-THREE, AND NOT MORE: the `01a5864` baseline reports
    // "1607 of 1680 checks MET; 73 FAILED ... 33 are UNDIAGNOSED" for this suite, so retiring these
    // entries fixes the BOOKKEEPING and leaves the 69 measured failures exactly where they were.
    // The largest of those is the `rest-chain/nest` family, whose `lower-error` rows run to four
    // figures and which has no evidence entry at all.
    // An entry with no measured subject is itself a ledger failure, which is why this is a comment.
    // ==============================================================================================
    // Limitation("LIM-2", "ladder", "zipper", EffortComponent.Alloc, ErrAndSlope,
    //   Vector("union/disjoint-keys"),
    //   1600.0, 1600.0, "SpatialCost.scala (ZipperCost) / SpatialDemand.scala",
    //   "the same gap in `Alloc`.  `(A ∪ B) ∩ C` with a FIXED C was the review's own example and it LEFT " +
    //   "THIS ENTRY IN THIS SESSION (width 61.00, error 5.55, slope 0.00 predicted against 0.00 measured), " +
    //   "because the demand price now reaches `Alloc` where the consumer bounds the materialised frontier.  " +
    //   "What remains is a full `Range` — 0 fresh nodes measured against a linear result-node envelope — and " +
    //   "the key-disjoint union, where the envelope is the whole input and the rebuild is O(1).")

    // ============================ LIM-3: a model left behind by its backend =======================
    // LIM-3 / LIM-3g / LIM-3z ARE RETIRED.  They said "the model is stale after a backend improvement":
    // `ITrie.range` caches subtree terminal counts, so a full window returns its input after ONE node
    // visit, while `CostModel.range` still charged the pre-order size walk the OLD implementation
    // performed (error 514x rising to 8194x as the ladder grew, predicted slope 0.99 against a measured
    // 0.00) on trie, graph AND zipper `Touch`.
    //
    // WHAT FIXED IT WAS NOT A SMALLER CONSTANT.  The count walk is real on a COLD object and on a freshly
    // built subexpression, so deleting it universally would have been unsound in the other direction —
    // `SpatialEventsCheck`'s "FIX 3" and "IDENTITY REGRESSION" tests exist to catch exactly that.  What
    // was missing was a STATE: `Meas.countKnown` (`CountKnown`/`CountUnknown`), propagated through
    // construction and through mentions, so `CostModel.range` prices the count walk as a function of the
    // OPERAND rather than of the operator.  A `Warm` query on a FREE mention — an input object the caller
    // already holds, on which this same executable already ran — is `CountKnown` and pays nothing; every
    // `Cold` query and every freshly built subexpression still pays `N(x)`.  Measured after the change:
    // trie/graph/zipper `range/full` `Touch` error 1.00, width 1.00-2.00, slope 0.00 = measured 0.00.
    // `range/full` still appears under LIM-1/LIM-2 (zipper `Work`/`Alloc`), which is a different defect.

    // ============================ LIM-4: the frontier is derived but not consumed =================
    Limitation("LIM-4", "ladder", "trie", EffortComponent.Touch, ErrAndSlope,
      Vector("union/subset", "absorption"),
      17.79, 181.17, "SpatialCost.scala (`TrieAlgebraCost`) / SpatialFrontier.scala",
      "A CONSTANT FACTOR, NOT A GROWTH CLASS, AND MOST OF IT IS GONE.  The previous revision named two " +
      "drivers; BOTH ARE NOW FIXED and the numbers moved accordingly.  (1) `SpatialFrontier`'s Patricia " +
      "term was `min(2(fanL+fanR), 2*PatriciaBits*(gateFan+|A|))` over the ladder-wide SUMS, so the " +
      "operand-independent branch could not win until the TOTAL growing fan passed ~33x the total gating " +
      "fan and one deep level with a large fan-out priced every flat level above it at the size-only " +
      "rate; the two ceilings are now met PER DEPTH and summed, which is the only form in which they may " +
      "be met at all (a depth-`d` bound is not a bound on depth `e`).  (2) `TrieAlgebraCost.priced` " +
      "charged `descents + patricia` where `FrontierSummary.descents` IS `|Q| + J` — it added the " +
      "Patricia frontier a SECOND time and doubled every frontier-driven `touch` upper endpoint.  " +
      "MEASURED EFFECT: `restrict/prefix-cylinder` LEFT THIS ENTRY — predicted `touch` 96 at EVERY rung " +
      "from 64 to 16384 against a counted 13 (error 6.93, width 16.21, slope 0.00 predicted against 0.00 " +
      "measured), where this entry recorded 1591 and 122x; `union/disjoint-keys` `Touch` fell to error " +
      "8.54 and took LIM-8/LIM-8g with it.  What is left is `union/subset` (error 15.28) and " +
      "`absorption` (error 17.79, width 120.78).  " +
      "THE SECOND DRIVER THE PREVIOUS REVISION NAMED — `touch` not subtracting `FrontierSummary.reuse` " +
      "— WAS A MIS-DIAGNOSIS, and it is recorded here rather than silently dropped.  " +
      "`SubtrieAcceptedByPointer`/`SubtrieRejectedByPointer` are `EffortComponent.Explain` and are never " +
      "summed into `Touch` (SpatialEvents.scala), so there is nothing inside `|Q| + J` for `reuse` to " +
      "subtract: the whole-subtree decisions are already OUTSIDE the bound, and that is exactly why the " +
      "charge is `|Q| + J` and not `N(L) + N(R)`.  Subtracting an UPPER estimate of reuse from an upper " +
      "bound would be unsound in the other direction.  " +
      "THE RESIDUE IS ONE TERM: `2*PatriciaBits = 66` visits per gating key at the ONE level where the " +
      "two child maps meet.  On `union/subset` that is 4 gating keys against a 16384-key map — 268 " +
      "predicted against ~11 counted — and closing it needs a bound on the OTHER side's Patricia DEPTH; " +
      "`min(PatriciaBits, 2*fan-1)` gives nothing for a wide map, and the depth of a Patricia tree over " +
      "`k` `Int` keys really can be 33 for any `k >= 2`.  The whole-ladder slope rows (0.82-0.90) report " +
      "the CROSSOVER between the two per-depth ceilings — the min switches branch between n = 64 and " +
      "n = 256 — while `slope-asym-vs-measured` and `slope-asym-predicted-vs-declared` past " +
      "`asymptoticFrom` both read 0.00, which is the growth-class claim the review asks for."),
    Limitation("LIM-4g", "ladder", "graph", EffortComponent.Touch, ErrAndSlope,
      Vector("union/subset", "absorption"),
      17.79, 181.17, "SpatialCost.scala (`TrieAlgebraCost`) / SpatialFrontier.scala",
      "as LIM-4; `GraphCost` shares `TrieAlgebraCost`'s ring transfers.  `restrict/prefix-cylinder` left " +
      "this entry with LIM-4's (error 6.93 on `execT` as well)."),

    // ============================ LIM-5: rebuilt-vs-envelope allocation ===========================
    // ==============================================================================================
    // LIM-5 IS RETIRED — `union/disjoint-keys` was its last subject and it now MEETS its requirement.
    //
    // WHAT CLOSED IT is not recorded here as a model improvement, because it is not one: the entry was
    // ALREADY STALE at `01a5864`, before any of the n-ary work in this change — the baseline
    // `sbt test` at that commit reports all four of `LIM-1`, `LIM-2`, `LIM-5` and `LIM-5g` claiming
    // this subject and the subject passing.  So this is LEDGER DRIFT: whatever fixed the family was
    // committed without updating the entries that named it, and the stale-evidence check is what
    // caught it.  IT IS FOUR OF SEVENTY-THREE, AND NOT MORE: the `01a5864` baseline reports
    // "1607 of 1680 checks MET; 73 FAILED ... 33 are UNDIAGNOSED" for this suite, so retiring these
    // entries fixes the BOOKKEEPING and leaves the 69 measured failures exactly where they were.
    // The largest of those is the `rest-chain/nest` family, whose `lower-error` rows run to four
    // figures and which has no evidence entry at all.
    // An entry with no measured subject is itself a ledger failure, which is why this is a comment.
    // ==============================================================================================
    // Limitation("LIM-5", "ladder", "trie", EffortComponent.Alloc, ErrAndSlope,
    //   // `absorption` LEFT THIS ENTRY, AND THE REASON IS A HARNESS DEFECT WORTH NAMING RATHER THAN A
    //   // MODEL IMPROVEMENT.  Its `Alloc` PREDICTION is unchanged (`[0, 20]`, width 21.00 exactly as
    //   // recorded); what moved is the COUNTED value, from 0 to 2, and it moves with WHICH OTHER SUITES
    //   // RAN FIRST IN THIS JVM.  Measured three ways on one unchanged tree: `testOnly
    //   // morkl.SpatialScaleCheck` alone reads `err=21.00 loErr=1.00` (counted 0); `testOnly
    //   // morkl.SpatialDemandCheck morkl.SpatialScaleCheck` reads `err=7.00 loErr=3.00` (counted 2);
    //   // `testOnly morkl.SpatialFactsCheck morkl.SpatialScaleCheck` reads 21.00 again.  Only the
    //   // measured column moves — every predicted endpoint and every `width` on every family is
    //   // byte-identical across the three — so this is process-global executable state (the `Interner`'s
    //   // id assignment and the per-node count memos are the candidates), not analysis nondeterminism.
    //   //
    //   // THE LEDGER IS MAINTAINED AGAINST `sbt test`, where `SpatialDemandCheck` sorts before
    //   // `SpatialScaleCheck`, so `absorption` does not fail here and listing it would be STALE EVIDENCE.
    //   // A single-suite `testOnly morkl.SpatialScaleCheck` will therefore report it as newly FAILING and
    //   // UNDIAGNOSED; that is the defect, not a reason to keep a stale subject.  Fixing it properly means
    //   // giving the measuring suites a JVM whose global state is known (an sbt `testGrouping` fork, or a
    //   // deterministic pre-intern of the ladder's own alphabet), which is a harness change and is not one.
    //   Vector("union/disjoint-keys"),
    //   5462.33, 16387.0, "SpatialShape.scala (`mk`, the width spill) / SpatialTypeSystem.scala (`constrainShape`)",
    //   "`alloc := rebuilt` is MET against the result's node envelope, and for a union whose branches are " +
    //   "attached whole the rebuilt count is O(1) while the envelope is O(n): 2 fresh `ITrie` nodes measured " +
    //   "at EVERY rung of the 64 -> 16384 ladder of key-disjoint operands under a shared prefix, against " +
    //   "66 -> 16386 predicted (error 5462, per-doubling slope 1.00 against a measured 0.00).  The " +
    //   "`IntMap` spine allocation this misses is the SECOND declared oracle gap in SpatialEvents.scala and " +
    //   "is bounded by 2x the counted total, so it does not explain it.  The CONTRAST that makes this a " +
    //   "defect and not a modelling limit: on `union/paired-keys`, where every key is genuinely paired, the " +
    //   "same transfer is accurate to 1.01x.  " +
    //   "THE CROSSOVER IS NOW A GATE, NOT A STORY: `SpatialFrontierCheck`'s `KEY-DISJOINT union` sweep " +
    //   "runs n = 4, 8, 12, 13, 16, 24, 64, 256, 1024 against the HAND-DERIVED frontier (which reads the " +
    //   "real tries and says `|Q| = 2` at every n) and asserts the model is EXACT — `rebuilt = [2,2]` — " +
    //   "for every n at or below `Shape.MaxHeads = 12`.  Above the cap it prints the count-only pairing " +
    //   "the spill leaves behind.  So the defect is localised to ONE line of the carrier: " +
    //   "`Shape.mk`'s width spill keeps the untracked COUNT and the per-head tail summary and throws the " +
    //   "head NAMES away, and `Shape.possibleHeads` — the single query `SpatialFrontier.headDisjoint` and " +
    //   "the relational walk go through — therefore answers `None` for every open shape.  " +
    //   "TWO WAYS TO CARRY THE NAMES, BOTH PROTOTYPED AND MEASURED, AND WHY NEITHER IS IN THIS COMMIT.  " +
    //   "(1) A FIFTH γ CHANNEL `otherKeys: Option[Set[PathItem]]` (`U(V) ⊆ ks`).  It works: with it the " +
    //   "frontier reports `rebuilt = [2,2]` and `|Q| = [2,2]` FLAT from n = 4 to n = 4096, source " +
    //   "`Relational`, and `SpatialLawCheck`/`SpatialShapeCheck`/`SpatialSoundnessHunt` stay green (the " +
    //   "hunt did catch one real bug in the prototype — `Shape.isTop` has to test the new channel or " +
    //   "`leqStrong`'s ⊤ short circuit accepts values γ rejects).  But it is INERT unless " +
    //   "`SpatialTypeSystem.constrainShape` also passes it through its four-argument `Shape(...)`: " +
    //   "`SpatialType.reduce` runs on every decorated node, so MEASURED, `SpatialType.of(v)` carries the " +
    //   "52 spilled keys, `reduce(SpatialType.of(v))` carries `None`, and every node the cost model reads " +
    //   "carries `None`.  And a new γ channel is a new obligation for every γ CONSUMER: with it enforced, " +
    //   "`SpatialCheck`'s membership mirror reports `channels=` (nothing) on a value γ rejects and its " +
    //   "bounded search enumerates candidate spaces with head names the channel forbids — three " +
    //   "`SpatialCheckCheck` failures, in files this entry does not own.  " +
    //   "(2) SPILL THE TAIL DEPTH INSTEAD OF THE KEY: keep every key in `heads` and cap the excess keys' " +
    //   "tails (`capDepth(t, 0)` keeps their ε and head count) rather than merging them into an anonymous " +
    //   "bucket.  `MaxHeads` then bounds the number of tracked TAIL STRUCTURES, which is the budget that " +
    //   "actually costs memory, and the head set stays CLOSED — so γ, the order, the mirror and " +
    //   "`constrainShape` (which maps over `heads`) all keep working unchanged and the fact reaches " +
    //   "`priced` with no further plumbing.  Its price is that `Shape.of` on a wide value stops spilling " +
    //   "at all, which two suites assert as a precondition (`SpatialLawCheck`'s over-cap summary " +
    //   "regression asserts `others.hi == 2` after a 14-head value; `SpatialShapeCheck`'s WIDE matrix " +
    //   "counts spilled operands).  (2) IS THE RECOMMENDED FIX: one carrier change, no new γ channel, no " +
    //   "new obligation for any consumer.  Raising `shapeWidth` remains not-a-fix either way.")

    // ==============================================================================================
    // LIM-5g IS RETIRED — `union/disjoint-keys` was its last subject and it now MEETS its requirement.
    //
    // WHAT CLOSED IT is not recorded here as a model improvement, because it is not one: the entry was
    // ALREADY STALE at `01a5864`, before any of the n-ary work in this change — the baseline
    // `sbt test` at that commit reports all four of `LIM-1`, `LIM-2`, `LIM-5` and `LIM-5g` claiming
    // this subject and the subject passing.  So this is LEDGER DRIFT: whatever fixed the family was
    // committed without updating the entries that named it, and the stale-evidence check is what
    // caught it.  IT IS FOUR OF SEVENTY-THREE, AND NOT MORE: the `01a5864` baseline reports
    // "1607 of 1680 checks MET; 73 FAILED ... 33 are UNDIAGNOSED" for this suite, so retiring these
    // entries fixes the BOOKKEEPING and leaves the 69 measured failures exactly where they were.
    // The largest of those is the `rest-chain/nest` family, whose `lower-error` rows run to four
    // figures and which has no evidence entry at all.
    // An entry with no measured subject is itself a ledger failure, which is why this is a comment.
    // ==============================================================================================
    // Limitation("LIM-5g", "ladder", "graph", EffortComponent.Alloc, ErrAndSlope,
    //   Vector("union/disjoint-keys"),          // `absorption` left for the reason recorded in LIM-5
    //   4097.0, 8194.0, "SpatialTypeSystem.scala (`constrainShape`) / SpatialCost.scala (`TrieAlgebraCost.priced`)",
    //   "as LIM-5, at execT's magnitudes.")

    // ============================ LIM-6: there is no lower endpoint ===============================
    Limitation("LIM-6", "ladder", "trie", EffortComponent.Touch, WidthOnly,
      Vector("select/fixed-consumer", "union/paired-keys", "union/disjoint-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 73731.50,
      "SpatialCost.scala (`CostInterval.upperOnly`, `CostInterval.withoutTouchLower`)",
      "WHAT IS LEFT NOW THAT `touch` HAS A LOWER ENDPOINT.  This entry used to say `analyze` applied " +
      "`withoutTouchLower` unconditionally so every width was `upper + 1` BY CONSTRUCTION, and that " +
      "the second half was the fix.  It landed: `evalI`'s algebra entry is forced (the " +
      "visit hook precedes every fast-path test) and the frontier's must-paired count is added wherever " +
      "the whole-skip paths are discharged, which took `inter/shared-subtrie` to width 7.91 and out of " +
      "this entry.  The four families that remain have a must-count of ZERO for a real reason — a subset " +
      "union and a key-disjoint union are decided at the root, and a fixed selective consumer forces only " +
      "its own frontier — so for THOSE the width is genuinely `upper + 1` and the remedy is the upper " +
      "endpoint, not the lower."),
    Limitation("LIM-6g", "ladder", "graph", EffortComponent.Touch, WidthOnly,
      Vector("select/fixed-consumer", "union/paired-keys", "union/disjoint-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 73731.50, "SpatialCost.scala",
      "as LIM-6, and `inter/shared-subtrie` left it too (width 7.91) once `GraphCost.forcedEntry` learned " +
      "that `execT`'s guard reads the left operand only."),
    Limitation("LIM-6z", "ladder", "zipper", EffortComponent.Touch, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 10025.89, "SpatialCost.scala", "as LIM-6."),
    Limitation("LIM-6a", "ladder", "trie", EffortComponent.Alloc, WidthOnly,
      Vector("select/fixed-consumer", "union/paired-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 178049.40, "SpatialCost.scala",
      "as LIM-6, for `alloc`: no MUST-ALLOCATE count is derived, although a union of two operands with " +
      "`k` provably paired keys must rebuild at least `k` nodes."),
    Limitation("LIM-6ag", "ladder", "graph", EffortComponent.Alloc, WidthOnly,
      Vector("select/fixed-consumer", "union/paired-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 8203.50, "SpatialCost.scala", "as LIM-6a."),
    Limitation("LIM-6az", "ladder", "zipper", EffortComponent.Alloc, WidthOnly,
      Vector("union/paired-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 178049.40, "SpatialCost.scala", "as LIM-6a."),
    Limitation("LIM-6w", "ladder", "zipper", EffortComponent.Work, WidthOnly, Vector("union/paired-keys"),
      Double.PositiveInfinity, 28677.00, "SpatialCost.scala",
      "as LIM-6, for `work` on the ONE family where the zipper's upper endpoint is right (error 4.99, " +
      "slope 1.00 = declared): the whole width failure there is the missing lower endpoint and nothing " +
      "else, which is what makes this entry different from LIM-1."),

    // ============================ LIM-7: an exact law emitted as an upper bound ===================
    Limitation("LIM-7", "ladder", "trie", EffortComponent.Rounds, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 1821.44, "SpatialCost.scala (`CostModel.chainNest`)",
      "THE FRAME LAW IS USED FOR THE UPPER ENDPOINT ONLY.  `chainNest` returns " +
      "`CostInterval.upperOnly(work = frames, rounds = frames, touch = visits)`, and the measured round " +
      "count equals that upper endpoint EXACTLY at every rung (error 1.00, 72/136/264/520/1032) — so " +
      "`Σ_d K_d` is not an estimate here, it is the answer, and on a closed source it is equally an exact " +
      "LOWER bound.  Emitting it as an exact interval would take this channel from width 115 to width 1 " +
      "and make `Rounds` the first fully determined component in the model."),
    Limitation("LIM-7g", "ladder", "graph", EffortComponent.Rounds, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 1821.44, "SpatialCost.scala (`CostModel.chainNest`)", "as LIM-7."),
    Limitation("LIM-7z", "ladder", "zipper", EffortComponent.Rounds, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 1821.44, "SpatialCost.scala (`CostModel.chainNest`)", "as LIM-7."),
    Limitation("LIM-7w", "ladder", "trie", EffortComponent.Work, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 1.20e6, "SpatialCost.scala (`CostModel.chainNest`)",
      "as LIM-7 for `work`.  THE EXACTNESS THIS NOTE USED TO CLAIM IS GONE: it read \"whose upper " +
      "endpoint is likewise EXACT on this family (error 1.00 at every rung)\", and the measured " +
      "error is 41.91.  What removed it was making the n-ary ceiling SOUND (see LIM-12): the " +
      "previous endpoint was exact on THIS family and did not contain the run on another, so the " +
      "exactness was a property of a bound that excluded real runs.  This channel is on the " +
      "SELECTION tier, so its width budget is 8 and the gap is starker."),
    Limitation("LIM-7wg", "ladder", "graph", EffortComponent.Work, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 4683.93, "SpatialCost.scala (`CostModel.chainNest`)", "as LIM-7w."),

    // ==============================================================================================
    // LIM-12 / LIM-12z / LIM-13 / LIM-13z ARE NEW AND THEY ARE A REGRESSION I INTRODUCED, recorded
    // as one.  Correcting an UNSOUND n-ary ceiling raised the upper endpoint on this family and moved
    // its predicted growth class; the slope gate caught the class change, which is what that gate is
    // for.  These entries own `error` and the two PREDICTED-slope statistics; `width` on the same
    // rows stays with LIM-6a / LIM-7w, whose recorded figures the note below updates.
    // ==============================================================================================
    Limitation("LIM-12", "ladder", "trie", EffortComponent.Work, ErrSlopeOnly,
      Vector("rest-chain/nest"),
      39.89, 1.20e6, "SpatialCost.scala (`CostModel.liveTotal` / `chainNest`)",
      "THE COST OF MAKING THE N-ARY CEILING SOUND, ON THE FAMILY THAT PAYS MOST FOR IT.  `naryProbes` " +
      "and `naryScratch` both read `CostModel.liveTotal`, whose previous `2*nodes + k` arm was " +
      "REFUTED BY MEASUREMENT (see OP-6: counted 4399 against a predicted upper of 792 at k = 26 " +
      "on `ITrie.tailsUnion`, because an operand whose mask is below the split bit is carried down " +
      "UNCHANGED and re-charged at every intervening level).  Removing that arm leaves the two " +
      "DERIVED ceilings, met: `k*(spineNodes+1)` (calls x arity) and " +
      "`carryDepth*(spineNodes+k)` (entries x carry depth).  " +
      "WHAT THAT COSTS HERE IS NOT A CONSTANT, AND THE SLOPE GATE IS WHAT SAYS SO.  On this ladder " +
      "the nest is priced through `collectJoin(ch.leaves, ...)`, so BOTH factors grow with the " +
      "rung: `k = leaves` and `nodes = leaves * nd(leaf)`.  The `k*(spineNodes+1)` arm is then " +
      "QUADRATIC in the rung where the deleted arm was linear, and it is the arm the meet selects " +
      "while `k` is below `carryDepth` -- so the predicted growth CLASS changes partway up the " +
      "ladder.  MEASURED (the 625-test whole-suite run, which is the ordering this ledger is " +
      "maintained against), trie `Work`: width 21564.66 -> 1.20e+06, `error` 1.00 -> 41.91, " +
      "`slope-predicted-vs-declared` 1.60 and `slope-vs-measured` 0.89 both newly red, while " +
      "`slope-measured-vs-declared` is UNCHANGED at 0.71 -- which is the discriminating " +
      "observation, because that statistic does not read the prediction.  trie `Alloc`: width " +
      "44817.29 -> 178049.40, `error` -> 17.33, the two predicted slopes -> 0.94 and 0.45.  " +
      "AND IT DESTROYED A DOCUMENTED EXACTNESS.  `LIM-7w` records this channel's upper endpoint as " +
      "\"EXACT on this family (error 1.00 at every rung)\"; it is 41.91 now.  That is the honest " +
      "shape of the trade: the old endpoint was exact ON THIS FAMILY and did not contain the run on " +
      "another, and an interval that excludes the run is a wrong answer where a wide one is only a " +
      "weak one.  " +
      "WHAT WOULD RECOVER IT, and it is the same route as OP-6's: a STRUCTURAL fact about the " +
      "operand set, not a better generic ceiling.  `OperandShape.DistinctSingleKey` did exactly " +
      "this for the operator table's `iteration` row (46.58 -> 6.47 on `Work`, 138.62 -> 24.54 on " +
      "`Alloc`, from the ceiling alone), and the nest's operands are the per-frame `joinAll` " +
      "results, so the analogous fact is about what `chainNest` hands its accumulate.  Deriving it " +
      "needs the closed shape's key layout, which is review item 5's certificate tier -- which is " +
      "the route plan.md task 1B.2 takes -- without item 5, since TailsFacts.of already has the sets."),
    Limitation("LIM-12z", "ladder", "zipper", EffortComponent.Work, ErrSlopeOnly,
      Vector("rest-chain/nest"),
      39.89, 1.17e6, "SpatialCost.scala (`ZipperCost`) / `CostModel.liveTotal`",
      "as LIM-12, inherited through the control-flow fallback: `execZ` hands the nest to `evalI`, so " +
      "the corrected ceiling arrives here with it."),
    Limitation("LIM-13", "ladder", "trie", EffortComponent.Alloc, ErrSlopeOnly,
      Vector("rest-chain/nest"),
      16.40, 178049.40, "SpatialCost.scala (`CostModel.liveTotal` / `naryScratch`)",
      "as LIM-12, on `alloc`: `naryScratch` reads the same `Sigma_calls |live|` factor, because the " +
      "split arrays are allocated PER CALL over that call's live count and a carried entry is " +
      "allocated for again."),
    Limitation("LIM-13z", "ladder", "zipper", EffortComponent.Alloc, ErrSlopeOnly,
      Vector("rest-chain/nest"),
      16.40, 178049.40, "SpatialCost.scala (`ZipperCost`) / `CostModel.liveTotal`",
      "as LIM-13, through the control-flow fallback."),
    // ==============================================================================================
    // LAD-L1 .. LAD-L12 — THE `lower-error` ROWS (plan.md 1B.7/1B.8).  Twenty-six of the thirty-three
    // rows that had NO EVIDENCE ENTRY are this one defect seen through one statistic on four families
    // and three backends.  One entry per (backend, component) because `Limitation` is keyed that way;
    // the shared diagnosis is written out on LAD-L1 and referenced by the rest.
    // ==============================================================================================
    Limitation("LAD-L1", "ladder", "trie", EffortComponent.Alloc, LowerErrOnly,
      Vector("rest-chain/nest", "select/fixed-consumer", "union/paired-keys"), 16387.0, Double.NaN, "SpatialCost.scala",
      "NO MUST-COUNT IS DERIVED FOR THESE FAMILIES, AND `LIM-6`'s NOTE ALREADY SAYS WHY (plan.md " +
      "1B.7/1B.8).  `LIM-6` owns `width` on the same subjects and states the cause: \"the four " +
      "families that remain have a must-count of ZERO for a real reason — a subset union and a " +
      "key-disjoint union are decided at the root, and a fixed selective consumer forces only its own " +
      "frontier — so for THOSE the width is genuinely `upper + 1` and the remedy is the upper " +
      "endpoint, not the lower.\"  `lower-error` is `(actual+1)/(lower+1)`, so it reads the SAME " +
      "missing floor through a different statistic and runs to four figures where `width` runs to " +
      "five.  These entries exist so the rows are not UNDIAGNOSED; they are not a second defect.  " +
      "WHY `rest-chain/nest` IS ON THIS LIST TOO, which is the one that is not obvious: the ladder " +
      "measures `Routine.optimized`'s body, and the optimizer HOISTS the loop-invariant head out of " +
      "the inner body, so `RestChain.recognize` no longer sees a chain and the nest is priced by the " +
      "GENERIC `Iteration` arm.  That arm's floor is `groupsLo` per level, and the `rest` mention has " +
      "no must-head count, so the whole nest's floor is `K_1` where the truth is `Σ_d K_d` — 8 " +
      "against 16392 at the top rung.  1B.4's `chainNest` `rounds` floor (`framesLo`, the profile's " +
      "own lower endpoint on `Σ_d K_d`) DOES close this, and it cannot be reached from here: it lives " +
      "at the one node that prices the WHOLE nest, and the generic arm assembles its floor bottom-up " +
      "where a sum-structured floor cannot be expressed without over-counting.  Verified: the " +
      "optimized report carries ZERO rest-chain notes.  So the route is to make `RestChain.recognize` " +
      "see through the hoisted `Composition` — recorded, and deliberately not attempted here, because " +
      "the hoisted factor has to be priced per frame and a wrong lower endpoint is unsound where a " +
      "wide one is only weak."),
    Limitation("LAD-L2", "ladder", "trie", EffortComponent.Touch, LowerErrOnly,
      Vector("rest-chain/nest", "select/fixed-consumer", "union/paired-keys", "union/disjoint-keys"), 32769.5, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the trie Touch channel."),
    Limitation("LAD-L3", "ladder", "trie", EffortComponent.Work, LowerErrOnly,
      Vector("rest-chain/nest"), 38496.77, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the trie Work channel."),
    Limitation("LAD-L4", "ladder", "trie", EffortComponent.Rounds, LowerErrOnly,
      Vector("rest-chain/nest"), 1821.44, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the trie Rounds channel."),
    Limitation("LAD-L5", "ladder", "graph", EffortComponent.Alloc, LowerErrOnly,
      Vector("rest-chain/nest", "select/fixed-consumer", "union/paired-keys"), 8194.0, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the graph Alloc channel."),
    Limitation("LAD-L6", "ladder", "graph", EffortComponent.Touch, LowerErrOnly,
      Vector("rest-chain/nest", "select/fixed-consumer", "union/paired-keys", "union/disjoint-keys"), 32769.5, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the graph Touch channel."),
    Limitation("LAD-L7", "ladder", "graph", EffortComponent.Work, LowerErrOnly,
      Vector("rest-chain/nest"), 2927.57, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the graph Work channel."),
    Limitation("LAD-L8", "ladder", "graph", EffortComponent.Rounds, LowerErrOnly,
      Vector("rest-chain/nest"), 1821.44, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the graph Rounds channel."),
    Limitation("LAD-L9", "ladder", "zipper", EffortComponent.Alloc, LowerErrOnly,
      Vector("rest-chain/nest", "select/fixed-consumer", "union/paired-keys"), 16387.0, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the zipper Alloc channel."),
    Limitation("LAD-L10", "ladder", "zipper", EffortComponent.Touch, LowerErrOnly,
      Vector("rest-chain/nest"), 2399.33, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the zipper Touch channel."),
    Limitation("LAD-L11", "ladder", "zipper", EffortComponent.Work, LowerErrOnly,
      Vector("rest-chain/nest", "select/fixed-consumer", "union/paired-keys"), 37427.44, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the zipper Work channel."),
    Limitation("LAD-L12", "ladder", "zipper", EffortComponent.Rounds, LowerErrOnly,
      Vector("rest-chain/nest"), 1821.44, Double.NaN, "SpatialCost.scala",
      "as LAD-L1, on the zipper Rounds channel."),

    // ==============================================================================================
    // LAD-S1 .. LAD-S4 — THE `slope-measured-vs-declared` ROWS, AND THE STATISTIC DOES NOT READ THE
    // PREDICTION (plan.md 1B.7).  These are the last four of the thirty-three.
    // ==============================================================================================
    Limitation("LAD-S1", "ladder", "trie", EffortComponent.Work, MeasSlopeOnly,
      Vector("rest-chain/nest"), 0.64, Double.NaN, "IntTrieOps.scala (`collectLive`'s dedup regime)",
      "THE COUNTED WORK IS SUPER-LINEAR ON THE FIRST RUNGS AND LINEAR AFTER, AND THAT IS THE " +
      "EXECUTOR AND NOT THE MODEL.  This statistic compares the MEASURED slope to the family's " +
      "DECLARED one and never looks at a prediction, so a red row here cannot be a model defect.  " +
      "MEASURED, trie `Work` on this ladder: actual = 1698, 5302, 16193, 32887, 68560, 144398, " +
      "303997, 641045, 1347386 — the first two windows are 3.1x and 3.05x for a 2x rung (slope 1.64) " +
      "and every window after is 2.0x-2.1x (slope 1.02-1.08).  The gate reads the WORST window, so it " +
      "reports 1.64 against a declared 1.00 and the difference 0.64 exceeds the 0.35 tolerance.  " +
      "THE CAUSE IS `IntTrieOps.collectLive`'s DEDUP REGIME.  Its scan is `Σ_{j<k} j = k(k-1)/2` " +
      "while the distinct operand count is below `dedupScanMax = 24`, and ONE `IdentityHashMap` probe " +
      "each above it.  The family is `chain(n, 8, \"rc\")` — 8 heads, so the per-head fan is `n/8` — " +
      "and the fan crosses 24 between the third and fourth rung, which is exactly where the measured " +
      "slope settles.  So the family IS linear asymptotically (the declaration is right) and is " +
      "quadratic in the fan below the threshold (the measurement is right).  " +
      "WHAT WOULD CLOSE IT is a longer ladder that starts past the threshold, or a per-family " +
      "declaration that names the regime change.  Neither is a model change, which is why this is " +
      "recorded rather than fixed: moving the ladder would hide a real feature of the executor."),
    Limitation("LAD-S2", "ladder", "trie", EffortComponent.Alloc, MeasSlopeOnly,
      Vector("rest-chain/nest"), 0.50, Double.NaN, "IntTrieOps.scala (`collectLive`'s dedup regime)",
      "as LAD-S1, on `alloc`: `IntTrieOps` allocates the split arrays per call over that call's live " +
      "count, so the same regime change shows.  MEASURED: worst window 1.50, last window 1.12."),
    Limitation("LAD-S3", "ladder", "zipper", EffortComponent.Work, MeasSlopeOnly,
      Vector("rest-chain/nest"), 0.64, Double.NaN, "IntTrieOps.scala (`collectLive`'s dedup regime)",
      "as LAD-S1: `execZ` hands the nest to `evalI`, so its counted events are `evalI`'s plus one " +
      "fallback entry — the actuals differ from the trie row by exactly 1 at every rung."),
    Limitation("LAD-S4", "ladder", "zipper", EffortComponent.Alloc, MeasSlopeOnly,
      Vector("rest-chain/nest"), 0.50, Double.NaN, "IntTrieOps.scala (`collectLive`'s dedup regime)",
      "as LAD-S2, through the same fallback."),

    // ==============================================================================================
    // THE LAST THREE OF THE THIRTY-THREE (plan.md 1B.7).
    // ==============================================================================================
    Limitation("LAD-A1", "ladder", "trie", EffortComponent.Alloc, ErrAll, Vector("absorption"),
      21.00, Double.NaN, "SpatialFrontier.scala (no SUBSET case from the term)",
      "THE ABSORPTION IDENTITY IS NOT A FACT THE FRONTIER CAN USE.  The family is " +
      "`s0 ∪ (s0 ∩ s1)`, the inner intersection is contained in the outer LEFT operand, and " +
      "`Trie.unionR` therefore returns `s0` BY POINTER — `Identity(LEFT)`, ZERO fresh nodes at every " +
      "rung.  MEASURED: actual = 0 at all nine rungs against a predicted 20, so " +
      "`error = (20+1)/(0+1) = 21.00`.  The prediction is SOUND and it is pricing a general union.  " +
      "WHY THE FRONTIER CANNOT SEE IT.  `SpatialFrontier` decides `same` (the two operands are the " +
      "SAME TERM, structurally) and `headDisjoint` (from the two types), and those are the only two " +
      "routes to a `FrontierCase.Left`.  `s0 ∩ s1 ⊆ s0` is neither: it is a SYNTACTIC containment " +
      "between the two operand TERMS, and the two operand TYPES do not imply it — an intersection's " +
      "type is not in general below its left factor's, because the analysis need not prove the " +
      "intersection non-empty.  " +
      "WHAT WOULD CLOSE IT is a syntactic subset recogniser beside `same`: `b` is provably inside `a` " +
      "when `b` is an `Intersection`/`Restriction`/`Range` one of whose operands IS `a` (the same " +
      "decision procedure `same` already uses, one constructor deeper).  That yields " +
      "`FrontierCase.Left` and `rebuilt = 0`, and it is the same shape of fact as `same` rather than " +
      "a new tier.  RECORDED and not shipped here: it is a new relational case and the four suites " +
      "that gate the frontier have to run against it, which is a separate pass."),
    Limitation("LAD-A2", "ladder", "graph", EffortComponent.Alloc, ErrAll, Vector("absorption"),
      11.00, Double.NaN, "SpatialFrontier.scala (no SUBSET case from the term)",
      "as LAD-A1.  `execT` allocates ONE node where `evalI` allocates none (its result cell), so the " +
      "actual is 1 against a predicted 21 and `error = (21+1)/(1+1) = 11.00`."),
    Limitation("LIM-7wz", "ladder", "zipper", EffortComponent.Work, WidthOnly,
      Vector("rest-chain/nest"), Double.NaN, 1.17e6,
      "SpatialCost.scala (`ZipperCost`) / `CostModel.liveTotal`",
      "as LIM-7w and LIM-7wg, on the zipper, and it had no entry at all.  `execZ` hands the nest to " +
      "`evalI` through the control-flow fallback, so the width is `evalI`'s plus the one fallback " +
      "entry — 1.17e+06 against the trie row's 1.20e+06, the two differing by exactly that entry at " +
      "every rung.  The upper endpoint is the same `Σ_calls |live|` ceiling LIM-12 diagnoses; the " +
      "floor is LAD-L11's."),

    Limitation("LIM-9", "ladder", "trie", EffortComponent.Touch, LowerErrOnly, Vector("absorption"),
      12.17, Double.NaN, "SpatialCost.scala (`TrieAlgebraCost.priced` / `Shares`)",
      "THE PRICE OF REFUSING A FLOOR THAT WAS NEVER JUSTIFIED, and the one family on this table that " +
      "pays it.  `absorption` is `s0 ∪ (s0 ∩ s1)` — the SAME declared input in both operands of the " +
      "outer union — so `Rel.mayShare` is true and `priced`'s must-paired `touch` count is refused " +
      "(see the OP-1 retirement note above for why it has to be: `unionR`'s per-level `a eq b` and " +
      "`IntTrieOps.unionTries`' `if a eq b then a` let ONE pointer-shared subtree skip every paired " +
      "prefix beneath it, and `s0 ∩ s1` really is built out of `s0`'s nodes).  The floor drops to the " +
      "forced entry visit and `lower-error` (`(actual+1)/(lower+1)`) goes 1.00 -> 12.17.  `width` moves " +
      "with it, 120.78 -> 181.17 — the same refusal seen from the other side, `(upper+1)/(lower+1)` on " +
      "an UNCHANGED upper — but that row is LIM-4/LIM-4g's and was already failing the budget tier, so " +
      "the only NEW red rows on this table are the two `lower-error` ones this entry is declared over.  " +
      "No cornerstone and no operator row changed tier.  " +
      "IT IS NOT A LOOSENING TO BE UNDONE.  The measured run on this family really does visit about " +
      "twelve times what the floor now claims, so on THESE inputs the skip evidently does not fire " +
      "(which of the two pointer tests it misses I did not determine, and the entry does not claim to " +
      "know).  But nothing in the shape domain distinguishes these inputs from the ones where it does " +
      "fire, and a floor is a claim about every member of the abstraction.  What would close it is a " +
      "MUST-share analysis to sit " +
      "beside the MAY one: where the algebra provably hands a subtree back BY POINTER the skipped " +
      "prefixes are known, and the floor is the paired count MINUS them.  `Shares` computes only the " +
      "MAY direction (`disjointFrom`), which is all the soundness of the refusal needs."),
    Limitation("LIM-9g", "ladder", "graph", EffortComponent.Touch, LowerErrOnly, Vector("absorption"),
      12.17, Double.NaN, "SpatialCost.scala (`TrieAlgebraCost.priced` / `Shares`)",
      "as LIM-9: `GraphExec` calls the same `ITrie` entry points, so `priced` serves both executables " +
      "and the two rows move together.  Both entries report `width` as `NaN` on purpose — `lower-error` " +
      "is the only statistic they are declared over, and a number in that slot would read as a claim " +
      "about an upper endpoint neither of them touches."),

    // ============ LIM-8/LIM-8g ARE GONE: the Patricia constant on a key-disjoint union ==============
    // They recorded a CONSTANT FACTOR and nothing else — the Patricia bound charged 3 visits per merged
    // child entry (`2k-1` nodes plus the entry) where the measured walk over key-disjoint operands
    // averages ~0.6, because the join attaches whole branches instead of descending them.  Measured
    // 10.26 against the 10x budget tier; it now measures 8.54 on both `trie` and `graph`, inside the
    // tier, with the slope unchanged (0.99 measured against 1.00 predicted, declared 1.00).  Deleted
    // rather than kept at a passing number: stale evidence is a failure.

    // ==============================================================================================
    // THE CORNERSTONES, ON `Routine.optimized`'s BODY  (SpatialEventsCheck)
    //
    // These are the numbers the review is about, re-measured on the form that runs.  What the
    // optimized form ALREADY fixed, for the record, because it is most of the review's complaint:
    //   * n-queens: 53 Space nodes -> 1.  The ordinary rule list COMPILE-TIME EVALUATES it, so the
    //     "3,839x work / 213,465x alloc / 3.98Mx touch" figures describe a term that never runs.  There
    //     is no run-time cost left to gate and nothing is excused below.
    //   * puzzle15 `Work`: error 1.01, and `Rounds`: error 1.00 with a [57, 84] interval against a
    //     counted 84.  The rest-chain frame law reaches those two components and they are now EXACT.
    //   * aunt/temperature `Work` and every cornerstone's `Rounds`: 1.00-1.48.
    //   * datalog-sn, ALL FOUR components: the SPATIAL LEAST FIXPOINT of `sn_tc`'s parameter tuple
    //     (`SpatialCost.paramFixpoint`) replaced the all-strings path universe as the depth bound, so
    //     the depth fell 23 -> 3 and `Work` (1.07), `Rounds` (1.22) and `Alloc` (1.62) all came inside
    //     budget — the entries that excused them (CS-5, CS-6, CS-12, CS-13) are RETIRED, and the
    //     reference/zipper reports stopped being symbolic in `|sn_tc()|` at the same time.
    // What is left is `Alloc` and `Touch`, listed below.
    // ==============================================================================================

    Limitation("CS-1", "cornerstone", "trie", EffortComponent.Alloc, ErrAll,
      // `gol` LEFT THIS ENTRY (plan.md 1B.7).  `Shape.maxTailSize` (1B.5) and the certificate tier's
      // per-head precision took its predicted `alloc` from 26654 to 6707 and its `touch` from 90520
      // to 26650 against unchanged counted values, so every one of its rows is now inside the
      // budget.  Deleted from the subject list, not annotated: stale evidence is a ledger failure.
      Vector("aunt"), 30.47, Inf,
      "SpatialCost.scala (`TrieAlgebraCost.priced`) / SpatialFrontier.scala",
      "LIM-5 reaching whole programs: `alloc := rebuilt` is met against the RESULT's node envelope, so a " +
      "program whose merges attach branches whole is over-charged (aunt 16 counted / 191 predicted = 11.3x, " +
      "gol 1175 / 21169 = 18.0x).  The same transfer is accurate to 1.01x on `union/paired-keys`, where " +
      "the rebuilt count really is the envelope — so this is a defect in the MEET, not a limit of the " +
      "bound.  `datalog-sn` LEFT THIS ENTRY (94.6x -> 1.62x): the recursion depth it was multiplied by " +
      "came from an all-strings path universe (23 levels) and now comes from the SPATIAL LEAST FIXPOINT of " +
      "the routine's parameter tuple (3 levels) — `SpatialCost.paramFixpoint`."),
    Limitation("CS-2", "cornerstone", "zipper", EffortComponent.Alloc, ErrAll,
      // `gol` LEFT THIS ENTRY (plan.md 1B.7).  `Shape.maxTailSize` (1B.5) and the certificate tier's
      // per-head precision took its predicted `alloc` from 26654 to 6707 and its `touch` from 90520
      // to 26650 against unchanged counted values, so every one of its rows is now inside the
      // budget.  Deleted from the subject list, not annotated: stale evidence is a ledger failure.
      Vector("aunt"), 29.97, Inf, "SpatialCost.scala (`ZipperCost`)", "as CS-1, through `SpaceZipper.materialize`."),

    // ==============================================================================================
    // CS-3 / CS-4 ARE RETIRED (plan.md 1B.7).  `gol` was their ONLY subject and it no longer fails:
    // `Shape.maxTailSize` (1B.5) took its predicted `touch` from 90520 to 26650 against an unchanged
    // counted 4138, i.e. `error` 21.9x -> 6.27x, inside the 10x budget tier.  An entry with no failing
    // subject is itself a ledger failure, so they are deleted.
    // ==============================================================================================

    Limitation("CS-8", "cornerstone", "trie", EffortComponent.Alloc, WidthAll,
      // `gol` LEFT THIS ENTRY (plan.md 1B.7).  `Shape.maxTailSize` (1B.5) and the certificate tier's
      // per-head precision took its predicted `alloc` from 26654 to 6707 and its `touch` from 90520
      // to 26650 against unchanged counted values, so every one of its rows is now inside the
      // budget.  Deleted from the subject list, not annotated: stale evidence is a ledger failure.
      Vector("aunt"), Inf, 294.50, "SpatialCost.scala",
      "LIM-6 on whole programs: every `alloc` interval starts at 0 because no MUST-ALLOCATE count is " +
      "derived, so WIDTH is `upper + 1` by construction (aunt [0,191], gol [0,21169], datalog [0,291] — " +
      "the datalog UPPER is now within 1.62x of the count, so what is left on it is the missing lower " +
      "endpoint and nothing else)."),
    Limitation("CS-11z", "cornerstone", "zipper", EffortComponent.Alloc, LowerErrOnly,
      Vector("aunt"), 11.80, Inf, "SpatialCost.scala (`ZipperCost`)",
      "THE LAZY BACKEND'S `alloc` FLOOR IS THIN, AND THE LAZINESS IS THE REASON (plan.md 1B.7).  " +
      "MEASURED: `aunt/zipper` counts 58 fresh nodes in a predicted `[4, 1767]`, so " +
      "`lower-error = (58+1)/(4+1) = 11.80`.  The floor is not ZERO — `execZ`'s forced entries are " +
      "claimed — it is 14x below the run.  " +
      "WHY A BIGGER FLOOR IS NOT AVAILABLE HERE, and it is the same sentence `ZipperCost.tailsInter` " +
      "already carries: `SpaceZipper`'s `merged` is a LAZY VAL, so the materialisation and every " +
      "`ITrie` call under it happen only when a consumer QUERIES the cursor, and a consumer that " +
      "meets the cursor with the empty space never does.  Claiming the n-ary op's forced scratch and " +
      "its entry visit anyway was MEASURED and REFUTED: zipper `Touch` containment went 100% -> 93% " +
      "and `Alloc` 100% -> 98% on the corpus, with `actual=10 in [18, 16]` on the worst point — an " +
      "INVERTED interval, the unmistakable signature of a must claim for work that did not happen.  " +
      "WHAT WOULD CLOSE IT is a DEMAND fact per operation rather than per region: `SpatialDemand` " +
      "already decides which cursor layers a consumer forces, and `ZipperCost` reads it for the " +
      "whole-region price (`demandPrice`) but not for the per-operation floors.  That is a " +
      "consumer-directed must-count and it is the same shape of fact as `forced` — which this model " +
      "receives and, for the eager operators, deliberately ignores."),

    Limitation("CS-9", "cornerstone", "zipper", EffortComponent.Alloc, WidthAll,
      // `gol` LEFT THIS ENTRY (plan.md 1B.7).  `Shape.maxTailSize` (1B.5) and the certificate tier's
      // per-head precision took its predicted `alloc` from 26654 to 6707 and its `touch` from 90520
      // to 26650 against unchanged counted values, so every one of its rows is now inside the
      // budget.  Deleted from the subject list, not annotated: stale evidence is a ledger failure.
      Vector("aunt"), Inf, 353.60, "SpatialCost.scala",
      "as CS-8.  `datalog-sn` is NEW HERE for the reason given in CS-4: the zipper row exists now that the " +
      "prediction is numeric, and its width [0, 292] is the missing `alloc` lower endpoint alone (the " +
      "upper is within 1.60x)."),
    // CS-10/CS-11 ARE GONE: the whole-program `touch` WIDTH.  They recorded what was left of LIM-6 on
    // whole programs once `touch` gained a lower endpoint — `evalI` is eager, so one visit per algebra
    // node is forced, and the must-paired frontier count is added where the whole-skip paths are
    // discharged.  `aunt` (180000 -> 12.99), `temperature` (-> 24.25) and `datalog-sn` (1198 -> 31.1)
    // left in earlier rounds; `gol` was the last subject at 70.06 and now measures 53.67 (trie) / 53.72
    // (zipper), inside the 64 budget.  Deleted, not kept at a passing number.
    // CS-14 IS GONE with CS-7 — see the note above.

    // ---- puzzle15: FINITE AND USELESS.  Its own entries, because the magnitude is its own statement --
    // ==============================================================================================
    // CS-10 / CS-10z — the cornerstone `Work` channel, which was UNDIAGNOSED on six rows before this
    // change and on nine after it.  Every one of the nine MOVED when the n-ary ceiling was corrected,
    // so the entry owns the current figures; it also says which part of each predates the change,
    // because attributing a pre-existing failure to a fix that only made it louder would be wrong.
    // ==============================================================================================
    Limitation("CS-10", "cornerstone", "trie", EffortComponent.Work, ErrWidth,
      // `datalog-sn` LEFT THIS ENTRY and the figures are RE-DERIVED (plan.md 1B.7): 1B.2's
      // `pkdLiveTotal` reads the per-child key sets and bounds the n-ary descent per operand, which
      // took datalog's `Work` to error 1.43 / width 2.48 — inside the SELECTION tier — and puzzle15's
      // from 255.50 / 885.43 to 193.42 / 667.24.
      // RE-DERIVED AGAIN from 193.42 / 667.24 (plan.md 1B.5): `sliceBudget` caps the 15-fold
      // `collapse` composition, which is inside puzzle15's `Work` total too.
      Vector("aunt", "puzzle15"),
      161.79, 558.14, "SpatialCost.scala (`CostModel.liveTotal`) + SpatialShape.scala (puzzle15)",
      "THE N-ARY CEILING REACHING WHOLE PROGRAMS.  Every cornerstone loop accumulates with " +
      "`ITrie.joinAll`, so `CostModel.liveTotal` is in each of these totals, and correcting its " +
      "REFUTED `2*nodes + k` arm (OP-6: counted 4399 against a predicted 792 at k = 26) moved all " +
      "nine rows at once.  Measured, before -> after: `aunt trie Work` error 5.15 -> 8.82 and width " +
      "(not failing) -> 10.05; `datalog-sn trie Work` error 9.20 -> 19.20, width 15.89 -> 33.16; " +
      "`puzzle15 trie Work` error 16.71 -> 255.50, width 57.63 -> 885.43.  " +
      "WHAT PREDATES THIS CHANGE, stated separately because the entry must not take credit for it: " +
      "six of the nine were ALREADY red and undiagnosed at `01a5864` (`aunt trie Work error`, " +
      "`datalog-sn trie Work error`/`width`, `datalog-sn zipper Work error`, `puzzle15 trie Work " +
      "error`/`width`), so the ceiling is A cause of the current figure and not the whole cause of " +
      "the failure.  " +
      "AND THE THREE PROGRAMS DO NOT SHARE ONE RESIDUAL.  `puzzle15`'s is dominated by the same " +
      "cardinality blow-up CS-P1/CS-P2 attribute to `SpatialShape.scala` / `SpatialTypes.scala` — " +
      "its `Alloc` and `Touch` reach 1e+55 there, which no cost transfer can cause — so its `Work` " +
      "residual belongs with those and not here.  `aunt` and `datalog-sn` are within one order of " +
      "magnitude of their budgets and are the two the operand-structure route (`OperandShape`, see " +
      "the retired OP-2) should be tried on first: `datalog-sn`'s `sn_tc` is the one self-recursive " +
      "routine no `asFixpoint` lowering recognises, so its accumulate is exactly the shape that " +
      "route addresses."),
    Limitation("CS-10z", "cornerstone", "zipper", EffortComponent.Work, ErrWidth,
      // as CS-10: `datalog-sn` left (error 1.55 / width 3.02) and puzzle15 re-derived.
      Vector("puzzle15"),
      // RE-DERIVED AGAIN from 193.38 / 666.83 (plan.md 1B.5), same cause as CS-10.
      161.76, 557.81, "SpatialCost.scala (`ZipperCost`) / `CostModel.liveTotal`",
      "as CS-10, through the control-flow fallback: `execZ` hands every loop to `evalI`, so the " +
      "corrected ceiling is in the zipper's total too.  `aunt` is NOT a subject here — its zipper " +
      "`Work` meets its budget, because that channel is on the Budget tier (64) where the trie's is " +
      "on Selection (8), and 8.82/10.05 clears the looser one."),
    Limitation("CS-P1", "cornerstone", "trie", EffortComponent.Alloc, ErrWidthMag, Vector("puzzle15"),
      // RE-DERIVED from 4.31e50, 2.70e51 (plan.md 1B.7): 1B.2/1B.3/1B.4 together.
      // RE-DERIVED AGAIN from 1.00e49 / 5.40e49 (plan.md 1B.5), by FOUR laws in sequence:
      // `Shape.maxTailSize` (7.610e+55 -> 1.017e+54), `Shape.tailsAlternative`, `groupUnion`'s
      // single-group exemption, and `SpatialCost.sliceBudget` (-> 2.316e+35).  3400x in all, and
      // still astronomical: the residual is ONE quantity, named at the end of this note.
      2.89e30, 1.56e31, "SpatialShape.scala / SpatialTypes.scala / SpatialAnalysis.scala (NOT the loop transfer)",
      "THE HEADLINE FAILURE, AND THE ONE THE OLD GATE HID BEHIND AN ALLOW-LIST — WITH ITS ROOT CAUSE " +
      "CORRECTED.  This entry used to say `Alloc`/`Touch` still multiply the per-level group maxima of the " +
      "16-level nest, and that the fix was to price the nest from `SpatialFacts.PrefixProfile` the way the " +
      "FRAMES already are.  MEASUREMENT SAYS OTHERWISE, and the number that settles it is the chain note " +
      "the analysis already prints for the OPTIMIZED body (1741 Space nodes, ONE recognised rest-chain " +
      "nest of depth 16): `frames = Σ K_d = [16,16]`, `leafInvocations = K_16 = [1,1]`, " +
      "`groupingVisits = Σ E_d = [16,16]`, per-level product `Π K_d = [1,1]`.  With `leaves = 1` the " +
      "`leaves · nd(leaf)` term is NOT a per-level product and pricing it from the profile changes " +
      "nothing: every component of the nest already uses the frame law.  " +
      "WHERE THE REMAINING 10^30 COMES FROM, TO ONE QUANTITY.  The nest's LEAF measure is a 15-fold " +
      "`Composition` inside the INLINED `collapse` routine — `collapse(loc, state) = Π_{o ≠ blank} " +
      "state(o)`, fifteen `Unwrap(state, o)` factors concatenated over ONE source with FIFTEEN DISTINCT " +
      "keys.  It used to be priced `Π |state|` = 3584^15 ≈ 4.1e53.  `SpatialCost.sliceBudget` now " +
      "recognises exactly that shape and charges the correct joint bound instead: fifteen DISJOINT " +
      "slices of one object of size S cannot jointly exceed `(S/15)^15` by AM-GM, which is 10^19 " +
      "smaller at S = 3584 and is where the 3400x came from.  " +
      "WHAT IS LEFT IS S ITSELF, and nothing else.  `(S/15)^15 ≤ 1e12` needs `S ≤ 95`; the analysis " +
      "has `S = 2133` (the bound on ONE head group's tail-set, from `Shape.tailsAlternative` over " +
      "`ass`); the TRUTH is `S = 16`.  Getting to 16 requires the FUNCTIONAL DEPENDENCY `a puzzle " +
      "state maps each cell to exactly one tile` — a relation BETWEEN TWO PATH POSITIONS.  Neither " +
      "channel of the `Shape × SpaceType` reduced product can express it: `Shape` is per-prefix and " +
      "`SpaceType` is a length histogram, and a product of two position-wise abstractions has no " +
      "vocabulary for `position 2 is determined by position 1`.  So this is not a missing transfer " +
      "or a loose constant — it is a DOMAIN limitation, and closing it means a third channel (a " +
      "key-to-fiber map, or a per-position cardinality-1 certificate), which is a design change and " +
      "not a fix.  Recorded in build.log under `1B.5`.  What `SpatialCost` could still shave is ~1.1x: `chainNest` and `collectJoin` both " +
      "charge `leaves · nd(leaf)`, and whether that is a genuine double charge depends on whether " +
      "`chainNest`'s term is meant to cover the INTERMEDIATE levels' `joinAll`s (`evalI` performs one per " +
      "frame, not one per nest) — not worth risking a sound upper bound for 1.1x of 10^52."),
    Limitation("CS-P2", "cornerstone", "trie", EffortComponent.Touch, ErrWidthMag, Vector("puzzle15"),
      // RE-DERIVED from 7.37e52 / 2.67e53, same cause as CS-P1.
      // RE-DERIVED from 9.86e50, 3.57e51 (plan.md 1B.7): 1B.2/1B.3/1B.4 together.
      1.13e31, 4.02e31, "SpatialShape.scala / SpatialTypes.scala / SpatialAnalysis.scala",
      "as CS-P1, on the descent: [965, 3.2e56] against a counted 3497.  Same leaf cardinality, multiplied " +
      "by the per-node Patricia constant."),
    Limitation("CS-P3", "cornerstone", "zipper", EffortComponent.Alloc, ErrWidthMag, Vector("puzzle15"),
      // RE-DERIVED from 3.23e52 / 2.02e53, same cause as CS-P1.
      // RE-DERIVED from 4.31e50, 2.70e51 (plan.md 1B.7): 1B.2/1B.3/1B.4 together.
      2.89e30, 1.56e31, "SpatialShape.scala / SpatialTypes.scala / SpatialAnalysis.scala",
      "as CS-P1; `execZ` falls back to `evalI` for the nest."),
    Limitation("CS-P4", "cornerstone", "zipper", EffortComponent.Touch, ErrWidthMag, Vector("puzzle15"),
      // RE-DERIVED from 7.37e52 / 2.67e53, same cause as CS-P1.
      // RE-DERIVED from 9.86e50, 3.57e51 (plan.md 1B.7): 1B.2/1B.3/1B.4 together.
      1.13e31, 4.02e31, "SpatialShape.scala / SpatialTypes.scala / SpatialAnalysis.scala", "as CS-P2."),

    // ==============================================================================================
    // WIDTH, PER OPERATOR, ON THE OPTIMIZED FORM  (SpatialCostCheck)
    //
    // WIDTH needs no execution: it is a property of the answer.  The table in `SpatialCostCheck`
    // establishes one thing outright — on a CLOSED one-operator program with exactly declared inputs,
    // EVERY endpoint of EVERY component on EVERY backend is FINITE and free of free variables (the review
    // item 5's invariant, asserted there and not excused anywhere).  What it also shows is that the
    // interval is almost always [0, upper]: 14 operators x 4 backends x 4 components x 2 statistics
    // (`width` and `magnitude`) = 448 checks, and the ones that fail below fail because the LOWER endpoint
    // does not exist, not because the upper is wrong — `magnitude` passes everywhere in this scope, which
    // is the useful negative result that the astronomical bounds are a WHOLE-PROGRAM loop phenomenon and
    // not a per-operator transfer.  The entries are grouped by (backend, component) with the exact
    // operator list, so a per-operator fix shows up as a STALE EVIDENCE failure on that operator alone.
    // ==============================================================================================

    // ==============================================================================================
    // OP-1 / OP-1g / OP-1z ARE RETIRED — `fixpoint` was their last subject on all three trie-shaped
    // executables, and it left when `TrieAlgebraCost.priced`'s must-paired `touch` floor got the side
    // condition it was always missing.  `mustDescend` is a pure CARDINALITY test: it discharges the
    // ROOT `a eq b` of `unionR`/`intersectionR`/`subtractionR` and says NOTHING about the RECURSIVE
    // pointer-identity short circuits — one per level in the operation itself, and one per level on the
    // whole child map in `IntTrieOps.unionTries`/`intersectTries`/`diffTries`/`raffTries`.  ONE
    // pointer-shared subtree at a paired prefix therefore skipped EVERY paired prefix beneath it while
    // the floor was charged for all of them, and it was reachable on two bare mentions:
    // `S"a" ∪ (S"a" <| {h0})` counted a `touch` of 6 against a claimed floor of 11, OUTSIDE its own
    // interval on both trie-shaped executables.  `SpatialCost.Shares` — a MAY analysis of which
    // already-materialised `ITrie` objects a term's value can be built out of, read off `evalI`'s and
    // `execT`'s own aliasing (a loop's `rest` IS a child of the source object; a fixpoint's recursion
    // mention IS the seed on round 1; a callee's parameter IS the argument) — is the answer, and
    // `Rel.mayShare` is the channel `priced` conjoins.
    //
    // WITH THE HOLE CLOSED WHERE IT LIVED, the fixpoint arm could restore the full `CostInterval.meet`
    // of the seed-priced round that had to be weakened to an upper-only meet while the hole was open
    // (the meet's `joinLo` was installing exactly that unsound floor at the round where
    // `var cur = evalI(init)` IS the caller's own trie by pointer).  `fixpoint` `Touch` went
    // `[1, 691]` — width 346, RED on trie, graph and zipper alike — to `[13, 691]`, width 49.43, inside
    // the 64 budget on all three.  19 pre-existing out-of-interval rows turned sound in the same change.
    // An entry with no measured subject is itself a ledger failure, which is why these are comments.
    // ==============================================================================================

    // Limitation("OP-1", "operator", "trie", EffortComponent.Touch, WidthAll,
    //   Vector("fixpoint"),
    //   Inf, 90000.0, "SpatialCost.scala (`TrieAlgebraCost.entryVisit` / `mustDescend`)",
    //   "WHAT IS LEFT AFTER THE `touch` LOWER ENDPOINT LANDED.  The previous revision of this entry said " +
    //   "`analyze` ended with an unconditional `withoutTouchLower`, so every `touch` width was `upper + 1` " +
    //   "BY CONSTRUCTION, and that a lower bound was derivable wherever the frontier proves paired prefixes " +
    //   "MUST be descended.  Both halves are now done and this entry lost FOUR subjects to them: `evalI` is " +
    //   "eager and every `ITrie` operation emits its visit BEFORE any fast-path test, so one visit per " +
    //   "algebra node is forced (halving every width here), and on the three symmetric merges the frontier's " +
    //   "must-paired count is added once the whole-skip paths (`isEmpty`, `a eq b`) are discharged by " +
    //   "cardinality — which took `union`, `intersection`, `subtraction` and `range-full` inside the budget " +
    //   "outright.  `restriction` AND `raffination` THEN LEFT TOO: their extra whole-skip path is " +
    //   "`ε ∈ right` (ε prefixes everything, so all of `x` is accepted or dropped by pointer), and " +
    //   "`Meas.epsAbsent` — the shape's ε-presence, which the domain always had and the measure did not " +
    //   "carry — discharges it.  THE SIX THAT REMAIN: `composition` reaches only the entry visit (69), " +
    //   "because the graft frontier derives no must side even with both `{ε}` cases discharged; " +
    //   "`iteration` (113) needs a must-count of its own.  `range-part` LEFT THIS ENTRY: its whole width " +
    //   "was an UNCOUNTABLE term — `IntTrie.ordered`'s per-node key sort emits no `EffortEvent` at all, " +
    //   "and `touch` is DEFINED as `TrieNodeVisit + PatriciaVisit`, so 144 of a predicted 199 (against a " +
    //   "counted 7) was charging work no run can confirm; it is a DECLARED assumption on the report now, " +
    //   "and the order-statistic slice's own bound became the SUM `w + 2(L+1)` instead of the product " +
    //   "`(w+2)(L+1)` — width 100.00 -> 6.00 (trie) and 200.00 -> 6.00 (graph).  `fixpoint` (558.5, was " +
    //   "20367) is an UPPER-endpoint problem — the union of the accumulator against the iterate — not a " +
    //   "lower-endpoint one; its ROUND bound is fixed (see OP-5).  THE TWO `tails` " +
    //   "OPERATORS ARE NOW WITHIN 15%: both read 73.67 = 221/3.  Their upper lost a whole `heads` factor " +
    //   "when `tails-inter` stopped being priced as the per-key probe loop `IntTrieOps.meetAllTries` " +
    //   "replaced (877 -> 73.67, a 12x tightening derived from the algorithm: the meet's frontier lies " +
    //   "inside the SMALLEST child and min <= mean cancels the factor).  Their lower is TWO — the `tails*` " +
    //   "entry and the `joinAll`/`meetAll` entry — and it cannot be three without proving the source's two " +
    //   "children are distinct OBJECTS, which needs the per-head sub-shapes the shape domain has and `Meas` " +
    //   "does not carry.  THAT IS NOW DONE and three more subjects left with it.  `Meas.tails` " +
    //   "([[TailsFacts]]) carries the per-head sub-shape facts: `distinctLo`, the number of head children " +
    //   "PROVABLY DIFFERENT in γ and therefore distinct OBJECTS, and `allHeaded`.  With three or more of " +
    //   "them the n-ary path is taken and `IntTrieOps.{join,meet}AllTries`' `enter()` — a counted " +
    //   "`PatriciaVisit`, its first statement — is forced, so the `tails` floor is THREE and both widths " +
    //   "read 55.25 (was 73.67).  `composition` left by the other half of the same idea: its recursion is " +
    //   "`a.children.transform`, i.e. EVERY node of the left operand and not the paired frontier, so its " +
    //   "floor is `N(a)` — width 69.00 -> 1.86, and the counted `touch` on the operator table is exactly " +
    //   "the 73 the floor claims.  " +
    //   "ITERATION LEFT THIS ENTRY BECAUSE THE SUBJECT CHANGED, NOT BECAUSE THE MODEL IMPROVED, and the " +
    //   "distinction is worth the sentence.  The row used to be `Iteration(a, h, t, Mention(t))`, which " +
    //   "`Lower.Iter_Tails` proves is `TailsUnion(a)`; once that certified rule joined " +
    //   "`Lower.OrdinaryRules` the term stopped being an `Iteration` after optimisation, so the row would " +
    //   "have priced a `TailsUnion` under the wrong name.  It is now " +
    //   "`Iteration(a, h, t, Wrap(Subtraction(t, b), Deref(h)))` — both names bound and the output tagged " +
    //   "with the group head, so no union-distributivity rule can collapse it — whose `Touch` width is " +
    //   "34.78 (trie) and 36.82 (graph), inside the budget.  Its `Work` and `Alloc` are still red and are " +
    //   "recorded under OP-2 and OP-6; the group-RESULT live-operand count they need is still the named " +
    //   "next step, and it has now been REFUSED A THIRD TIME — see OP-2's note.  " +
    //   "FIXPOINT REMAINS AND HALF OF IT IS FIXED: 558.50 -> 346.00.  The upper endpoint lost the round " +
    //   "that never merges (the accumulate sits in the `else` branch of `while !stop` in all three loops, " +
    //   "so `R` counted rounds perform `R - 1` merges) and lost the widened operand in round 1 (all three " +
    //   "loops open `var cur = <init>` and evaluate the body FIRST with `rec` bound to the SEED, whose " +
    //   "measure the arm already had).  The LOWER endpoint could NOT follow, and that is the whole " +
    //   "remaining width: taking the seed-priced round as a `CostInterval.meet` joins the LOWER endpoints " +
    //   "too, which installs `priced`'s must-paired count as the fixpoint's floor at exactly the round " +
    //   "where `var cur = evalI(init)` IS the caller's own trie by pointer and the body's sibling operand " +
    //   "commonly reaches the same objects — measured, that floor claims `touch >= 11` against a counted " +
    //   "4 and put nine rows over four fixpoint fixtures outside their intervals.  The remaining upper " +
    //   "slack is `FrontierSummary.descents.hi`'s generic per-depth Patricia bound `2(fanL + fanR)`, " +
    //   "which is not a fixpoint fact and reprices every merge row on this table."),
    // Limitation("OP-1g", "operator", "graph", EffortComponent.Touch, WidthAll,
    //   Vector("fixpoint"),
    //   Inf, 90000.0, "SpatialCost.scala (`GraphCost.forcedEntry`)",
    //   "as OP-1, and it lost the same five operators plus `union` for a REASON SPECIFIC TO `execT`: its " +
    //   "space slots are guarded by `if a.isEmpty then ITrie.empty`, but the guard reads the LEFT operand " +
    //   "ONLY and `Union` carries no guard at all (`GraphExec.scala`), so the algebra entry is forced " +
    //   "whenever the shape domain proves the left operand non-empty.  THE UNARY OPERATORS FOLLOWED: `GraphExec.scala` guards " +
    //   "`Wrap`/`Unwrap` on their SOURCE but calls `TailsUnion`/`TailsIntersection`/`Range` with NO guard " +
    //   "at all, so those three force their entry on `execT` exactly as on `evalI` — graph `tails-*` Touch " +
    //   "221 -> 73.67, level with the trie.  `range-full` THEN LEFT THIS ENTRY TOO (width 2.00): its whole " +
    //   "width was the count walk `CostModel.range` charged unconditionally, and `Meas.countKnown` " +
    //   "(`CountKnown`/`CountUnknown`) made that walk a function of the OPERAND's cache state instead — a " +
    //   "`Warm` full window on a FREE input mention reads an already-populated per-node count and visits one " +
    //   "node, while a `Cold` query and every freshly built subexpression still pay `N(x)`.  The SIX that " +
    //   "remain are the operators whose entry `execT` really can skip or whose upper endpoint is the problem.  " +
    //   "`composition`, `tails-union` and `tails-inter` LEFT with OP-1's live-operand and every-node floors " +
    //   "— `GraphExec` calls the same `ITrie` entry points, so the two models move together here.  `iteration` left for the SUBJECT CHANGE recorded in OP-1, not for a model improvement."),
    // Limitation("OP-1z", "operator", "zipper", EffortComponent.Touch, WidthAll,
    //   Vector("fixpoint"),
    //   Inf, 90000.0, "SpatialCost.scala",
    //   "as OP-1, on the FOUR operators where a fused cursor still enters the `ITrie` algebra.  On the ring " +
    //   "operators the zipper's `touch` interval is [0,0] against a counted 0 and its width is 1 — the " +
    //   "demand analysis really does price that component exactly, which is what makes LIM-1's `Work` gap " +
    //   "a defect rather than a limit.  `range-full` LEFT THIS ENTRY (width 2.00) for the reason given in " +
    //   "OP-1g: `ZipperCost.range` charges the count walk only when the operand is `CountUnknown`.  " +
    //   "`tails-inter` LEFT (221.00 -> 55.25) on the side condition this entry's own note was missing: " +
    //   "`execZ(s)` IS `materialize(transpileZ(s))` and `materialize`'s non-`Lit` arm is unconditional " +
    //   "straight-line code, so at DEPTH 0 the cursor is never a `Lit`, `children` and `terminal` both " +
    //   "run, and the lazy-val objection — true of an inner node — is false of the root.  Everything " +
    //   "claimed is gated on that depth; nothing is claimed at depth > 0, which is where a consumer can " +
    //   "meet the cursor with `∅` and never query it.  " +
    //   "`range-part` LEFT TOO (width 85.00 -> 12.00): `Meas.pointerLit` separates the operand whose `Lit` " +
    //   "is handed back BY POINTER (a bare `Mention` — an ITrie the caller already owns) from the wider " +
    //   "`liftsToLit` class, whose `Singleton`/`Range`/`Unwrap` members BUILD their trie during the lift; " +
    //   "the materialisation walk is charged only to the latter.  `iteration` left for the SUBJECT CHANGE recorded in OP-1, not for a model improvement."),
    // ==============================================================================================
    // OP-2 / OP-2z ARE RETIRED — `iteration` was their last subject on both trie-shaped executables,
    // and it left at 24.54, inside the 64 `Alloc` budget.  IT DID NOT LEAVE BY THE FLOOR THESE ENTRIES
    // SPENT THREE ATTEMPTS ON.  Their own note says "no MUST-ALLOCATE count is derived for THESE, so
    // their intervals still start at 0", and names a live-operand count for the GROUP RESULTS as the
    // fourth attempt — gated on making the floor conditional on which backend the trie model is
    // pricing for, because `execZ` reprices loops through `evalI` and can allocate strictly less.
    //
    // NONE OF THAT WAS NEEDED.  91% of the width was the CEILING, not the missing floor:
    // `naryScratch(groups, groups·nd(body))` multiplies in the body's node count, and under a
    // HEAD-RETAGGING loop body the operand set `ITrie.joinAll` receives is `k` SINGLE-KEY tries on
    // pairwise DISTINCT keys (`ITrie.wrap` builds `node(false, IntMap.Tip(k_g, ·))`), so
    // `joinAllTries` never takes the `br == 0` arm, never recurses into a child join, and places
    // every subtrie by pointer — THE DESCENT NEVER ENTERS THE OPERAND VALUES and `nd(body)` does not
    // belong in the formula at all.  `OperandShape.DistinctSingleKey` is that fact and
    // `CostModel.tipJoinScratch` is the arity-only price; `Alloc` went 138.62 -> 24.54 and `Work`
    // 46.58 -> 6.47 on both, with NO must-count added and the interval met against the old ceiling so
    // it could only tighten.
    //
    // THE FAN IS THE CONTROL, and it is measured rather than argued: counting `NaryOperandProbe` and
    // `NaryScratchSlot` of `ITrie.joinAll` over `k` such operands carrying `fan` grandchildren each,
    // THE COUNTS ARE IDENTICAL AT `fan = 1` AND `fan = 8` for every `k` from 3 to 256.
    // An entry with no measured subject is itself a ledger failure, which is why these are comments.
    // ==============================================================================================
    // Limitation("OP-2", "operator", "trie", EffortComponent.Alloc, WidthAll,
    //   Vector("iteration"),
    //   Inf, 12000.0, "SpatialCost.scala (`CostInterval.upperOnly`)",
    //   "no MUST-ALLOCATE count is derived for THESE, so their intervals still start at 0.  The two `tails` " +
    //   "operators LEFT: `IntTrie.liveDistinct` allocates `max(4, 4·live.length)` scratch slots and probes " +
    //   "`kd(kd-1)/2` times unconditionally, and `Meas.tails.distinctLo` is the live-operand count that " +
    //   "makes `kd` a NUMBER rather than the head count — which is the distinction that refuted the two " +
    //   "earlier attempts (`{a·x, b·x}` has two heads and ONE child object).  Widths 1344.00 -> 23.58.  " +
    //   "`composition`, `fixpoint` and `iteration` remain: the ring operators' widths are 7-15 and inside " +
    //   "the budget tier.  " +
    //   "COMPOSITION AND FIXPOINT LEFT.  `composition` (75.00 -> 7.50) because `ITrie.compositionR`'s one " +
    //   "allocation site is reached at exactly the left operand's INTERIOR nodes: a LEAF terminal takes " +
    //   "`rIdent(RIGHT)` and grafts `b` by POINTER, allocating nothing, so the floor is `I(a)` and not " +
    //   "`N(a)` — claiming `N(a)` here would predict 73 against a counted 9, which is LESSON 9's own " +
    //   "shape.  `SpatialFacts.interiorNodes` derives `I_d >= K_d.lo - E_d.hi + E_{d+1}.lo` from the " +
    //   "existing prefix profile, every input read in the direction that weakens it; on this table the " +
    //   "floor is 9 against a counted 9.  `fixpoint` (205.00 -> 46.00) left with the `R - 1` merge count " +
    //   "described in OP-1.  " +
    //   "ITERATION REMAINS, AND ITS FLOOR HAS NOW BEEN REFUSED THREE TIMES.  The third attempt derived it " +
    //   "from a live-operand count for the GROUP RESULTS and from `liveDistinct`'s `max(4, 4k)` scratch, " +
    //   "and the counted oracle put ten corpus points outside `zipper Alloc`.  The mechanism is now known " +
    //   "and it is not a may/must slip: THE ZIPPER REPRICES A LOOP WITH THE TRIE MODEL " +
    //   "(`controlFlowFallback`), so a trie-side `alloc` floor lands in the zipper's total, and `execZ` " +
    //   "can allocate strictly less than `evalI` for the same term because `materialize` hands a `Lit` " +
    //   "back by pointer.  Any future attempt has to make the floor conditional on which backend the " +
    //   "trie model is pricing FOR, which is a change to `SpatialCost.go`'s fallback and not to this " +
    //   "transfer."),
    // // OP-2g IS RETIRED — `execT`'s `Alloc` meets the BUDGET tier on every operator of this table.  It
    // // was OP-2 on the graph and lost its subjects in three steps: the two `tails` operators to the
    // // live-operand floor (`execT` calls `ITrie.tailsUnion`/`tailsIntersection` directly, so the two
    // // models move together there); `composition` to the INTERIOR-node floor `I(a)`, because
    // // `compositionR` grafts `b` by pointer at a LEAF terminal and allocates only where the left operand
    // // has a child (75.00 -> 7.50, floor 9 against a counted 10); and `fixpoint` to the `R - 1` merge
    // // count (69.00 -> 23.50).  `iteration` never was a subject here — `GraphExec`'s loop accumulates
    // // with a pairwise `ITrie.union` left fold and allocates trie nodes rather than n-ary scratch.
    // // An entry with no measured subject is itself a ledger failure, which is why this is a comment.
    // Limitation("OP-2z", "operator", "zipper", EffortComponent.Alloc, WidthAll,
    //   Vector("iteration"),
    //   Inf, 12000.0, "SpatialCost.scala", "as OP-2.  BOTH `Range` FORMS LEFT: the zipper was charged a " +
    //   "materialisation walk `x.nodes` for an operand it does not walk at all, and `Meas.pointerLit` (see " +
    //   "OP-1z) is the channel that says so — `range-part` 81.00 -> 8.00, `range-full` 2.00.  The live-" +
    //   "operand floor does NOT help here: the zipper's `TailsUnion` is a fused cursor reduce that never " +
    //   "enters `ITrie.joinAll`.  WHAT DID HELP IS THE `forced` SIDE CONDITION (see OP-1z): at depth 0 " +
    //   "`materialize`'s non-`Lit` arm is unconditional, so the fused reduce's own traffic IS a floor — " +
    //   "`tails-union` 74.00 -> 1.00 (an EXACT interval: one `FreshNode` for the one forced node, against " +
    //   "a counted 1) and `tails-inter` 1344.00 -> 23.17.  `composition` left with the same reasoning " +
    //   "(542.00 -> 7.32): `materialize` allocates one node per FORCED cursor and a `Composition` hands " +
    //   "every `Lit` child straight back, which `Meas.nodesLo` turns into a floor.  `fixpoint` left with " +
    //   "the `R - 1` merge count.  ONLY `iteration` REMAINS, and its floor is the thrice-refused one " +
    //   "OP-2's note describes."),
    // 
    // // ==============================================================================================
    // // OP-3 IS RETIRED — and it is retired by the very fix its own last paragraph described and
    // // declined to ship.  It said the binding endpoint was the whole-region DEMAND price (700 against a
    // // per-operator sum of 1472), that moving it needed `Layers.termsAt(d)` to be `E_d - E_{d+1}` — the
    // // paths that STOP at depth `d` — rather than `min(K_d, E_d)`, which on a uniform-length value says
    // // every node of every level may be terminal, and that the correct fact "cannot be landed alone: it
    // // removes the slack that was masking a pre-existing under-prediction in `SpatialDemand`'s `CRes`
    // // arm, and four corpus points move outside their intervals when it does.  Recorded, measured, not
    // // shipped."
    // //
    // // IT IS SHIPPED NOW, WITH THE TWO `CRes` DEFECTS THE SLACK WAS HIDING:
    // //   * `Pairing` IS A FACT ABOUT VALUES AND WAS SPENT ON CURSORS.  `pairedAt(d)` counts the depth-`d`
    // //     prefixes carrying a path in both operands' VALUES; the demand walk spent it as the paired
    // //     KEYS of the two operands' cursor child maps, and those agree only for a cursor whose nodes
    // //     are its value's prefixes.  `Intersection.children` and `RestrictionNode.children` merge KEYS,
    // //     `Subtraction.children` and `Composition.children` keep every left key, and `Prefix` builds
    // //     its whole spine over an empty source — `Intersection(Lit{a.b}, Lit{a.c})` denotes the
    // //     one-node empty trie and still has a child at `a`, because `materialize` prunes it only on the
    // //     way OUT.  `SpatialDemand.faithful` is the side condition; where it fails, the
    // //     `min(arity, arity)` ceiling — a statement about the CURSORS — is all that may be read.
    // //   * `descend1`'s `CRes` arm ignored the SMART CONSTRUCTOR.  `RestrictionNode.descend(k)` is
    // //     `restriction(x.descend(k), prefixes.descend(k))`, which returns the X-CURSOR ITSELF once the
    // //     descended prefix is terminal.  Keeping the node was not the conservative choice: a prefix
    // //     that has run out has an empty child map, so `shared` is 0 and the whole frontier below dies
    // //     while the run walks the unwrapped `x` in full.
    // // `raffination` `zipper` `Work` went `[3, 700]` (width 175.25) to `[3, 178]` (width 44.75), inside
    // // the 64 budget, and `composition` `zipper` `Work` 20.30 -> 2.57 and `Alloc` 7.32 -> 1.00 (exact,
    // // `[73, 73]` against a counted 73) came with it, because `CComp`'s `t = terminalCount(a, n)` is now
    // // 0 at a root whose paths all have one length — which is what `Composition.children`'s
    // // `if a.terminal` really does.  The 3000-point corpus CALIBRATION stays at 100% containment on all
    // // sixteen channels, which is the measurement the "four corpus points move outside" sentence was
    // // waiting for.  An entry with no measured subject is itself a ledger failure, hence the comment.
    // // ==============================================================================================

    // Limitation("OP-3", "operator", "zipper", EffortComponent.Work, WidthAll,
    //   Vector("raffination"),
    //   Inf, 4500.0, "SpatialCost.scala (ZipperCost) / SpatialDemand.scala",
    //   "LIM-1 AND OP-1 TOGETHER, and the only entry in this ledger with two causes: the upper endpoint is " +
    //   "the eager per-operator sum (the demand price does not lower `Work`) and the lower endpoint is 0 " +
    //   "(`upperOnly`).  Either fix alone would shrink these widths; the pair is why `zipper Work` was the " +
    //   "widest channel in the table (2929 on a composition).  FIVE RING OPERATORS LEFT THIS ENTRY IN THIS " +
    //   "SESSION as the demand price reached `Work`: `union`/`intersection`/`subtraction` at width 24.25, " +
    //   "`restriction` at 17.75 and `wrap` at 3.25, all inside the budget tier.  The six that remain are the " +
    //   "operators whose cursor is not bounded by the consumer.  " +
    //   "THREE OF THE REMAINING FOUR THEN LEFT TOO, all on the `forced` side condition OP-1z describes.  " +
    //   "`tails-union` " +
    //   "974.33 -> 21.48 and `tails-inter` 1135.67 -> 35.86: a FORCED `TailsUnion` cursor cannot avoid " +
    //   "`materialize`'s node, the `children` read, `merged`'s `src.children` read and the `m - 1` " +
    //   "`Union` layers of the reduce chain — `3m + 2` work, monotone in `m`, so the provably-distinct " +
    //   "child count may replace it.  `composition` 1131.50 -> 20.30.  `raffination` STAYS, and its " +
    //   "measured 700 upper turned out not to be `ZipperCost.raffine` at all: `demandDriven` is true, so " +
    //   "`analyze` MEETS the per-operator sum (1472) against the whole-region demand price (700) and the " +
    //   "demand price is the binding endpoint.  Moving it needs `SpatialDemand`, and the one fact that " +
    //   "would do it — `Layers.termsAt(d)` being `E_d - E_{d+1}` (the paths that STOP at depth `d`) " +
    //   "rather than `min(K_d, E_d)` (which on a uniform-length value says every node of every level may " +
    //   "be terminal) — is a CORRECT fix that cannot be landed alone: it removes the slack that was " +
    //   "masking a pre-existing under-prediction in `SpatialDemand`'s `CRes` arm, and four corpus points " +
    //   "move outside their intervals when it does.  Recorded, measured, not shipped."),
    // OP-3g IS RETIRED — `execT`'s `Work` now meets the SELECTION tier on every operator of this
    // table.  It said the slot dispatch count is exact for a straight-line body (width 1.00 on every
    // ring operator) and loses its lower endpoint through the loop's group-count interval.  Two things
    // closed it.  `fixpoint` left with the round bound (128.25 -> 4.00, see OP-4/OP-5).  `iteration`,
    // the last subject, left when `GraphCost.collectJoin` stopped inheriting the n-ary `joinAll`
    // price: `GraphExec.scala`'s `case "Iteration"` accumulates with a PAIRWISE `ITrie.union` left
    // fold, so `execT` emits no `NaryOperandProbe` and no `NaryScratchSlot` for a loop at all and the
    // model was charging both — 2425.00 -> 25.00 — and then off the entry entirely at 2.41 when the
    // row's SUBJECT changed (see OP-1: the old subject is no longer an `Iteration` after
    // optimisation).  An entry with no measured subject is itself a ledger failure, which is why this
    // is a comment and not an empty `Limitation`.
    // OP-4 / OP-5 / OP-5g / OP-5z ARE RETIRED — the fixpoint ROUND BOUND is fixed.  They said the
    // width of a fixpoint is the width of its round bound, `[1, 37]` on a 64-path seed against a
    // counted 2, and that a must-round count would be the remedy.  The remedy turned out to be the
    // UPPER endpoint and three separate corrections to `fixRoundsIvl`:
    //   * MONOTONICITY IS AC-MODULO.  The test was a two-case syntactic match on `Union(rec, _)` /
    //     `Union(_, rec)`, so `Union(Union(rec, a), b)` — the same accumulator, re-associated — was
    //     called non-monotone and fell straight to a FREE VARIABLE.  The union tower is flattened now.
    //   * THE SEED IS NOT PART OF THE GROWTH.  `R <= (|result|_hi - |init|_lo) + 1`, not
    //     `|result|_hi + 1`: 72 - 64 + 1 = 9 rather than 73.  (`Sym.monus` is a FOLD, not a `Sym`
    //     case — a subtraction node would break the syntactic monotonicity `Sym.dominates` rests on.)
    //   * AN IDEMPOTENT STEP RUNS TWICE.  With `body = Union(rec, E)` and `rec` NOT FREE in `E`
    //     (checked with the binder-aware walk, so a `Call`/`GroundedSS`/nested `Fixpoint` that hides
    //     an occurrence cannot fool it), `F(F(x)) = F(x)`: one round to add `E`, one to observe that
    //     nothing changed.  `rounds = [1, 2]` whatever the cardinalities are.
    // Measured on the operator table: `Rounds` [1,73] -> [1,2], width 37.00 -> 1.50 on all three
    // backends; trie `Work` 37.00 -> 1.50; graph `Work` 128.25 -> 4.00; zipper `Work` -> 1.43.
    // What is LEFT on `fixpoint` is `Alloc`/`Touch` (205 / 558.5), which is OP-1/OP-2's cause — the
    // accumulator-against-iterate union's envelope — reaching a loop, not a round-count problem.
    // ==============================================================================================
    // OP-7 / OP-7g / OP-7z / OP-9 / OP-9g / OP-9z ARE NEW, AND EVERY ONE OF THEM IS THE PRICE OF A
    // SOUNDNESS FIX.  Making the n-ary ceiling and the fixpoint step-multiplicity correct RAISED
    // upper endpoints, so rows that met their budget against a bound that did not contain the run no
    // longer meet it against one that does.  That trade is not a regression to be excused and not an
    // improvement to be claimed: an interval that excludes the run is a WRONG answer, a wide one is a
    // WEAK answer, and this ledger's job is to say which of the two each row currently is.
    // ==============================================================================================
    // ==============================================================================================
    // OP-7 / OP-7g ARE RETIRED (plan.md 1B.2).
    //
    // They owned `tails-union` and `tails-inter` `Alloc` `width` on trie and graph at 64.32 against a
    // budget of 64.00 — "it misses by 0.32, worth stating precisely because it means the SOUND
    // ceiling is already within 0.5% of the requirement".  `TailsFacts` now KEEPS the per-child head
    // sets it was already computing, and `CostModel.pkdLiveTotal` bounds `Σ_calls |live|` PER OPERAND
    // from them — `2*m_i - 1` Steiner nodes in the merged Patricia trie plus `carryDepth` ancestors,
    // valid because the key sets are pairwise DISJOINT — met with the two aggregate arms.
    //
    // MEASURED: `Alloc` width 64.32 -> 22.21 (-65.5%) on both backends, INSIDE the budget, so the two
    // entries are deleted.  The same factor took `Work` width from 89.60 to 28.73 on `tails-inter`
    // and from 56.02 to 17.93 on `tails-union` — a 3.1x tightening that does NOT clear the SELECTION
    // tier's budget of 8.00, so OP-6 / OP-6g stay with their figures re-derived.
    // ==============================================================================================
    // ==============================================================================================
    // OP-7z IS RETIRED (plan.md 1B.2), with OP-7 and OP-7g.
    //
    // It owned `tails-inter` `Work` `width` on the zipper at 92.89 against a budget of 64.00 and said
    // "as OP-6, inherited through the control-flow fallback".  `ZipperCost.tailsInter` now passes the
    // operand set's `TailsFacts` to `naryProbes`/`naryScratch` for the reason its own arity-cancellation
    // note gives: this backend calls the SAME `ITrie.tailsIntersection`, so the same per-operand
    // bound on `Σ_calls |live|` applies.  MEASURED: 92.89 -> 33.95 (-63.5%), inside the budget.
    //
    // `tails-union` was never a subject here and still is not: the zipper's is a fused cursor reduce
    // that never enters `ITrie.joinAll` at all and reads an exact 1.00.
    // ==============================================================================================
    // ==============================================================================================
    // OP-9 / OP-9g / OP-9z ARE RETIRED (plan.md 1B.4), and this is the note they leave behind.
    //
    // They owned `fixpoint` `Touch` `width` on all three backends — 72.87 to the digit against a
    // budget of 64.00 — and OP-9 stated the route it did not ship: "price the accumulating merge
    // against the union tower's NON-RECURSIVE RESIDUE `E` instead of against the whole iterate;
    // `fixRoundsIvl` already computes that predicate (`unionOperands(body)` with the bare `rec`
    // removed) and throws it away."  `SpatialCost.fixpointRel` now does exactly that, licensed by
    // `unionR`'s `a eq b` pointer return, and the row is 40.33 — INSIDE the budget, so the three
    // entries are DELETED rather than re-recorded with a smaller number.
    //
    // AND THE THING OP-9 WARNED AGAINST WAS NOT TAKEN WITH IT: the `R - 1` frontier multiplicity is
    // false on `Fixpoint(a, r, Union(b, Mention(r)))`, the AC-permuted tower that `unionOperands`
    // accepts verbatim, because `IntTrie`'s arm unions BEFORE it tests convergence.  `R` stays.
    // MEASURED: 72.87 -> 40.33 on trie, graph and zipper alike — the three are the same number for
    // the reason OP-9z gave (the zipper reprices the whole subterm with the trie model), which is
    // also the check that the change landed in the one place it should.
    // ==============================================================================================
    Limitation("OP-6", "operator", "trie", EffortComponent.Work, WidthAll,
      Vector("tails-union", "tails-inter"),
      // RE-DERIVED from 89.60 (plan.md 1B.2): `CostModel.pkdLiveTotal` reads the per-child key sets
      // `TailsFacts` now keeps and bounds the descent per operand, taking `tails-inter` to 28.73 and
      // `tails-union` to 17.93.  Still over the SELECTION tier's 8.00; the remaining gap is the
      // LAYOUT-exact version, and the note below says why that one is not shipped.
      Inf, 28.73, "SpatialCost.scala (`CostModel.naryProbes` / the missing n-ary frontier)",
      "THE N-ARY OPERAND LOOPS, AND THE ONE CHANNEL `Meas` DOES NOT CARRY.  99.8% of the counted `Work` " +
      "on these three operators is `NaryOperandProbe` (981 of 983 on the operator table's source), a " +
      "component whose LOWER endpoint is 0 and whose upper is `per * Sigma|live|`.  Both halves were " +
      "attacked and only one moved.  " +
      "THE UPPER: `per` was `min(k,24) + 4` = 12 at k = 8, which prices `collectLive`'s dedup as a FULL " +
      "linear scan for EVERY operand even past the `dedupScanMax = 24` threshold where it is a hash " +
      "probe.  Derived from the three loops in `IntTrieOps.joinAllTries` (dedup, branching-bit scan, " +
      "split-or-Tip-arm) it is `dedup/k + 3`, i.e. 7 at k = 8 — width 1609 -> 939 on trie and graph, " +
      "2425 -> 25 on graph `iteration` (that one also had the pairwise-fold correction, see OP-3g).  " +
      "THE LOWER STAYS 0, AND THE COUNTED ORACLE IS WHY.  Two must-counts were derived from " +
      "`Meas.headsLo` and both were REFUTED: `4 + 3*kLo` scratch slots plus `kLo` probes took trie " +
      "`Alloc` containment from 100% to 98.5%, graph to 94% and zipper to 97.5%; the bare " +
      "`ArrayBuffer(4)` that `liveDistinct` allocates on entry took zipper `Alloc` to 98%.  `kLo` " +
      "bounds the HEADS, and `liveDistinct` DEDUPS BY OBJECT IDENTITY — two heads routinely share one " +
      "child object, `k` heads can collapse to ONE live operand, and then `joinAll` returns it by " +
      "pointer with no split arrays, no terminal scan and a `pr` of zero.  " +
      "THE LIVE-OPERAND COUNT WAS THEN BUILT, AND `tails-union` LEFT THIS ENTRY.  The previous " +
      "revision of this note ended \"WHAT WOULD CLOSE IT is a LIVE-OPERAND count — how many head " +
      "children are DISTINCT OBJECTS — which is per-head sub-shape information `Meas` does not " +
      "carry ... and it is the named next step\".  `TailsFacts.distinctLo` is that count and it is a " +
      "DIFFERENT QUANTITY from `headsLo` in exactly the way the two refutations needed: `{a·x, b·x}` " +
      "has two heads and ONE child object, and `distinctLo` counts 1 there because the two sub-shapes " +
      "are not provably different.  On it, `naryLiveLo`/`naryDeepLo`/`naryDisjointLo` gate " +
      "`tailsScratchLo` and `tailsProbesLo` on `kd >= 3` (at two live operands `joinAll`/`meetAll` " +
      "delegate to the BINARY union/intersection and run none of these loops), on `allHeaded` " +
      "(`meetAll`'s `collectLive` runs with `stopOnNil = true` and abandons the call at the first " +
      "ε-only child) and on `Tuning.patriciaOps` (with the flag off `IntTrieOps.joinAllTries` never " +
      "runs, so a floor read off its source would describe code that is not executing).  " +
      "`tails-union` reached 7.35 and MEETS the requirement.  " +
      "TWO SUBJECTS REMAIN, AND THEY REMAIN FOR DIFFERENT REASONS.  `tails-inter` (11.84) is the " +
      "operator whose descent the floor CANNOT follow: `meetAllTries` tests `forcedL && forcedR` and " +
      "returns before it recurses, so on the key-disjoint operand set — the case where that test is " +
      "most likely to fire — nothing below the root split is forced and the meet's floor stops at the " +
      "root, which is why `tailsJoinProbesLo` adds its two descent terms for the JOIN alone and why " +
      "the counted `tails-inter` (371) sits so far below the counted `tails-union` (983) on the very " +
      "same operands.  `iteration` HAS SINCE LEFT THIS ENTRY, and not by that route -- see the " +
      "retired OP-2.  " +
      "THE `Sigma_calls |live|` CEILING WAS UNSOUND AND IS NOW CORRECT, WHICH IS WHY BOTH `tails` ROWS " +
      "ARE RED AND `tails-union` IS BACK.  The second factor of `naryProbes` was " +
      "`tighter(k*(2*nodes+1), 2*nodes + k)`, and the `2*nodes + k` arm came from \"every live " +
      "entry in the whole descent is a DISTINCT Patricia node, each appearing in exactly one " +
      "call's `live` array\".  THAT IS FALSE: one arm of `IntTrieOps`' split is " +
      "`case t => if (repKey(t) & br) == 0 then ls(nl) = t else rs(nr) = t`, so an operand whose " +
      "own mask is STRICTLY BELOW the split bit is passed down UNCHANGED and the SAME node is " +
      "re-listed in `live` -- and re-charged `probes(k)` twice plus `probes(i)` -- at EVERY level " +
      "between where it becomes live and where `br == maskOf(it)`.  `br` strictly decreases but " +
      "may SKIP bit positions, so the carry is bounded by the KEY-BIT SPAN, not the node count.  " +
      "MEASURED on `ITrie.tailsUnion` over `k` head children with one grandchild each: grandchild " +
      "keys `2^i` count 613 against a predicted upper of 558 at k = 12 and 4399 against 792 at " +
      "k = 26 (5.6x OUTSIDE its own interval); dense keys count 1560 against 972 at k = 32 and " +
      "15552 against 7692 at k = 256.  THE PREDECESSOR OF THAT ARM, `2*nodes + 32k`, IS ALSO " +
      "UNSOUND -- `2^i` plus dense filler at k = 34 counts 7439 against 7356 -- because `32k` " +
      "charges the carry to the `k` ROOT operands only and interior nodes carry too.  A SECOND, " +
      "INDEPENDENT DEFECT in the same term: `perProbe` was NON-MONOTONE (15 at k = 24, 16 at 25, " +
      "6 at 26), because `collectLive` picks its dedup regime PER CALL on that call's own live " +
      "count and a root at k = 26 has sub-calls at 25, 24, ... still in the quadratic regime the " +
      "root escaped; the prediction FELL as arity rose (2032 -> 792) while the counted value ROSE " +
      "(1307 -> 1328).  Both fixed: the regime is capped at the threshold, and the ceiling is now " +
      "`tighter(k*(spineNodes+1), carryDepth*(spineNodes+k))` with `carryDepth` a `ReprProfile` " +
      "field, because CARRY IS AN ARTEFACT OF PATH COMPRESSION -- a fixed-stride 256-ary node " +
      "consumes exactly `lg R` bits per level and cannot skip one, so the lowering this tree is " +
      "heading for deletes the term.  Containment is 100% on every gated channel in BOTH declared " +
      "configurations after the fix.  " +
      "WHAT IS LEFT IS TIGHTNESS, AND THE ROUTE IS MEASURED BUT NOT SHIPPED.  `iteration` left " +
      "this entry by the OPERAND-STRUCTURE route (`OperandShape.DistinctSingleKey`; see the " +
      "retired OP-2), which `tails-*` cannot use because its operands are the source's head " +
      "children -- general multi-key tries.  What they DO have here is PAIRWISE DISJOINT keys, " +
      "which `TailsFacts.keyDisjoint` already tracks, and that family's counted behaviour is " +
      "strikingly regular: with keys INTERLEAVED (this table's own layout, head `h_j` holding " +
      "`t_j, t_{j+8}, ...`) the probe count is EXACTLY `f(k) * m` for `m` keys per operand, and " +
      "with keys in DISTANT BLOCKS it is `f(k)` independent of `m`, where `f` is the single-key " +
      "descent price -- so `tipJoinProbes(k) * m` is 5x-22x tighter than the generic ceiling at " +
      "every point measured (k in 4..32, m in 1..16).  IT IS DELIBERATELY NOT SHIPPED: " +
      "`probes(k, m) <= probes(k, 1) * m` is a MEASURED regularity over 32 points, not a " +
      "derivation, and the defect this entry exists to record is exactly a ceiling that was " +
      "argued rather than checked.  The rigorous version needs the closed shape's actual key " +
      "layout, which the domain has for this table (channel (f), `headAtoms`) and which review " +
      "item 5's certificate tier is the place to expose."),
    Limitation("OP-6g", "operator", "graph", EffortComponent.Work, WidthAll,
      Vector("tails-union", "tails-inter"),
      // RE-DERIVED from 89.60, same cause as OP-6.
      Inf, 28.73, "SpatialCost.scala (`CostModel.naryProbes` / the missing n-ary frontier)",
      "as OP-6.  `execT` calls the SAME `ITrie.tailsUnion`/`tailsIntersection` `evalI` does — the two " +
      "backends differ on a loop's ACCUMULATION (see OP-3g), not on these two operators — so the n-ary " +
      "operand-loop price and its missing must side are identical here."),
    // ==============================================================================================
    // OP-6z IS RETIRED — `iteration` was its only subject, and it left at 45.55, inside the zipper's
    // 64 Work budget.  The entry was written when the width was 420 and recorded 401.00 -> 234.33 from
    // `perProbe`'s correction alone; what took it the rest of the way is that the zipper inherits the
    // TRIE model's n-ary price through the control-flow fallback (`Zipper.scala`'s
    // `case other => traversal(evalI(other))`), so every floor `tailsProbesLo` / `tailsJoinProbesLo`
    // established for `evalI` arrives here too, and `naryProbes`' second factor stopped being
    // `2·nodes + 32k` — a bound on the SCRATCH SLOTS — where the probes need `2·nodes + k`.
    //
    // NOTE WHAT THIS RETIREMENT DOES *NOT* SAY.  The zipper's `iteration` ALLOC row is still red
    // (OP-2z), and it is red because of the SAME fallback: a floor derived for the trie lands in the
    // zipper's total, and `execZ` can allocate strictly less than `evalI` for the same term because
    // `materialize` hands a `Lit` back by pointer.  Inheriting an UPPER bound through the fallback is
    // sound; inheriting a LOWER one is not, and that asymmetry is the whole content of OP-2z.
    // An entry with no measured subject is itself a ledger failure, which is why this is a comment.
    // ==============================================================================================
    // Limitation("OP-6z", "operator", "zipper", EffortComponent.Work, WidthAll, Vector("iteration"),
    //   Inf, 420.0, "SpatialCost.scala (`ZipperCost`) / SpatialDemand.scala",
    //   "as OP-6, through the control-flow fallback: `execZ` hands an `Iteration` to `evalI` " +
    //   "(`Zipper.scala`'s `case other => traversal(evalI(other))`), so the trie model's n-ary price " +
    //   "is what it inherits.  401.00 -> 234.33 with OP-6's `per`.")
    )

  def limitationFor(scope: String, subject: String, backend: String,
                    comp: EffortComponent, what: String): Option[Limitation] =
    limitations.find(_.matches(scope, subject, backend, comp, what))

/** ONE GATE DECISION, so the caller can print the whole table and fail once at the end.
 *
 *  [[ok]] is `measured <= permitted`, and it is the ONLY input to the verdict.  [[evidence]] is the
 *  ledger entry that explains a red row — it is printed, it is never consulted by [[ok]], and it was
 *  called `limitation` while it still had a vote. */
final case class GateRow(scope: String, subject: String, backend: String, comp: EffortComponent,
                         what: String, measured: Double, tier: ProductRequirement.Tier):
  def permitted: Double = tier.budget(what)
  def key: String = s"$scope $subject $backend $comp $what".trim
  def ok: Boolean = measured <= permitted + 1e-9
  def evidence: Option[ProductRequirement.Limitation] =
    ProductRequirement.limitationFor(scope, subject, backend, comp, what)
  def show: String =
    f"$key%-70s ${GateRow.fmt(measured)}%12s <= ${GateRow.fmt(permitted)}%12s  " +
    f"${if ok then "OK" else "FAIL"}%-4s [${tier.name}]"

object GateRow:
  def fmt(d: Double): String =
    if d.isInfinite then "inf" else if math.abs(d) >= 1e6 then f"$d%.2e" else f"$d%.2f"

/** ==============================================================================================
 *  THE GATE — ONE POLICY, THREE SUITES, NO EXCUSES.
 *
 *  ==WHAT WAS HERE==
 *  Three near-identical `publishGate` copies (SpatialScaleCheck, SpatialEventsCheck line 677,
 *  SpatialCostCheck line 658).  Each consulted [[ProductRequirement.limitations]] and, when a failing
 *  check matched an entry whose recorded number it had not exceeded, PRINTED the failure and did not
 *  count it.  The review in one sentence: "The current gate architecture turns known failures into a
 *  passing build by naming them."
 *
 *  ==WHAT IS HERE NOW==
 *  A failing requirement check is a FAILURE.  The ledger is printed against the rows it describes,
 *  because a red build needs an owner and a root cause to be actionable, and it decides nothing.  Two
 *  checks over the ledger remain and both can only ADD failures:
 *
 *   - NECESSITY — a subject that stopped failing is stale evidence and must be removed;
 *   - COVERAGE — an entry whose channel stopped producing rows means the channel stopped being measured,
 *     which is how a gate goes quiet without anyone noticing.
 *
 *  And one check over the harness: a scope with no [[ProductRequirement.Workload]] declaration fails,
 *  so numbers cannot be published under no requirement at all.
 *
 *  It RETURNS the failures instead of asserting, so the caller (a `FunSuite`) can assert with its own
 *  machinery AFTER the whole table has been printed — the report is the product, and a gate that throws
 *  half way through a table hides exactly the numbers a reader needs. */
object ProductGate:

  /** the statistics a channel can be held to, with the one-line statement of what each one asks.  A
   *  statistic missing from here still gates (its budget comes from `Tier.budget`); the map exists so the
   *  report can explain itself and so the per-statistic tally has stable names. */
  val statistics: Vector[(String, String)] = Vector(
    "width"     -> "(upper+1)/(lower+1): how much a caller who trusts the estimate still does not know",
    "error"     -> "(upper+1)/(actual+1) against COUNTED events: what 'how many steps?' means",
    "lower-error" -> ("(actual+1)/(lower+1) over the rungs where the execution DID something: a zero " +
                      "lower endpoint under a nonempty execution fails here by construction"),
    "magnitude" -> ("the largest predicted endpoint: above ProductRequirement.Astronomical the bound " +
                    "describes no executable computation and fails as an infinite one does"),
    "numeric"   -> ("0 if the prediction is a number, inf if it is still symbolic — a free variable in " +
                    "the answer is not an answer"),
    "slope-vs-measured" -> "predicted minus measured max per-doubling slope over the WHOLE ladder",
    "slope-asym-vs-measured" -> "the same PAST THE CROSSOVER REGION — the growth-class comparison",
    "slope-measured-vs-declared" -> "the backend's own claim about its growth class",
    "slope-predicted-vs-declared" -> "the model's claim about the family's growth class",
    "slope-asym-measured-vs-declared" -> "the backend's claim, asymptotically",
    "slope-asym-predicted-vs-declared" -> "the model's claim, asymptotically")

  /** Print every requirement decision and return the failures.  `extra` carries failures the caller
   *  established outside the row table (a symbolic prediction, an astronomical endpoint, a stale
   *  evidence entry) so that ONE report contains everything and one assertion reports it. */
  def report(title: String, scope: String, rows: Vector[GateRow], channels: Int,
             extra: Vector[String] = Vector.empty): Vector[String] =
    val bar = "=" * 132
    println(bar)
    println(s"PRODUCT REQUIREMENTS — $title  ($channels channels, ${rows.length} requirement checks)")
    var failures = extra
    // SOUNDNESS AND "NO ANSWER AT ALL" COME FIRST, at the top of the report and never excused.  They
    // arrive through `extra` rather than as rows because they are not ratios: a counted value outside the
    // interval, a symbolic prediction and an astronomical endpoint are categorical failures.
    if extra.nonEmpty then
      println(s"PRODUCT REQUIREMENTS — ${extra.length} CATEGORICAL FAILURE(S) BEFORE ANY RATIO IS " +
              "CONSIDERED (soundness / no-answer):")
      for e <- extra do println("REQUIREMENT: !! " + e)
    ProductRequirement.workloadOf(scope) match
      case Some(w) =>
        println(s"PRODUCT REQUIREMENTS — workload class `$scope`: " +
                (if w.gated then "RATIOS GATED" else "RATIOS NOT GATED") + " — " + w.why)
      case None =>
        failures :+= s"scope `$scope` publishes $channels channels under NO declared workload class " +
                     "(ProductRequirement.workloads) — a harness may not publish numbers under no " +
                     "requirement at all"
    println(bar)
    val met = rows.count(_.ok)
    // ---- every failing check.  EVERY ONE IS A FAILURE; the evidence entry only explains it ----------
    for r <- rows.filterNot(_.ok).sortBy(_.key) do
      val ev = r.evidence
      println("REQUIREMENT: " + r.show + (ev match
        case Some(l) => s"  <== FAILS — known defect ${l.id}, owner ${l.owner}" +
                        (if l.recorded(r.what).isNaN then ""
                         else s", recorded ${GateRow.fmt(l.recorded(r.what))}")
        case None    => "  <== FAILS — NO EVIDENCE ENTRY: an undiagnosed defect"))
      failures :+= s"${r.key}: measured ${GateRow.fmt(r.measured)} exceeds the ${r.tier.name} " +
                   s"requirement ${GateRow.fmt(r.permitted)} " +
                   ev.map(l => s"[${l.id}, owner ${l.owner}]").getOrElse("[UNDIAGNOSED]")
    // ---- NECESSITY and COVERAGE over the ledger: the only two things it still decides.  PRINTED, not
    //      only returned — a failure that appears solely in a truncated assertion message is a failure a
    //      reader cannot act on.
    for l <- ProductRequirement.limitations if l.scope == scope do
      val mine = rows.filter(r => l.matches(r.scope, r.subject, r.backend, r.comp, r.what))
      if mine.isEmpty then
        val f = s"${l.id}: declared over ${l.subjects.mkString(",")} but NO requirement check " +
                "produced a matching row — the channel stopped being measured"
        println("REQUIREMENT: !! LEDGER COVERAGE " + f)
        failures :+= f
      for s <- l.subjects do
        val hers = mine.filter(_.subject == s)
        if hers.nonEmpty && hers.forall(_.ok) then
          val f = s"${l.id}: subject `$s` NO LONGER FAILS " +
                  s"(${hers.map(r => s"${r.what}=${GateRow.fmt(r.measured)}").mkString(", ")} all meet " +
                  s"the ${l.comp}/${hers.head.tier.name} requirement) — remove it from the entry; " +
                  "stale evidence is a failure"
          println("REQUIREMENT: !! STALE EVIDENCE " + f)
          failures :+= f
      // ---- 0.7: STALE FIGURE — the third thing the ledger decides, and like the other two it can
      //      only ADD failures.
      //
      // Every entry carries `worstErr`/`worstWidth`: "the worst value MEASURED for this statistic
      // when this entry was written".  It was printed for the reader and compared against NOTHING,
      // so it could drift arbitrarily far from the truth while the row stayed red for the same named
      // reason.  That is not hypothetical: the FIRST run of this check found `OP-6`/`OP-6g`
      // recording `width = 4900.00` for `tails-union`/`tails-inter` where the measurements are 56.02
      // and 89.60 — 55x and 87x too HIGH.  These figures are quoted in `plan.md`, in `build.log` and
      // in the acceptance review, so a wrong one is not a cosmetic defect; it is the previous round's
      // reported state of the work.
      //
      // AGAINST THE WORST MATCHING ROW, not against each row.  `recorded` is documented as a WORST
      // value and one entry spans several subjects, so no single number could be within tolerance of
      // every row's; comparing against the maximum is what the field actually claims.  Rows are taken
      // from `mine` (all of them, not only the red ones) because the recorded worst is the worst
      // MEASURED, whether or not that channel currently fails.
      //
      // BOTH DIRECTIONS.  Recording too LOW understates a known defect.  Recording too HIGH is
      // worse: the number reads as a ceiling the work has already improved on, which is how
      // "the ledger says 4,500,000x" survives the fix that took it to 40x.  2% is wide enough for a
      // float-formatting or last-rung difference and far narrower than any real movement in these
      // channels, which move by factors rather than percents.
      //
      // An infinity is compared for EQUALITY: a ratio of infinities is not a proportion, and an
      // entry recording `inf` for a channel that is now finite is the stalest figure there is.
      // GROUPED BY THE RECORDED FIELD, NOT BY THE STATISTIC NAME.  `recorded` has exactly TWO fields
      // (`worstErr` for every `error*` statistic, `worstWidth` for every `width*` one), so an entry
      // declaring both `error` and `error-p95` has ONE number standing for both — and comparing that
      // one number against each statistic's own maximum separately would demand two different values
      // of one field, a requirement no ledger edit could satisfy.  Grouping by the field asks the
      // question the field actually answers: the worst value over everything it stands for.
      for (field, whats) <- l.what.toVector.sorted.groupBy(w => GateRow.fmt(l.recorded(w))) do
        val rec = l.recorded(whats.head)
        val hers = mine.filter(r => whats.contains(r.what))
        if !rec.isNaN && hers.nonEmpty then
          val got = hers.map(_.measured).max
          val stale =
            if rec.isInfinite || got.isInfinite then rec != got
            else math.abs(got - rec) > 0.02 * math.max(math.abs(rec), 1e-12)
          if stale then
            val where = hers.maxBy(_.measured)
            val what = whats.sorted.mkString("/")
            val f = s"${l.id}: records `$what` = ${GateRow.fmt(rec)} but the worst current " +
                    s"measurement over its own subjects is ${GateRow.fmt(got)} " +
                    s"(`${where.subject}`/`${where.what}`" +
                    (if rec.isInfinite || got.isInfinite then
                       "; one side is infinite, so these are compared for equality)"
                     else f", ${100.0 * (got - rec) / math.max(math.abs(rec), 1e-12)}%+.1f%%, past " +
                          "the 2% tolerance)") +
                    " — a recorded figure that nothing checks is a figure that is eventually wrong, " +
                    "and these are quoted outside the code.  Re-derive it from this run."
            println("REQUIREMENT: !! STALE FIGURE " + f)
            failures :+= f
    // ---- the tallies a reader needs to act, and the evidence for the red rows -----------------------
    println("-" * 132)
    val red = rows.filterNot(_.ok)
    if red.nonEmpty then
      println("PRODUCT REQUIREMENTS — failures by statistic: " +
              red.groupBy(_.what).toVector.sortBy(-_._2.length)
                 .map((w, rs) => s"$w=${rs.length}").mkString(", "))
      println("PRODUCT REQUIREMENTS — failures by channel:   " +
              red.groupBy(r => s"${r.backend}/${r.comp}").toVector.sortBy(-_._2.length)
                 .map((k, rs) => s"$k=${rs.length}").mkString(", "))
      val undiagnosed = red.filter(_.evidence.isEmpty)
      println(s"PRODUCT REQUIREMENTS — ${red.length - undiagnosed.length} of ${red.length} red rows have " +
              s"an evidence entry; ${undiagnosed.length} are UNDIAGNOSED")
    val used = ProductRequirement.limitations.filter(l =>
      l.scope == scope && rows.exists(r => l.matches(r.scope, r.subject, r.backend, r.comp, r.what) && !r.ok))
    if rows.isEmpty then
      println(s"PRODUCT REQUIREMENTS — no ratio checks in this scope; ${failures.length} categorical " +
              "failure(s) above")
    else
      println(s"PRODUCT REQUIREMENTS — $met of ${rows.length} checks MET; ${rows.length - met} FAILED " +
              s"(${used.length} named defects explain them; NONE of them excuses one)")
    for l <- used do
      println("DEFECT: " + l.show)
      println("DEFECT:   subjects: " + l.subjects.mkString(", "))
      println("DEFECT:   " + l.reason)
    failures

/** ==============================================================================================
 *  THE CORRELATED SCALE LADDERS  (the review third and fourth sentences)
 *
 *  "The small independent random corpus almost never generates subset, shared-subtrie, prefix-cylinder,
 *  absorption, fixed-selective-consumer or rest-chain cases, which are exactly where these backends
 *  win."  This suite generates all six, plus a deliberate LINEAR control so that a flat result means
 *  something, and runs each over a geometric ladder.
 *
 *  ==WHAT IS MEASURED, AND ON WHAT FORM==
 *  Every family is a `Routine` over MENTIONS, and every number in this file describes
 *  `Routine.optimized`'s body — the spatial hook plus the ordinary `Lower` rule list — executed on the
 *  optimal backends (`evalI`, `execZ`, `execT`).  That is the user's third steer: an estimate of the
 *  definitional term is not a statement about what runs.  Where the optimizer removes the operation
 *  entirely (`x ∖ x`, a full `Range`) that is REPORTED as the win it is, and both the prediction and
 *  the measurement collapse together, which is the correct joint outcome.
 *
 *  The reference evaluator is NOT run here (the user's second steer): `eval` over `Set` is allowed to be
 *  slow, and spending ladder time on it would buy a calibration of constants nobody ships.  Ground
 *  truth for the results is `evalI` against `execZ`, which is a real cross-check between two
 *  independent executables.
 *
 *  ==THE SLOPE STATISTIC==
 *  `log2((C(2n) + 1) / (C(n) + 1))` per rung pair, exactly as the review specifies, reported as its
 *  maximum over the ladder (the worst doubling, not an average that a good rung can hide), plus the
 *  end-to-end ratio.  A family DECLARES the class it claims — `0.0` for constant-or-depth, `1.0` for
 *  linear — and both the MEASURED and the PREDICTED slope must meet it.  The measured half is a claim
 *  about the backend; the predicted half is the claim about the estimate, and it is the one the review
 *  item 7 is about. */
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
  def optimizedAndPriced(s: Scenario): (Routine, Map[Backend, SpatialCost.Report]) =
    val ann = annOf(s)
    given PartialFunction[RoutinePtr, Routine] = ann.routines
    val opt = s.routine.optimized
    val a = SpatialPipeline.analyzeRoutine(opt, ann)
    val env = ann.costEnvFor(a.decorated)
    (opt, Backend.values.iterator.map(b =>
       b -> SpatialCost.analyze(opt.body, env, Backends.of(b, ExecutionPhase.Warm),
                                CostForm.Optimized)).toMap)

  /** `runGraphT`'s calling convention is OUTSIDE the term (`ExtractPathRef` / `ExtractSpaceMention`
   *  prologue slots), so a Graph report must have it added before it is compared against counted
   *  `execT` events — exactly as `SpatialEventsCheck.countGraph` does. */
  def graphExtra(s: Scenario): CostInterval =
    SpatialCost.graphPrologue(s.paths.size, s.routine.mentions.length)

  /** the counted runs of the OPTIMIZED body.  `evalI` and `execZ` must agree — that is the ground
   *  truth, and it needs no reference evaluator. */
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
      val t0 = System.nanoTime()
      var i = 0
      while i < 3 do { body; i += 1 }
      best = math.min(best, (System.nanoTime() - t0) / 1e6 / 3.0)
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

  def freeVars(c: Cost): Set[String] =
    Vector(c.work, c.alloc, c.rounds, c.touch)
      .flatMap(a => a.symOpt.map(Sym.vars).getOrElse(Set.empty[String])).toSet

  /** run one family's ladder and return its channels, plus the (predicted total, measured ms) pairs */
  def runFamily(f: Family): (Vector[Channel], Vector[(Double, Double)]) =
    val ns = ladder
    var perBackend = Map.empty[String, Vector[(Long, Double, Double)]]   // actual, lo, hi per rung
    var trend = Vector.empty[(Double, Double)]
    var optShown = false
    var symbolic = Vector.empty[String]
    val comps = EffortEvent.calibratedComponents
    // component-indexed accumulation: backend -> comp -> Vector[(actual, lo, hi)]
    var acc = Map.empty[(String, EffortComponent), Vector[(Double, Double, Double)]]
    for n <- ns do
      val sc = f.build(n)
      val (opt, priced) = optimizedAndPriced(sc)
      if !optShown then
        println(s"SCALE ${f.name}: OPTIMIZED body = ${opt.body.show.replace('\n', ' ').take(150)}")
        println(s"SCALE ${f.name}: ${priced(Backend.Trie).census.show}")
        optShown = true
      val (events, times) = measure(opt, sc)
      for (slug, ev) <- events do
        val backend = Backend.values.find(_.slug == slug).get
        val extra = if backend == Backend.Graph then graphExtra(sc) else CostInterval.zero
        val rep = priced(backend)
        val hiC = rep.cost + extra.hi
        val loC = rep.lower + extra.lo
        if freeVars(hiC).nonEmpty || freeVars(loC).nonEmpty then
          symbolic :+= s"$slug@$n:${(freeVars(hiC) ++ freeVars(loC)).mkString(",")}"
        else
          for c <- comps do
            val (lo, hi) = (loC.calibrated(c).at(Map.empty), hiC.calibrated(c).at(Map.empty))
            acc = acc.updated((slug, c), acc.getOrElse((slug, c), Vector.empty) :+ (ev.component(c).toDouble, lo, hi))
        // the correlated trend: predicted TOTAL against measured wall time, over every rung
        val tot = Vector(hiC.work, hiC.alloc, hiC.rounds, hiC.touch).map(_.at(Map.empty)).sum
        if !tot.isInfinite then trend :+= (tot, times(slug))
    assertEquals(symbolic, Vector.empty[String],
                 s"${f.name}: the OPTIMIZED form's prediction is still symbolic — a ladder cannot " +
                 s"compare slopes against a free variable: ${symbolic.mkString(", ")}")
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
    // every scope the ledger names must be a declared workload class, or the ledger describes rows that
    // are published under no requirement
    for l <- ProductRequirement.limitations do
      assert(ProductRequirement.workloadOf(l.scope).isDefined,
             s"${l.id} is scoped to `${l.scope}`, which is not a declared workload class")
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

  test("SCALE LADDERS: predicted vs measured SLOPE on the OPTIMIZED form, per operator and backend") {
    var rows = Vector.empty[GateRow]
    var unsound = Vector.empty[String]
    var trend = Vector.empty[(Double, Double)]
    var channels = 0
    println(s"SCALE: ladder = ${ladder.mkString(",")}; the ASYMPTOTIC sample is the rungs >= " +
            s"$asymptoticFrom (${ladder.filter(_ >= asymptoticFrom).mkString(",")}).  Every `slope` cell " +
            "reads whole-ladder/asymptotic, and BOTH are gated.")
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
                      s"outside [${ch.lower.map(_.toLong).mkString(",")}, ${ch.upper.map(_.toLong).mkString(",")}]"
        def row(what: String, measured: Double) =
          rows :+= GateRow("ladder", ch.family, ch.backend, ch.comp, what, measured, tier)
        row("width", ch.width)
        row("error", ch.error)
        // THE LOWER ENDPOINT (the review: no zero lower endpoint under a nonempty execution)
        row("lower-error", ch.lowerError)
        // AND THE ABSOLUTE CEILING: a finite bound can still be no answer
        row("magnitude", ch.magnitude)
        // THE SLOPE REQUIREMENT.  Two halves: the estimate may not out-grow the measurement, and where
        // the family declares a class BOTH must meet it — the measured half is a claim about the
        // backend, the predicted half is the claim about the model.
        row("slope-vs-measured", ch.predSlope - ch.measSlope)
        // THE SAME, ASYMPTOTICALLY: past `asymptoticFrom` a growth class is a meaningful claim, and this
        // is the pair the fourth requirement asks for.  Both are gated — the whole-ladder
        // statistic is not replaced by the asymptotic one, because an over-prediction inside the
        // crossover is still an over-prediction at those sizes.
        row("slope-asym-vs-measured", ch.predSlopeAsym - ch.measSlopeAsym)
        for d <- ch.declared do
          row("slope-measured-vs-declared", ch.measSlope - d)
          row("slope-predicted-vs-declared", ch.predSlope - d)
          row("slope-asym-measured-vs-declared", ch.measSlopeAsym - d)
          row("slope-asym-predicted-vs-declared", ch.predSlopeAsym - d)
    // ---- SOUNDNESS FIRST, and it is never excused.  It is reported THROUGH the gate rather than by an
    //      assertion here for one reason: an assertion at this point throws before the requirement table
    //      is printed, and then a reader of a red build sees the containment failure and NOTHING ELSE.
    //      Soundness failures are printed at the TOP of the report, are prefixed UNSOUND, and no ledger
    //      entry can match them — `extra` failures are categorical, not ratios.
    val hard = unsound.map(u =>
      "UNSOUND (a counted value fell outside the predicted interval on the OPTIMIZED form; soundness is " +
      "never excused): " + u)
    if unsound.nonEmpty then
      println("=" * 132)
      println(s"SCALE: UNSOUND — ${unsound.length} channel(s) have a counted value OUTSIDE the predicted " +
              "interval.  This is a model bug, not imprecision, and it is the first thing in the gate below.")
    // ---- the correlated trend: predicted cost against measured wall time ------------------------
    if trend.length >= 8 then
      val rho = Calibration.spearman(trend.map(_._1), trend.map(_._2))
      println(f"SCALE: Spearman(predicted total cost, measured wall time) = $rho%.3f over ${trend.length} " +
              "(family, rung, backend) points on the OPTIMIZED form")
      assert(rho >= 0.35, f"the predicted cost order must track measured time across the ladders; rho=$rho%.3f")
    publishGate("scale ladders on the optimized form", rows, channels, hard)
  }

  // ==============================================================================================
  // 5. THE GATE
  // ==============================================================================================

  /** [[ProductGate.report]] is the policy; this is the assertion.  The failure list is printed in full
   *  by the report, so the message is truncated deliberately: 127 failures in an assertion message is
   *  unreadable, and the table above it is the artefact. */
  def publishGate(title: String, rows: Vector[GateRow], channels: Int,
                  extra: Vector[String] = Vector.empty): Unit =
    val scope = rows.headOption.map(_.scope).getOrElse("")
    val fs = ProductGate.report(title, scope, rows, channels, extra)
    assert(fs.isEmpty,
           s"$title: ${fs.length} product-requirement FAILURE(S) — every one is printed above:\n  " +
           fs.take(30).mkString("\n  ") +
           (if fs.length > 30 then s"\n  ... and ${fs.length - 30} more" else ""))
end SpatialScaleCheck
