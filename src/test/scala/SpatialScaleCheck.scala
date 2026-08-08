package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==============================================================================================
 *  THE PRODUCT REQUIREMENTS FOR A COST ESTIMATE  (review.md item 7)
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
 *  It FAILS, with the measured number printed — unless it appears in [[exclusions]], which requires a
 *  named reason and the measured value.  Every exclusion is checked for NECESSITY: if the channel now
 *  meets its tier, the exclusion FAILS too.  That is what stops the ledger from rotting into an
 *  allow-list, which is what the previous gate was. */
object ProductRequirement:

  /** one requirement tier: the three budgets plus the decision they exist to support */
  final case class Tier(name: String, width: Double, error: Double, slopeExcess: Double, why: String):
    def show: String = f"$name%-12s width<=$width%8.1f error<=$error%8.1f slope<=+$slopeExcess%.2f"
    /** the budget for one named statistic.  `error`/`error-p95` share the error budget and
     *  `width`/`width-p95` the width budget: a p95 is the SAME requirement measured over a sample where
     *  a single outlier program is not the claim, not a second, softer requirement. */
    def budget(what: String): Double =
      if what.startsWith("width") then width
      else if what.startsWith("error") then error
      else slopeExcess

  val Selection: Tier = Tier("selection", 8.0, 4.0, 0.35,
    "this channel decides which executable to run; the inter-backend gap on real programs is 1.3x-7x, " +
    "so an estimate with more error than that cannot resolve the choice it is used for")
  val Budget: Tier = Tier("budget", 64.0, 10.0, 0.35,
    "this channel answers 'does this fit in my time/memory budget'; one order of magnitude is the " +
    "outer edge of usable for capacity planning")
  val GrowthClass: Tier = Tier("growth-class", 1024.0, 100.0, 0.35,
    "this channel is a CLASSIFIER, not a predictor: its absolute value is not usable and this tier " +
    "says so out loud, but its SLOPE is held to the full budget")

  /** THE REFERENCE EVALUATOR IS NOT GATED (the user's second steer).  `eval` over `Set[PathValue]` is
   *  allowed to be slow, its constants are not a product, and its `touch` has no oracle at all
   *  (`CostModel.touchNoOracle`).  Its rows are PRINTED wherever they are measured — an ungated row is
   *  still published — but no threshold is asserted on them, because calibrating the reference
   *  evaluator's constants is the wrong place to spend the budget. */
  val NotGated: Tier = Tier("not-gated", Double.PositiveInfinity, Double.PositiveInfinity,
    Double.PositiveInfinity,
    "the reference evaluator is not a product: `eval` over Set[PathValue] is allowed to be slow, its " +
    "constants are not gated, and its `touch` component has no counted oracle (the Set internals carry " +
    "no hooks). The rows are published, not asserted")

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
   *  THIS IS NOT A THRESHOLD.  Every entry is a recorded FAILURE.  Three properties keep it from
   *  decaying into the allow-list it replaces:
   *
   *   1. NECESSITY.  Every `subject` listed must still produce a failing row.  When the owner fixes the
   *      model, the entry stops being necessary and the suite FAILS until the subject is removed.
   *      "A channel that becomes bounded must also fail so the ledger cannot rot."
   *   2. NO REGRESSION.  `permitted` is the recorded worst plus 50% headroom for measurement noise.  A
   *      number above it is a regression and fails even though the channel is excluded.
   *   3. NAMED OWNER.  Every entry says which file must change.  An entry with no owner would be an
   *      admission that nobody intends to fix it. */
  final case class Limitation(id: String, scope: String, backend: String, comp: EffortComponent,
                              what: Set[String], subjects: Vector[String],
                              errCap: Double, widthCap: Double, owner: String, reason: String):
    def matches(scope: String, subject: String, backend: String, comp: EffortComponent, what: String): Boolean =
      this.scope == scope && this.backend == backend && this.comp == comp &&
      this.what.contains(what) && subjects.contains(subject)
    /** THE NO-REGRESSION CAP for one statistic: the recorded worst plus ~50% for measurement noise.
     *  The slope cap is FIXED at 1.35 — one whole growth class plus the tier's 0.35 tolerance — because
     *  a channel that over-grows by more than a full doubling per doubling is a different bug from the
     *  one recorded here and must not be absorbed by an existing entry. */
    def cap(what: String): Double =
      if what.startsWith("error") then errCap
      else if what.startsWith("width") then widthCap
      else 1.35
    def show: String =
      f"$id%-8s $scope%-11s $backend%-8s $comp%-6s ${what.toVector.sorted.mkString("/")}%-58s " +
      f"errCap ${fmt(errCap)}%10s widthCap ${fmt(widthCap)}%10s  owner: $owner"
    private def fmt(d: Double): String =
      if d.isInfinite then "inf" else if d >= 1e6 then f"$d%.2e" else f"$d%.2f"

  private val ErrAndSlope = Set("error", "width", "slope-vs-measured", "slope-predicted-vs-declared")
  private val WidthOnly = Set("width")
  /** the whole-program scopes report a p95 alongside the worst; both names carry the same requirement */
  private val ErrAll = Set("error", "error-p95")
  private val WidthAll = Set("width", "width-p95")
  private val ErrWidth = ErrAll ++ WidthAll
  private val Inf = Double.PositiveInfinity

  /** THE LEDGER — twenty entries, seven distinct root causes, every one with the file that owns the fix.
   *
   *  Read the `id` prefixes as the root causes; the `g`/`z`/`a`/`w` suffixes are the same cause reaching
   *  another (backend, component) through shared code.
   *
   *   LIM-1/2  the zipper's demand analysis lowers `Touch` and not `Work`/`Alloc`  (review.md item 3)
   *   LIM-3    the `Range` transfer is stale after `ITrie.range` became O(1)       (review.md item 4)
   *   LIM-4    the frontier's whole-subtree accepts do not reach `touch`           (review.md item 2)
   *   LIM-5    `alloc` is met against the result envelope, not the rebuilt count   (review.md item 2)
   *   LIM-6    NO LOWER ENDPOINT is derived, so every width is `upper + 1`         (review.md item 5)
   *   LIM-7    the rest-chain frame law is exact but emitted `upperOnly`           (review.md item 5)
   *   LIM-8    the Patricia-visit constant is 3 per merged entry, measured ~0.6    (constant factor) */
  val limitations: Vector[Limitation] = Vector(

    // ============================ LIM-1/2: the demand analysis, one component short ================
    Limitation("LIM-1", "ladder", "zipper", EffortComponent.Work, ErrAndSlope,
      Vector("restrict/prefix-cylinder", "restrict/epsilon", "union/disjoint", "union/subset",
             "inter/shared-subtrie", "inter/disjoint", "absorption", "compose/epsilon", "range/full",
             "select/fixed-consumer", "union/disjoint-keys"),
      3100.0, 9000.0, "SpatialCost.scala (ZipperCost) / SpatialDemand.scala",
      "THE DEMAND ANALYSIS LOWERS `Touch` AND NOT `Work`.  `execZ`'s counted cursor reads are CONSTANT on " +
      "every one of these terms (9-105, flat across four doublings) and the predicted `Touch` is correctly " +
      "0 at every rung — so the demand region IS recognised and the fused cursor algebra IS priced.  " +
      "`Work` is still the per-operator sum: `ZipperCost` charges `ZipperBuild` + `ZipperCursorRead` in " +
      "proportion to each operand's `Meas.nodes`, and `demandPrice + demandExtra + handedOff` does not come " +
      "out below that, so the meet keeps the eager number.  Worst measured error 2053x (range/full), and " +
      "the predicted slope is 0.96-1.00 against a measured 0.00 — a GROWTH-CLASS error, not a constant.  " +
      "This is review.md item 3 verbatim, still open for one component."),

    Limitation("LIM-2", "ladder", "zipper", EffortComponent.Alloc, ErrAndSlope,
      Vector("range/full", "select/fixed-consumer", "union/disjoint-keys"),
      1600.0, 1600.0, "SpatialCost.scala (ZipperCost) / SpatialDemand.scala",
      "the same gap in `Alloc`.  `(A ∪ B) ∩ C` with a FIXED C is the review's own example: `execZ` " +
      "materialises 10 fresh nodes at every rung of a 64 -> 1024 ladder, and the prediction is the " +
      "result-node envelope of the EAGER union, 85 -> 1045 (error 95x, predicted slope 0.97 against a " +
      "measured 0.00).  A full `Range` is worse: 0 fresh nodes measured against 66 -> 1026 predicted."),

    // ============================ LIM-3: a model left behind by its backend =======================
    Limitation("LIM-3", "ladder", "trie", EffortComponent.Touch, ErrAndSlope, Vector("range/full"),
      800.0, 1600.0, "SpatialCost.scala (`CostModel.range`)",
      "THE MODEL IS STALE AFTER A BACKEND IMPROVEMENT — the most important kind of failure this gate can " +
      "catch.  `ITrie.range` now caches subtree terminal counts, so a full window returns its input after " +
      "ONE node visit (measured: 1, flat over four doublings; `OptimalTrieCheck`'s 'a full Range is O(1)' " +
      "gate asserts the same thing).  `CostModel.range(x, window, identity = true)` still charges the " +
      "pre-order size walk the OLD implementation performed: 67 -> 1027, error 514x, predicted slope 0.99 " +
      "against a measured 0.00."),
    Limitation("LIM-3g", "ladder", "graph", EffortComponent.Touch, ErrAndSlope, Vector("range/full"),
      800.0, 1600.0, "SpatialCost.scala (`CostModel.range`)", "as LIM-3, through `GraphCost.range`."),
    Limitation("LIM-3z", "ladder", "zipper", EffortComponent.Touch, ErrAndSlope, Vector("range/full"),
      800.0, 1600.0, "SpatialCost.scala (`CostModel.range`)", "as LIM-3, through `ZipperCost.range`."),

    // ============================ LIM-4: the frontier is derived but not consumed =================
    Limitation("LIM-4", "ladder", "trie", EffortComponent.Touch, ErrAndSlope,
      Vector("restrict/prefix-cylinder", "union/subset", "absorption"),
      180.0, 8000.0, "SpatialCost.scala (`TrieAlgebraCost`) / SpatialFrontier.scala",
      "A CONSTANT FACTOR, NOT A GROWTH CLASS — CORRECTED BY MEASUREMENT.  The slope statistic below " +
      "reads 0.87-0.93 against a measured 0.00 and an earlier revision of this entry called that a " +
      "growth-class failure.  IT IS NOT.  `SpatialFrontier`'s Patricia term is " +
      "`min(2(fanL+fanR), 2*PatriciaBits*(gateFan+|A|))` with `PatriciaBits = 33`, so the " +
      "OPERAND-INDEPENDENT branch cannot win until the growing fan passes ~33x the gating fan — and the " +
      "five-rung ladder (64..1024) sits entirely inside that crossover.  Run out to n = 65536 and the " +
      "predicted `touch` is FLAT: restrict/prefix-cylinder 311, 567, 1079, 1591, then 1591 at every one " +
      "of the next SIX doublings (per-doubling slopes 0.86, 0.93, 0.56, then 0.00 x 6); union/subset " +
      "216, 408, 792, 1458, then 1458 x 6; inter/shared-subtrie 86 at every rung from 64 to 65536.  " +
      "So the whole-subtree accept DOES reach `touch` and the asymptotics are right; what remains is a " +
      "constant of 122x (1591 against a measured 13), 56x and 3.3x, driven by the `2*PatriciaBits` " +
      "factor and by `touch := descents + patricia` not subtracting `FrontierSummary.reuse`.  This entry " +
      "stays because a 122x constant still fails the budget tier, and because the SLOPE statistic on a " +
      "five-rung ladder cannot see the difference — the honest fix is to lengthen the ladder AND lower " +
      "the constant, not to relabel the failure."),
    Limitation("LIM-4g", "ladder", "graph", EffortComponent.Touch, ErrAndSlope,
      Vector("restrict/prefix-cylinder", "union/subset", "absorption"),
      180.0, 8000.0, "SpatialCost.scala (`TrieAlgebraCost`) / SpatialFrontier.scala",
      "as LIM-4; `GraphCost` shares `TrieAlgebraCost`'s ring transfers."),

    // ============================ LIM-5: rebuilt-vs-envelope allocation ===========================
    Limitation("LIM-5", "ladder", "trie", EffortComponent.Alloc, ErrAndSlope,
      Vector("absorption", "union/disjoint-keys"),
      520.0, 1600.0, "SpatialCost.scala (`TrieAlgebraCost.priced`)",
      "`alloc := rebuilt` is MET against the result's node envelope, and for a union whose branches are " +
      "attached whole the rebuilt count is O(1) while the envelope is O(n): 2 fresh `ITrie` nodes measured " +
      "at every rung of a 64 -> 1024 ladder of key-disjoint operands under a shared prefix, against " +
      "66 -> 1026 predicted (error 342x).  The `IntMap` spine allocation this misses is the SECOND declared " +
      "oracle gap in SpatialEvents.scala and is bounded by 2x the counted total, so it does not explain " +
      "a 342x.  Note the CONTRAST that makes this a real defect and not a modelling limit: on " +
      "`union/paired-keys`, where every key is genuinely paired, the same transfer is accurate to 1.01x.  " +
      "UNLIKE LIM-4 THIS ONE REALLY IS A GROWTH CLASS: measured out to n = 65536 the predicted `alloc` is " +
      "66, 130, 258, ..., 65538 — per-doubling slope 1.00 at every rung against a measured 2, flat.  The " +
      "cause is located: sweeping the keys-per-side from 1 upward, the frontier reports source `Exact` " +
      "and a FLAT predicted alloc of 3 for 1..12 keys, and switches to `Relational` with 16, 18, 26, 66 " +
      "at 14, 16, 24, 64 — the crossover is `SpatialConfig.default.shapeWidth = 12`, above which the head " +
      "set spills into `Shape.others` and key-disjointness stops being provable, so `paired(d)` falls " +
      "back to `min(K_d, K_d) = n`.  The fix is a per-depth disjointness FACT (or a key-set summary) " +
      "instead of an enumerated head set; raising `shapeWidth` only moves the crossover."),
    Limitation("LIM-5g", "ladder", "graph", EffortComponent.Alloc, ErrAndSlope,
      Vector("absorption", "union/disjoint-keys"),
      400.0, 800.0, "SpatialCost.scala (`TrieAlgebraCost.priced`)", "as LIM-5, at execT's magnitudes."),

    // ============================ LIM-6: there is no lower endpoint ===============================
    Limitation("LIM-6", "ladder", "trie", EffortComponent.Touch, WidthOnly,
      Vector("select/fixed-consumer", "union/paired-keys", "union/disjoint-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 25000.0,
      "SpatialCost.scala (`CostInterval.upperOnly`, `Cost.withoutTouchLower`)",
      "WHAT IS LEFT NOW THAT `touch` HAS A LOWER ENDPOINT.  This entry used to say `analyze` applied " +
      "`withoutTouchLower` unconditionally so every width was `upper + 1` BY CONSTRUCTION, and that " +
      "review.md item 5's second half was the fix.  It landed: `evalI`'s algebra entry is forced (the " +
      "visit hook precedes every fast-path test) and the frontier's must-paired count is added wherever " +
      "the whole-skip paths are discharged, which took `inter/shared-subtrie` to width 7.91 and out of " +
      "this entry.  The four families that remain have a must-count of ZERO for a real reason — a subset " +
      "union and a key-disjoint union are decided at the root, and a fixed selective consumer forces only " +
      "its own frontier — so for THOSE the width is genuinely `upper + 1` and the remedy is the upper " +
      "endpoint, not the lower."),
    Limitation("LIM-6g", "ladder", "graph", EffortComponent.Touch, WidthOnly,
      Vector("select/fixed-consumer", "union/paired-keys", "union/disjoint-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 25000.0, "SpatialCost.scala",
      "as LIM-6, and `inter/shared-subtrie` left it too (width 7.91) once `GraphCost.forcedEntry` learned " +
      "that `execT`'s guard reads the left operand only."),
    Limitation("LIM-6z", "ladder", "zipper", EffortComponent.Touch, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 18000.0, "SpatialCost.scala", "as LIM-6."),
    Limitation("LIM-6a", "ladder", "trie", EffortComponent.Alloc, WidthOnly,
      Vector("select/fixed-consumer", "union/paired-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 6500.0, "SpatialCost.scala",
      "as LIM-6, for `alloc`: no MUST-ALLOCATE count is derived, although a union of two operands with " +
      "`k` provably paired keys must rebuild at least `k` nodes."),
    Limitation("LIM-6ag", "ladder", "graph", EffortComponent.Alloc, WidthOnly,
      Vector("select/fixed-consumer", "union/paired-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 800.0, "SpatialCost.scala", "as LIM-6a."),
    Limitation("LIM-6az", "ladder", "zipper", EffortComponent.Alloc, WidthOnly,
      Vector("union/paired-keys", "rest-chain/nest"),
      Double.PositiveInfinity, 6500.0, "SpatialCost.scala", "as LIM-6a."),
    Limitation("LIM-6w", "ladder", "zipper", EffortComponent.Work, WidthOnly, Vector("union/paired-keys"),
      Double.PositiveInfinity, 14000.0, "SpatialCost.scala",
      "as LIM-6, for `work` on the ONE family where the zipper's upper endpoint is right (error 4.99, " +
      "slope 1.00 = declared): the whole width failure there is the missing lower endpoint and nothing " +
      "else, which is what makes this entry different from LIM-1."),

    // ============================ LIM-7: an exact law emitted as an upper bound ===================
    Limitation("LIM-7", "ladder", "trie", EffortComponent.Rounds, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 180.0, "SpatialCost.scala (`CostModel.chainNest`)",
      "THE FRAME LAW IS USED FOR THE UPPER ENDPOINT ONLY.  `chainNest` returns " +
      "`CostInterval.upperOnly(work = frames, rounds = frames, touch = visits)`, and the measured round " +
      "count equals that upper endpoint EXACTLY at every rung (error 1.00, 72/136/264/520/1032) — so " +
      "`Σ_d K_d` is not an estimate here, it is the answer, and on a closed source it is equally an exact " +
      "LOWER bound.  Emitting it as an exact interval would take this channel from width 115 to width 1 " +
      "and make `Rounds` the first fully determined component in the model."),
    Limitation("LIM-7g", "ladder", "graph", EffortComponent.Rounds, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 180.0, "SpatialCost.scala (`CostModel.chainNest`)", "as LIM-7."),
    Limitation("LIM-7z", "ladder", "zipper", EffortComponent.Rounds, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 180.0, "SpatialCost.scala (`CostModel.chainNest`)", "as LIM-7."),
    Limitation("LIM-7w", "ladder", "trie", EffortComponent.Work, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 100.0, "SpatialCost.scala (`CostModel.chainNest`)",
      "as LIM-7 for `work`, whose upper endpoint is likewise EXACT on this family (error 1.00 at every " +
      "rung).  This channel is on the SELECTION tier, so its width budget is 8 and the gap is starker."),
    Limitation("LIM-7wg", "ladder", "graph", EffortComponent.Work, WidthOnly, Vector("rest-chain/nest"),
      Double.PositiveInfinity, 450.0, "SpatialCost.scala (`CostModel.chainNest`)", "as LIM-7w."),

    // ============================ LIM-8: a constant factor, named as one =========================
    Limitation("LIM-8", "ladder", "trie", EffortComponent.Touch, Set("error"),
      Vector("union/disjoint-keys"),
      16.0, Double.PositiveInfinity, "SpatialCost.scala (`TrieAlgebraCost.tPer`)",
      "A CONSTANT FACTOR, and the only entry in this ledger that is one.  The Patricia bound charges 3 " +
      "visits per merged child entry (the `2k-1` node fact plus the entry itself); the measured walk over " +
      "key-disjoint operands averages ~0.6, because the Patricia join attaches whole branches instead of " +
      "descending them.  Measured 10.26 against the 10x budget tier — the SLOPE is correct (0.99 measured, " +
      "1.00 predicted, declared 1.00), so this is a factor and not a growth class, and it is recorded " +
      "rather than absorbed by a looser tier."),
    Limitation("LIM-8g", "ladder", "graph", EffortComponent.Touch, Set("error"),
      Vector("union/disjoint-keys"),
      16.0, Double.PositiveInfinity, "SpatialCost.scala (`TrieAlgebraCost.tPer`)", "as LIM-8."),

    // ==============================================================================================
    // THE CORNERSTONES, ON `Routine.optimized`'s BODY  (SpatialEventsCheck)
    //
    // These are the numbers review.md item 7 is about, re-measured on the form that runs.  What the
    // optimized form ALREADY fixed, for the record, because it is most of the review's complaint:
    //   * n-queens: 53 Space nodes -> 1.  The ordinary rule list COMPILE-TIME EVALUATES it, so the
    //     "3,839x work / 213,465x alloc / 3.98Mx touch" figures describe a term that never runs.  There
    //     is no run-time cost left to gate and nothing is excused below.
    //   * puzzle15 `Work`: error 1.01, and `Rounds`: error 1.00 with a [57, 84] interval against a
    //     counted 84.  The rest-chain frame law reaches those two components and they are now EXACT.
    //   * aunt/temperature `Work` and every cornerstone's `Rounds`: 1.00-1.48.
    // What is left is `Alloc` and `Touch` (and Datalog's fixpoint size), listed below.
    // ==============================================================================================

    Limitation("CS-1", "cornerstone", "trie", EffortComponent.Alloc, ErrAll,
      Vector("aunt", "gol", "datalog-sn"), 150.0, Inf,
      "SpatialCost.scala (`TrieAlgebraCost.priced`) / SpatialFrontier.scala",
      "LIM-5 reaching whole programs: `alloc := rebuilt` is met against the RESULT's node envelope, so a " +
      "program whose merges attach branches whole is over-charged (aunt 16 counted / 191 predicted = 11.3x, " +
      "gol 1175 / 21169 = 18.0x, datalog 19 / 1891 = 94.6x).  The same transfer is accurate to 1.01x on " +
      "`union/paired-keys`, where the rebuilt count really is the envelope — so this is a defect in the " +
      "MEET, not a limit of the bound."),
    Limitation("CS-2", "cornerstone", "zipper", EffortComponent.Alloc, ErrAll, Vector("aunt", "gol"),
      30.0, Inf, "SpatialCost.scala (`ZipperCost`)", "as CS-1, through `SpaceZipper.materialize`."),

    Limitation("CS-3", "cornerstone", "trie", EffortComponent.Touch, ErrAll, Vector("gol", "datalog-sn"),
      700.0, Inf, "SpatialCost.scala (`TrieAlgebraCost`) / SpatialFrontier.scala",
      "LIM-4 reaching whole programs: the frontier's whole-subtree accepts do not reduce " +
      "`touch := descents + patricia` (gol 4138 counted / 119028 predicted = 28.8x, datalog 143 / 62296 = " +
      "432.6x).  Datalog's factor is the larger because its fixpoint round bound (CS-5/CS-6) multiplies the " +
      "per-round descent, so the two defects compound."),
    Limitation("CS-4", "cornerstone", "zipper", EffortComponent.Touch, ErrAll, Vector("gol"),
      60.0, Inf, "SpatialCost.scala (`TrieAlgebraCost`)", "as CS-3."),

    Limitation("CS-5", "cornerstone", "trie", EffortComponent.Work, ErrAll, Vector("datalog-sn"),
      10.0, Inf, "SpatialCost.scala / SpatialRecursion.scala",
      "THE DATALOG FIXPOINT SIZE (review.md item 5, second half).  Semi-naive transitive closure runs 17 " +
      "counted frames and the analysis predicts up to 121, because the round count is `|all at the " +
      "fixpoint| + 2` and there is no interprocedural least-fixpoint SIZE summary to bound `|all|` — the " +
      "body's size transformer is never solved, so the bound falls back to the path universe.  The " +
      "estimate is finite (it is no longer `inf`, and the reference/zipper reports are still SYMBOLIC in " +
      "`|sn_tc()|`), but 6x on a 4-edge graph is not a capacity answer."),
    Limitation("CS-6", "cornerstone", "trie", EffortComponent.Rounds, ErrAll, Vector("datalog-sn"),
      10.0, Inf, "SpatialCost.scala / SpatialRecursion.scala", "as CS-5, on the round count itself: 17 " +
      "counted against a predicted 121."),

    Limitation("CS-7", "cornerstone", "zipper", EffortComponent.Work, ErrAll, Vector("temperature"),
      24.0, Inf, "SpatialCost.scala (ZipperCost) / SpatialDemand.scala",
      "LIM-1 reaching a whole program: 41 counted cursor reads against a predicted 589 on two fused " +
      "restrictions of one mention.  `Touch` on the same term is exact ([0,0] against 0)."),

    // ---- the width half: there is no lower endpoint (LIM-6), on whole programs ----------------------
    Limitation("CS-8", "cornerstone", "trie", EffortComponent.Alloc, WidthAll,
      Vector("aunt", "gol", "datalog-sn"), Inf, 32000.0, "SpatialCost.scala",
      "LIM-6 on whole programs: every `alloc` interval starts at 0 because no MUST-ALLOCATE count is " +
      "derived, so WIDTH is `upper + 1` by construction (aunt [0,191], gol [0,21169])."),
    Limitation("CS-9", "cornerstone", "zipper", EffortComponent.Alloc, WidthAll, Vector("aunt", "gol"),
      Inf, 32000.0, "SpatialCost.scala", "as CS-8."),
    Limitation("CS-10", "cornerstone", "trie", EffortComponent.Touch, WidthAll,
      Vector("gol", "datalog-sn"), Inf, 180000.0, "SpatialCost.scala",
      "WHAT IS LEFT OF LIM-6 ON WHOLE PROGRAMS.  `touch` now HAS a lower endpoint: `evalI` is eager and " +
      "every `ITrie` operation emits its visit before any fast-path test, so one visit per algebra node " +
      "is forced, and the must-paired frontier count is added where the whole-skip paths are discharged. " +
      "That removed `aunt` (width 180000 -> 12.99) and `temperature` (-> 24.25) from this entry outright: " +
      "on both, the missing lower endpoint WAS the whole gap, exactly as the previous revision of this " +
      "entry predicted.  `gol` (70.06) and `datalog-sn` (1198) remain, and their residue is the UPPER " +
      "endpoint — LIM-4's Patricia constant on `gol`, CS-5's fixpoint round bound on `datalog-sn` — not " +
      "the lower one."),
    Limitation("CS-11", "cornerstone", "zipper", EffortComponent.Touch, WidthAll, Vector("gol"),
      Inf, 180000.0, "SpatialCost.scala", "as CS-10; `aunt` (width 13.11) left this entry with it."),
    Limitation("CS-12", "cornerstone", "trie", EffortComponent.Work, WidthAll, Vector("datalog-sn"),
      Inf, 16.0, "SpatialCost.scala / SpatialRecursion.scala", "as CS-5: the round bound widens the " +
      "interval [87, 901] around a counted 149."),
    Limitation("CS-13", "cornerstone", "trie", EffortComponent.Rounds, WidthAll, Vector("datalog-sn"),
      Inf, 16.0, "SpatialCost.scala / SpatialRecursion.scala", "as CS-6: [11, 121] around a counted 17."),
    Limitation("CS-14", "cornerstone", "zipper", EffortComponent.Work, WidthAll, Vector("temperature"),
      Inf, 120.0, "SpatialCost.scala (ZipperCost)", "as CS-7: [7, 589] around a counted 41."),

    // ---- puzzle15: FINITE AND USELESS.  Its own entries, because the magnitude is its own statement --
    Limitation("CS-P1", "cornerstone", "trie", EffortComponent.Alloc, ErrWidth, Vector("puzzle15"),
      1.0e54, 1.0e57, "SpatialCost.scala (`CostModel.chainNest`, the loop transfer)",
      "THE HEADLINE FAILURE, AND THE ONE THE OLD GATE HID BEHIND AN ALLOW-LIST.  On the optimized body " +
      "`puzzle15` is no longer INFINITE — `Work` is now accurate to 1.01x and `Rounds` to 1.00x, because " +
      "the rest-chain frame law reaches those two components.  `Alloc` and `Touch` do not use it: the loop " +
      "transfer still multiplies the per-level group maxima of a 16-level nest, giving [0, 8.3e55] against " +
      "a counted 1334.  Replacing `inf` with a 10^55 polynomial is not progress, and this entry exists so " +
      "that nothing can call it progress: the fix is to price the nest's ALLOCATION and DESCENT from " +
      "`SpatialFacts.PrefixProfile` (`frameEntries` / `chainBound`) the same way its FRAMES already are."),
    Limitation("CS-P2", "cornerstone", "trie", EffortComponent.Touch, ErrWidth, Vector("puzzle15"),
      1.0e54, 1.0e57, "SpatialCost.scala (`CostModel.chainNest`, the loop transfer)",
      "as CS-P1, on the descent: [0, 3.2e56] against a counted 3478."),
    Limitation("CS-P3", "cornerstone", "zipper", EffortComponent.Alloc, ErrWidth, Vector("puzzle15"),
      1.0e54, 1.0e57, "SpatialCost.scala", "as CS-P1; `execZ` falls back to `evalI` for the nest."),
    Limitation("CS-P4", "cornerstone", "zipper", EffortComponent.Touch, ErrWidth, Vector("puzzle15"),
      1.0e54, 1.0e57, "SpatialCost.scala", "as CS-P2."),

    // ==============================================================================================
    // WIDTH, PER OPERATOR, ON THE OPTIMIZED FORM  (SpatialCostCheck)
    //
    // WIDTH needs no execution: it is a property of the answer.  The table in `SpatialCostCheck`
    // establishes one thing outright — on a CLOSED one-operator program with exactly declared inputs,
    // EVERY endpoint of EVERY component on EVERY backend is FINITE and free of free variables (review.md
    // item 5's invariant, asserted there and not excused anywhere).  What it also shows is that the
    // interval is almost always [0, upper]: 14 operators x 4 backends x 4 components = 224 checks, and
    // the ones that fail below fail because the LOWER endpoint does not exist, not because the upper is
    // wrong.  The entries are grouped by (backend, component) with the exact operator list, so a
    // per-operator fix shows up as a NECESSITY failure on that operator alone.
    // ==============================================================================================

    Limitation("OP-1", "operator", "trie", EffortComponent.Touch, WidthAll,
      Vector("composition", "range-part", "iteration", "fixpoint", "tails-union", "tails-inter"),
      Inf, 90000.0, "SpatialCost.scala (`TrieAlgebraCost.entryVisit` / `mustDescend`)",
      "WHAT IS LEFT AFTER THE `touch` LOWER ENDPOINT LANDED.  The previous revision of this entry said " +
      "`analyze` ended with an unconditional `withoutTouchLower`, so every `touch` width was `upper + 1` " +
      "BY CONSTRUCTION, and that a lower bound was derivable wherever the frontier proves paired prefixes " +
      "MUST be descended.  Both halves are now done and this entry lost FOUR subjects to them: `evalI` is " +
      "eager and every `ITrie` operation emits its visit BEFORE any fast-path test, so one visit per " +
      "algebra node is forced (halving every width here), and on the three symmetric merges the frontier's " +
      "must-paired count is added once the whole-skip paths (`isEmpty`, `a eq b`) are discharged by " +
      "cardinality — which took `union`, `intersection`, `subtraction` and `range-full` inside the budget " +
      "outright.  `restriction` AND `raffination` THEN LEFT TOO: their extra whole-skip path is " +
      "`ε ∈ right` (ε prefixes everything, so all of `x` is accepted or dropped by pointer), and " +
      "`Meas.epsAbsent` — the shape's ε-presence, which the domain always had and the measure did not " +
      "carry — discharges it.  THE SIX THAT REMAIN: `composition` reaches only the entry visit (69), " +
      "because the graft frontier derives no must side even with both `{ε}` cases discharged; " +
      "`iteration` (113) and `range-part` (136.5) need a must-count of their own; and `fixpoint` " +
      "(28434) is an UPPER-endpoint problem — its round bound — not a lower-endpoint one.  THE TWO `tails` " +
      "OPERATORS ARE NOW WITHIN 15%: both read 73.67 = 221/3.  Their upper lost a whole `heads` factor " +
      "when `tails-inter` stopped being priced as the per-key probe loop `IntTrieOps.meetAllTries` " +
      "replaced (877 -> 73.67, a 12x tightening derived from the algorithm: the meet's frontier lies " +
      "inside the SMALLEST child and min <= mean cancels the factor).  Their lower is TWO — the `tails*` " +
      "entry and the `joinAll`/`meetAll` entry — and it cannot be three without proving the source's two " +
      "children are distinct OBJECTS, which needs the per-head sub-shapes the shape domain has and `Meas` " +
      "does not carry.  That, or `nodesHi` reaching this transfer, is what closes the last 15%."),
    Limitation("OP-1g", "operator", "graph", EffortComponent.Touch, WidthAll,
      Vector("composition", "range-full", "range-part", "iteration", "fixpoint", "tails-union",
             "tails-inter"),
      Inf, 90000.0, "SpatialCost.scala (`GraphCost.forcedEntry`)",
      "as OP-1, and it lost the same five operators plus `union` for a REASON SPECIFIC TO `execT`: its " +
      "space slots are guarded by `if a.isEmpty then ITrie.empty`, but the guard reads the LEFT operand " +
      "ONLY and `Union` carries no guard at all (`GraphExec.scala`), so the algebra entry is forced " +
      "whenever the shape domain proves the left operand non-empty.  THE UNARY OPERATORS FOLLOWED: `GraphExec.scala` guards " +
      "`Wrap`/`Unwrap` on their SOURCE but calls `TailsUnion`/`TailsIntersection`/`Range` with NO guard " +
      "at all, so those three force their entry on `execT` exactly as on `evalI` — graph `tails-*` Touch " +
      "221 -> 73.67, level with the trie.  The SEVEN that remain are the operators whose entry `execT` " +
      "really can skip or whose upper endpoint is the problem."),
    Limitation("OP-1z", "operator", "zipper", EffortComponent.Touch, WidthAll,
      Vector("range-full", "range-part", "iteration", "fixpoint", "tails-inter"),
      Inf, 90000.0, "SpatialCost.scala",
      "as OP-1, on the FIVE operators where a fused cursor still enters the `ITrie` algebra.  On the ring " +
      "operators the zipper's `touch` interval is [0,0] against a counted 0 and its width is 1 — the " +
      "demand analysis really does price that component exactly, which is what makes LIM-1's `Work` gap " +
      "a defect rather than a limit."),

    Limitation("OP-2", "operator", "trie", EffortComponent.Alloc, WidthAll,
      Vector("composition", "fixpoint", "iteration", "tails-union", "tails-inter"),
      Inf, 12000.0, "SpatialCost.scala (`CostInterval.upperOnly`)",
      "no MUST-ALLOCATE count is derived, so these intervals also start at 0.  The five operators listed " +
      "are the ones whose upper endpoint grows with the input; the ring operators' widths are 7-15 and " +
      "inside the budget tier."),
    Limitation("OP-2g", "operator", "graph", EffortComponent.Alloc, WidthAll,
      Vector("composition", "fixpoint", "tails-union", "tails-inter"),
      Inf, 12000.0, "SpatialCost.scala", "as OP-2."),
    Limitation("OP-2z", "operator", "zipper", EffortComponent.Alloc, WidthAll,
      Vector("composition", "fixpoint", "iteration", "range-full", "range-part", "tails-union", "tails-inter"),
      Inf, 12000.0, "SpatialCost.scala", "as OP-2, plus the two `Range` forms, where the zipper " +
      "materialises and the trie does not."),

    Limitation("OP-3", "operator", "zipper", EffortComponent.Work, WidthAll,
      Vector("union", "intersection", "subtraction", "restriction", "raffination", "composition",
             "range-full", "range-part", "wrap", "tails-union", "tails-inter"),
      Inf, 4500.0, "SpatialCost.scala (ZipperCost) / SpatialDemand.scala",
      "LIM-1 AND OP-1 TOGETHER, and the only entry in this ledger with two causes: the upper endpoint is " +
      "the eager per-operator sum (the demand price does not lower `Work`) and the lower endpoint is 0 " +
      "(`upperOnly`).  Either fix alone would shrink these widths; the pair is why `zipper Work` is the " +
      "widest channel in the table (2929 on a composition)."),
    Limitation("OP-3g", "operator", "graph", EffortComponent.Work, WidthAll,
      Vector("fixpoint", "iteration"),
      Inf, 200.0, "SpatialCost.scala (`GraphCost`)",
      "`execT`'s slot dispatch count is exact for a straight-line body (width 1.00 on every ring " +
      "operator) and loses its lower endpoint through the loop/fixpoint round interval — the same cause " +
      "as OP-4."),
    Limitation("OP-4", "operator", "trie", EffortComponent.Work, WidthAll, Vector("fixpoint"),
      Inf, 60.0, "SpatialCost.scala (the fixpoint transfer)",
      "the round count is an INTERVAL ([1, R] for a monotone accumulator), and the body cost is " +
      "multiplied by its upper endpoint while the lower endpoint gets the lower round count — so the " +
      "width of a fixpoint is the width of its round bound.  Every other operator's `trie Work` width in " +
      "the table is exactly 1.00, which is what makes this the single outlier rather than a general gap."),
    Limitation("OP-5", "operator", "trie", EffortComponent.Rounds, WidthAll, Vector("fixpoint"),
      Inf, 60.0, "SpatialCost.scala (the fixpoint transfer)",
      "as OP-4, on the round count itself: [1, 37] for a monotone accumulator over a 64-path seed.  A " +
      "must-round count (the accumulator grows by at least one path per continuing round, so the FIRST " +
      "round is mandatory and so is every round until the seed is absorbed) would tighten the lower " +
      "endpoint; only the trivial `>= 1` is claimed."),
    Limitation("OP-5g", "operator", "graph", EffortComponent.Rounds, WidthAll, Vector("fixpoint"),
      Inf, 60.0, "SpatialCost.scala", "as OP-5."),
    Limitation("OP-5z", "operator", "zipper", EffortComponent.Rounds, WidthAll, Vector("fixpoint"),
      Inf, 60.0, "SpatialCost.scala", "as OP-5."))

  def limitationFor(scope: String, subject: String, backend: String,
                    comp: EffortComponent, what: String): Option[Limitation] =
    limitations.find(_.matches(scope, subject, backend, comp, what))

/** ONE GATE DECISION, so the caller can print the whole table and fail once at the end. */
final case class GateRow(scope: String, subject: String, backend: String, comp: EffortComponent,
                         what: String, measured: Double, tier: ProductRequirement.Tier):
  def permitted: Double = tier.budget(what)
  def key: String = s"$scope $subject $backend $comp $what".trim
  def ok: Boolean = measured <= permitted + 1e-9
  def limitation: Option[ProductRequirement.Limitation] =
    ProductRequirement.limitationFor(scope, subject, backend, comp, what)
  def show: String =
    f"$key%-64s ${GateRow.fmt(measured)}%12s <= ${GateRow.fmt(permitted)}%12s  " +
    f"${if ok then "OK" else "FAIL"}%-4s [${tier.name}]"

object GateRow:
  def fmt(d: Double): String =
    if d.isInfinite then "inf" else if math.abs(d) >= 1e6 then f"$d%.2e" else f"$d%.2f"

/** ==============================================================================================
 *  THE CORRELATED SCALE LADDERS  (review.md item 7, third and fourth sentences)
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
 *  `log2((C(2n) + 1) / (C(n) + 1))` per rung pair, exactly as review.md specifies, reported as its
 *  maximum over the ladder (the worst doubling, not an average that a good rung can hide), plus the
 *  end-to-end ratio.  A family DECLARES the class it claims — `0.0` for constant-or-depth, `1.0` for
 *  linear — and both the MEASURED and the PREDICTED slope must meet it.  The measured half is a claim
 *  about the backend; the predicted half is the claim about the estimate, and it is the one review.md
 *  item 7 is about. */
class SpatialScaleCheck extends FunSuite:
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

  /** the geometric ladder.  Five rungs / four doublings: enough that a linear channel separates from a
   *  flat one by a factor of 16, small enough that the analysis of every rung is affordable. */
  val ladder: Vector[Int] = Vector(64, 128, 256, 512, 1024)

  /** `log2((C(2n) + 1) / (C(n) + 1))` — review.md item 2's statistic, verbatim */
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
   *  decorated analysis of that body is what the cost env consumes (review.md item 8), so the prediction
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
    def measSlope: Double = maxSlope(actual)
    def predSlope: Double = maxSlope(upper)
    def ratio: Double = (actual.last + 1.0) / (actual.head + 1.0)
    def predRatio: Double = (upper.last + 1.0) / (upper.head + 1.0)
    def show: String =
      f"  $backend%-8s $comp%-6s actual=${actual.map(_.toLong).mkString(",")}%-34s " +
      f"pred=${upper.map(fmt).mkString(",")}%-40s " +
      f"slope meas=${measSlope}%5.2f pred=${predSlope}%5.2f " +
      f"decl=${declared.map(d => f"$d%.2f").getOrElse("  - ")}%s  " +
      f"err=${error}%9.2f width=${width}%9.2f"
    private def fmt(d: Double): String =
      if d.isInfinite then "inf" else if d >= 1e7 then f"$d%.1e" else d.toLong.toString

  // ==============================================================================================
  // 3. THE FAMILIES
  // ==============================================================================================

  def routine(name: String, ments: Vector[String], body: Space): Routine =
    Routine(RoutinePtr(name), Vector.empty, ments.map(sm), body)

  /** THE SIX CASES review.md names, plus a linear control and three degenerate identities. */
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

    // ---- KEY-DISJOINT union under a SHARED prefix: review.md item 2's union row, "non-overlapping
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
        // THE SLOPE REQUIREMENT.  Two halves: the estimate may not out-grow the measurement, and where
        // the family declares a class BOTH must meet it — the measured half is a claim about the
        // backend, the predicted half is the claim about the model.
        row("slope-vs-measured", ch.predSlope - ch.measSlope)
        for d <- ch.declared do
          row("slope-measured-vs-declared", ch.measSlope - d)
          row("slope-predicted-vs-declared", ch.predSlope - d)
    // ---- SOUNDNESS FIRST, and it is never excused ----------------------------------------------
    assertEquals(unsound, Vector.empty[String],
                 "a counted value fell outside the predicted interval on the optimized form:\n  " +
                 unsound.mkString("\n  "))
    // ---- the correlated trend: predicted cost against measured wall time ------------------------
    if trend.length >= 8 then
      val rho = Calibration.spearman(trend.map(_._1), trend.map(_._2))
      println(f"SCALE: Spearman(predicted total cost, measured wall time) = $rho%.3f over ${trend.length} " +
              "(family, rung, backend) points on the OPTIMIZED form")
      assert(rho >= 0.35, f"the predicted cost order must track measured time across the ladders; rho=$rho%.3f")
    publishGate("scale ladders on the optimized form", rows, channels)
  }

  // ==============================================================================================
  // 5. THE GATE
  // ==============================================================================================

  /** Print every requirement decision, consult the named limitations, and fail on anything left over —
   *  including a limitation that is NO LONGER NECESSARY, and any regression past one. */
  def publishGate(title: String, rows: Vector[GateRow], channels: Int): Unit =
    val scope = rows.headOption.map(_.scope).getOrElse("")
    println("=" * 132)
    println(s"PRODUCT REQUIREMENTS — $title  ($channels channels, ${rows.length} requirement checks)")
    println("=" * 132)
    var failures = Vector.empty[String]
    val met = rows.count(_.ok)
    // ---- every failing check, with the named limitation that covers it (or without one) -----------
    for r <- rows.filterNot(_.ok).sortBy(_.key) do
      r.limitation match
        case Some(l) =>
          println("REQUIREMENT: " + r.show + s"  <== NOT MET — named limitation ${l.id}")
          if r.measured > l.cap(r.what) + 1e-9 then
            failures :+= s"${r.key}: ${GateRow.fmt(r.measured)} REGRESSED past named limitation " +
                         s"${l.id}'s recorded ${GateRow.fmt(l.cap(r.what))}"
        case None =>
          println("REQUIREMENT: " + r.show + "  <== FAILS THE PRODUCT REQUIREMENT, UNNAMED")
          failures :+= s"${r.key}: measured ${GateRow.fmt(r.measured)} exceeds the ${r.tier.name} " +
                       s"requirement ${GateRow.fmt(r.permitted)} — ${r.tier.why}"
    // ---- NECESSITY: every subject of every limitation in this scope must still be failing ---------
    for l <- ProductRequirement.limitations if l.scope == scope do
      val mine = rows.filter(r => l.matches(r.scope, r.subject, r.backend, r.comp, r.what))
      if mine.isEmpty then
        failures :+= s"${l.id}: declared over ${l.subjects.mkString(",")} but NO requirement check " +
                     "produced a matching row — the channel stopped being measured"
      for s <- l.subjects do
        val hers = mine.filter(_.subject == s)
        if hers.nonEmpty && hers.forall(_.ok) then
          failures :+= s"${l.id}: subject `$s` NO LONGER FAILS " +
                       s"(${hers.map(r => s"${r.what}=${GateRow.fmt(r.measured)}").mkString(", ")} all meet " +
                       s"the ${l.comp}/${hers.head.tier.name} requirement) — remove it from the limitation; " +
                       "the ledger may not keep a fixed channel excused"
    // ---- the ledger itself, printed in full ------------------------------------------------------
    val used = ProductRequirement.limitations.filter(l =>
      l.scope == scope && rows.exists(r => l.matches(r.scope, r.subject, r.backend, r.comp, r.what) && !r.ok))
    println("-" * 132)
    println(s"PRODUCT REQUIREMENTS — $met of ${rows.length} checks MET; ${rows.length - met} not met, " +
            s"covered by ${used.length} named limitations")
    for l <- used do
      println("LIMITATION: " + l.show)
      println("LIMITATION:   subjects: " + l.subjects.mkString(", "))
      println("LIMITATION:   " + l.reason)
    assertEquals(failures, Vector.empty[String],
                 s"$title: ${failures.length} product-requirement failure(s) with no named limitation " +
                 s"(or a stale one):\n  " + failures.mkString("\n  "))
end SpatialScaleCheck
