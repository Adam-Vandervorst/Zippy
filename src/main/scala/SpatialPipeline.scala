package morkl

/** ==================================================================================================
 *  THE SPATIAL PIPELINE — one ordinary entry point.
 *
 *  ==THE PROBLEM==
 *  Everything the spatial subsystem knows was reachable only by a caller who already knew which of
 *  `SpatialTyping.infer` / `SpatialAnalysis.of` / `SpatialFacts.specializations` /
 *  `SpatialTypes.eliminate` / `SpatialRecursion.residualise` / `SpatialCost.analyze` to call, in
 *  which order, with which of six budget constants.  `Routine.optimized` consumed none of it;
 *  `transpile`, graph `optimize`, `execT` and `execZ` consumed none of it.  The subsystem was an
 *  island.
 *
 *  `Routine.optimized` (MORKL.scala:248-251) no longer is one of those: it runs [[SpatialHook.rewrite]]
 *  on every body it compiles, which is the unconditional half of stage 2 under a measured budget.  See
 *  [[SpatialHook]] for the policy, the switch and the numbers.
 *
 *  ==THE THREE STAGES==
 *  {{{
 *  val a = SpatialPipeline.analyzeRoutine(r, ann)        // facts, with provenance and a SCOPE
 *  val g = SpatialPipeline.optimizeGuarded(r, a)         // a GUARDED artifact: residual + fallback
 *  val l = SpatialPipeline.lower(g, Backend.Graph)       // candidates consumed by ONE backend
 *  }}}
 *  and the whole flow in one call, [[SpatialPipeline.run]].
 *
 *  ==THE SCOPE DISCIPLINE, WHICH IS THE POINT==
 *  A fact derived under a declared input type is CONDITIONAL: it holds for the inputs the annotation
 *  admits and for no others.  A fact derived with no annotation at all is UNCONDITIONAL.  The two must
 *  not produce the same artifact, and that is exactly what the previous generation of the API did:
 *  `SpatialTypes.eliminateIn` returned a bare `(Routine, Vector[Removed])` whose `Routine` has the
 *  SAME NAME as the original and no trace of the precondition, so installing it in a routine table
 *  silently replaces a general routine by a conditionally-valid one.
 *
 *  Everything here routes through the safe artifact instead:
 *
 *   - [[FactScope]] on the analysis says which kind of facts these are;
 *   - [[GuardedRoutine]] carries `residual` AND `fallback` AND all three precondition channels, and
 *     its `choose` is the dispatcher;
 *   - `optimize` returns `SpatialTyping.SpecializedRoutine`, which cannot be mistaken for a `Routine`;
 *   - an UNCONDITIONAL result is exactly a `SpecializedRoutine` with an EMPTY precondition, whose
 *     `applicableTo` is vacuously true — so "unconditional" is a fact about the data, not a promise
 *     in a comment.
 *
 *  ==NO EVALUATION==
 *  Nothing in this file calls `eval` / `evalI` / `evalT` / `exec` / `execT` / `execZ` /
 *  `transpileZ` / `runGraph*`, directly or transitively: the stages consume `SpatialAnalysis`,
 *  `SpatialFacts`, `SpatialRecursion` and `SpatialCost`, none of which does either.  `lower` calls
 *  `transpile` and the graph `optimize`, which are COMPILATION, not execution — they build and rewrite
 *  an operation graph and never run it.  The gate is mechanical and lives in `SpatialAcceptance`: every
 *  pipeline stage is run inside `EffortSink.count`, and every executor in the tree is instrumented, so
 *  a single dispatch of a single interpreter would show up as a non-zero event count.
 *  ================================================================================================ */

// ==================================================================================================
// 1.  THE ONE INPUT VALUE
// ==================================================================================================

/** WHAT THE ANALYSIS IS ALLOWED TO ASSUME, and the budgets it may spend — one value for every stage
 *  (the requirement: "use one `SpatialAnnotations`/`SpatialConfig` value for all analysis
 *  stages").
 *
 *  The three input channels are deliberately separate because they mean different things and are
 *  checked differently at a call site:
 *
 *   - `spaces`   a declared spatial type per mention — checked by full γ-membership;
 *   - `paths`    a path parameter KNOWN to equal a constant — checked by equality;
 *   - `pathLens` a path parameter of unknown value but bounded ITEM LENGTH — checked by length.
 *
 *  An entry that admits everything (`SpatialType.top`, `LenBounds.unknown`) is NOT a precondition and
 *  is filtered out of [[scope]]: declaring `⊤` must not turn an unconditional rewrite into a guarded
 *  one, and must not turn a guarded one into an unconditional one either. */
final case class SpatialAnnotations(
  spaces: Map[SpaceMention, SpatialType] = Map.empty,
  paths: Map[PathRef, PathValue] = Map.empty,
  pathLens: Map[PathRef, Lower.LenBounds] = Map.empty,
  routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
  /** EVERY budget EVERY stage spends — one value.  The fact stage's
   *  `SpatialFacts.Config` and the residualiser's `SpatialRecursion.Limits` are PROJECTIONS of it
   *  ([[factConfig]], [[limits]]) and no longer separate fields, so a caller who narrows the analysis
   *  cannot leave the two downstream stages on their defaults by accident. */
  config: SpatialConfig = SpatialConfig.default,
  /** the largest exact value the pipeline will fold a subterm to.  `SpatialFacts.exactValue`
   *  ENUMERATES the pinned space, so folding is only attempted where the type already bounds its
   *  cardinality — otherwise a 12-wide 4-deep closed shape would be enumerated at every node. */
  maxFoldPaths: Long = 64L,
  /** the largest proved head set the trie lowering will unroll an `Iteration` over */
  maxUnrollHeads: Int = 8,
  /** re-analyse the Call-free residual so the later per-node rewrites see ITS positions.  Off makes
   *  residualisation and node rewriting mutually exclusive rather than composed. */
  refineAfterResidual: Boolean = true,
  /** MARK THE ROUTINE UNDER ANALYSIS AS ACTIVE, so a direct self-call widens to ⊤ instead of being
   *  inlined one level by the ordinary interprocedural transfer.
   *
   *  Off by default: `SpatialTyping.goShape` already adds a callee to `active` before descending, so a
   *  self-recursive routine is inlined EXACTLY ONE level and the inner self-call degrades to ⊤ —
   *  terminating and sound, and one level more precise.  `SpatialCheck.report` turns it ON, because a
   *  VERDICT should not depend on how far the inliner got; turn it on here too when the pipeline's
   *  premises must be identical to the checker's (`SpatialAcceptance`'s definition-of-done test does). */
  selfActive: Boolean = false,
  /** RUN THE ORDINARY `Lower` RULE LIST (`Routine.optimized`) after the spatial rewrites.
   *
   *  Keep it on to get the artifact the ordinary pipeline would actually install — the spatial
   *  rewrites feed it new `Empty`s and new `Literal`s, and its own laws propagate them.
   *
   *  Turn it OFF to get a PURELY SPATIAL artifact.  That matters for one specific reason:
   *  `Lower.ConstantOps` (MORKL.scala:1613) is a partial evaluator — it *tries* `eval` on every node
   *  and folds the ones that do not throw — and `Lower.LiteralSpaceOps` calls `eval` on every
   *  literal-operand algebra node.  Those are legitimate COMPILE-TIME EVALUATIONS of closed subterms
   *  and they long predate this file, but they mean `Routine.optimized` runs the program, so a
   *  pipeline stage that calls it cannot be gated by "no executor event was counted".  With
   *  `ordinaryLower = false` the whole pipeline is provably evaluation-free, which is what
   *  `SpatialPipelineCheck` and `SpatialAcceptance` assert. */
  ordinaryLower: Boolean = true,
):
  import Lower.LenBounds

  /** the fact/profile/candidate stage's budgets — a PROJECTION of [[config]], not a second value */
  /** THE DECLARED INPUTS AS THE RESOURCE ANALYSIS READS THEM: summaries for the spaces,
   *  values or length bounds for the paths.  Nothing is evaluated to build them. */
  def costInputs: CostSem.Inputs = CostSem.Inputs(summaries = spaces, paths = paths, pathLens = pathLens)
  def factConfig: SpatialFacts.Config = config.facts
  /** the recursion residualiser's budgets — likewise */
  def limits: SpatialRecursion.Limits = config.recursion

  /** the shape/histogram environment.  `active` marks routines whose ordinary interprocedural
   *  transfer must not be entered (see the note on self-recursion in
   *  [[SpatialPipeline.analyzeRoutine]]). */
  def env(active: Set[RoutinePtr] = Set.empty): SpatialTyping.Env =
    SpatialTyping.Env(spaces = spaces, paths = paths, opaque = pathLens,
                      lenv = SpatialEnv(routines = routines, active = active))

  /** the cost environment over the SAME facts — `withRoutines` keeps the two routine tables
   *  (`SpatialCost.Env.routines` and the one inside `facts.lenv`) from drifting apart.
   *
   *  THIS FORM HAS NO DECORATED ANALYSIS, so every per-node type query inside `SpatialCost` is a FRESH
   *  `SpatialTyping.infer` and every law/spatial refinement the decorated analysis made is thrown away
   *.  Use [[costEnvFor]] wherever a decorated analysis exists — which is everywhere
   *  in this pipeline. */
  def costEnv: SpatialCost.Env = SpatialCost.Env(facts = env()).withRoutines(routines)
  /** the cost environment THAT CONSUMES THE DECORATED, `NodeId`-INDEXED ANALYSIS. */
  def costEnvFor(d: SpatialAnalysis): SpatialCost.Env = costEnv.withDecorated(d)

  def restrictingSpaces: Map[SpaceMention, SpatialType] =
    spaces.filter((_, t) => !SpatialAnnotations.admitsEverything(t))
  def restrictingLens: Map[PathRef, LenBounds] =
    pathLens.filter((_, k) => !SpatialAnnotations.admitsEveryLength(k))
  /** does any annotation exclude an input?  If not, every fact derived under it is UNCONDITIONAL. */
  def restrictsInput: Boolean = restrictingSpaces.nonEmpty || paths.nonEmpty || restrictingLens.nonEmpty
  def scope: FactScope =
    if restrictsInput then FactScope.Conditional(restrictingSpaces, paths, restrictingLens)
    else FactScope.Unconditional

  def withRoutines(rc: PartialFunction[RoutinePtr, Routine]): SpatialAnnotations = copy(routines = rc)
  def withSpace(kv: (SpaceMention, SpatialType)): SpatialAnnotations = copy(spaces = spaces + kv)
  def withPathLen(kv: (PathRef, LenBounds)): SpatialAnnotations = copy(pathLens = pathLens + kv)
  def show: String = scope.show

object SpatialAnnotations:
  /** NO assumption about any input: every derived fact is unconditional. */
  def open(rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): SpatialAnnotations =
    SpatialAnnotations(routines = rc)
  /** the cheap setting (`SpatialConfig.cheap`) — for a hook on a hot compilation path */
  def cheap(rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): SpatialAnnotations =
    SpatialAnnotations(routines = rc, config = SpatialConfig.cheap)
  /** the PURELY SPATIAL setting: no `Routine.optimized`, hence no compile-time evaluation at all */
  def spatialOnly(rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): SpatialAnnotations =
    SpatialAnnotations(routines = rc, ordinaryLower = false)

  /** `t` excludes no concrete space.  Decided with the SOUND-BUT-INCOMPLETE order, so the answer may
   *  be `false` for a type that in truth admits everything — which errs towards calling a rewrite
   *  CONDITIONAL, i.e. towards the guarded artifact.  The other direction would be the unsafe one. */
  private[morkl] def admitsEverything(t: SpatialType): Boolean =
    !t.uninhabited && SpatialType.leq(SpatialType.top, t)
  private[morkl] def admitsEveryLength(k: Lower.LenBounds): Boolean =
    !k.isEmpty && k.lo <= 0L && k.hi >= Lower.LenBounds.INF

/** WHOSE INPUTS a set of facts is about.  `Unconditional` facts hold for every input the routine
 *  accepts; `Conditional` facts hold only for inputs satisfying all three channels. */
enum FactScope:
  case Unconditional
  case Conditional(spaces: Map[SpaceMention, SpatialType],
                   paths: Map[PathRef, PathValue],
                   pathLens: Map[PathRef, Lower.LenBounds])
  def conditional: Boolean = this match
    case Unconditional => false
    case Conditional(_, _, _) => true
  def show: String = this match
    case Unconditional => "UNCONDITIONAL (no input annotation restricts the input)"
    case Conditional(s, p, l) =>
      "CONDITIONAL on " + (s.keys.map(m => s"S\"${m.s}\"") ++ p.keys.map(r => s"P\"${r.s}\"=const") ++
                           l.keys.map(r => s"P\"${r.s}\":len")).mkString(", ")

// ==================================================================================================
// 2.  WHAT THE PIPELINE DID
// ==================================================================================================

/** One rewrite the pipeline performed, with the position it happened at and enough detail to check
 *  it.  This is the audit trail: an artifact that claims to differ from the unanalysed program has to
 *  say WHERE and WHY. */
enum Rewrite:
  /** the decorated analysis proved this occurrence denotes `∅` — the whole computation goes */
  case EliminateEmpty(at: NodeId, subterm: String, nodes: Int)
  /** the reduced product pins this occurrence to exactly one concrete space */
  case ConstantFold(at: NodeId, subterm: String, paths: Int, nodes: Int)
  /** a bounded self-recursion became a Call-free residual (whispers §6) */
  case Residualise(routine: RoutinePtr, levels: Int, measureBound: Long, inputMaxLen: Long)
  /** an `Iteration` over a PROVED head set became an explicit union — no dynamic group dispatch */
  case UnrollHeads(at: NodeId, heads: Vector[PathItem])
  /** every path shares this spine, so the backend focuses through it once */
  case Prefocus(prefix: PathValue)
  /** the ordinary `Lower` rule list, run on the spatially rewritten body */
  case OrdinaryLower(before: Int, after: Int)
  /** THE RELATIONAL FRONTIER PROVED THE RESULT IS AN OPERAND (or ∅): a ring node whose case set is a
   *  singleton is not a cost verdict, it is a semantic one — see [[SpatialPipeline.frontierEdits]] */
  case FrontierIdentity(at: NodeId, op: String, side: String)
  /** an `Iteration` over a source with exactly ONE head is a SUBSTITUTION, not a loop */
  case IterationSubstitute(at: NodeId, head: PathItem)
  /** the source has no headed path, or the body is provably ∅: the loop yields ∅ */
  case IterationDrop(at: NodeId, why: String)
  /** the shape PROVES no path of the source starts with this prefix, so the `Unwrap` is ∅ */
  case UnwrapAbsent(at: NodeId, prefix: List[PathItem])
  /** the window provably covers the whole space, whatever its size: `Range` is the identity */
  case RangeIdentity(at: NodeId, why: String)
  def show: String = this match
    case FrontierIdentity(at, op, side) => s"frontier-identity at ${at.show}: $op = $side"
    case IterationSubstitute(at, h) => s"iteration-substitute at ${at.show}: the one head is `$h`"
    case IterationDrop(at, why) => s"iteration-drop at ${at.show}: $why"
    case UnwrapAbsent(at, p) => s"unwrap-absent at ${at.show}: prefix ${p.mkString(".")} is PROVED absent"
    case RangeIdentity(at, why) => s"range-identity at ${at.show}: $why"
    case EliminateEmpty(at, s, n) => s"eliminate-empty at ${at.show}: $n nodes ($s)"
    case ConstantFold(at, s, p, n) => s"constant-fold at ${at.show}: $n nodes -> $p paths ($s)"
    case Residualise(r, k, mb, l) => s"residualise ${r.s}: $k levels (measure bound $mb, input maxLen $l), Call-free"
    case UnrollHeads(at, hs) => s"unroll-heads at ${at.show}: ${hs.mkString(",")}"
    case Prefocus(p) => s"zipper pre-focus on ${p.show}"
    case OrdinaryLower(a, b) => s"ordinary Lower rules: $a -> $b nodes"

// ==================================================================================================
// 3.  STAGE 1 RESULT
// ==================================================================================================

/** THE ROUTINE-LEVEL ANALYSIS: the decorated per-node analysis, plus the scope of its facts, plus the
 *  backend-facing candidates it licenses.
 *
 *  ==WHY NOT THE NAME `SpatialAnalysis`==
 *  The review sketches `analyzeRoutine(r, ann): SpatialAnalysis`.  `SpatialAnalysis` is now the
 *  DECORATED PER-NODE analysis of one `Space` (SpatialAnalysis.scala) — the answer to the review
 *  finding 4 — and it carries no routine, no annotations and no scope, so it cannot be the return type
 *  of a routine-level query without either duplicating it or lying about what it contains.  This type
 *  WRAPS it: `decorated` IS that value, unchanged, and every projection here is a projection of it
 *  rather than a second inference. */
final case class RoutineAnalysis(routine: Routine,
                                 annotations: SpatialAnnotations,
                                 decorated: SpatialAnalysis,
                                 scope: FactScope,
                                 facts: Vector[Fact],
                                 candidates: Vector[SpecializationCandidate],
                                 nodeCandidates: Map[NodeId, Vector[SpecializationCandidate]],
                                 notes: Vector[String]):
  /** the inferred input→output spatial type of the routine */
  def result: SpatialType = decorated.root
  def unconditional: Boolean = !scope.conditional
  /** FALSE means the ANNOTATIONS ARE UNSATISFIABLE (or a transfer is unsound): the product reduced to
   *  the explicit bottom, whose γ is empty.  Every ∀-input claim is then vacuously true, so NO
   *  rewrite may be derived from it — [[SpatialPipeline.optimizeGuarded]] refuses. */
  def consistent: Boolean = !decorated.root.uninhabited
  def factsAt(id: NodeId): Vector[Fact] = decorated.factsAt(id)
  def at(id: NodeId): Option[NodeAnalysis] = decorated.at(id)
  /** the per-depth prefix profile of the result, when the two components are consistent */
  def profile: Option[PrefixProfile] = SpatialFacts.profile(result, annotations.factConfig).toOption

  /** THE COST ENVIRONMENT THIS ANALYSIS LICENSES.  It carries `decorated`, so `SpatialCost` reads every
   *  per-node type out of the analysis that already ran — law refinements and per-node spatial
   *  refinements included — instead of starting a fresh `SpatialTyping.infer` traversal and discarding
   *  them (the requirement: "Life tightens cardinality from 5,785 to 45 without changing its predicted
   *  work"). */
  def costEnv: SpatialCost.Env = annotations.costEnvFor(decorated)

  /** every executable's predicted warm interval over the SAME facts, CONSUMING the
   *  decorated result.  The form is `AsGiven`: this is whatever body the analysis was run on — use
   *  [[SpatialPipeline.costOfOptimized]] / [[SpatialPipeline.costOfResidual]] for a statement about what
   *  actually runs. */
  def backendCost: Map[Backend, CostReport] = SpatialPipeline.priceAll(routine, annotations)
  /** the same, as a vector in backend order */
  def backendReports: Vector[CostReport] = Backend.values.toVector.map(backendCost)
  def show: String =
    (s"routine ${routine.name.s}  ${scope.show}" +:
     s"  result ${result.show}" +:
     s"  facts  ${facts.map(_.show).mkString(", ")}" +:
     candidates.map(c => s"  candidate ${c.show}") ++: notes.map(n => s"  ! $n")).mkString("\n")

// ==================================================================================================
// 4.  STAGE 2 RESULT — THE SAFE ARTIFACT
// ==================================================================================================

/** A SPECIALISATION AND ITS FALLBACK.  This is the artifact the review asks for: "conditional
 *  facts must produce a guarded version plus fallback, or rewrite only callers already proved to
 *  satisfy the precondition".
 *
 *  `residual` is valid where the precondition holds; `fallback` is valid everywhere (it is the
 *  ORDINARY optimizer's output, so choosing it costs nothing relative to not having run this pipeline
 *  at all).  [[choose]] is the dispatcher, and it decides with FULL γ-membership
 *  (`SpatialTyping.accepts`) rather than the weaker `withinEnvelope`, because a dispatcher that admits
 *  an argument outside the precondition installs a conditionally-valid body on an input that violates
 *  the condition. */
final case class GuardedRoutine(original: Routine,
                                residual: Routine,
                                fallback: Routine,
                                spacePrecondition: Map[SpaceMention, SpatialType],
                                pathValuePrecondition: Map[PathRef, PathValue],
                                pathLenPrecondition: Map[PathRef, Lower.LenBounds],
                                facts: Vector[Fact],
                                applied: Vector[Rewrite],
                                candidates: Vector[SpecializationCandidate],
                                notes: Vector[String]):
  /** is this artifact conditional at all?  `false` means `residual` may replace `original` outright. */
  def guarded: Boolean =
    spacePrecondition.nonEmpty || pathValuePrecondition.nonEmpty || pathLenPrecondition.nonEmpty
  /** did the pipeline actually change anything relative to the ordinary optimizer? */
  def changed: Boolean = residual.body != fallback.body

  def applicableTo(spaces: Map[SpaceMention, SpaceValue],
                   paths: Map[PathRef, PathValue] = Map.empty): Boolean =
    spacePrecondition.forall((m, t) => spaces.get(m).exists(v => SpatialTyping.accepts(v, t))) &&
      pathValuePrecondition.forall((r, v) => paths.get(r).contains(v)) &&
      pathLenPrecondition.forall { (r, k) =>
        paths.get(r).exists(v => !k.isEmpty && k.lo <= v.items.length && v.items.length <= k.hi)
      }

  /** THE DISPATCHER.  Never returns `residual` for an input the precondition excludes. */
  def choose(spaces: Map[SpaceMention, SpaceValue],
             paths: Map[PathRef, PathValue] = Map.empty): Routine =
    if applicableTo(spaces, paths) then residual else fallback

  /** THE `SpatialTyping.SpecializedRoutine` VIEW — the `optimize(...): SpecializedRoutine`.
   *
   *  `SpecializedRoutine.precondition` is a `Map[SpaceMention, SpatialType]` and has nowhere to put a
   *  PATH precondition.  Handing back the conditional residual with only the space half of the
   *  precondition would produce an artifact whose `applicableTo` answers `true` for inputs the
   *  condition excludes — precisely the failure this file exists to prevent.  So when a path
   *  precondition is present this view DEGRADES to the unconditional fallback (with no facts
   *  attached, since the facts were derived under the condition), and the full-fidelity artifact stays
   *  reachable as `this`.  See the report's API request. */
  def asSpecialized: SpatialTyping.SpecializedRoutine =
    if pathValuePrecondition.isEmpty && pathLenPrecondition.isEmpty then
      SpatialTyping.SpecializedRoutine(spacePrecondition, residual, facts)
    else SpatialTyping.SpecializedRoutine(Map.empty, fallback, Vector.empty)

  def pathPreconditionRepresentable: Boolean =
    pathValuePrecondition.isEmpty && pathLenPrecondition.isEmpty

  def show: String =
    val head = s"${original.name.s}: ${if guarded then "GUARDED" else "unconditional"}" +
               (if changed then "" else " (no change)")
    (head +: applied.map(r => "  " + r.show) ++: notes.map(n => "  ! " + n)).mkString("\n")

// ==================================================================================================
// 5.  STAGE 3 RESULT
// ==================================================================================================

/** ONE BACKEND'S LOWERED FORM of a specialisation, with the candidates that were CONSUMED (not merely
 *  reported) and the predicted interval for that executable.
 *
 *  `graph` is present exactly for [[Backend.Graph]]: `transpile` + the graph `optimize` are the real
 *  lowering step for `execT`.  The other three executables interpret a `Space` directly, so their
 *  lowered form IS `routine.body` after the candidate rewrites. */
final case class LoweredRoutine(backend: Backend,
                                routine: Routine,
                                graph: Option[RecursiveOpGraph],
                                specialized: SpatialTyping.SpecializedRoutine,
                                consumed: Vector[SpatialSpecialization],
                                applied: Vector[Rewrite],
                                offered: Vector[SpecializationCandidate],
                                cost: EventBounds,
                                notes: Vector[String]):
  def precondition: Map[SpaceMention, SpatialType] = specialized.precondition
  def body: Space = routine.body
  def callFree: Boolean = SpatialPipeline.isCallFree(routine.body)
  def nodes: Int = SpatialPipeline.nodeCount(routine.body)
  def graphNodes: Option[Int] = graph.map(SpatialPipeline.graphNodeCount)
  def show: String =
    val head = f"${backend.slug}%-9s ${nodes}%5d nodes${graphNodes.map(n => f" / $n%4d graph slots").getOrElse("")}" +
               s"  consumed ${if consumed.isEmpty then "-" else consumed.map(_.show).mkString(", ")}"
    (head +: notes.map(n => "  ! " + n)).mkString("\n")

// ==================================================================================================
// 6.  THE PIPELINE
// ==================================================================================================

object SpatialPipeline:
  import Lower.LenBounds

  // ------------------------------------------------------------------------------------------------
  // STAGE 1 — analyse
  // ------------------------------------------------------------------------------------------------

  /** THE ANALYSIS.  One decorated traversal of the routine body under the declared inputs, and every
   *  consumer downstream is a projection of it.
   *
   *  ==SELF-RECURSION==
   *  The routine's own name is NOT added to the `active` set.  `SpatialTyping.goShape` already adds a
   *  callee to `active` before descending, so a self-recursive routine is inlined EXACTLY ONE level
   *  and the inner self-call degrades to ⊤ — terminating and sound.  Marking the routine active up
   *  front (whispers §2 does) only throws that level of precision away; the certified-summary path it
   *  is worried about is `SpatialRecursion.residualise`, which stage 2 calls separately and which
   *  never goes through this transfer at all.  Set [[SpatialAnnotations.selfActive]] for the
   *  CONSERVATIVE reading, which is the one `SpatialCheck.report` uses for a verdict — turn it on when
   *  the pipeline's premises must be identical to the checker's. */
  def analyzeRoutine(r: Routine, ann: SpatialAnnotations): RoutineAnalysis =
    val active = if ann.selfActive then Set(r.name) else Set.empty[RoutinePtr]
    val decorated = SpatialAnalysis.of(r.body, ann.env(active), ann.config)
    val notes = Vector.newBuilder[String]
    notes ++= decorated.notes
    val root = decorated.root
    if root.uninhabited then
      notes += "the reduced product is BOTTOM: the declared input types are unsatisfiable (or a " +
               "transfer is unsound).  No rewrite may be derived from a vacuous ∀-input claim."
    val cands = if root.uninhabited then Vector.empty else SpatialFacts.specializations(root, ann.factConfig)
    val perNode =
      if root.uninhabited then Map.empty[NodeId, Vector[SpecializationCandidate]]
      else decorated.nodes.iterator
        .map(n => n.id -> SpatialFacts.specializations(n.result, ann.factConfig))
        .filter(_._2.nonEmpty).toMap
    SpatialFacts.contradiction(root, ann.factConfig).foreach(c => notes += c.show)
    RoutineAnalysis(r, ann, decorated, ann.scope, decorated.rootFacts, cands, perNode, notes.result())

  /** the same, for a bare term (no routine): the entry point a term-level consumer wants */
  def analyzeTerm(s: Space, ann: SpatialAnnotations): RoutineAnalysis =
    analyzeRoutine(Routine(RoutinePtr("#term#"), Vector.empty, Vector.empty, s), ann)

  // ------------------------------------------------------------------------------------------------
  // STAGE 2 — optimize
  // ------------------------------------------------------------------------------------------------

  /** the signature.  The result is the SAFE artifact: a `SpecializedRoutine` whose
   *  precondition is EMPTY exactly when the facts were unconditional.  Use [[optimizeGuarded]] to get
   *  the fallback as well (and see [[GuardedRoutine.asSpecialized]] for the one case this view cannot
   *  represent). */
  def optimize(r: Routine, analysis: RoutineAnalysis): SpatialTyping.SpecializedRoutine =
    optimizeGuarded(r, analysis).asSpecialized

  /** THE OPTIMIZER.  Three consumers of the analysis, then the ordinary rule list:
   *
   *   1. BOUNDED SELF-RECURSION → a Call-free residual (`SpatialRecursion.residualise`, whispers §6).
   *      Tried first because it replaces the whole body, which would invalidate every [[NodeId]].
   *   2. PER-NODE ELIMINATION: an occurrence the reduced product proves empty becomes `Space.Empty`.
   *      This is strictly stronger than `SpatialTypes.eliminate` (histogram only) and than
   *      `Lower.SizeEmpty` (syntactic), and it is driven by the DECORATED analysis, so a subterm is
   *      judged under the binder environment it actually sits in.
   *   3. PER-NODE CONSTANT FOLDING: an occurrence whose reduced product pins exactly one concrete
   *      space becomes that `Literal`.  No evaluation: the value comes out of the shape domain and is
   *      then re-checked against full γ-membership.
   *   4. the ordinary `Lower` rule list (`Routine.optimized`), which propagates the `Empty`s and the
   *      new `Literal`s through their parents.
   *
   *  The FALLBACK is `original.optimized` — the same rule list with no spatial input — so a guarded
   *  artifact never trades away the optimization the program would have had anyway. */
  def optimizeGuarded(r: Routine, analysis: RoutineAnalysis): GuardedRoutine =
    given PartialFunction[RoutinePtr, Routine] = analysis.annotations.routines
    val ann = analysis.annotations
    val notes = Vector.newBuilder[String]
    notes ++= analysis.notes
    // THE FALLBACK: the artifact the ordinary pipeline would install with NO SPATIAL INPUT AT ALL, so
    // choosing it never costs the program an optimization it would otherwise have had.  It is
    // `optimizedPlain` and not `optimized` because `optimized` now runs the unconditional spatial tier
    // itself (`SpatialHook`): taking that as the baseline would make `changed` mean "beyond the
    // unconditional tier" and would pay for a second decorated analysis here.  The residual gets the
    // hook anyway, through stage 4 below.  With `ordinaryLower = false` there is no ordinary pass to
    // run, so the fallback is the original.
    val fallback = if ann.ordinaryLower then r.optimizedPlain else r
    if !ann.ordinaryLower then
      notes += "ordinaryLower = false: the `Lower` rule list did NOT run, so the residual is the " +
               "purely spatial rewrite and the fallback is the unmodified routine"

    def unchanged(why: String): GuardedRoutine =
      notes += why
      GuardedRoutine(r, fallback, fallback, Map.empty, Map.empty, Map.empty, Vector.empty,
                     Vector.empty, analysis.candidates, notes.result())

    if !analysis.consistent then
      unchanged("refusing to rewrite: the analysis reduced to bottom, so every ∀-input claim it " +
                "licenses is vacuous")
    else
      val applied = Vector.newBuilder[Rewrite]

      // ---- 1. bounded self-recursion -----------------------------------------------------------
      val recursive = residualiseBounded(r, ann)
      val (afterRec, recAnalysis) = recursive match
        case Right(b) =>
          applied += Rewrite.Residualise(b.routine, b.maxCallDepth, b.measureBound, b.inputMaxLen)
          val rr = b.residual
          val re =
            if !ann.refineAfterResidual then None
            else if nodeCount(rr.body) > ann.config.maxNodes then
              notes += s"the residual has ${nodeCount(rr.body)} nodes, past the ${ann.config.maxNodes} " +
                       "recording budget: per-node rewrites are skipped on it"
              None
            else Some(analyzeRoutine(rr, ann))
          (rr, re)
        case Left(why) =>
          notes += s"no bounded-recursion residual: $why"
          (r, Some(analysis))

      // ---- 2 + 3. per-node elimination and constant folding -------------------------------------
      val base = recAnalysis match
        case Some(a) if a.consistent =>
          val (b2, rs) = rewriteNodes(afterRec.body, a.decorated, ann)
          applied ++= rs
          Routine(afterRec.name, afterRec.refs, afterRec.mentions, b2)
        case Some(_) =>
          notes += "the residual's own analysis reduced to bottom; no per-node rewrite applied to it"
          afterRec
        case None => afterRec

      // ---- 4. the ordinary rule list, on the spatially rewritten body ---------------------------
      val before = nodeCount(base.body)
      val opt = if ann.ordinaryLower then base.optimized else base
      if nodeCount(opt.body) != before then applied += Rewrite.OrdinaryLower(before, nodeCount(opt.body))

      val rewrites = applied.result()
      if rewrites.isEmpty then
        unchanged("the analysis licensed no rewrite this pipeline can perform")
      else
        val (sp, pv, pl) = analysis.scope match
          case FactScope.Unconditional => (Map.empty[SpaceMention, SpatialType],
                                           Map.empty[PathRef, PathValue], Map.empty[PathRef, LenBounds])
          case FactScope.Conditional(s, p, l) => (s, p, l)
        if pv.nonEmpty || pl.nonEmpty then
          notes += "the precondition has a PATH channel, which `SpatialTyping.SpecializedRoutine` " +
                   "cannot represent: `asSpecialized` therefore degrades to the fallback (see the " +
                   "scaladoc), while `choose` still dispatches on all three channels"
        GuardedRoutine(r, opt, fallback, sp, pv, pl, analysis.facts, rewrites,
                       analysis.candidates, notes.result())

  /** whispers §6's `specializeBoundedRecursion`, with its `require(b.callFree)` replaced by a checked
   *  `Left`: a proof obligation that fails in a pipeline is a REASON, not an exception. */
  def residualiseBounded(r: Routine, ann: SpatialAnnotations)
      : Either[String, SpatialRecursion.BoundedRecursion] =
    if !ann.routines.isDefinedAt(r.name) then
      Left(s"the routine table does not contain ${r.name.s}, so the self-call cannot be resolved")
    else if ann.routines(r.name).body != r.body then
      Left(s"the routine table's ${r.name.s} is not the routine being optimized")
    else
      SpatialRecursion.residualise(r.name, ann.routines, spaces = ann.spaces,
                                   paths = ann.pathLens, limits = ann.limits) match
        case SpatialRecursion.DepthBound.NoBound(why) => Left(why)
        case SpatialRecursion.DepthBound.Bounded(b) =>
          if !b.callFree then Left("the residual still contains a Call")
          else Right(b)

  // ------------------------------------------------------------------------------------------------
  // STAGE 3 — lower
  // ------------------------------------------------------------------------------------------------

  /** the signature.  The precondition travels ON the artifact, so this can rebuild
   *  the analysis environment from it; what it cannot recover is the ROUTINE TABLE (a
   *  `SpecializedRoutine` does not carry one), so `Call` nodes are analysed as ⊤ here.  Pass the
   *  annotations through [[lower]]'s three-argument form to keep the table. */
  def lower(s: SpatialTyping.SpecializedRoutine, backend: Backend): LoweredRoutine =
    lower(s, backend, SpatialAnnotations(spaces = s.precondition))

  def lower(s: SpatialTyping.SpecializedRoutine, backend: Backend,
            ann: SpatialAnnotations): LoweredRoutine =
    lowerRoutine(s.residual, s, backend, ann)

  /** the full-fidelity entry: the guarded artifact keeps the fallback, the audit trail and all three
   *  precondition channels, and lowering only ever touches the RESIDUAL. */
  def lower(g: GuardedRoutine, backend: Backend, ann: SpatialAnnotations): LoweredRoutine =
    lower(g, backend, ann, analyzeRoutine(g.residual, ann))

  /** the same with the RESIDUAL'S analysis supplied.  Lowering the same artifact onto several backends
   *  would otherwise repeat one decorated analysis per backend, which on a big cornerstone is the
   *  dominant cost (measured: 40 s for `puzzle15`, four times over). */
  def lower(g: GuardedRoutine, backend: Backend, ann: SpatialAnnotations,
            residualAnalysis: RoutineAnalysis): LoweredRoutine =
    require(residualAnalysis.routine.body == g.residual.body,
            "the supplied analysis is not the residual's")
    val l = lowerRoutine(g.residual, g.asSpecialized, backend, ann, residualAnalysis)
    l.copy(applied = g.applied ++ l.applied, notes = g.notes ++ l.notes)

  private def lowerRoutine(r: Routine, spec: SpatialTyping.SpecializedRoutine, backend: Backend,
                           ann: SpatialAnnotations): LoweredRoutine =
    lowerRoutine(r, spec, backend, ann, analyzeRoutine(r, ann))

  private def lowerRoutine(r: Routine, spec: SpatialTyping.SpecializedRoutine, backend: Backend,
                           ann: SpatialAnnotations, a: RoutineAnalysis): LoweredRoutine =
    val notes = Vector.newBuilder[String]
    val consumed = Vector.newBuilder[SpatialSpecialization]
    val applied = Vector.newBuilder[Rewrite]
    val offered = a.candidates ++ a.nodeCandidates.valuesIterator.flatten
    var body = r.body

    if !a.consistent then
      notes += "the residual's analysis reduced to bottom: no candidate is consumed"
    else backend match
      // -- GRAPH: exact constant folding, then transpile + the graph optimizer -------------------
      case Backend.Graph =>
        val (b2, rs) = foldExactNodes(body, a.decorated, ann)
        val rootFold = a.candidates.collectFirst {
          case SpecializationCandidate(g: SpatialSpecialization.GraphConstantFold, _, _) => g
        }
        if rs.nonEmpty then
          body = b2
          applied ++= rs
          rootFold.foreach(consumed += _)
          if rootFold.isEmpty then
            notes += "a PROPER SUBTERM folded to a constant; the root itself is not pinned, so the " +
                     "consumed candidate is the per-node one recorded in `applied`"
        else
          // stage 2 may already have folded it — the candidate is still CONSUMED, by that stage
          (rootFold, body) match
            case (Some(g @ SpatialSpecialization.GraphConstantFold(v)), Space.Literal(w)) if v == w =>
              consumed += g
              notes += "the root constant fold was already performed by stage 2 (`optimize`)"
            case _ => ()

      // -- TRIE: bounded unrolling of an iteration over a PROVED head set ------------------------
      case Backend.Trie =>
        val (b2, rs) = unrollProvedHeads(body, a, ann)
        if rs.nonEmpty then
          body = b2
          applied ++= rs
          a.candidates.collect { case SpecializationCandidate(t: SpatialSpecialization.TrieUnroll, _, _) => t }
            .foreach(consumed += _)

      // -- ZIPPER: pre-focus through the common spine --------------------------------------------
      case Backend.Zipper =>
        val cp = SpatialFacts.commonPrefix(a.result, ann.factConfig)
        // an ALREADY CONCRETE body lifts to `SpaceZipper.Lit`, whose `materialize` returns the trie
        // without a single cursor read.  Pre-focusing that is a pure loss (measured: 0 -> 7
        // `ZipperCursorRead`), so the candidate is only consumed where there is fusion to steer.
        val concrete = body match
          case Space.Literal(_) | Space.Empty => true
          case _ => false
        if concrete && cp.nonTrivial then
          notes += "the body is already a concrete literal, which the zipper lifts to `Lit` and " +
                   "materialises with no cursor reads at all: pre-focusing it would only add work"
        if cp.nonTrivial && !concrete then
          body = Space.Wrap(Space.Unwrap(body, Path.Constant(cp.path)), Path.Constant(cp.path))
          applied += Rewrite.Prefocus(cp.path)
          consumed += SpatialSpecialization.ZipperPrefocus(cp.path)
          if !cp.definitelyPresent then
            notes += "the spine claim is ∀-path and therefore VACUOUS on ∅: the rewrite is still an " +
                     "identity, but a backend may not assume the spine exists"

      // -- REFERENCE: the reference interpreter has no structural candidate to consume ------------
      case Backend.Reference =>
        notes += "the reference evaluator interprets the `Space` directly and exposes no structural " +
                 "candidate; its lowered form is the specialised body itself"

    val lowered = Routine(r.name, r.refs, r.mentions, body)
    val graph =
      if backend != Backend.Graph then None
      else
        // `morkl.optimize` is the GRAPH optimizer (MORKL.scala:1388) — qualified because this object
        // also has an `optimize`, which is the pipeline's stage 2.
        try Some(morkl.optimize(transpile(lowered)))
        catch
          case e: NotImplementedError =>
            notes += s"transpile cannot lower this term to an operation graph: ${e.getMessage}"
            None
          case e: MatchError =>
            notes += s"transpile has no operation-graph node for a subterm of this program: ${e.getMessage.take(90)}"
            None
    // COST CONSUMES THE DECORATED ANALYSIS whenever the lowering left the body's
    // positions intact.  A candidate rewrite invalidates every `NodeId`, and `SpatialCost` refuses a
    // position whose subterm does not match, so in that case the decorated input is dropped explicitly
    // rather than silently ignored — and it is SAID, because it costs precision.
    val cost = price(Routine(r.name, r.refs, r.mentions, body), ann, backend, graph).bounds
    LoweredRoutine(backend, lowered, graph, spec, consumed.result(), applied.result(),
                   offered.distinct, cost, notes.result())

  /** the whole flow, for the caller who just wants the answer */
  def run(r: Routine, ann: SpatialAnnotations, backend: Backend): LoweredRoutine =
    val a = analyzeRoutine(r, ann)
    lower(optimizeGuarded(r, a), backend, ann)

  /** every backend's lowered form over the SAME analysis — ONE decorated analysis of the routine and
   *  ONE of its residual, shared by all four lowerings */
  def runAll(r: Routine, ann: SpatialAnnotations): Map[Backend, LoweredRoutine] =
    val a = analyzeRoutine(r, ann)
    val g = optimizeGuarded(r, a)
    val ra = if g.residual.body == r.body then a else analyzeRoutine(g.residual, ann)
    Backend.values.iterator.map(b => b -> lower(g, b, ann, ra)).toMap

  // ------------------------------------------------------------------------------------------------
  // COST ON THE FORM THAT ACTUALLY RUNS  (the user's third steer; the second half)
  // ------------------------------------------------------------------------------------------------

  /** THE COST OF `Routine.optimized`'s BODY — the spatial hook plus the ordinary `Lower` rule list.
   *
   *  This, not the definitional term, is what a cost estimate should describe: one runs the optimized
   *  backend rather than the reference, and the same asymmetry applies to the program.  The analysis is
   *  re-run on the OPTIMIZED body so the decorated result addresses the term being priced. */
  def costOfOptimized(r: Routine, ann: SpatialAnnotations): Map[Backend, CostReport] =
    given PartialFunction[RoutinePtr, Routine] = ann.routines
    priceAll(r.optimized, ann)

  /** ONE BACKEND'S RESOURCE BOUNDS for a routine body over the annotations' declared inputs — the A4
   *  abstract interpretation of the counted event semantics (`SpatialCostSemantics`).  The graph
   *  backend is priced on the operation graph `execT` runs when one is given or can be built; when the
   *  transpiler refuses the body the term-level graph rules stand in and the report says so. */
  def price(r: Routine, ann: SpatialAnnotations, backend: Backend,
            graph: Option[RecursiveOpGraph] = None): CostReport =
    priceInputs(r, ann.costInputs, ann.routines, backend, graph)

  /** the same over explicit inputs — VALUES for a closed program, summaries otherwise */
  def priceInputs(r: Routine, inputs: CostSem.Inputs, routines: PartialFunction[RoutinePtr, Routine], backend: Backend,
                  graph: Option[RecursiveOpGraph] = None): CostReport =
    backend match
      case Backend.Graph =>
        val g = graph.orElse(try Some(morkl.optimize(transpile(r))) catch case scala.util.control.NonFatal(_) => None)
        // the callees' graphs, as execT's `index` finds them: transpiled on demand from the routine table
        val memo = scala.collection.mutable.HashMap.empty[String, Option[RecursiveOpGraph]]
        val index: PartialFunction[String, RecursiveOpGraph] = new PartialFunction[String, RecursiveOpGraph]:
          private def get(name: String): Option[RecursiveOpGraph] = memo.getOrElseUpdate(name,
            if routines.isDefinedAt(RoutinePtr(name)) then (try Some(transpile(routines(RoutinePtr(name)))) catch case scala.util.control.NonFatal(_) => None) else None)
          def isDefinedAt(name: String): Boolean = get(name).isDefined
          def apply(name: String): RecursiveOpGraph = get(name).get
        g match
          case Some(og) => CostSem.analyzeGraph(og, inputs, index)
          case None =>
            val rep = CostSem.analyze(r.body, inputs, Backend.Graph, routines)
            rep.copy(notes = rep.notes :+ "no operation graph could be built for this body: priced with the term-level graph rules")
      case b => CostSem.analyze(r.body, inputs, b, routines)

  def priceAll(r: Routine, ann: SpatialAnnotations): Map[Backend, CostReport] =
    Backend.values.iterator.map(b => b -> price(r, ann, b)).toMap

  /** THE COST OF AN `SC.reduce` RESIDUAL, where the supercompiler produces one.  `None` when it does
   *  not change the term (then `costOfOptimized` is the right answer and this would be a second name for
   *  it) or when it raises. */
  def costOfResidual(r: Routine, ann: SpatialAnnotations,
                     cap: Int = 100000): Option[(Space, Map[Backend, CostReport])] =
    given PartialFunction[RoutinePtr, Routine] = ann.routines
    val base = r.optimized.body
    val res = try SC.reduce(base, cap) catch case scala.util.control.NonFatal(_) => base
    if res == base then None
    else Some((res, priceAll(Routine(r.name, r.refs, r.mentions, res), ann)))

  /** THE DEFINITIONAL ESTIMATE, LABELLED AS SUCH.  Kept reachable because sometimes there is nothing
   *  else — a term with no routine, a body the optimizer refuses — but its `CostForm` says, in the
   *  report, that it is not a prediction about what runs. */
  def costOfDefinitional(body: Space, ann: SpatialAnnotations): Map[Backend, CostReport] =
    priceAll(Routine(RoutinePtr("#definitional"), Vector.empty, ann.spaces.keys.toVector, body), ann)

  // ------------------------------------------------------------------------------------------------
  // BACKEND COMPARISON  —  AUTOMATIC SELECTION IS A NON-GOAL
  // ------------------------------------------------------------------------------------------------

  /** ONE BACKEND'S PER-COMPONENT INTERVAL at a valuation, plus the symbolic form it came from. */
  final case class BackendBracket(backend: Backend,
                                  numeric: Map[EffortComponent, (Double, Double)],
                                  report: CostReport,
                                  touchModelled: Boolean):
    def show: String =
      val cells = BackendComparison.Components.map { c =>
        val (lo, hi) = numeric(c)
        f"${c.toString.toLowerCase}%-7s[${BackendBracket.f(lo)}%10s, ${BackendBracket.f(hi)}%10s]"
      }.mkString("  ")
      f"  ${backend.slug}%-10s $cells${if touchModelled then "  (touch MODELLED)" else ""}"
  object BackendBracket:
    def f(d: Double): String = if d.isInfinite then "inf" else if math.abs(d) >= 1e6 then f"$d%.2e" else f"$d%.0f"

  /** ==============================================================================================
   *  THE BACKEND COMPARISON REPORT.  THERE IS NO `best`.
   *
   *  Picking a backend automatically is a NON-GOAL of this analysis, and the previous API's confidence
   *  was not supportable.  It scored each backend as `work + alloc + rounds + touch` at one valuation
   *  and took an `argmin`.  Four defects, each fatal on its own:
   *
   *   1. THE SUM IS DIMENSIONALLY INCOHERENT.  The four components have four different counted oracles
   *      ([[EffortComponent]]): `work` is AST/trie dispatches and cursor reads, `alloc` is fresh trie
   *      nodes and frames, `rounds` is loop-body entries and fixpoint rounds, `touch` is
   *      `TrieNodeVisit` + `PatriciaVisit`.  Adding a `FixpointRound` to a Patricia node visit has no
   *      meaning; and since `touch` is Θ(n) per merge while `rounds` is O(1), the "four-component
   *      score" was `touch` plus rounding noise on every trie-shaped program.
   *   2. ONLY THE UPPER ENDPOINT WAS COMPARED (`Report.cost` is `interval.hi`), so a backend bracketed
   *      `[1, 1000]` "beat" one bracketed `[900, 1001]`.  [[SpatialCost.Report.bracket]] — which hands
   *      out `(lower, upper)` per component and exists for exactly this — was never called.
   *   3. NO OVERLAP TEST AND NO SYMBOLIC TEST.  `minBy` over `Double`s at ONE valuation, while
   *      [[Sym.dominates]] (which decides the ordering for EVERY assignment with variables ≥ 2) sits
   *      unused in the same tree.
   *   4. IT MINIMISED ACROSS A DECLARED ORACLE GAP.  `ReferenceCost.touchNoOracle` says `eval`'s
   *      `touch` is a MODEL with no counted evidence, and `SpatialCost.analyze` therefore forces that
   *      backend's `touch` LOWER endpoint to 0 — so nothing can ever be proved to dominate the
   *      reference on `touch`.  Declaring the gap and then computing an argmin across it is precisely
   *      the over-confidence.
   *
   *  ==WHAT THIS REPORTS INSTEAD==
   *  Every backend's per-component INTERVAL over the same facts, and a DOMINANCE relation that holds
   *  only when the intervals are disjoint on every component.  `INCOMPARABLE` — the normal answer — is
   *  a result, not a failure: four models of differing fidelity predicting overlapping intervals is
   *  what the evidence supports, and the caller is the one who knows which component it is paying for.
   *  ============================================================================================== */
  final case class BackendComparison(form: CostForm,
                                     brackets: Map[Backend, BackendBracket],
                                     notes: Vector[String]):
    /** `a` dominates `b` iff on EVERY component `a`'s interval lies strictly below `b`'s — the two are
     *  disjoint and `a` is the lower one.  Never true when an endpoint is infinite. */
    def dominates(a: Backend, b: Backend): Boolean =
      a != b && BackendComparison.Components.forall { c =>
        val (_, ahi) = brackets(a).numeric(c)
        val (blo, _) = brackets(b).numeric(c)
        ahi.isFinite && blo.isFinite && ahi < blo
      }
    def dominated: Vector[(Backend, Backend)] =
      for a <- Backend.values.toVector; b <- Backend.values.toVector if dominates(a, b) yield (a, b)
    /** THE ONLY CIRCUMSTANCE under which this API names a backend: it dominates all three others on
     *  all four components.  `None` — the normal answer — means INCOMPARABLE. */
    def unanimous: Option[Backend] =
      Backend.values.find(a => Backend.values.forall(b => a == b || dominates(a, b)))
    def verdict: String = unanimous match
      case Some(b) => s"${b.slug} dominates on every component (disjoint intervals)"
      case None => "INCOMPARABLE — no backend's intervals are disjoint-and-below on every component"
    def show: String =
      (s"backend comparison on ${form.show}: $verdict" +:
       Backend.values.toVector.map(brackets(_).show) ++:
       dominated.map((a, b) => s"  · ${a.slug} < ${b.slug} (all four components disjoint)") ++:
       notes.map("  ! " + _)).mkString("\n")

  object BackendComparison:
    val Components: Vector[EffortComponent] =
      Vector(EffortComponent.Work, EffortComponent.Alloc, EffortComponent.Rounds, EffortComponent.Touch)

  /** EVERY EXECUTABLE'S PER-COMPONENT INTERVAL OVER THE SAME FACTS.  A report, not a choice. */
  def compareBackends(body: Space, ann: SpatialAnnotations, form: CostForm = CostForm.AsGiven): BackendComparison =
    compareReports(priceAll(Routine(RoutinePtr("#compare"), Vector.empty, ann.spaces.keys.toVector, body), ann), form)

  private def compareReports(reports: Map[Backend, CostReport], form: CostForm): BackendComparison =
    def num(i: Ivl): (Double, Double) = (i.lo.toDouble, if i.hi >= Ivl.INF then Double.PositiveInfinity else i.hi.toDouble)
    val brackets = reports.map { (b, r) =>
      // the reference evaluator's `touch` has no counted oracle (its Set internals carry no hooks): the
      // analysis reports it as [0, 0] and nothing can be proved to dominate it there
      b -> BackendBracket(b, BackendComparison.Components.map(c => c -> num(r.component(c))).toMap, r, b == Backend.Reference)
    }
    val notes = Vector(
      "the components are NOT summed: `work`, `alloc`, `rounds` and `touch` have four different " +
      "counted oracles (see EffortComponent) and no common unit, so a scalar score over them is " +
      "meaningless and an argmin over that score is not a backend recommendation.",
      "dominance requires the intervals to be DISJOINT on every component; any overlap is reported " +
      "as INCOMPARABLE rather than resolved by an arbitrary tie-break.",
      "the reference evaluator's `touch` has no counted oracle: it is reported as 0 and nothing can be " +
      "proved to dominate it there") ++
      (if form.describesWhatRuns then Vector.empty
       else Vector(s"priced on ${form.show}; prefer `costOfOptimized` / `costOfResidual` for a " +
                   "statement about what actually runs"))
    BackendComparison(form, brackets, notes)

  /** THE COMPARISON ON THE FORM THAT RUNS: `Routine.optimized`'s body. */
  def compareBackendsOptimized(r: Routine, ann: SpatialAnnotations): BackendComparison =
    compareReports(costOfOptimized(r, ann), CostForm.Optimized)

  // ------------------------------------------------------------------------------------------------
  // THE HOOK FOR THE ORDINARY OPTIMIZER
  // ------------------------------------------------------------------------------------------------

  /** THE HOOK `Routine.optimized` RUNS (MORKL.scala:248-251), as one function.
   *
   *  It consumes ONLY unconditional facts — it is called with no input annotation, so every rewrite it
   *  performs is valid for every input — and it calls NOTHING inside `Routine.optimized`, so composing
   *  it into that method cannot recurse.  The installed edit is one line:
   *
   *  {{{
   *  //  all_forever(Lower.inline(using rc)(body), List(Lower.ConstantOps, ...))
   *      all_forever(Lower.inline(using rc)(SpatialHook.rewrite(body, rc)), List(Lower.ConstantOps, ...))
   *  }}}
   *
   *  Cost: one decorated spatial analysis per `optimized` call, under [[SpatialHook]]'s policy (the
   *  cheap config and a body-size budget).  [[SpatialHook]] owns that policy and the measurements. */
  def unconditionalRewrite(body: Space,
                           rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Space =
    rewriteUnconditional(body, SpatialAnnotations.open(rc))

  def unconditionalRewriteCheap(body: Space,
                                rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Space =
    rewriteUnconditional(body, SpatialAnnotations.cheap(rc))

  /** the rewrite itself.  It goes through [[SpatialAnalysis.of]] rather than [[analyzeRoutine]] on
   *  purpose: the two per-node rewrites need only the DECORATED analysis, while `analyzeRoutine`
   *  additionally runs `SpatialFacts.specializations` at every node — useful to a backend, pure
   *  overhead on a compilation path that will not consume a candidate. */
  private[morkl] def rewriteUnconditional(body: Space, ann: SpatialAnnotations): Space =
    require(!ann.restrictsInput, "unconditionalRewrite must be called with no input annotation")
    val d = SpatialAnalysis.of(body, ann.env(), ann.config)
    if d.root.uninhabited then body else rewriteNodes(body, d, ann)._1

  /** REWRITE ONLY THE CALL SITES ALREADY PROVED TO SATISFY THE PRECONDITION — the review 3's
   *  second option for conditional facts.
   *
   *  A `Call(rp, refs, mentions)` in `host` is redirected to `to` exactly when every mention argument's
   *  own inferred spatial type is BELOW the corresponding precondition entry, so γ of the argument is
   *  contained in γ of the precondition and the residual is valid there.  The test is the sound
   *  incomplete order, so an unproved call site keeps the general routine — the safe direction.  Path
   *  precondition channels are checked against the argument path's constant value / length bound.
   *
   *  `hostEnv` is the environment the ARGUMENT EXPRESSIONS live in, which is the caller's, not the
   *  callee's; it defaults to the callee's annotation environment only because that is right for a
   *  closed host.  Passing the wrong one cannot make an unproved site proved by accident — a mention
   *  with no entry is ⊤ and ⊤ is below almost nothing — but it can lose provable sites. */
  def specialiseProvedCallSites(host: Space, target: RoutinePtr, to: RoutinePtr,
                                g: GuardedRoutine, ann: SpatialAnnotations,
                                hostEnv: SpatialTyping.Env = null): (Space, Int, Int) =
    val henv = if hostEnv == null then ann.env() else hostEnv
    var proved = 0
    var skipped = 0
    val out = subs(host)(spost = {
      case c @ Space.Call(`target`, refs, mentions) =>
        val paramTypes = g.original.mentions.zip(mentions).toMap
        val spaceOk = g.spacePrecondition.forall { (m, t) =>
          paramTypes.get(m).exists(arg => SpatialType.leq(SpatialTyping.infer(arg, henv), t))
        }
        val refMap = g.original.refs.zip(refs).toMap
        val valueOk = g.pathValuePrecondition.forall { (r, v) =>
          refMap.get(r).contains(Path.Constant(v))
        }
        val lenOk = g.pathLenPrecondition.forall { (r, k) =>
          refMap.get(r).exists { p =>
            val b = Lower.pathLenBounds(p, ann.pathLens)
            !b.isEmpty && !k.isEmpty && k.lo <= b.lo && b.hi <= k.hi
          }
        }
        if spaceOk && valueOk && lenOk then { proved += 1; Space.Call(to, refs, mentions) }
        else { skipped += 1; c }
    })
    (out, proved, skipped)

  // ------------------------------------------------------------------------------------------------
  // THE PER-NODE REWRITES
  // ------------------------------------------------------------------------------------------------

  /** ==============================================================================================
   *  THE ANALYSIS-DRIVEN REWRITES, driven by the decorated analysis.
   *
   *  It takes the DECORATED analysis rather than the `RoutineAnalysis` wrapper because that is all it
   *  reads — which is what lets the `Routine.optimized` hook skip the candidate stage entirely.
   *
   *  ==WHAT THIS USED TO BE, AND WHY THAT WAS THE COMPLAINT==
   *  Two rewrites: `provablyEmpty` -> `Empty`, and `SpatialFacts.exactValue` -> `Literal`.  Both read
   *  the SIZE of a node's type and nothing else.  Meanwhile the analysis derives, at every node, a
   *  `SpatialType` with a six-channel `Shape` (the two head-set certificate channels included), a
   *  per-node `Fact` vector, and — for every binary ring
   *  node — a `SpatialFrontier` summary that is the analysis-side mirror of `Trie.AlgebraicResult`.
   *  A census of the consumers was blunt: of the eleven `Fact` cases, exactly ONE (`ExactHeadSet`)
   *  was read anywhere outside `SpatialTypeSystem`, and that read was inside a Trie-backend-only
   *  candidate.  The rest — `DefinitelyNonEmpty`, `MinimumCardinality`, `MaximumCardinality`,
   *  `AllPathsHaveAtLeast`, `MaximumPathLength`, `HeadSetWithin`, `MinimumHeadCount`,
   *  `MaximumHeadCount`, `PrefixAbsent` — had NO consumer at all, and neither did the whole
   *  relational layer: `SpatialFrontier` was used to PRICE a node, never to REPLACE it.
   *
   *  ==THE FIVE ADDED, EACH WITH THE FACT IT READS AND WHY IT IS SOUND==
   *  R1 [[frontierEdits]]  — the relational frontier's SINGLETON case sets.
   *  R2 [[iterationEdits]] — a one-head source turns an `Iteration` into a substitution.
   *  R3 [[iterationEdits]] — a headless source, or a provably-empty body, makes it `∅`.
   *  R4 [[prefixEdits]]    — `Fact.PrefixAbsent` makes an `Unwrap` `∅`.
   *  R5 [[windowEdits]]    — a pinned cardinality makes a `Range` window the identity.
   *
   *  EVERY ONE IS GATED BY THE SAME DIFFERENTIAL AS THE OLD TWO: `SpatialPipelineCheck`'s
   *  "the hooked `Routine.optimized` agrees with `eval` on the fuzzed corpus" runs the whole hook
   *  over the 1000-program corpus and compares against the reference evaluator.  A rewrite that
   *  reads a fact wrongly fails there, not in review. */
  /** the rewrite set and the rewritten body, for diagnostics and for the size-contract test */
  private[morkl] def rewriteNodesFor(body: Space, d: SpatialAnalysis,
                                     ann: SpatialAnnotations): (Space, Vector[Rewrite]) =
    rewriteNodes(body, d, ann)

  private def rewriteNodes(body: Space, d: SpatialAnalysis,
                           ann: SpatialAnnotations): (Space, Vector[Rewrite]) =
    val empties = d.provablyEmpty.iterator
      .filter(n => n.expression != Space.Empty)
      .map(n => (n.id, Space.Empty: Space,
                 Rewrite.EliminateEmpty(n.id, show(n.expression), nodeCount(n.expression)))).toVector
    val exacts = exactEdits(d, ann)
    apply(body, dropNested(empties ++ frontierEdits(d, ann) ++ exacts ++
                           iterationEdits(d, ann) ++ prefixEdits(d) ++ windowEdits(d)))

  /** R1 — THE RELATIONAL FRONTIER, CONSUMED AS A REWRITE.
   *
   *  `SpatialFrontier.atNode` returns, for every binary ring node, the SET of
   *  `Trie.AlgebraicResult` cases that MAY hold, computed from the two children's decorated types.
   *  A SINGLETON set is not an estimate — it is a proof:
   *
   *    `{Empty}`        the result is `∅`            (an empty operand, or head-disjointness, or a
   *                                                   covering prefix set on a raffination)
   *    `{Left}`         the result IS the left operand   (an empty right operand, `ε ∈ right` on a
   *                                                   restriction, `covers(l, r)`, …)
   *    `{Right}`        the result IS the right operand
   *    `{Left, Right}`  `Identity(BOTH)` — the two operands denote the SAME set, so either will do
   *
   *  ==THE TWO THINGS THIS DELIBERATELY DOES NOT DO==
   *  It does NOT use `FrontierCase.isIdentity`, which is `cs.nonEmpty && !cs.contains(Bespoke)` and
   *  therefore true of `{Empty, Left}` — "∅ or L", which for a head-disjoint `Intersection` is a
   *  genuine disjunction and not a rewrite.  And it does NOT act on any set containing `Bespoke`.
   *  Only the four sets above fire.
   *
   *  ==WHY IT IS SOUND AT AN OCCURRENCE, NOT JUST AT A VALUE==
   *  `atNode` reads the two children's DECORATED types, which are the JOIN over every observation of
   *  that occurrence — every binder environment the analysis saw it in.  γ of each observation is
   *  contained in γ of the join, so a case proved from the join holds under all of them, which is
   *  exactly what rewriting inside a binder body requires (the same argument [[exactEdits]] uses).
   *
   *  NOTE FOR THE WIDTH SPILL: `headDisjoint` goes through `Shape.possibleHeads`, so this rewrite's
   *  yield is bounded by whether the head set is enumerable — which is what the [[Cert]] certificate
   *  restored past `Shape.MaxHeads`, at any width. */
  private def frontierEdits(d: SpatialAnalysis, ann: SpatialAnnotations)
      : Vector[(NodeId, Space, Rewrite)] =
    import FrontierCase.*
    d.nodes.iterator.flatMap { n =>
      SpatialFrontier.opOf(n.expression).flatMap { op =>
        SpatialFrontier.atNode(d, n.id, FrontierConfig(facts = ann.factConfig)).flatMap { s =>
          def child(i: Int): Option[Space] = n.expression match
            case Space.Union(a, b) => Some(if i == 0 then a else b)
            case Space.Intersection(a, b) => Some(if i == 0 then a else b)
            case Space.Subtraction(a, b) => Some(if i == 0 then a else b)
            case Space.Restriction(a, b) => Some(if i == 0 then a else b)
            case Space.Raffination(a, b) => Some(if i == 0 then a else b)
            case Space.Composition(a, b) => Some(if i == 0 then a else b)
            case _ => None
          val repl: Option[(Space, String)] =
            if s.cases == Set(Empty) then Some((Space.Empty, "∅"))
            else if s.cases == Set(Left) || s.cases == Set(Left, Right) then child(0).map(_ -> "L")
            else if s.cases == Set(Right) then child(1).map(_ -> "R")
            else None
          repl.filter((r, _) => r != n.expression)
              .map((r, side) => (n.id, r, Rewrite.FrontierIdentity(n.id, op.toString, side)))
        }
      }
    }.toVector

  /** R2/R3 — WHAT THE HEAD FACTS SAY ABOUT A LOOP.
   *
   *  `eval`'s `Iteration(src, sym, rest, body)` groups `src`'s paths by head (dropping the headless
   *  `ε` path) and unions `body` over the groups with `sym` bound to the head and `rest` to that
   *  head's tail set (MORKL.scala).  Two facts about the SOURCE decide the loop outright:
   *
   *  R2  `Fact.ExactHeadSet(hs)` with `|hs| = 1`.  The union has exactly ONE term, so the loop is a
   *      substitution: `body[sym := h][rest := TailsUnion(src)]`.  `tails(src, h) = TailsUnion(src)`
   *      because every headed path of `src` starts with `h`.  Unlike [[unrollProvedHeads]] this needs
   *      only the head SET, not a pinned source value — and it duplicates nothing, so the measurement
   *      that killed the `rest := Unwrap(src, h)` form (work 16 -> 25, graph slots 6 -> 11) does not
   *      apply.  It is REFUSED when the body rebinds either name (the same hygiene check the unroller
   *      uses) or mentions `rest` more than once, which would duplicate `src`.
   *
   *  R3  `Fact.MaximumHeadCount(0)`: no path of `src` has a head, so there are no groups and the
   *      union is empty.  Also when the BODY's joined result is provably empty — the join is `∅` only
   *      if every observation is, so the join test suffices.  This is the semantic form of the two
   *      syntactic identities `Lower` already has for `Iteration(Empty, …)`. */
  private def iterationEdits(d: SpatialAnalysis, ann: SpatialAnnotations)
      : Vector[(NodeId, Space, Rewrite)] =
    d.nodes.iterator.flatMap { n =>
      n.expression match
        case Space.Iteration(src, sym, rest, tmpl) =>
          val srcNode = d.at(n.id.child(0))
          val bodyNode = d.at(n.id.child(1))
          val facts = srcNode.toVector.flatMap(_.facts)
          val headless = facts.exists { case Fact.MaximumHeadCount(0) => true; case _ => false }
          val emptyBody = bodyNode.exists(_.result.isProvablyEmpty)
          if headless then
            Some((n.id, Space.Empty: Space,
                  Rewrite.IterationDrop(n.id, "the source has no headed path, so no group runs")))
          else if emptyBody then
            Some((n.id, Space.Empty: Space,
                  Rewrite.IterationDrop(n.id, "the body is provably ∅ in every observed environment")))
          else
            facts.collectFirst { case Fact.ExactHeadSet(hs) if hs.size == 1 => hs.head }
              .filter(_ => !rebinds(tmpl, sym, rest))
              .map { h =>
                val c = Path.Constant(PathValue(List(h)))
                // THROUGH `Subst`, AND THIS IS THE ONE OF THE TWO WHERE IT MATTERS.  The
                // `rebinds` guard above refuses the rewrite when `tmpl` REBINDS `sym` or `rest`,
                // which handles SHADOWING by refusal — but capture is the OTHER direction and
                // `rebinds` cannot see it: the replacement here is `TailsUnion(src)`, which is NOT
                // closed, so a binder inside `tmpl` named after a FREE name of `src` captured it and
                // the substituted term silently started reading that binder.  (`unrollProvedHeads`
                // below substitutes only closed `Literal`/`Constant` terms, so it was safe on that
                // count; its header's "the substitution would then capture" describes shadowing, not
                // capture.)  `Subst` alpha-renames the offending binder instead.
                val sub = Subst(tmpl, Map(rest -> Space.TailsUnion(src)), Map(sym -> c))
                (n.id, sub, Rewrite.IterationSubstitute(n.id, h))
              }
              // AND IT MUST NOT GROW THE TERM.  When the body never mentions `rest` the substitution
              // deletes the source outright and this is free; when it does, `rest := TailsUnion(src)`
              // puts a copy of `src` back, and one copy of a large source is bigger than the loop it
              // replaced.  `Routine.optimized`'s contract is that the hooked body is never larger
              // than the plain one (`SpatialPipelineCheck`'s corpus gate asserts it), so the size
              // test is the gate, not a mention count: a two-node `src` under two mentions is still
              // a win and a fifty-node `src` under one is not.
              .filter((_, sub, _) => nodeCount(sub) <= nodeCount(n.expression))
        case _ => None
    }.toVector

  /** how many times does `s` mention `m`? — the guard that keeps R2 from duplicating its source */
  private def mentionCount(s: Space, m: SpaceMention): Int =
    collect(s)({ case Space.Mention(`m`) => () }, PartialFunction.empty)._1.size

  /** R4 — `Fact.PrefixAbsent` FINALLY HAS A CONSUMER.
   *
   *  `SpatialAnalysis.constantPrefixes` probes exactly the constant paths the term itself mentions
   *  and emits `Fact.PrefixAbsent(p)` when `Shape.mayHavePrefix(p)` is FALSE — which is a PROOF of
   *  absence, not an estimate (a closed head set with no `p` head, or a tracked child that rejects
   *  the rest).  `Unwrap(src, p)` keeps exactly the paths of `src` that start with `p`, so an absent
   *  prefix makes it `∅`.  Until now nothing read the fact: it was manufactured at every node and
   *  consumed nowhere. */
  private def prefixEdits(d: SpatialAnalysis): Vector[(NodeId, Space, Rewrite)] =
    d.nodes.iterator.flatMap { n =>
      n.expression match
        case Space.Unwrap(_, Path.Constant(PathValue(items))) if items.nonEmpty =>
          d.at(n.id.child(0)).toVector.flatMap(_.facts)
            .collectFirst { case Fact.PrefixAbsent(p) if p == items => p }
            .map(p => (n.id, Space.Empty: Space, Rewrite.UnwrapAbsent(n.id, p)))
        case _ => None
    }.toVector

  /** R5 — A PINNED CARDINALITY MAKES A WINDOW THE IDENTITY.
   *
   *  `RangeBounds.normalize(size, lo, hi)` clamps the window to `[0, size)`, and `sliceRange` /
   *  `ITrie.range` return their input unchanged when it covers everything.  Two ways to know it does
   *  without knowing the size: the window is syntactically full (`(lo == 0 || lo == 1) && hi == 0`,
   *  which `SpatialCost.rangeIsIdentity` already decides and prices), or the operand's cardinality is
   *  PINNED (`MinimumCardinality(k)` and `MaximumCardinality(k)` agree) and the normalised window
   *  covers `[0, k)`.  The second reads two facts that had no consumer at all. */
  private def windowEdits(d: SpatialAnalysis): Vector[(NodeId, Space, Rewrite)] =
    d.nodes.iterator.flatMap { n =>
      n.expression match
        case Space.Range(x, lo, hi) =>
          val whole =
            if SpatialCost.rangeIsIdentity(lo, hi) then Some("the window is syntactically full")
            else
              val fs = d.at(n.id.child(0)).toVector.flatMap(_.facts)
              val kLo = fs.collectFirst { case Fact.MinimumCardinality(k) => k }
              val kHi = fs.collectFirst { case Fact.MaximumCardinality(k) => k }
              (kLo, kHi) match
                case (Some(a), Some(b)) if a == b && a <= Int.MaxValue.toLong =>
                  val (l, h) = RangeBounds.normalize(a.toInt, lo, hi)
                  if l == 0 && h.toLong == a then
                    Some(s"the operand holds exactly $a paths and the window covers all of them")
                  else None
                case _ => None
          whole.map(w => (n.id, x, Rewrite.RangeIdentity(n.id, w)))
        case _ => None
    }.toVector

  /** ONLY the exact-value folding (what the graph lowering consumes) */
  private def foldExactNodes(body: Space, d: SpatialAnalysis,
                             ann: SpatialAnnotations): (Space, Vector[Rewrite]) =
    apply(body, dropNested(exactEdits(d, ann)))

  /** A node whose reduced product pins EXACTLY ONE concrete space folds to that `Literal`.
   *
   *  Sound WITHOUT evaluating anything: `SpatialFacts.exactValue` reads the value out of the shape
   *  (every level with a decided ε, a closed head set and a definitely-present exact child) and then
   *  re-checks it with full γ-membership, so γ(t) = {v}.  The node's `result` is the JOIN over all its
   *  observations, and each observation's γ is contained in the join's, so γ(observation) ⊆ {v}: the
   *  occurrence denotes `v` under EVERY binder environment it is analysed in, which is exactly what a
   *  rewrite of a binder body needs. */
  private def exactEdits(d: SpatialAnalysis, ann: SpatialAnnotations)
      : Vector[(NodeId, Space, Rewrite)] =
    d.nodes.iterator.flatMap { n =>
      val sz = n.result.size
      if n.result.uninhabited || sz.hi == Ivl.INF || sz.hi > ann.maxFoldPaths then None
      else SpatialFacts.exactValue(n.result).flatMap { v =>
        val already = n.expression match
          case Space.Literal(w) => w == v
          case Space.Empty => v.paths.isEmpty
          case _ => false
        if already then None
        else
          val repl: Space = if v.paths.isEmpty then Space.Empty else Space.Literal(v)
          val rw =
            if v.paths.isEmpty then Rewrite.EliminateEmpty(n.id, show(n.expression), nodeCount(n.expression))
            else Rewrite.ConstantFold(n.id, show(n.expression), v.paths.size, nodeCount(n.expression))
          Some((n.id, repl, rw))
      }
    }.toVector

  /** BOUNDED TRIE UNROLLING: `Iteration(src, h, rest, body)` over a source whose trie is PINNED becomes
   *  straight-line code with the per-head tail-sets materialised as constants.
   *
   *  `eval`'s `Iteration` groups the source's paths by head (dropping the headless `ε` path) and unions
   *  the body over the groups, with `h` bound to the head and `rest` to that head's TAIL SET.  So
   *
   *  {{{ Iteration(src, h, rest, body)  =  ⋃_{x ∈ heads(src)}  body[h ↦ x][rest ↦ tails(src, x)] }}}
   *
   *  and the rewrite needs the head set and every tail set to be KNOWN.  Both come from the shape:
   *  `SpatialFacts.exactValue` on the SOURCE node's type pins the whole source trie (every level with a
   *  decided ε, a closed head set and a definitely-present exact child, then re-checked against full
   *  γ-membership), and `Fact.ExactHeadSet` confirms the group set.  Nothing is evaluated — the value is
   *  read out of the abstract domain.
   *
   *  ==WHY THE EXACT SOURCE IS REQUIRED==
   *  A first version used `rest ↦ Unwrap(src, x)`, which needs only the head set.  It was MEASURED and
   *  is a wash at best: `src` then appears once per arm, so an interpreter without sharing recomputes it
   *  `|hs|` times.  On the E2E example counted work went 16 → 25 and the post-CSE operation graph grew
   *  6 → 11 slots, in exchange for `LoopBodyEntry` 2 → 0.  Trading a loop for duplicated work is not an
   *  optimization, so that form was removed rather than reported as a win.  With a pinned source the
   *  tail sets are constants, nothing is duplicated, and the rewrite is a strict improvement.
   *
   *  HYGIENE: refused when `body` REBINDS `sym` or `rest`.  That is SHADOWING, not capture — an
   *  inner binder of the same name means the inner occurrences belong to it and must not be
   *  rewritten — and the two are separate hazards.  Capture (a binder here swallowing a free name of
   *  the REPLACEMENT) cannot arise in this rewrite because both replacements are closed, and is
   *  handled by `Subst` in any case; `iterationSubstitute` above is the sibling where it could. */
  private def unrollProvedHeads(body: Space, a: RoutineAnalysis,
                                ann: SpatialAnnotations): (Space, Vector[Rewrite]) =
    val edits = a.decorated.nodes.iterator.flatMap { n =>
      n.expression match
        case Space.Iteration(src, sym, rest, tmpl) =>
          val srcNode = a.at(NodeId(n.id.position :+ 0))
          val heads = srcNode.toVector.flatMap(_.facts).collectFirst {
            case Fact.ExactHeadSet(hs) => hs.toVector.sorted
          }
          val pinned = srcNode.flatMap(sn => SpatialFacts.exactValue(sn.result))
          for
            hs <- heads
            v <- pinned
            if hs.nonEmpty && hs.size <= ann.maxUnrollHeads && !rebinds(tmpl, sym, rest)
            if v.paths.count(_.items.nonEmpty) <= ann.maxFoldPaths
          yield
            val arms = hs.map { h =>
              val c = Path.Constant(PathValue(List(h)))
              val tail = SpaceValue(v.paths.collect { case PathValue(x :: t) if x == h => PathValue(t) })
              val tailTerm: Space = if tail.paths.isEmpty then Space.Empty else Space.Literal(tail)
              // THROUGH `Subst`; both replacements are closed here (a `Literal`/`Empty` and a
              // `Constant`), so this one was never a capture hazard — it goes through the one
              // substitution so that there is only one, and so the `rebinds` guard stops being the
              // thing correctness rests on.
              Subst(tmpl, Map(rest -> tailTerm), Map(sym -> c))
            }
            (n.id, arms.reduce((x, y) => Space.Union(x, y)), Rewrite.UnrollHeads(n.id, hs))
        case _ => None
    }.toVector
    apply(body, dropNested(edits))

  /** does `s` rebind either name?  A substitution under a rebinding would capture. */
  private def rebinds(s: Space, pr: PathRef, m: SpaceMention): Boolean =
    var found = false
    def go(x: Space): Unit =
      if !found then
        x match
          case Space.Iteration(_, sym, rest, _) => if sym == pr || rest == m then found = true
          case Space.Fold(_, _, acc, sym, rest, _, _) =>
            if acc == pr || sym == pr || rest == m then found = true
          case Space.Fixpoint(_, rec, _) => if rec == m then found = true
          case _ => ()
        if !found then SizeZ3.children(x).foreach(go)
    go(s)
    found

  // ------------------------------------------------------------------------------------------------
  // POSITIONAL REWRITING
  // ------------------------------------------------------------------------------------------------

  /** keep only the OUTERMOST selected positions: an outer rewrite subsumes everything inside it, and
   *  two positions that are not nested are independent (a replacement preserves every ancestor's
   *  arity, hence every other position). */
  private def dropNested(edits: Vector[(NodeId, Space, Rewrite)]): Vector[(NodeId, Space, Rewrite)] =
    val chosen = edits.map(_._1.position).toSet
    edits.filter { (id, _, _) =>
      !id.position.indices.exists(k => chosen.contains(id.position.take(k)))
    }.distinctBy(_._1)

  private def apply(body: Space, edits: Vector[(NodeId, Space, Rewrite)]): (Space, Vector[Rewrite]) =
    var out = body
    val done = Vector.newBuilder[Rewrite]
    for (id, repl, rw) <- edits do
      replaceAt(out, id.position, repl) match
        case Some(next) => out = next; done += rw
        case None => ()          // a position the term does not have: skip, never guess
    (out, done.result())

  /** replace the subterm at a [[NodeId]] position.  Child indices are `SpatialAnalysis.childrenOf`'s
   *  order, which is the order the shape transfer visits operands in, which is what a `NodeId` counts. */
  def replaceAt(s: Space, pos: Vector[Int], repl: Space): Option[Space] =
    if pos.isEmpty then Some(repl)
    else
      val kids = SpatialAnalysis.childrenOf(s)
      val i = pos.head
      if i < 0 || i >= kids.size then None
      else replaceAt(kids(i), pos.tail, repl).map(k => rebuild(s, kids.updated(i, k)))

  def subtermAt(s: Space, pos: Vector[Int]): Option[Space] =
    if pos.isEmpty then Some(s)
    else
      val kids = SpatialAnalysis.childrenOf(s)
      val i = pos.head
      if i < 0 || i >= kids.size then None else subtermAt(kids(i), pos.tail)

  /** rebuild a node over new operands.  `SpatialAnalysis.rebuild` is the same function and is
   *  `private` there; see the report's request to widen it to `private[morkl]` so this copy can go. */
  private def rebuild(s: Space, kids: Vector[Space]): Space = s match
    case Space.Union(_, _) => Space.Union(kids(0), kids(1))
    case Space.Intersection(_, _) => Space.Intersection(kids(0), kids(1))
    case Space.Subtraction(_, _) => Space.Subtraction(kids(0), kids(1))
    case Space.Restriction(_, _) => Space.Restriction(kids(0), kids(1))
    case Space.Raffination(_, _) => Space.Raffination(kids(0), kids(1))
    case Space.Composition(_, _) => Space.Composition(kids(0), kids(1))
    case Space.Wrap(_, p) => Space.Wrap(kids(0), p)
    case Space.Unwrap(_, p) => Space.Unwrap(kids(0), p)
    case Space.TailsUnion(_) => Space.TailsUnion(kids(0))
    case Space.TailsIntersection(_) => Space.TailsIntersection(kids(0))
    case Space.Range(_, lo, hi) => Space.Range(kids(0), lo, hi)
    case Space.Iteration(_, sym, rest, _) => Space.Iteration(kids(0), sym, rest, kids(1))
    case Space.Fold(_, i, acc, sym, rest, _, u) => Space.Fold(kids(0), i, acc, sym, rest, kids(1), u)
    case Space.Fixpoint(_, rec, _) => Space.Fixpoint(kids(0), rec, kids(1))
    case Space.Call(r, refs, _) => Space.Call(r, refs, kids)
    case leaf => leaf

  // ------------------------------------------------------------------------------------------------
  // SMALL SHARED HELPERS
  // ------------------------------------------------------------------------------------------------

  /** THE ONE `Space` NODE COUNTER, over [[SizeZ3.children]] — which is TOTAL on the `Space` enum.
   *
   *  Four test files used to carry their own hand-written copy, each missing a different set of
   *  constructors (`Raffination`, `TailsIntersection`, `Fixpoint`, `Fold`, `Range`, `TailsUnion`).  A
   *  missing arm does not fail: it falls into `case _ => 0`, so the whole subtree below that node is
   *  counted as a LEAF.  Since the corpus generator's accept filter is `nodeCount(prog) >= 12`, a
   *  miscount silently changes which programs are in the corpus.  One implementation, driven by the
   *  same total child enumerator the SMT encoder uses, is the fix. */
  def nodeCount(s: Space): Int = 1 + SizeZ3.children(s).map(nodeCount).sum
  def isCallFree(s: Space): Boolean =
    var free = true
    def gp(p: Path): Unit = p match
      case Path.GroundedSP(x, _) => go(x)
      case Path.Concat(l, r) => gp(l); gp(r)
      case Path.GroundedPP(x, _) => gp(x)
      case _ => ()
    def go(x: Space): Unit =
      if free then
        x match
          case Space.Call(_, _, _) => free = false
          case Space.Singleton(p) => gp(p)
          case Space.Wrap(_, p) => gp(p)
          case Space.Unwrap(_, p) => gp(p)
          case _ => ()
        if free then SizeZ3.children(x).foreach(go)
    go(s)
    free

  def graphNodeCount(g: RecursiveOpGraph): Int =
    g.nodes.iterator.map { case Left(_) => 1; case Right(sg) => graphNodeCount(sg) }.sum

  private def show(s: Space): String =
    try s.show.replace('\n', ' ').take(90) catch case _: Throwable => s.toString.take(90)
end SpatialPipeline

// ==================================================================================================
// 7.  THE HOOK INSTALLED IN `Routine.optimized` — its policy, its switch, and its meter
// ==================================================================================================

/** THE SPATIAL TIER, ON THE ORDINARY COMPILATION PATH.
 *
 *  `Routine.optimized` (MORKL.scala:248-251) runs [[rewrite]] on the body before `Lower.inline` and
 *  the ordinary rule list.  Only UNCONDITIONAL facts are available there — `optimized` takes no
 *  annotation, so the analysis is run with none — which means every rewrite it performs is valid for
 *  every input and needs no guard, no fallback and no dispatcher.  What it can prove is exactly what
 *  the term's own syntax and the routine table support: a subterm the reduced product proves EMPTY
 *  becomes `Space.Empty`, a subterm it pins to ONE concrete value becomes that `Literal`.
 *
 *  ==WHY IT IS SAFE TO PUT ON A HOT PATH==
 *  Three limits, in the order they fire:
 *
 *   1. [[enabled]] — the switch.  `-Dmorkl.spatialHook=false` turns the tier off process-wide and
 *      restores the byte-for-byte previous behaviour of `optimized`; the `var` is there so a
 *      benchmark can measure both states in ONE process (that is how the numbers in
 *      `SpatialPipelineCheck`'s cost test are produced).
 *   2. [[config]] = `SpatialConfig.cheap` — the budgets, and this is the one that actually bounds the
 *      price.  Body size is a POOR cost predictor here (n-queens `place(8)` is 137 nodes and used to
 *      cost 4.4 s, because `SpatialTyping` re-analyses a binder body once per head group, inlines
 *      `Call`s interprocedurally, and iterates a `Fixpoint` per Kleene round), so what the hook caps
 *      is the number of TRANSFERS: `cheap.nodeBudget = 2000`, after which the traversal degrades the
 *      remaining subterms to ⊤.  See `SpatialConfig.cheap` for the measured table.
 *   3. [[maxBodyNodes]] — a second, cruder belt: a body past this many nodes is handed straight through
 *      UNANALYSED.  A compile-time hook may lose an optimization; it may not lose a compile.
 *
 *  It also never propagates a failure: an analysis that raises is counted ([[Stats.raised]]) and
 *  answered with the unmodified body.
 *
 *  ==WHAT IT COSTS AND WHAT IT BUYS==
 *  Both are MEASURED, per call, by this object ([[stats]]), so the claim is a number and not an
 *  argument.  `SpatialPipelineCheck` prints the per-routine table and gates three of those numbers
 *  (worst absolute delta, the ratio on a call that was already expensive, and the whole table's total),
 *  and its corpus test measures what the tier BUYS: on 250 fuzzed corpus programs it rewrote 71 of them
 *  and took the compiled bodies from 8710 to 7796 nodes for 1.2 ms of analysis per call.  On the CLOSED
 *  cornerstone routines it saves nothing at all — `Lower.ConstantOps` is a partial evaluator and folds
 *  those anyway — so the honest summary is: it pays on OPEN bodies and is a small tax on closed ones. */
object SpatialHook:
  /** the switch.  Default ON; `-Dmorkl.spatialHook=false` restores the previous `optimized`. */
  @volatile var enabled: Boolean = !sys.props.get("morkl.spatialHook").contains("false")
  /** bodies with more nodes than this are handed through unanalysed (see the class comment).
   *  `-Dmorkl.spatialHookMaxNodes=<n>` overrides it. */
  @volatile var maxBodyNodes: Int =
    sys.props.get("morkl.spatialHookMaxNodes").flatMap(_.toIntOption).getOrElse(600)
  /** the budgets the hook's analysis runs under.  `SpatialConfig.cheap` plus a TRANSFER budget: the
   *  cost of one analysis is bounded by how many shape transfers it is allowed to run, and on a
   *  compilation path that bound is what makes the price predictable rather than program-dependent. */
  @volatile var config: SpatialConfig = SpatialConfig.cheap

  private val nCalls = new java.util.concurrent.atomic.AtomicLong(0L)
  private val nSkipped = new java.util.concurrent.atomic.AtomicLong(0L)
  private val nChanged = new java.util.concurrent.atomic.AtomicLong(0L)
  private val nNanos = new java.util.concurrent.atomic.AtomicLong(0L)
  private val nNodesIn = new java.util.concurrent.atomic.AtomicLong(0L)
  private val nNodesOut = new java.util.concurrent.atomic.AtomicLong(0L)
  private val nRaised = new java.util.concurrent.atomic.AtomicLong(0L)
  @volatile private var lastError: String = ""

  /** what the hook has done in this process: calls, calls skipped by the size budget, calls that
   *  CHANGED the body, calls whose analysis RAISED (and were therefore no-ops), total time, and total
   *  body nodes before/after.  `raised` is here so that a hook silently declining to work is a NUMBER
   *  a test can assert on rather than something nobody notices. */
  final case class Stats(calls: Long, skipped: Long, changed: Long, raised: Long, nanos: Long,
                         nodesIn: Long, nodesOut: Long, lastError: String):
    def millis: Double = nanos / 1e6
    def perCallMicros: Double = if calls == 0 then 0.0 else nanos / 1000.0 / calls
    def show: String =
      f"$calls calls ($skipped over budget, $changed changed, $raised raised), ${millis}%.1f ms total, " +
      f"${perCallMicros}%.0f us/call, $nodesIn -> $nodesOut nodes" +
      (if lastError.isEmpty then "" else s"; last error: $lastError")
  def stats: Stats = Stats(nCalls.get, nSkipped.get, nChanged.get, nRaised.get, nNanos.get,
                           nNodesIn.get, nNodesOut.get, lastError)
  def reset(): Unit =
    for c <- Vector(nCalls, nSkipped, nChanged, nRaised, nNanos, nNodesIn, nNodesOut) do c.set(0L)
    lastError = ""

  /** run `body` with the hook forced into a given state, then restore it.  For benchmarks and for the
   *  ONE place a caller legitimately wants the pre-existing behaviour: a differential test that has to
   *  compare the spatial tier against the ordinary rule list alone. */
  def withEnabled[A](on: Boolean)(f: => A): A =
    val was = enabled
    enabled = on
    try f finally enabled = was

  /** THE ENTRY POINT `Routine.optimized` CALLS.  Total: it never throws, and on any refusal (switch
   *  off, body too big, analysis inconsistent) it returns `body` unchanged. */
  def rewrite(body: Space, rc: PartialFunction[RoutinePtr, Routine]): Space =
    if !enabled then body
    else
      val n = SpatialPipeline.nodeCount(body)
      if n > maxBodyNodes then
        nCalls.incrementAndGet(); nSkipped.incrementAndGet()
        body
      else
        val t0 = System.nanoTime()
        val out =
          try SpatialPipeline.rewriteUnconditional(body,
                SpatialAnnotations(routines = rc, config = config))
          catch
            // a compile-time hook is not allowed to break a compilation that used to work: the
            // analysis raising anything at all means "no rewrite", never "no program".  It IS counted,
            // and the message kept, so the failure is visible instead of merely harmless.
            case e: StackOverflowError =>
              nRaised.incrementAndGet(); lastError = "StackOverflowError"; body
            case scala.util.control.NonFatal(e) =>
              nRaised.incrementAndGet()
              lastError = s"${e.getClass.getName}: ${Option(e.getMessage).getOrElse("").take(120)}"
              body
        nNanos.addAndGet(System.nanoTime() - t0)
        nCalls.incrementAndGet()
        nNodesIn.addAndGet(n.toLong)
        nNodesOut.addAndGet(SpatialPipeline.nodeCount(out).toLong)
        if out != body then nChanged.incrementAndGet()
        out
end SpatialHook
