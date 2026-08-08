package morkl

/** ==================================================================================================
 *  SEMANTIC LAWS AS PRODUCTION INPUTS TO THE ANALYSIS  (review.md 2).
 *
 *  ==THE PROBLEM THIS FILE FIXES==
 *  The subsystem knew several facts it could not USE.  `SpatialAcceptance` 6a–6c proved, in standalone
 *  Scala, that a directed transitive closure has at most `|E|²` edges, that a Life step lies inside the
 *  radius-1 image of its input, and that 4-queens has exactly two solutions — and then hand-built a
 *  `SpatialType` beside the analyzer to show the fact "could be" an annotation.  `PatternImage` and
 *  `SpatialFacts.chainBound` were in the same position: real bounds, computed by production code, with
 *  no route into `SpatialAnalysis`, the facts, the cost or the residual.  A law validated NEXT TO the
 *  analyzer is not an input to it.
 *
 *  ==THE CHANNEL==
 *  {{{
 *  val law = SpatialLaws.digraphTransitiveClosure(RoutinePtr("sn_tc"), evidence)
 *  val ann = SpatialAnnotations.open(rc).withLaws(law)          // carried in SpatialAnnotations…
 *  val a   = SpatialPipeline.analyzeRoutine(r, ann)             // …consumed by the decorated analysis
 *  a.decorated.lawsAt(NodeId(Vector.empty))                     // WHICH law tightened WHAT, with why
 *  }}}
 *  A law is carried on [[SpatialConfig.laws]], which `SpatialAnnotations` already holds, so every stage
 *  that takes annotations takes laws — no new plumbing at any call site.
 *
 *  ==A MEET IS NOT A SAFETY ARGUMENT  (review.md 9)==
 *  The channel is a MEET, so `γ(after) ⊆ γ(before)` holds by the ALGEBRA whatever the law says.  That
 *  used to be written here as if it were the safety argument, and it is NOT one.  An OVER-approximation
 *  is only useful because it CONTAINS the real value; a bound that narrows it below the real value
 *  breaks exactly that, and "meet cannot widen" says nothing about whether the narrowing was true.  A
 *  FALSE narrowing law is the most dangerous input this subsystem takes: it makes a live `Mention` look
 *  empty, `optimizeGuarded` erases the term, and the residual is wrong on every input.
 *
 *  ==SO THE EVIDENCE IS ENFORCED, NOT DOCUMENTED  ([[LawEvidencePolicy]])==
 *  Every law carries [[LawEvidence]] — `executable-checked`, `SMT-proved` or `ASSUMED` — and
 *  [[SpatialLaws.refine]] takes a [[LawEvidencePolicy]] that DECIDES on it.  Under the production
 *  policy ([[LawEvidencePolicy.RequireDischarged]], the default at every call site including
 *  `SpatialAnalysis`' recorder) an UNDISCHARGED bound is computed, REPORTED, and NOT MET: the outcome
 *  is [[LawOutcome.Refused]], the answer is the one the transfers derived, and therefore no fact, no
 *  candidate, no rewrite and no certificate downstream can rest on it.  The refusal is in the engine,
 *  in one place, so an optimizer does not have to remember to check — a law that would license a
 *  rewrite has to carry a discharged proof obligation to reach the optimizer at all.
 *  `SpatialAnalysis.assumedLaws` is consequently EMPTY under the production policy, and that is now a
 *  theorem about the engine rather than a hope about consumers.
 *
 *  ==WHAT A LAW IS RESPONSIBLE FOR, THEN==
 *  Exactly one thing: that the bound it contributes is TRUE of the values the site can denote.  It is a
 *  SOUNDNESS PREMISE, which is why the provenance travels all the way to the node
 *  ([[NodeAnalysis.laws]]) instead of being folded silently into a number, and why a consumer can name
 *  every law an answer depends on ([[LawApplication.tightened]]).
 *
 *  ==ORDER INDEPENDENCE IS A SATURATION, NOT A COMMUTATIVITY REMARK  (review.md 9)==
 *  `refine` used to apply laws left to right with each one OBSERVING the previous one's result, and
 *  argue order-independence from the commutativity of meet.  That argument is wrong: a law's `bound`
 *  reads `site.inferred`, so a permutation changes the BOUNDS, not only the order they are combined in
 *  (`finiteSolutionCount` needs a pinned length; a law that pins the length enables it).  The engine now
 *  runs a MONOTONE SATURATION — in each round every law is asked against the SAME baseline, the bounds
 *  are combined in a CANONICAL order derived from the laws themselves, and the rounds repeat until the
 *  answer stops moving.  The result is a function of the law SET.  See [[SpatialLaws.refine]].
 *
 *  ==A CONTRADICTION IS REFUSED, NOT PROPAGATED==
 *  If meeting a law's bound would produce [[SpatialType.bottom]] — the law and the transfers describe
 *  no common concrete value — the law is DROPPED and the outcome recorded as
 *  [[LawOutcome.Contradicted]].  Letting it through would turn every ∀-input claim vacuous and hand
 *  the optimizer a licence to rewrite anything, which is precisely the failure mode a "law" must not
 *  be able to cause by being wrong.
 *
 *  ==NO EVALUATION==
 *  Nothing here calls `eval`/`evalI`/`evalT`/`exec*`.  The laws in this file read declared types, the
 *  term's syntax and `SpatialTyping.infer`/`SpatialFacts` — all analysis.  A law's bound may have been
 *  ESTABLISHED by running a reference program (that is what `ExecutableChecked` means) but that
 *  happens in the test that constructs the law, never inside an analysis.
 *  ================================================================================================ */

/** WHY a law's bound may be believed.  This is the justification tag review.md 2 asks for, and it is
 *  a sum type rather than a string so a consumer can DECIDE on it ([[discharged]]). */
enum LawEvidence:
  /** checked against a reference executor / an independent reference implementation.  `what` names the
   *  case space that was covered — "all 512 digraphs on 3 nodes", not "tested". */
  case ExecutableChecked(what: String)
  /** discharged by the SMT layer (`SizeZ3`/`LengthConstraints`) */
  case SmtProved(what: String)
  /** an axiom the caller takes responsibility for.  The analysis still uses it, and still says so. */
  case Assumed(what: String)
  def tag: String = this match
    case ExecutableChecked(_) => "executable-checked"
    case SmtProved(_) => "SMT-proved"
    case Assumed(_) => "ASSUMED"
  /** the case space that was covered / the query that was discharged / the axiom that was asserted */
  def detail: String = this match
    case ExecutableChecked(w) => w
    case SmtProved(w) => w
    case Assumed(w) => w
  /** is there a discharged proof obligation behind the bound?  `false` for [[Assumed]] — a consumer
   *  that must not rest on an undischarged axiom reads THIS, not the free-text tag. */
  def discharged: Boolean = this match
    case Assumed(_) => false
    case _ => true
  def show: String = s"$tag ($detail)"

/** WHICH JUSTIFICATIONS MAY NARROW AN ANSWER  (review.md 9: "make the policy explicit and enforced in
 *  code, not documented").
 *
 *  A law's bound is a soundness PREMISE, and a false one breaks an over-approximation — so the question
 *  "may this bound be met into the analysis" is a policy decision with exactly one honest default.
 *  [[RequireDischarged]] is that default at every call site in the tree, and it is enforced by
 *  [[SpatialLaws.refine]] rather than by the consumers: a bound with no discharged proof obligation is
 *  computed, reported as [[LawOutcome.Refused]], and NOT met.  Nothing downstream — facts, candidates,
 *  the residual, the cost, a [[CheckCertificate]] — can then rest on it, because the per-node type it
 *  would have moved was never moved.
 *
 *  [[TrustAll]] exists so that "what would this axiom buy?" is answerable, and it is deliberately NOT
 *  reachable from `SpatialConfig`: a caller has to invoke `refine` directly, and the resulting
 *  applications still report the undischarged evidence, so [[SpatialCheck]] still refuses to certify a
 *  result that rests on one. */
enum LawEvidencePolicy:
  /** THE PRODUCTION POLICY: `executable-checked` and `SMT-proved` bounds are met, `ASSUMED` ones are
   *  refused.  This is the default parameter of [[SpatialLaws.refine]] and therefore what the decorated
   *  analysis, the optimizer and the checker all see. */
  case RequireDischarged
  /** meet every applicable bound, undischarged axioms included — an EXPLORATION setting.  The records
   *  still carry the evidence, and `LawApplication.assumed` still marks the tightenings that rest on an
   *  axiom, which is what a certificate refuses on. */
  case TrustAll
  /** may a bound with this justification narrow an answer? */
  def licenses(e: LawEvidence): Boolean = this match
    case RequireDischarged => e.discharged
    case TrustAll => true
  def show: String = this match
    case RequireDischarged => "require-discharged (an ASSUMED bound is refused, not met)"
    case TrustAll => "TRUST-ALL (an ASSUMED bound is met; exploration only)"

object LawEvidencePolicy:
  /** the policy every production call site uses */
  val production: LawEvidencePolicy = RequireDischarged

/** WHERE a law is asked to contribute: the occurrence, the term at it, the binder environment it was
 *  analysed in, and the type the TRANSFERS derived for it (already refined by any earlier law in the
 *  same set).  A law may read `inferred` as a premise — "all paths here have one length, so a total
 *  count claim can be placed in that class" is a legitimate and useful law shape. */
final case class LawSite(id: NodeId, term: Space, env: SpatialTyping.Env, inferred: SpatialType):
  /** the DECLARED type of a mention — an annotation premise (`|E|` for a closure law) */
  def declared(m: SpaceMention): Option[SpatialType] = env.spaces.get(m)
  def routines: PartialFunction[RoutinePtr, Routine] = env.lenv.routines
  def show: String = s"${id.show} ${term.show.take(40)}"

/** ONE SEMANTIC LAW.  `applies` is the applicability predicate on the term/annotation, `bound` is the
 *  bound it contributes, `evidence` is why that bound may be believed.
 *
 *  `applies` must be CHEAP — it is evaluated at every visited occurrence — and `bound` may be
 *  expensive, because it runs only where `applies` held. */
final case class SpatialBoundLaw(name: String,
                                 applies: LawSite => Boolean,
                                 bound: LawSite => Option[SpatialType],
                                 evidence: LawEvidence):
  def show: String = s"$name [${evidence.tag}]"

/** what happened when one law met one occurrence */
enum LawOutcome:
  /** the meet changed the recorded type */
  case Tightened
  /** applicable, contributed a bound, and the analysis already knew at least that much */
  case Unchanged
  /** applicable but declined to contribute (a premise it needs is not established here) */
  case NoBound
  /** the bound and the transfers describe no common value: the law was DROPPED */
  case Contradicted
  /** applicable, contributed a bound, and the ACTIVE [[LawEvidencePolicy]] refused it: the bound was
   *  NOT met and the answer is the transfers' own (review.md 9).  The bound it WOULD have contributed is
   *  reported in [[LawApplication.why]], so the cost of the missing proof obligation is visible. */
  case Refused
  def show: String = toString

/** ONE LAW APPLICATION, kept ON the node so a consumer can see WHICH law tightened WHAT (review.md 2).
 *  `occurrences` counts the observations of this position at which the same (law, outcome) recurred —
 *  a binder body under a 16-level nest has thousands, and keeping one record per observation would be
 *  a memory leak dressed up as provenance. */
final case class LawApplication(law: String, evidence: LawEvidence, at: NodeId, outcome: LawOutcome,
                                before: SpatialType, after: SpatialType, why: String,
                                occurrences: Int = 1):
  def tightened: Boolean = outcome == LawOutcome.Tightened
  /** the bound is in use AND rests on an undischarged axiom.  Under
   *  [[LawEvidencePolicy.RequireDischarged]] this is UNREACHABLE by construction — `refine` refuses to
   *  meet an undischarged bound — which is the point: a consumer reading this does not have to trust
   *  that some other consumer checked. */
  def assumed: Boolean = tightened && !evidence.discharged
  /** the bound was computed and REFUSED by the evidence policy: nothing rests on it, and the report says
   *  what a discharged proof obligation would have bought */
  def refused: Boolean = outcome == LawOutcome.Refused
  /** does the answer at this occurrence DEPEND on this law?  This is the predicate a certificate
   *  enumerates over ("name every law it depended on"). */
  def dependedOn: Boolean = tightened
  def show: String =
    s"$law ${outcome.show} at ${at.show}" + (if occurrences > 1 then s" (x$occurrences)" else "") +
    s" [${evidence.tag}]" + (if outcome == LawOutcome.Tightened then s": ${before.show.take(60)} -> ${after.show.take(60)}" else "") +
    (if why.isEmpty then "" else s" — $why")

object SpatialLaws:
  import Lower.{LenBounds, SizeBounds}

  // ================================================================================================
  // 1.  THE ENGINE
  // ================================================================================================

  /** rounds of the saturation below.  Round 0 asks every law against the transfers' own answer; a
   *  further round runs only when the previous one MOVED the answer, so a law set whose bounds do not
   *  read `site.inferred` costs exactly one extra confirming round and a set that cannot be saturated in
   *  four stops with the (sound, weaker) answer it reached. */
  val SaturationRounds: Int = 4

  /** MEET every applicable law's bound into `site.inferred` and report what each law did.
   *
   *  ==A CHECKED MONOTONE SATURATION, NOT A LEFT FOLD  (review.md 9)==
   *  The previous engine walked the vector left to right and handed each law the PREVIOUS law's result.
   *  That makes the answer depend on the permutation, because a law's `bound` reads `site.inferred` as a
   *  premise: `finiteSolutionCount` declines unless the length is pinned, so `[pin, count]` produces a
   *  count bound and `[count, pin]` does not.  Commutativity of meet does not rescue that — the two
   *  orders meet DIFFERENT bounds.
   *
   *  This engine instead runs rounds:
   *
   *   1. in one round, every law is asked `applies`/`bound` against the SAME baseline — the answer the
   *      previous round produced (round 0: the transfers' own answer).  No law observes a sibling's
   *      refinement WITHIN a round, so the set of contributed bounds is a function of the baseline;
   *   2. the bounds are combined in a CANONICAL order — `(name, evidence tag, rendered bound)`, taken
   *      from the laws and their bounds rather than from their position — so the accumulation, and in
   *      particular WHICH law is blamed when two laws jointly contradict, does not depend on the
   *      permutation either;
   *   3. rounds repeat while the baseline moves, up to [[SaturationRounds]].  Each round's result is a
   *      MEET with the previous baseline, so the sequence descends and the saturation is monotone by
   *      construction; it normally terminates at the first round that changes nothing, which is the
   *      fixpoint.  And the fixpoint claim is CHECKED rather than assumed: if the round budget runs out
   *      while the answer is still moving, every record says so, because that answer is sound but weaker
   *      than the law set implies and a reader must not mistake it for a fixpoint.
   *
   *  The result is therefore a function of the law SET, which `SpatialLawsCheck` 8 gates by permuting a
   *  baseline-SENSITIVE law set and comparing the answer AND the records.  γ-monotonicity of the whole
   *  engine — "no law, in any combination, ADDS a concrete value" — is gated by `SpatialLawsCheck` 2 over
   *  a 368640-check random sweep, which is where a bug in `meet` itself would surface.
   *
   *  ==WHAT EACH RECORD MEANS NOW==
   *  `before`/`after` are the law's OWN contribution against its round's COMMON baseline — "what this law
   *  proves beyond what was already known when the round started" — not "given the laws that happen to
   *  precede it in the vector".  A law that tightens in some round is recorded `Tightened` even if a
   *  sibling would have reached the same answer, because it did prove that much; the joint answer is the
   *  meet of everything that was accepted.
   *
   *  ==THE EVIDENCE POLICY IS ENFORCED HERE  (review.md 9)==
   *  A bound whose evidence `policy` does not license is computed (so the report can say what it would
   *  have bought) and then NOT met: [[LawOutcome.Refused]].  Under the default
   *  [[LawEvidencePolicy.RequireDischarged]] no undischarged axiom can move the answer, hence none can
   *  license a rewrite or be depended on by a certificate. */
  def refine(laws: Vector[SpatialBoundLaw], site: LawSite,
             policy: LawEvidencePolicy = LawEvidencePolicy.production,
             rounds: Int = SaturationRounds): (SpatialType, Vector[LawApplication]) =
    if laws.isEmpty then (site.inferred, Vector.empty)
    else
      // ---- the laws the policy REFUSES: asked once, against the transfers' answer, and never met ----
      val (licensed, refusedLaws) = laws.partition(l => policy.licenses(l.evidence))
      val refusedApps = Vector.newBuilder[LawApplication]
      for law <- refusedLaws do
        if law.applies(site) then
          val what = law.bound(site) match
            case Some(b) =>
              val would = SpatialType.meet(site.inferred, b)
              s"REFUSED by the ${policy.show} evidence policy: the bound ${b.show.take(60)} is " +
                s"${law.evidence.show} and no proof obligation was discharged for it, so it was NOT met" +
                (if would != site.inferred && !would.uninhabited then
                   s" — a discharged proof would have given ${would.show.take(60)}"
                 else " — and it would not have tightened this occurrence anyway")
            case None =>
              s"REFUSED by the ${policy.show} evidence policy (and its premises are not established " +
                "at this occurrence either)"
          refusedApps += LawApplication(law.name, law.evidence, site.id, LawOutcome.Refused,
                                        site.inferred, site.inferred, what)

      // ---- the saturation over the licensed laws ---------------------------------------------------
      // one record per law, keyed by the law's own identity so the output is a function of the SET
      val keep = collection.mutable.LinkedHashMap.empty[(String, String), LawApplication]
      /** which of two records for the SAME law survives across rounds: a law that tightened in ANY round
       *  really did tighten, and that is the record a consumer must see; otherwise the latest round is
       *  the most informed one. */
      def better(old: LawApplication, fresh: LawApplication): LawApplication =
        def rank(o: LawOutcome): Int = o match
          case LawOutcome.Tightened => 3
          case LawOutcome.Contradicted => 2
          case LawOutcome.Refused => 2
          case _ => 1
        if rank(old.outcome) >= rank(fresh.outcome) then old else fresh
      var baseline = site.inferred
      var round = 0
      var moved = true
      while moved && round < rounds do
        moved = false
        val here = site.copy(inferred = baseline)
        // (1) EVERY law against the SAME baseline
        val offers = licensed.filter(_.applies(here)).map(l => (l, l.bound(here)))
        // (2) a CANONICAL combination order, from the laws and bounds rather than their position
        val ordered = offers.sortBy((l, b) => (l.name, l.evidence.tag, b.map(_.show).getOrElse("")))
        var cur = baseline
        for (law, offer) <- ordered do
          def rec(outcome: LawOutcome, after: SpatialType, why: String): Unit =
            val app = LawApplication(law.name, law.evidence, site.id, outcome, baseline, after, why)
            val k = (law.name, law.evidence.tag)
            keep(k) = keep.get(k).map(better(_, app)).getOrElse(app)
          offer match
            case None =>
              rec(LawOutcome.NoBound, baseline,
                  "applicable, but its premises are not established at this occurrence")
            case Some(b) =>
              // the law's OWN contribution, against the round's common baseline: order-independent
              val own = SpatialType.meet(baseline, b)
              if own.uninhabited && !baseline.uninhabited then
                rec(LawOutcome.Contradicted, baseline,
                    s"the law's bound ${b.show.take(60)} and the transfers describe no common concrete " +
                      "space: the law is DROPPED, not propagated")
              else
                // the JOINT answer.  `cur eq baseline` until some law has been accepted, and then the
                // extra meet is what a second bound costs — not one per law unconditionally.
                val joint = if cur == baseline then own else SpatialType.meet(cur, b)
                if joint.uninhabited && !cur.uninhabited then
                  rec(LawOutcome.Contradicted, baseline,
                      s"the law's bound ${b.show.take(60)} is consistent with the transfers but " +
                        "contradicts another law in the same set (canonical order): it is DROPPED")
                else if own == baseline then
                  rec(LawOutcome.Unchanged, baseline, "the transfers already proved at least this much")
                else
                  rec(LawOutcome.Tightened, own, "")
                  cur = joint
        if cur != baseline then { baseline = cur; moved = true }
        round += 1
      // THE FIXPOINT CLAIM IS CHECKED, not assumed.  The loop stops either because a round changed
      // nothing — the answer IS the saturation's fixpoint — or because the round budget ran out while the
      // answer was still moving.  The second case is sound (every round is a meet, so the answer only
      // ever narrowed) but WEAKER than the law set implies, and it is said so rather than passed off as a
      // fixpoint.  It is also the only way the result can depend on `rounds`, which is why it is reported
      // on every record instead of being left for a reader to infer from the round count.
      val unsaturated = moved && round >= rounds
      val suffix =
        if !unsaturated then ""
        else s"  [the law saturation was STILL MOVING after $rounds round(s): this answer is sound — " +
             "every round is a meet — but may be weaker than the law set implies]"
      // the records are sorted CANONICALLY too, so even the audit trail is permutation-invariant
      val apps = (refusedApps.result() ++ keep.values.toVector)
        .sortBy(a => (a.law, a.evidence.tag, a.outcome.ordinal))
      (baseline, if suffix.isEmpty then apps else apps.map(x => x.copy(why = x.why + suffix)))

  /** merge two records of the same (law, outcome) at the same position — see
   *  [[LawApplication.occurrences]] */
  private[morkl] def mergeApplications(existing: Vector[LawApplication],
                                       fresh: Vector[LawApplication]): Vector[LawApplication] =
    var acc = existing
    for f <- fresh do
      acc.indexWhere(e => e.law == f.law && e.outcome == f.outcome) match
        case -1 => acc = acc :+ f
        case i => acc = acc.updated(i, acc(i).copy(occurrences = acc(i).occurrences + f.occurrences))
    acc

  // ================================================================================================
  // 2.  LAW CONSTRUCTORS — the three applicability shapes that cover every law below
  // ================================================================================================

  /** A law keyed on the EXACT TERM its bound was established for.  This is the narrowest possible
   *  applicability predicate and it is the right one for an EXHAUSTIVELY SEARCHED finite problem: a
   *  backtracking search that counted the solutions of one board proved a fact about that board and
   *  about nothing else, so the predicate is structural equality with that board's program. */
  def forTerm(name: String, term: Space, evidence: LawEvidence)
             (bound: LawSite => Option[SpatialType]): SpatialBoundLaw =
    SpatialBoundLaw(name, site => site.term == term, bound, evidence)

  /** A law about the RESULT OF A CALL to a named routine.  `applies` is the cheap syntactic half (is
   *  this a call to THAT routine); `bound` receives the argument terms and is where the ANNOTATION
   *  PREMISE is decided ("the edge relation is declared a digraph with at most `m` edges"), returning
   *  `None` when the premise does not hold — which the channel records as `NoBound`, not as a win. */
  def callResult(name: String, ptr: RoutinePtr, evidence: LawEvidence)
                (bound: (LawSite, Vector[Space]) => Option[SpatialType]): SpatialBoundLaw =
    SpatialBoundLaw(name,
      { case LawSite(_, Space.Call(p, _, _), _, _) => p == ptr; case _ => false },
      site => site.term match
        case Space.Call(_, _, args) => bound(site, args)
        case _ => None,
      evidence)

  /** A law about a REST-CHAINED ITERATOR NEST (`SpatialFacts.RestChain`).  Recognition is syntactic
   *  and cheap; the bound may run the full chain analysis. */
  def restChain(name: String, evidence: LawEvidence)
               (bound: (LawSite, RestChain) => Option[SpatialType]): SpatialBoundLaw =
    SpatialBoundLaw(name,
      site => site.term match
        case Space.Iteration(_, _, _, _) => true
        case _ => false,
      site => RestChain.recognize(site.term).flatMap(c => bound(site, c)),
      evidence)

  // ================================================================================================
  // 3.  THE LAW LIBRARY
  // ================================================================================================

  /** `|closure(E)| ≤ |E|²`, and `closure(E) ⊇ E`, for a SEMI-NAIVE transitive closure routine called
   *  as `tc(E, E, E)` (edges, accumulated, delta — the three arguments start equal).
   *
   *  ==THE UPPER BOUND IS GENERAL, NOT A SAMPLE==
   *  Every pair `(u,v)` in the closure has a path `u → … → v`, so `u` has out-degree ≥ 1 and `v` has
   *  in-degree ≥ 1 in `E`.  At most `|E|` vertices have positive out-degree and at most `|E|` have
   *  positive in-degree, so the closure is contained in a product of two sets of size ≤ `|E|`:
   *  `|closure| ≤ |E|²`.  `SpatialAcceptance` 6a checks it exhaustively on all 512 digraphs on three
   *  nodes against an independent saturation closure, which is what the `ExecutableChecked` evidence
   *  refers to.
   *
   *  ==THE PREMISE==
   *  The declared type of the edge mention must prove (a) a finite cardinality and (b) that every edge
   *  is a length-2 path — a digraph.  With no annotation there is no `|E|`, so the law contributes
   *  nothing (which is why `SpatialAcceptance` 5's datalog cornerstone stays ⊤ and 6a's does not). */
  def digraphTransitiveClosure(ptr: RoutinePtr, evidence: LawEvidence): SpatialBoundLaw =
    callResult(s"DirectedTransitiveClosure(${ptr.s})", ptr, evidence) { (site, args) =>
      for
        e <- args.headOption
        m <- e match { case Space.Mention(mm) => Some(mm); case _ => None }
        if args.size == 3 && args.forall(_ == e)
        t <- site.declared(m)
        ln = t.len
        if !ln.isEmpty && ln.lo == 2L && ln.hi == 2L && t.size.hi != SizeBounds.INF
      yield SpatialType(Shape.top,
                        SpaceType.closed(2L -> Ivl(t.size.lo, Ivl.mul(t.size.hi, t.size.hi))))
    }

  /** `|step(S)| ≤ 9·|S|` and every result cell is a `Cell.x.y` path, for a Game-of-Life step routine
   *  called as `nextStep(field)`.
   *
   *  A live cell of the next generation must have at least one live neighbour in the previous one, so
   *  it lies in the radius-1 image of `S`, which has at most `9·|S|` members.  `SpatialAcceptance` 6b
   *  checks it exhaustively on all 512 3×3 fields against the plain-Scala reference step. */
  def lifeStepImage(ptr: RoutinePtr, evidence: LawEvidence): SpatialBoundLaw =
    callResult(s"SubsetOfImage(${ptr.s}, radius-1)", ptr, evidence) { (site, args) =>
      for
        f <- args.headOption
        m <- f match { case Space.Mention(mm) => Some(mm); case _ => None }
        if args.size == 1
        t <- site.declared(m)
        ln = t.len
        if !ln.isEmpty && ln.lo == 3L && ln.hi == 3L && t.size.hi != SizeBounds.INF
      yield SpatialType(Shape.wrap(List("Cell"), Shape.top),
                        SpaceType.closed(3L -> Ivl(0L, Ivl.mul(9L, t.size.hi))))
    }

  /** THE EXACT SOLUTION COUNT of a finite constraint problem, as a bound on the Zippy program that
   *  enumerates it.  `solutions` comes from an exhaustive independent search (a backtracking counter),
   *  never from running the Zippy program.
   *
   *  Two directions, and the zero case is the interesting one:
   *
   *   - `solutions == 0` ⇒ the program denotes `∅`.  That is a bound the ordinary transfers cannot
   *     reach at all (they report "up to 1650688 paths" for a 4×4 board), and it makes the whole term
   *     an elimination candidate — a LAW CHANGING A RESIDUAL.
   *   - `solutions > 0` ⇒ at least `solutions` paths, because the solutions are distinct prefixes of
   *     the result and every prefix carries at least one path.  Placed in the length class the site's
   *     OWN inferred type pins down; with no pinned length the law declines rather than guess. */
  def finiteSolutionCount(name: String, program: Space, solutions: Long,
                          evidence: LawEvidence): SpatialBoundLaw =
    forTerm(name, program, evidence) { site =>
      if solutions == 0L then Some(SpatialType.empty)
      else
        val ln = site.inferred.len
        if ln.isEmpty || ln.lo != ln.hi then None
        else Some(SpatialType(Shape.top, SpaceType.closed(ln.lo -> Ivl(solutions, Ivl.INF))))
    }

  /** [[PatternImage]] ROUTED THROUGH THE CHANNEL: `q` pointwise output alternatives per source path,
   *  with both proofs `PatternImage.cardinality` requires (pairwise global disjointness of the
   *  alternatives, injectivity in a key that identifies the source path), give `q·N` EXACTLY — and the
   *  LOWER endpoint of that is what the union transfer cannot recover, because `Union` collapses equal
   *  outputs and the transfer has no way to know these do not collide.
   *
   *  `leaf`/`depth` pin the applicability to the nest whose leaf was actually RECOGNISED as emitting
   *  `outputs`: the same leaf term one level in is a different claim (its source is a tail-set, not the
   *  nest's source), and a law must not be allowed to answer a question nobody proved anything about.
   *  `keyVariables` names the pattern variables that identify one source path. */
  def patternImage(name: String, leaf: Space, depth: Int, keyVariables: Set[String],
                   outputs: Vector[PathPattern], evidence: LawEvidence): SpatialBoundLaw =
    restChain(name, evidence) { (site, chain) =>
      if chain.depth != depth || chain.leaf != leaf then None
      else
        val src = SpatialTyping.infer(chain.source, site.env)
        val n = src.size
        val len = outputs.map(_.items.size).distinct
        if n.hi == SizeBounds.INF || len.size != 1 then None
        else
          val card = PatternImage.cardinality(Ivl(n.lo, n.hi), keyVariables, outputs)
          Some(SpatialType(Shape.top, SpaceType.closed(len.head.toLong -> card)))
    }

  /** [[SpatialFacts.chainBound]] ROUTED THROUGH THE CHANNEL: the POINTWISE result bound of a
   *  rest-chained iterator nest, `leafInvocations · |leaf|`, which is `Σ K_i`-shaped rather than
   *  `Π K_i`-shaped (whispers §4).
   *
   *  This is where the channel earns its keep: the ordinary `Iteration` shape transfer must OPEN THE
   *  COUNT CHANNELS when the source's head set is not closed (`Shape.openCounts` — an unknown number
   *  of untracked groups are unioned), so a nest over a source whose SHAPE is ⊤ but whose CARDINALITY
   *  is declared infers `size ≤ ∞`.  `chainBound` reads `K_d ≤ E_d ≤ N` off the reduced product
   *  instead and returns a finite number. */
  def restChainPointwise(name: String, evidence: LawEvidence,
                         cfg: SpatialFacts.Config = SpatialFacts.defaults): SpatialBoundLaw =
    restChain(name, evidence) { (site, chain) =>
      SpatialFacts.chainBound(chain, site.env, cfg = cfg).toOption.flatMap { b =>
        val card = b.resultCardinality
        val ln = b.leafType.len
        if card.hi == Ivl.INF || ln.isEmpty then None
        else Some(SpatialType(Shape.top, SpaceType.bounded(ln, card.hi)))
      }
    }

/** carry laws on the annotations every stage already takes (review.md 2: "Carry it in
 *  `SpatialAnnotations`").  An extension rather than a field because `SpatialAnnotations` holds a
 *  [[SpatialConfig]], and THAT is where every other per-run budget and knob lives — a second channel
 *  for the same kind of value would be exactly the drift review.md 3 objects to. */
extension (ann: SpatialAnnotations)
  def withLaws(ls: SpatialBoundLaw*): SpatialAnnotations = ann.copy(config = ann.config.withLaws(ls*))
  def laws: Vector[SpatialBoundLaw] = ann.config.laws
