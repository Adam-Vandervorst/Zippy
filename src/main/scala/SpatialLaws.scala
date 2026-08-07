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
 *  ==WHY A LAW CAN NEVER WIDEN==
 *  The channel is a MEET.  A law supplies one operand of [[SpatialType.meet]]; the other is the type
 *  the transfers derived.  `meet` is the greatest lower bound of the product (componentwise
 *  `Shape.meet` / `SpatialGamma.meetSpace`, then the bidirectional reducer), so
 *  `γ(after) ⊆ γ(before)` holds by the ALGEBRA, whatever the law says — a law can only remove concrete
 *  values from the answer, never add one.  An INAPPLICABLE law is not consulted at all, and a law that
 *  is applicable but contributes no bound is recorded as such and changes nothing.
 *
 *  ==WHAT A LAW IS RESPONSIBLE FOR, THEN==
 *  Exactly one thing: that the bound it contributes is TRUE of the values the site can denote.  It is
 *  not a widening hazard, it is a SOUNDNESS PREMISE, and that is why every law carries
 *  [[LawEvidence]] — `executable-checked`, `SMT-proved`, or `ASSUMED` — and why the provenance travels
 *  all the way to the node ([[NodeAnalysis.laws]]) instead of being folded silently into a number.
 *  `SpatialAnalysis.assumedLaws` names every law that tightened an answer without a discharged proof
 *  obligation, so a consumer can refuse to act on one.
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
  def show: String = toString

/** ONE LAW APPLICATION, kept ON the node so a consumer can see WHICH law tightened WHAT (review.md 2).
 *  `occurrences` counts the observations of this position at which the same (law, outcome) recurred —
 *  a binder body under a 16-level nest has thousands, and keeping one record per observation would be
 *  a memory leak dressed up as provenance. */
final case class LawApplication(law: String, evidence: LawEvidence, at: NodeId, outcome: LawOutcome,
                                before: SpatialType, after: SpatialType, why: String,
                                occurrences: Int = 1):
  def tightened: Boolean = outcome == LawOutcome.Tightened
  /** the bound is in use AND rests on an undischarged axiom */
  def assumed: Boolean = tightened && !evidence.discharged
  def show: String =
    s"$law ${outcome.show} at ${at.show}" + (if occurrences > 1 then s" (x$occurrences)" else "") +
    s" [${evidence.tag}]" + (if outcome == LawOutcome.Tightened then s": ${before.show.take(60)} -> ${after.show.take(60)}" else "") +
    (if why.isEmpty then "" else s" — $why")

object SpatialLaws:
  import Lower.{LenBounds, SizeBounds}

  // ================================================================================================
  // 1.  THE ENGINE
  // ================================================================================================

  /** MEET every applicable law's bound into `site.inferred`, in order, and report what each did.
   *
   *  Laws are applied LEFT TO RIGHT and each sees the previous one's result, so a law whose premise is
   *  "the length is pinned" can be enabled by an earlier law that pinned it.  The result is
   *  order-INDEPENDENT in γ (meet is commutative and associative on the lattice) but the recorded
   *  `before`/`after` of an individual application is not, which is the honest reading of "this law
   *  tightened this much GIVEN what was already known". */
  def refine(laws: Vector[SpatialBoundLaw], site: LawSite): (SpatialType, Vector[LawApplication]) =
    if laws.isEmpty then (site.inferred, Vector.empty)
    else
      var cur = site.inferred
      val out = Vector.newBuilder[LawApplication]
      for law <- laws do
        val here = site.copy(inferred = cur)
        if law.applies(here) then
          law.bound(here) match
            case None =>
              out += LawApplication(law.name, law.evidence, site.id, LawOutcome.NoBound, cur, cur,
                                    "applicable, but its premises are not established at this occurrence")
            case Some(b) =>
              // THE MEET IS THE WHOLE SAFETY ARGUMENT: γ(next) ⊆ γ(cur) by construction, so a law
              // cannot widen no matter what it claims (see the file header).
              val next = SpatialType.meet(cur, b)
              if next.uninhabited && !cur.uninhabited then
                out += LawApplication(law.name, law.evidence, site.id, LawOutcome.Contradicted, cur, cur,
                                      s"the law's bound ${b.show.take(60)} and the transfers describe no " +
                                      "common concrete space: the law is DROPPED, not propagated")
              else if next == cur then
                out += LawApplication(law.name, law.evidence, site.id, LawOutcome.Unchanged, cur, cur,
                                      "the transfers already proved at least this much")
              else
                out += LawApplication(law.name, law.evidence, site.id, LawOutcome.Tightened, cur, next, "")
                cur = next
      (cur, out.result())

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
