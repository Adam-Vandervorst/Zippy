package morkl

import Lower.LenBounds

/** THE CONSUMER-FACING SPATIAL TYPECHECKER  (review.md 1).
 *
 *  ==THREE QUESTIONS, WHICH ONE BOOLEAN MUST NOT ANSWER==
 *  The subsystem already decided all three, in three adjacent places, with three different
 *  completeness stories.  This file is the one door, and it keeps them apart BY TYPE:
 *
 *  | question                                                     | entry point                    | soundness / completeness                                        |
 *  |--------------------------------------------------------------|--------------------------------|-----------------------------------------------------------------|
 *  | does this CONCRETE space inhabit this spatial type?           | [[SpatialCheck.value]]         | SOUND and COMPLETE for this carrier — it *is* γ                  |
 *  | is an inferred type ABSTRACTLY INCLUDED in a declared one?    | [[SpatialCheck.types]]         | `Proved` sound-incomplete; `Refuted` sound and witnessed         |
 *  | does this ROUTINE have the declared spatial signature?        | [[SpatialCheck.checkRoutine]]  | `Proved` sound modulo the annotations; never `Refuted` from imprecision |
 *
 *  ==WHAT EACH VERDICT MEANS, EXACTLY==
 *   - `Proved(inferred, cert)` — `SpatialType.leq(inferred, declared)` held, so `γ(inferred) ⊆
 *     γ(declared)`, and every concrete result of the routine inhabits `γ(inferred)` PROVIDED the
 *     declared input types hold and the transfers are sound.  The certificate names those assumptions
 *     instead of leaving them implicit, and carries a bounded exhaustive CORROBORATION of the order's
 *     answer, so a bug in the order does not silently become a guarantee.
 *   - `Refuted(inferred, witness)` — a CONCRETE `SpaceValue` was exhibited that inhabits `γ(inferred)`
 *     and not `γ(declared)`.  That is a complete refutation of ABSTRACT CONFORMANCE: no repair of the
 *     order can ever prove this signature from this inferred type, so the declaration, the input
 *     annotations, or the precision of the analysis has to change.  It is deliberately NOT a claim that
 *     the routine can produce that value — the inferred type OVER-approximates the routine's image, so
 *     the witness may be a spurious member introduced by abstraction (whispers.md §2 is right about
 *     this and the wording here follows it).  A SEMANTIC refutation needs an evaluated input/output
 *     witness, and an analysis may not evaluate its subject; see NO EVALUATION below.
 *   - `Unknown(inferred, reason)` — everything else, and in particular EVERY `false` from the order.  A
 *     `false` from `leq` is "not proved", never "does not typecheck": the order's own finite-universe
 *     measurement puts roughly 17% of true containments beyond it.  The reason says WHICH kind of
 *     not-proved it is — the order's documented incompleteness (an exhaustive search of the bounded
 *     universe found no witness), an exhausted search budget (no claim either way), a vacuous ⊥, or a
 *     missing annotation.
 *
 *  ==NO EVALUATION==
 *  Nothing in this file calls `eval`/`evalI`/`evalT`/`exec*`, directly or transitively.  The bounded
 *  refuter searches a finite universe of CONCRETE SPACES and asks γ about each; it never runs the
 *  routine.  That is exactly why `Refuted` is scoped to abstract conformance: refuting the routine
 *  itself would require executing it, which belongs to test ground truth — `SpatialCheckCheck` does run
 *  `eval` and compares its semantic verdict against this one, which is the honest place for it.
 *
 *  ==DIAGNOSTICS==
 *  A failed proof reports, per failing RESULT CHANNEL (ε / a tracked head / the untracked-head count /
 *  `otherTail` / a length class / the spill window / the spill aggregate / a reduced projection): what
 *  the inferred type says, what the declaration demands, whether that channel's test is a SUFFICIENT
 *  CONDITION ONLY (the documented incompleteness), the SOURCE NODE as a [[NodeId]] of the decorated
 *  analysis, and the ASSUMPTION the analysis relied on at that node. */

// ==================================================================================================
// 1.  THE SIGNATURE
// ==================================================================================================

/** THE declared type of one path parameter.
 *
 *  review.md 1 sketches `paths: Map[PathRef, PathType]`; whispers.md §2 spells the payload out as
 *  `SpatialPathInput(value: Option[PathValue], len: LenBounds)`.  They are the same thing, so this
 *  carries whispers' payload under the review's name.  The two cases are not interchangeable: a KNOWN
 *  path value is what keeps `Wrap`/`Unwrap`/`Singleton` exact (the shape transfer reads the actual
 *  items), while an OPAQUE ref carries only a length bound — what an iteration head, a fold accumulator
 *  or a caller-supplied path is.
 *
 *  One correction to whispers: a known value must SATISFY its own length type.  whispers lets the two
 *  fields disagree, and a disagreement is resolved differently by the two halves of the analysis
 *  (`SpatialTyping.Env.paths` uses the value's real length, `SpatialEnv.paths` the declared bound), so
 *  the same signature would mean two things. */
final case class PathType(value: Option[PathValue], len: LenBounds):
  require(value.forall(v => !len.isEmpty && len.lo <= v.items.length && v.items.length <= len.hi),
          s"a KNOWN path value must inhabit its own length type: ${value.map(_.show)} against " +
            s"[${len.lo}, ${len.hi}]")
  def isKnown: Boolean = value.isDefined
  def show: String = value match
    case Some(v) => s"= \"${v.show}\""
    case None => s"opaque[${len.lo}, ${if len.hi == LenBounds.INF then "inf" else len.hi}]"

object PathType:
  def known(v: PathValue): PathType = PathType(Some(v), LenBounds(v.items.length, v.items.length))
  def known(items: PathItem*): PathType = known(PathValue(items.toList))
  def opaque(k: LenBounds): PathType = PathType(None, k)
  def opaque(lo: Long, hi: Long): PathType = PathType(None, LenBounds(lo, hi))
  /** a ref that IS bound but about which nothing is declared */
  val unknown: PathType = PathType(None, LenBounds.unknown)

/** THE ROUTINE-LEVEL CONTRACT review.md 1 asks for: a declared type for every path ref and space
 *  mention the routine takes, and the expected result type.  Keyed by the routine's own PARAMETER
 *  names, so a signature is checkable against the routine without a call site. */
final case class SpatialSignature(paths: Map[PathRef, PathType],
                                  spaces: Map[SpaceMention, SpatialType],
                                  result: SpatialType):

  /** the analysis environment this signature denotes.
   *
   *  Two deliberate differences from whispers.md §2's `env`:
   *
   *   - it does NOT also populate `lenv.spaces`/`lenv.paths`.  `SpatialTyping.Env.lengths` already
   *     derives both from `spaces`/`paths`/`opaque`, and `lenv.paths` is layered ON TOP of the derived
   *     map — so filling it in duplicates the declaration and, when the two disagree, the duplicate
   *     silently wins.  [[PathType]]'s `require` closes the same hole from the other side.
   *   - `active` defaults to empty here and [[SpatialCheck.report]] passes `Set(routine.name)`:
   *     whispers is right that the routine under check must be marked ACTIVE, so a direct self-call
   *     widens to ⊤ instead of being inlined one level by the ordinary interprocedural transfer.  It
   *     costs nothing for a non-recursive routine and makes the verdict independent of how far the
   *     inliner happened to get before a budget fired.  A bound for recursion is `SpatialRecursion`'s
   *     job, through a certified summary. */
  def env(routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
          active: Set[RoutinePtr] = Set.empty): SpatialTyping.Env =
    SpatialTyping.Env(
      spaces = spaces,
      paths = paths.collect { case (r, PathType(Some(v), _)) => r -> v },
      lenv = SpatialEnv(routines = routines, active = active),
      opaque = paths.collect { case (r, PathType(None, k)) => r -> k })

  /** the parameters the signature says nothing about.  A missing annotation is not an error — the
   *  analysis widens to ⊤, which is sound, and a proof under ⊤ inputs is STRONGER than the signature
   *  asks for — but it is worth naming, because declaring them is usually what turns an `Unknown` into
   *  a `Proved`. */
  def missing(r: Routine): (Vector[PathRef], Vector[SpaceMention]) =
    (r.refs.filterNot(paths.contains), r.mentions.filterNot(spaces.contains))

  def show: String =
    val ps = paths.toVector.sortBy(_._1.s).map((r, t) => s"${r.s}: ${t.show}")
    val ss = spaces.toVector.sortBy(_._1.s).map((m, t) => s"${m.s}: ${t.show}")
    s"(${(ps ++ ss).mkString("; ")}) -> ${result.show}"

  /** THE BRIDGE to the pipeline's input-annotation value (review.md 6 asks for ONE of these, not one
   *  per stage).  A signature is exactly `SpatialAnnotations` plus a declared RESULT, and this is the
   *  isomorphism: [[PathType]]'s two cases are the pipeline's `paths` (known constant) and `pathLens`
   *  (bounded length) maps.  Going through here rather than re-deriving an environment is what keeps
   *  the checker and the optimizer analysing the same routine under the same premises. */
  def annotations(routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                  config: SpatialConfig = SpatialConfig.default): SpatialAnnotations =
    SpatialAnnotations(spaces = spaces,
                       paths = paths.collect { case (r, PathType(Some(v), _)) => r -> v },
                       pathLens = paths.collect { case (r, PathType(None, k)) => r -> k },
                       routines = routines, config = config)

object SpatialSignature:
  def of(result: SpatialType): SpatialSignature = SpatialSignature(Map.empty, Map.empty, result)

  /** the other direction of the bridge.  A ref the pipeline lists in BOTH maps is OPAQUE, because that
   *  is how `SpatialTyping.Env` reads it (`opaque` shadows `paths` in `constPath` and in `lengths`) — a
   *  signature that called it known would analyse a body the pipeline analyses differently. */
  def from(ann: SpatialAnnotations, result: SpatialType): SpatialSignature =
    SpatialSignature(
      ann.paths.view.mapValues(PathType.known).toMap ++ ann.pathLens.view.mapValues(PathType.opaque).toMap,
      ann.spaces, result)

// ==================================================================================================
// 2.  RESULT CHANNELS — where a check fails
// ==================================================================================================

/** ONE CHANNEL OF THE CARRIER, as a location a failure is attributed to.  These are exactly the clauses
 *  of the two predicates being mirrored — `SpatialType.accepts` (concrete membership) and
 *  `SpatialType.leq` = `Shape.leqStrong` × `SpatialGamma.leqSpace` (abstract inclusion) — so a
 *  diagnosis names the real reason the real predicate said no, not a plausible story about it.
 *
 *  `prefix` is the path of tracked head items from the root of the shape down to the node whose channel
 *  failed, so `Head(List("a","b"))` reads "the head `b` under `a`". */
enum ResultChannel:
  /** the declared type is the explicit ⊥: no concrete space inhabits it */
  case Bottom
  /** the ε (empty-path) presence channel of the shape node at `prefix` */
  case Eps(prefix: List[PathItem])
  /** the tracked head `prefix.last`: its subtree is not admitted */
  case Head(prefix: List[PathItem])
  /** the untracked-head COUNT (`others`) of the shape node at `prefix` */
  case UntrackedCount(prefix: List[PathItem])
  /** the untracked-head TAIL SUMMARY (`otherTail`) of the shape node at `prefix` */
  case OtherTail(prefix: List[PathItem])
  /** the comparison ran out of shape depth before deciding this subtree */
  case DepthCap(prefix: List[PathItem])
  /** the count class for paths of exactly `len` items */
  case LengthClass(len: Long)
  /** the spill bucket's LENGTH WINDOW (`restLens`) */
  case SpillWindow
  /** the spill bucket's AGGREGATE COUNT (`rest`) */
  case SpillAggregate
  /** the reduced cardinality projection */
  case Size
  /** the reduced ∀-path length projection */
  case Len

  /** the shape depth (or path length) this channel lives at — what the witness search needs in order to
   *  know how long the paths in its universe have to be */
  def depthHint: Long = this match
    case Eps(p) => p.length.toLong
    case Head(p) => p.length.toLong
    case UntrackedCount(p) => p.length.toLong + 1L
    case OtherTail(p) => p.length.toLong + 2L
    case DepthCap(p) => p.length.toLong + 1L
    case LengthClass(l) => l
    case SpillWindow | SpillAggregate => 1L
    case Size | Len | Bottom => 1L

  /** the channel's KIND, with the location dropped — what a summary groups by.  Two failures at
   *  different tracked heads are the same kind of failure and a histogram over `show` would drown in
   *  one row per head. */
  def kind: String = this match
    case Bottom => "bottom"
    case Eps(_) => "eps"
    case Head(_) => "head"
    case UntrackedCount(_) => "untracked-head count"
    case OtherTail(_) => "otherTail summary"
    case DepthCap(_) => "shape depth cap"
    case LengthClass(_) => "length class"
    case SpillWindow => "spill length window"
    case SpillAggregate => "spill aggregate count"
    case Size => "size projection"
    case Len => "length projection"

  def show: String =
    def at(p: List[PathItem]) = if p.isEmpty then "root" else p.mkString(".")
    this match
      case Bottom => "⊥ (the declared type admits nothing)"
      case Eps(p) => s"ε @ ${at(p)}"
      case Head(p) => s"head ${at(p)}"
      case UntrackedCount(p) => s"untracked-head count @ ${at(p)}"
      case OtherTail(p) => s"otherTail summary @ ${at(p)}"
      case DepthCap(p) => s"shape depth cap @ ${at(p)}"
      case LengthClass(l) => s"length class $l"
      case SpillWindow => "spill length window"
      case SpillAggregate => "spill aggregate count"
      case Size => "size projection"
      case Len => "length projection"

/** ONE FAILING CHANNEL, with both sides quoted.
 *
 *  `sufficientOnly` marks a channel whose test is documented as a SUFFICIENT CONDITION for the order
 *  and is known to reject genuine containments: the spill window and the spill aggregate (the
 *  integer-partition reasoning the order does not attempt), the untracked-count lower bound, the
 *  `otherTail` clauses, and the depth cap.  It is a HINT about where to look, never a verdict — the
 *  bounded witness search is what decides, and `Refuted` is only ever returned with a witness in hand. */
final case class ChannelFailure(channel: ResultChannel, inferredSays: String, declaredSays: String,
                                why: String, sufficientOnly: Boolean = false):
  def show: String =
    s"${channel.show}: inferred $inferredSays vs declared $declaredSays — $why" +
      (if sufficientOnly then "  [SUFFICIENT CONDITION ONLY]" else "")

// ==================================================================================================
// 3.  ASSUMPTIONS — what a `Proved` is proved *modulo*
// ==================================================================================================

/** The premises a spatial verdict rests on.  A `Proved` that does not name these is the "marketing fog"
 *  review.md 1 warns about: the analysis TRUSTS the declared input types, trusts its own transfers, and
 *  degrades to ⊤ in named places. */
enum SpatialAssumption:
  /** the declared type of a space parameter is TRUSTED, not verified — a caller that violates it
   *  invalidates the whole proof, which is what `SpecializedRoutine.applicableTo` re-checks */
  case InputSpaceAnnotation(m: SpaceMention, t: SpatialType)
  /** likewise for a path parameter (including a `PathRef.lengthHint`) */
  case InputPathAnnotation(r: PathRef, t: PathType)
  /** a parameter with NO declaration: the analysis used ⊤ */
  case MissingSpaceAnnotation(m: SpaceMention)
  case MissingPathAnnotation(r: PathRef)
  /** every transfer in `SpatialTypes`/`SpatialTyping`/`Shape` is sound (differentially tested against
   *  `eval`, γ-gated on the corpus, not mechanically verified) */
  case TransferSoundness
  /** the analysis budgets: a term past them degrades to ⊤ */
  case AnalysisBudgets(cfg: SpatialConfig)
  /** the traversal actually hit a budget at this occurrence and returned ⊤ */
  case BudgetTop(where: NodeId)
  /** a callee's body was analysed from the supplied table */
  case RoutineBody(r: RoutinePtr)
  /** a call to a routine the table does not contain: ⊤ */
  case MissingRoutine(r: RoutinePtr)
  /** a SELF-call: the routine under check is marked active, so the call is ⊤.  A recursive routine
   *  therefore needs `SpatialRecursion`'s certified summary, not this checker. */
  case RecursionWidened(r: RoutinePtr)
  /** an arbitrary Scala function: ⊤, nothing is claimed */
  case OpaqueGrounded
  /** the `Fixpoint` transfer's certified post-fixpoint (or ⊤ when none was found) */
  case FixpointPostFixpoint
  /** the head-group union: one body shape per group, count channels opened for the untracked arm */
  case HeadGroupUnion

  def show: String = this match
    case InputSpaceAnnotation(m, t) => s"declared input ${m.s}: ${t.show} (TRUSTED)"
    case InputPathAnnotation(r, t) => s"declared input ${r.s}: ${t.show} (TRUSTED)"
    case MissingSpaceAnnotation(m) => s"NO declaration for ${m.s} — analysed as ⊤"
    case MissingPathAnnotation(r) => s"NO declaration for ${r.s} — analysed as ⊤"
    case TransferSoundness => "the abstract transfers are sound"
    case AnalysisBudgets(c) => s"analysis budgets (shape ${c.shapeDepth}x${c.shapeWidth}, nodes " +
      s"${c.nodeBudget}, reduce ${c.reduceRounds}, fixpoint ${c.fixpointRounds})"
    case BudgetTop(w) => s"a budget fired at ${w.show}: that occurrence is ⊤"
    case RoutineBody(r) => s"the supplied body of ${r.s}"
    case MissingRoutine(r) => s"${r.s} is not in the routine table — the call is ⊤"
    case RecursionWidened(r) => s"the self-call to ${r.s} is ⊤ (use SpatialRecursion for a bound)"
    case OpaqueGrounded => "a grounded Scala function is ⊤"
    case FixpointPostFixpoint => "the Fixpoint transfer's certified post-fixpoint"
    case HeadGroupUnion => "the head-group union (one body per group; untracked arm count-opened)"

// ==================================================================================================
// 4.  THE CHANNEL MIRRORS
// ==================================================================================================

/** The two predicates, re-run clause by clause so that a failure has a LOCATION.
 *
 *  These are MIRRORS, not second implementations of the laws: the verdict is always taken from the
 *  owning domain (`SpatialTyping.accepts` / `SpatialType.leq`) and these only explain it.  When a
 *  mirror and its owner disagree, the verdict is unchanged and a NOTE says so
 *  ([[SpatialCheck.mirrorNote]] / [[SpatialCheck.orderMirrorNote]]) — a diagnosis that can drift from
 *  the law it explains is worse than no diagnosis, so `SpatialCheckCheck` gates that they never do over
 *  a randomized pool. */
object SpatialChannels:

  private def ivl(i: Ivl): String = i.show
  private def pres(p: Presence): String = p match
    case Presence.No => "absent"
    case Presence.May => "may be present"
    case Presence.Must => "PRESENT"

  // ---- concrete membership: why is `v` not in γ(t)?  (mirror of SpatialType.accepts) --------------

  /** every channel of `t` that the concrete value `v` violates.  Empty ⟺ `SpatialTyping.accepts`. */
  def valueFailures(v: SpaceValue, t: SpatialType): Vector[ChannelFailure] =
    if t.uninhabited then
      Vector(ChannelFailure(ResultChannel.Bottom, s"the value ${v.pretty}", "⊥",
                            "the declared type is the explicit bottom: no concrete space inhabits it"))
    else
      val out = Vector.newBuilder[ChannelFailure]
      out ++= shapeValueFailures(t.shape, v, Nil, 64)
      out ++= histValueFailures(t.lens, v)
      val n = v.paths.size.toLong
      val sz = t.size
      if n < sz.lo || n > sz.hi then
        out += ChannelFailure(ResultChannel.Size, s"[${sz.lo}, ${sz.hi}] paths", s"$n paths",
                              "the reduced cardinality projection excludes this count")
      val b = t.len
      val bad = v.paths.filter(p => b.isEmpty || p.items.length < b.lo || p.items.length > b.hi)
      if bad.nonEmpty then
        out += ChannelFailure(ResultChannel.Len, s"every path has [${b.lo}, ${b.hi}] items",
                              bad.map(_.show).toVector.sorted.take(3).mkString(", "),
                              "the reduced ∀-path length projection excludes those paths")
      out.result()

  /** mirror of `Shape.contains`, channel by channel */
  private def shapeValueFailures(sh: Shape, v: SpaceValue, prefix: List[PathItem],
                                 d: Int): Vector[ChannelFailure] =
    if d <= 0 then Vector.empty
    else
      val out = Vector.newBuilder[ChannelFailure]
      val hasEps = v.paths.contains(PathValue(Nil))
      val epsOk = sh.eps match
        case Presence.No => !hasEps
        case Presence.Must => hasEps
        case Presence.May => true
      if !epsOk then
        out += ChannelFailure(ResultChannel.Eps(prefix), pres(sh.eps),
                              if hasEps then "ε present" else "ε absent",
                              "the ε channel of this shape node excludes the value's empty path")
      val groups: Map[PathItem, SpaceValue] =
        v.paths.iterator.collect { case PathValue(h :: t) => (h, PathValue(t)) }
          .toVector.groupMap(_._1)(_._2).view.mapValues(ts => SpaceValue(ts.toSet)).toMap
      val untracked = groups.filter((h, _) => !sh.heads.contains(h))
      val n = untracked.size.toLong
      if n < sh.others.lo || n > sh.others.hi then
        out += ChannelFailure(ResultChannel.UntrackedCount(prefix), ivl(sh.others),
                              s"$n untracked heads (${untracked.keys.toVector.sorted.take(3).mkString(",")})",
                              "the untracked-head count channel excludes the value")
      for (h, tv) <- groups.toVector.sortBy(_._1) if sh.heads.contains(h) do
        out ++= shapeValueFailures(sh.heads(h), tv, prefix :+ h, d - 1)
      for (h, c) <- sh.heads.toVector if !groups.contains(h) do
        // a tracked head the value does NOT have: its child must admit the empty tail-set
        if shapeValueFailures(c, SpaceValue(Set.empty), prefix :+ h, d - 1).nonEmpty then
          out += ChannelFailure(ResultChannel.Head(prefix :+ h), c.show, "absent",
                                "this tracked head is FORCED present and the value does not have it")
      for ot <- sh.otherTail; (h, tv) <- untracked.toVector.sortBy(_._1) do
        if shapeValueFailures(ot, tv, prefix :+ h, d - 1).nonEmpty then
          out += ChannelFailure(ResultChannel.OtherTail(prefix), ot.show,
                                s"the tail-set under untracked head $h is ${tv.pretty}",
                                "the untracked-head tail summary does not admit that tail-set")
      out.result()

  /** mirror of `SpatialGamma.gammaSpace`.  The clause review.md 1's first required test is about is the
   *  tracked LOWER bound of a class the value leaves EMPTY — precisely the gap
   *  `SpatialTyping.withinEnvelope` has and `accepts` does not. */
  private def histValueFailures(t: SpaceType, v: SpaceValue): Vector[ChannelFailure] =
    val cnt: Map[Long, Long] = v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap
    val out = Vector.newBuilder[ChannelFailure]
    for (l, c) <- t.byLen do
      val n = cnt.getOrElse(l, 0L)
      if n < c.lo || n > c.hi then
        out += ChannelFailure(ResultChannel.LengthClass(l), ivl(c), s"$n paths of $l items",
          if n == 0 && c.lo >= 1 then
            s"the class demands at least ${c.lo} paths of $l items and the value has NONE — this is " +
              "exactly the tracked lower bound on an ABSENT length class that an envelope check skips"
          else "the count class excludes that many paths of that length")
    val residual = cnt.filter((l, _) => !t.byLen.contains(l))
    val outside = residual.filter((l, n) => n != 0L &&
      !(t.rest.hi > 0 && !t.restLens.isEmpty && t.restLens.lo <= l && l <= t.restLens.hi))
    if outside.nonEmpty then
      out += ChannelFailure(ResultChannel.SpillWindow,
        if t.rest.hi == 0 then "no untracked lengths at all"
        else s"untracked lengths [${t.restLens.lo}, ${t.restLens.hi}]",
        s"paths of ${outside.keys.toVector.sorted.mkString(",")} items",
        "the value populates a length the type neither tracks nor covers with its spill window")
    var tot = 0L
    for (_, n) <- residual do tot = Ivl.add(tot, n)
    if tot < t.rest.lo || tot > t.rest.hi then
      out += ChannelFailure(ResultChannel.SpillAggregate, ivl(t.rest), s"$tot paths",
        "the aggregate count at untracked lengths is outside the spill bucket")
    out.result()

  // ---- abstract inclusion: which clause of the order failed?  (mirror of SpatialType.leq) ---------

  /** every clause of `SpatialType.leq(a, b)` that failed.  Empty ⟺ the order holds. */
  def orderFailures(a: SpatialType, b: SpatialType): Vector[ChannelFailure] =
    if a.uninhabited then Vector.empty          // ⊥ is below everything — vacuously; see `SpatialCheck`
    else if b.uninhabited then
      Vector(ChannelFailure(ResultChannel.Bottom, a.show, "⊥",
                            "the declared type is the explicit bottom and the inferred one is not"))
    else shapeOrderFailures(a.shape, b.shape, Nil, 32) ++ histOrderFailures(a.lens, b.lens)

  /** mirror of `Shape.leqStrong`, clause for clause and with its own depth budget */
  private def shapeOrderFailures(a: Shape, b: Shape, prefix: List[PathItem],
                                 d: Int): Vector[ChannelFailure] =
    if b.isTop then Vector.empty
    else if d <= 0 then
      Vector(ChannelFailure(ResultChannel.DepthCap(prefix), a.show, b.show,
                            "the order ran out of depth before deciding this subtree",
                            sufficientOnly = true))
    else
      val out = Vector.newBuilder[ChannelFailure]
      if !(b.eps == Presence.May || b.eps == a.eps) then
        out += ChannelFailure(ResultChannel.Eps(prefix), pres(a.eps), pres(b.eps),
          "the declaration pins the ε channel and the inferred type does not match it")
      for h <- (a.heads.keySet ++ b.heads.keySet).toVector.sorted do
        out ++= shapeOrderFailures(a.under(h), b.under(h), prefix :+ h, d - 1)
      val hiOut = Ivl.add(a.heads.count((h, t) => !b.heads.contains(h) && t.possiblyNonEmpty).toLong,
                          a.others.hi)
      val bOnly = b.heads.keySet.diff(a.heads.keySet).size.toLong
      val loOut = Ivl.add(Ivl.relu(a.others.lo - bOnly),
                          a.heads.count((h, t) => !b.heads.contains(h) && t.definitelyNonEmpty).toLong)
      if hiOut > b.others.hi then
        out += ChannelFailure(ResultChannel.UntrackedCount(prefix),
          s"up to $hiOut heads outside the declared head set", ivl(b.others),
          "the inferred type permits more heads outside the declared head set than it allows")
      else if b.others.lo > loOut then
        out += ChannelFailure(ResultChannel.UntrackedCount(prefix),
          s"at least $loOut such heads are forced", ivl(b.others),
          "the declaration FORCES untracked heads the inferred type does not guarantee",
          sufficientOnly = true)
      for bt <- b.otherTail do
        val badTracked = a.heads.toVector.filter((h, t) =>
          !b.heads.contains(h) && t.possiblyNonEmpty && !Shape.leqStrong(t, bt))
        if badTracked.nonEmpty then
          out += ChannelFailure(ResultChannel.OtherTail(prefix),
            badTracked.map((h, t) => s"${h}·${t.show}").mkString(", "), bt.show,
            "a head the inferred type tracks falls outside the declared untracked-tail summary",
            sufficientOnly = true)
        if a.others.hi > 0 && !Shape.leqStrong(a.otherTail.getOrElse(Shape.top), bt) then
          out += ChannelFailure(ResultChannel.OtherTail(prefix),
            a.otherTail.map(_.show).getOrElse("⊤"), bt.show,
            "the inferred untracked-tail summary is not inside the declared one",
            sufficientOnly = true)
      out.result()

  /** mirror of `SpatialGamma.leqSpace`.  The spill clauses carry `sufficientOnly` because they are
   *  exactly the integer-partition reasoning the order documents itself as not attempting — the source
   *  of the false negatives review.md 1 measures at ~17.2%. */
  private def histOrderFailures(a: SpaceType, b: SpaceType): Vector[ChannelFailure] =
    val out = Vector.newBuilder[ChannelFailure]
    for l <- (a.byLen.keySet ++ b.byLen.keySet).toVector.sorted do
      val (x, y) = (a.at(l), b.at(l))
      if y.lo > x.lo || x.hi > y.hi then
        out += ChannelFailure(ResultChannel.LengthClass(l), ivl(x), ivl(y),
          if y.lo > x.lo then s"the declaration demands at least ${y.lo} paths of $l items and the " +
                              s"inferred type only guarantees ${x.lo}"
          else s"the inferred type permits up to ${x.hi} paths of $l items and the declaration " +
               s"allows ${y.hi}")
    if !(a.rest.hi == 0 || a.restLens.isEmpty ||
         (b.rest.hi > 0 && !b.restLens.isEmpty &&
          b.restLens.lo <= a.restLens.lo && a.restLens.hi <= b.restLens.hi)) then
      out += ChannelFailure(ResultChannel.SpillWindow,
        s"spill ${ivl(a.rest)} over lengths [${a.restLens.lo}, ${a.restLens.hi}]",
        if b.rest.hi == 0 then "no spill bucket at all"
        else s"spill ${ivl(b.rest)} over lengths [${b.restLens.lo}, ${b.restLens.hi}]",
        "the order requires the inferred spill window to nest inside the declared one; when the " +
          "declaration TRACKS those lengths instead, containment can still hold — the order does not " +
          "do that integer-partition reasoning",
        sufficientOnly = true)
    var hiOut = if a.rest.hi > 0 then a.rest.hi else 0L
    var loOut =
      if a.rest.lo == 0 || a.restLens.isEmpty then 0L
      else if b.byLen.keysIterator.exists(l => a.restLens.lo <= l && l <= a.restLens.hi) then 0L
      else a.rest.lo
    for (l, c) <- a.byLen if !b.byLen.contains(l) do
      hiOut = Ivl.add(hiOut, c.hi); loOut = Ivl.add(loOut, c.lo)
    if hiOut > b.rest.hi then
      out += ChannelFailure(ResultChannel.SpillAggregate,
        s"up to $hiOut paths at lengths the declaration does not track", ivl(b.rest),
        "the aggregate at untracked lengths exceeds the declared spill bucket")
    else if b.rest.lo > loOut then
      out += ChannelFailure(ResultChannel.SpillAggregate,
        s"at least $loOut such paths are guaranteed", ivl(b.rest),
        "the declared spill bucket has a lower bound the inferred type does not discharge; the order " +
          "gives up a side's spill lower bound as soon as the other side tracks a length inside its " +
          "window, so this clause rejects genuine containments",
        sufficientOnly = true)
    out.result()
end SpatialChannels

// ==================================================================================================
// 5.  THE BOUNDED EXHAUSTIVE REFUTER
// ==================================================================================================

/** THE BUDGET of the witness search, in the terms whispers.md §2 insists on reporting rather than
 *  hanging inside: an item alphabet, a maximum path length, hence a path count `P`, hence `2^P`
 *  candidate spaces.  For alphabet size `A` and length `L` the path count is `Σ A^i`, so two items with
 *  `L = 2` is `2^7 = 128` spaces while two items with `L = 4` is already `2^31` — which is why
 *  `maxPaths` exists and why a truncated universe is REPORTED as truncated. */
final case class WitnessSearch(maxItems: Int = 3, maxLen: Int = 3, maxPaths: Int = 16,
                               maxCandidates: Long = 200000L):
  require(maxItems >= 1 && maxLen >= 0 && maxPaths >= 0 && maxCandidates >= 1)

object WitnessSearch:
  val default: WitnessSearch = WitnessSearch()
  /** the cheap corroboration budget used on a `Proved`, where the search is a cross-check on the order
   *  rather than the decision procedure */
  val corroboration: WitnessSearch = WitnessSearch(maxItems = 3, maxLen = 2, maxPaths = 12,
                                                   maxCandidates = 8192L)
  /** no search at all — `Refuted` then becomes unreachable, which is why it is not the default */
  val off: WitnessSearch = WitnessSearch(maxItems = 1, maxLen = 0, maxPaths = 0, maxCandidates = 1L)

/** the finite universe actually searched — reported, never implied */
final case class WitnessUniverse(items: Vector[PathItem], lens: LenBounds, paths: Vector[PathValue],
                                 truncated: Boolean):
  def spaceCount: BigInt = BigInt(1) << paths.size
  def show: String =
    s"alphabet {${items.mkString(",")}}, path lengths [${lens.lo}, ${lens.hi}], ${paths.size} paths " +
      s"⇒ $spaceCount candidate spaces" +
      (if truncated then " (TRUNCATED: the full universe over that alphabet is larger)" else "")

/** the outcome of one bounded search.  FOUR states, and they mean different things:
 *   - `refutes` — a real member of `γ(inferred) ∖ γ(declared)`: abstract inclusion is REFUTED,
 *     completely and permanently;
 *   - `completeOnUniverse` — the whole enumerated universe was checked and holds no witness.  The
 *     order's `false` is then its own incompleteness AS FAR AS THIS UNIVERSE CAN SEE; it is NOT a proof
 *     of containment, because the universe is bounded (and possibly truncated);
 *   - `exhaustedBudget` — the search stopped early.  No claim in either direction;
 *   - `outOfScope` — NO space in the universe could inhabit the inferred type in the first place (it
 *     requires more paths than the universe has).  Every candidate was pruned, so "no witness found" is
 *     VACUOUSLY true and must not read as an exhaustive pass — the first version of this file reported
 *     that case as `completeOnUniverse`, which is exactly the kind of quiet over-claim the three-way
 *     API exists to prevent. */
final case class WitnessReport(universe: WitnessUniverse, examined: Long, budget: Long,
                               prunedByCardinality: BigInt, finished: Boolean, outOfScope: Boolean,
                               witness: Option[SpaceValue]):
  def refutes: Boolean = witness.isDefined
  def exhaustedBudget: Boolean = witness.isEmpty && !finished
  def completeOnUniverse: Boolean = witness.isEmpty && finished && !outOfScope
  def show: String =
    val head = witness match
      case Some(w) => s"WITNESS ${w.pretty}"
      case None if outOfScope =>
        "OUT OF SCOPE: no space in this universe has enough paths to inhabit the inferred type, so " +
          "nothing was decided"
      case None if finished => "no witness anywhere in the enumerated universe"
      case None => s"UNDECIDED: the budget of $budget candidates ran out"
    s"$head — ${universe.show}; examined $examined, $prunedByCardinality pruned by cardinality"

// ==================================================================================================
// 6.  THE VERDICTS
// ==================================================================================================

/** CONCRETE MEMBERSHIP — the question that can be, and here is, SOUND AND COMPLETE for this carrier.
 *  Decided by `SpatialTyping.accepts` (full γ), never by `withinEnvelope`, which admits values outside
 *  γ.  `Rejected` carries the channels the value violates, so "not a member" is actionable.  Adopted
 *  from whispers.md §2's `ValueCheck`, with the channel diagnosis added. */
enum ValueCheck:
  case Accepted(value: SpaceValue, expected: SpatialType)
  case Rejected(value: SpaceValue, expected: SpatialType, channels: Vector[ChannelFailure])
  def accepted: Boolean = this match
    case Accepted(_, _) => true
    case Rejected(_, _, _) => false
  def show: String = this match
    case Accepted(v, t) => s"ACCEPTED ${v.pretty} ∈ γ(${t.show})"
    case Rejected(v, t, cs) =>
      s"REJECTED ${v.pretty} ∉ γ(${t.show})\n" + cs.map("    " + _.show).mkString("\n")

/** WHAT A `Proved` IS PROVED FROM.  Not a rubber stamp: the order that was discharged, the channels it
 *  covered, every assumption the proof rests on, the validated facts it licenses, and — because a proof
 *  procedure can have bugs — a bounded exhaustive CORROBORATION that no concrete counterexample exists
 *  in a small universe.  If that corroboration ever contradicts the order, the verdict becomes
 *  `Refuted` (the witness is ground truth) and the alarm is recorded in the diagnosis. */
final case class CheckCertificate(order: String,
                                  inferred: SpatialType,
                                  declared: SpatialType,
                                  channels: Vector[String],
                                  assumptions: Vector[SpatialAssumption],
                                  facts: Vector[Fact],
                                  corroboration: Option[WitnessReport]):
  def show: String =
    (Vector(s"PROVED by $order", s"  inferred ${inferred.show}", s"  declared ${declared.show}",
            s"  channels: ${channels.mkString(", ")}") ++
      assumptions.map(a => s"  assuming ${a.show}") ++
      Vector(s"  facts: ${facts.map(_.show).mkString(", ")}") ++
      corroboration.map(c => s"  corroboration: ${c.show}").toVector).mkString("\n")

/** THE THREE-WAY RESULT review.md 1 requires, and nothing else may stand in for it. */
enum SpatialCheck:
  case Proved(inferred: SpatialType, certificate: CheckCertificate)
  /** `witness` inhabits `inferred` and NOT the declared type: ABSTRACT conformance is refuted.  Read
   *  the note on [[SpatialCheck]]'s companion documentation: this is not a claim about the routine's
   *  image, which only an evaluated witness could refute. */
  case Refuted(inferred: SpatialType, witness: SpaceValue)
  case Unknown(inferred: SpatialType, reason: String)

  /** the inferred type, whichever verdict this is.  (Named `inferredType` because every case already
   *  carries a field called `inferred`, which is the spelling review.md 1 asks for.) */
  def inferredType: SpatialType = this match
    case Proved(t, _) => t
    case Refuted(t, _) => t
    case Unknown(t, _) => t
  def isProved: Boolean = this match { case Proved(_, _) => true; case _ => false }
  def isRefuted: Boolean = this match { case Refuted(_, _) => true; case _ => false }
  def isUnknown: Boolean = this match { case Unknown(_, _) => true; case _ => false }
  def show: String = this match
    case Proved(_, c) => c.show
    case Refuted(t, w) =>
      s"REFUTED — ${w.pretty} inhabits the inferred type ${t.show} and not the declared one.\n" +
        "  This refutes ABSTRACT CONFORMANCE: no repair of the order can prove this signature from\n" +
        "  this inferred type.  It is NOT a claim that the routine can produce that value."
    case Unknown(t, r) => s"UNKNOWN — $r\n  inferred ${t.show}"

/** where a channel failure entered, with the premise the analysis used there.
 *
 *  The attribution rule, stated so it cannot be mistaken for a causal proof: an occurrence is blamed
 *  for a channel when the channel test fails AT it and at EVERY occurrence between it and the root, and
 *  at none of its children.  So the blamed occurrences are the deepest points on each spine at which
 *  the offending width is already present and from which it reaches the result unbroken. */
final case class Blame(channel: ResultChannel, node: NodeId, expression: String, cause: String,
                       assumption: SpatialAssumption):
  def show: String = s"${channel.show} enters at ${node.show} ($cause) in `$expression` — relying on " +
    s"${assumption.show}"

/** everything a caller needs in order to act on a failed proof (the verdict itself stays the three-way
 *  enum, which is what review.md 1 asks the API to expose). */
final case class CheckDiagnosis(failures: Vector[ChannelFailure],
                                blame: Vector[Blame],
                                assumptions: Vector[SpatialAssumption],
                                search: Option[WitnessReport],
                                notes: Vector[String]):
  def channels: Vector[ResultChannel] = failures.map(_.channel).distinct
  def show: String =
    (failures.map("  channel " + _.show) ++ blame.map("  blame " + _.show) ++
      assumptions.map("  assuming " + _.show) ++ search.map("  search " + _.show).toVector ++
      notes.map("  ! " + _)).mkString("\n")

/** the full answer: the verdict, its diagnosis, and the ONE decorated analysis both came from — so a
 *  consumer gets per-node facts with lexical provenance out of the same traversal (review.md 4). */
final case class SpatialCheckReport(check: SpatialCheck,
                                    signature: SpatialSignature,
                                    analysis: SpatialAnalysis,
                                    diagnosis: CheckDiagnosis):
  def inferred: SpatialType = check.inferredType
  def show: String = s"${signature.show}\n${check.show}\n${diagnosis.show}"

// ==================================================================================================
// 7.  THE ENTRY POINTS
// ==================================================================================================

/** THE ENTRY POINTS.  Three questions, three result types, one place each — the file header above
 *  states what each verdict means and why `Refuted` is scoped to ABSTRACT conformance.
 *
 *  {{{
 *  SpatialCheck.value(v, t)                     // concrete membership: sound AND complete
 *  SpatialCheck.types(inferred, declared)       // abstract inclusion:  Proved / Refuted / Unknown
 *  SpatialCheck.checkRoutine(r, signature)      // the routine contract: the same three
 *  SpatialCheck.report(r, signature)            // …plus diagnosis and the decorated analysis
 *  }}} */
object SpatialCheck:

  // ---- concrete membership -----------------------------------------------------------------------

  /** CONCRETE MEMBERSHIP — sound AND complete for this carrier.  The verdict is `SpatialTyping.accepts`
   *  (full γ); the channels only explain it. */
  def value(v: SpaceValue, t: SpatialType): ValueCheck =
    if SpatialTyping.accepts(v, t) then ValueCheck.Accepted(v, t)
    else
      val cs = SpatialChannels.valueFailures(v, t)
      ValueCheck.Rejected(v, t, if cs.nonEmpty then cs
        else Vector(ChannelFailure(ResultChannel.Bottom, "—", t.show,
          "γ rejects the value but the channel mirror found no failing clause — the MIRROR is " +
            "incomplete; the rejection itself stands")))

  /** does the membership mirror agree with the predicate it mirrors?  `None` when it does. */
  def mirrorNote(v: SpaceValue, t: SpatialType): Option[String] =
    val cs = SpatialChannels.valueFailures(v, t)
    if SpatialTyping.accepts(v, t) == cs.isEmpty then None
    else Some(s"membership mirror disagrees with γ on ${v.pretty} / ${t.show}: accepts=" +
      s"${SpatialTyping.accepts(v, t)}, channels=${cs.map(_.channel.show).mkString(",")}")

  /** the same for the order mirror */
  def orderMirrorNote(a: SpatialType, b: SpatialType): Option[String] =
    val cs = SpatialChannels.orderFailures(a, b)
    if SpatialType.leq(a, b) == cs.isEmpty then None
    else Some(s"order mirror disagrees with leq on ${a.show} ⊑ ${b.show}: leq=${SpatialType.leq(a, b)}, " +
      s"channels=${cs.map(_.channel.show).mkString(",")}")

  // ---- the bounded exhaustive refuter ------------------------------------------------------------

  /** every head item either shape tracks, to a bounded depth */
  private def headItems(s: Shape, d: Int): Set[PathItem] =
    if d <= 0 then Set.empty
    else s.heads.keySet.toSet ++ s.heads.valuesIterator.flatMap(headItems(_, d - 1)).toSet ++
      s.otherTail.iterator.flatMap(headItems(_, d - 1)).toSet

  /** an item NO type in play tracks — the only way a witness can escape a CLOSED declared head set */
  private def freshItem(taken: Set[PathItem]): PathItem =
    var i = 0
    var candidate = "#w"
    while taken.contains(candidate) do { i += 1; candidate = s"#w$i" }
    candidate

  /** the universe to search: the head items of BOTH types (so a witness can reach a declared subtree)
   *  plus one FRESH item (so it can escape a closed declared head set), over exactly the path lengths
   *  the INFERRED type admits, capped at `cfg.maxLen`.  Anything outside those lengths is not in
   *  `γ(inferred)` and could only burn budget, and anything above the cap is what the caller's budget
   *  said no to — so the ceiling is `min(inferred.len.hi, cfg.maxLen)` and nothing else.  A first draft
   *  also CAPPED the ceiling at the failing channel's depth, which silently shrank the searched universe
   *  below the caller's budget (a length-2 member of γ(inferred) went unexamined while the report said
   *  "exhaustive"); the channel depth is now only used to WARN when it sits deeper than the ceiling
   *  reached. */
  def universeFor(inferred: SpatialType, declared: SpatialType, cfg: WitnessSearch): WitnessUniverse =
    val heads = headItems(inferred.shape, 6) ++ headItems(declared.shape, 6)
    val items = (heads.toVector.sorted.take((cfg.maxItems - 1) max 0) :+ freshItem(heads)).distinct
    val ln = inferred.len
    val lo = if ln.isEmpty then 0L else ln.lo
    val cap =
      if ln.isEmpty then 0L
      else if ln.hi == LenBounds.INF then cfg.maxLen.toLong
      else ln.hi min cfg.maxLen.toLong
    // When `cap < lo` the caller's `maxLen` is BELOW the shortest path the inferred type admits, so a
    // universe capped at `maxLen` would contain no member of `γ(inferred)` at all.  The ceiling is
    // raised to `lo` instead — only lengths in `[lo, hi]` are ever kept, so this costs one level's worth
    // of paths and is what lets the refuter find a witness for a deep type at all — and the universe is
    // marked TRUNCATED, because it is no longer the full universe over its alphabet.  `HardLenCap` keeps
    // the level construction finite when `lo` is enormous (`SpatialTypes.MaxLen` is 8192); past it the
    // universe comes out EMPTY and `searchWitness` reports `outOfScope`, which is the honest answer.
    val HardLenCap = 64L
    val wanted = if cap < lo then lo else cap
    val hi = wanted min HardLenCap
    // level by level, so the SHORT paths — the legible witnesses — are what survives a truncation
    val out = Vector.newBuilder[PathValue]
    var kept = 0
    var truncated = wanted > HardLenCap || cap < lo
    var level = Vector(PathValue(Nil))
    var l = 0L
    val breadth = 4 * cfg.maxPaths + 64
    while l <= hi && level.nonEmpty do
      if l >= lo then
        for p <- level do
          if kept < cfg.maxPaths then { out += p; kept += 1 } else truncated = true
      if l < hi then
        val next = level.flatMap(pv => items.map(i => PathValue(pv.items :+ i)))
        if next.size > breadth then { truncated = true; level = next.take(breadth) } else level = next
      l += 1
    WitnessUniverse(items, LenBounds(lo, hi), out.result(), truncated)

  /** THE BOUNDED EXHAUSTIVE REFUTER.  Enumerates the finite universe by INCREASING CARDINALITY (a small
   *  witness is a legible witness), skips cardinalities `γ(inferred)` cannot contain at all, and returns
   *  an explicitly UNDECIDED report rather than a claim when the budget runs out.
   *
   *  ==WHY NOT whispers.md §2's `FiniteSpatialValidation.check`==
   *  That generator enumerates INPUT TUPLES and calls `eval` on the routine body, so (a) it cannot live
   *  in an analysis file under this tree's rule that an analysis never runs its subject, and (b) its
   *  counterexample is a SEMANTIC one about the routine, a different and stronger claim than the
   *  abstract gap this verdict is about.  What is taken from it, and taken whole, is the shape of the
   *  contract: compute and REPORT the path count and the space count before enumerating, enumerate under
   *  an explicit case budget, and return a distinct budget-exceeded state instead of hanging or
   *  pretending completeness.  `SpatialGamma.TestOnly.gammaLeqWitness` is also not used: it eagerly
   *  materialises all `2^P` values, it takes the universe as a parameter instead of deriving it from the
   *  two types, and production code may not read test support (review.md 6). */
  def searchWitness(inferred: SpatialType, declared: SpatialType, cfg: WitnessSearch): WitnessReport =
    val u = universeFor(inferred, declared, cfg)
    var examined = 0L
    var found: Option[SpaceValue] = None

    def test(v: SpaceValue): Unit =
      examined += 1
      if SpatialTyping.accepts(v, inferred) && !SpatialTyping.accepts(v, declared) then found = Some(v)

    // guided candidates first: the empty space (the witness whenever the declaration carries a tracked
    // lower bound the inferred type does not force) and the inferred type's exact value when it has one
    val guided = SpaceValue(Set.empty) +: SpatialFacts.exactValue(inferred).toVector
    var g = 0
    while found.isEmpty && g < guided.size && examined < cfg.maxCandidates do
      test(guided(g)); g += 1

    val n = u.paths.size
    val sz = inferred.size
    val kLo = if sz.lo > n then n + 1 else sz.lo.toInt
    val kHi = if sz.hi == Ivl.INF || sz.hi > n then n else sz.hi.toInt
    var k = kLo
    var stopped = false
    while found.isEmpty && !stopped && k <= kHi do
      val it = u.paths.combinations(k)
      while found.isEmpty && !stopped && it.hasNext do
        if examined >= cfg.maxCandidates then stopped = true
        else test(SpaceValue(it.next().toSet))
      k += 1
    var pruned = BigInt(0)
    for j <- 0 to n if j < kLo || j > kHi do pruned += binomial(n, j)
    WitnessReport(u, examined, cfg.maxCandidates, pruned, finished = found.isEmpty && !stopped,
                  outOfScope = kLo > kHi, found)

  private def binomial(n: Int, k: Int): BigInt =
    if k < 0 || k > n then BigInt(0)
    else
      var acc = BigInt(1)
      var i = 1
      while i <= k do { acc = acc * (n - k + i) / i; i += 1 }
      acc

  // ---- abstract conformance ----------------------------------------------------------------------

  private def hintDepth(failures: Vector[ChannelFailure]): Long =
    if failures.isEmpty then 1L else failures.map(_.channel.depthHint).max max 1L

  private val ChannelNames = Vector("ε", "tracked heads", "untracked-head count", "otherTail",
                                    "per-length counts", "spill window", "spill aggregate",
                                    "size projection", "length projection")

  /** ABSTRACT CONFORMANCE of two types, with no routine involved: `Proved` from the sound order,
   *  `Refuted` only with a witness in hand, `Unknown` otherwise.  This is the kernel [[checkRoutine]]
   *  and every other consumer share, so the three-way decision is made in exactly one place. */
  def types(inferred: SpatialType, declared: SpatialType,
            search: WitnessSearch = WitnessSearch.default,
            assumptions: Vector[SpatialAssumption] = Vector(SpatialAssumption.TransferSoundness),
            facts: Vector[Fact] = Vector.empty,
            corroborate: WitnessSearch = WitnessSearch.corroboration): (SpatialCheck, CheckDiagnosis) =
    val failures = SpatialChannels.orderFailures(inferred, declared)
    val mirror = orderMirrorNote(inferred, declared).toVector

    // ⊥ ⊑ everything, so a contradictory annotation set would "prove" every signature.  That is a
    // vacuous truth about a routine nothing can call, and reporting it as `Proved` is exactly the trap
    // review.md 1 is about.
    if inferred.uninhabited then
      (SpatialCheck.Unknown(inferred,
        "VACUOUS: the inferred type is the explicit ⊥ — no concrete space satisfies the declared " +
          "inputs, so abstract inclusion holds for EVERY declaration and proves nothing.  Fix the " +
          "input annotations (or the transfer that produced the contradiction)."),
       CheckDiagnosis(failures, Vector.empty, assumptions, None, mirror))
    else if SpatialType.leq(inferred, declared) then
      // the cross-check on a `Proved` is a CHEAPER search than the refuter: it exists to catch an
      // unsound order, not to decide the question, and the deciding branch below is the one that should
      // get the caller's full budget.
      val corr = if corroborate.maxPaths == 0 then None
                 else Some(searchWitness(inferred, declared, corroborate))
      corr.flatMap(_.witness) match
        case Some(w) =>
          // the order said yes and a concrete counterexample exists.  The witness is ground truth for
          // γ-containment and the order is a proof procedure, so the honest verdict is the refutation —
          // loudly, because it means `SpatialType.leq` is unsound on this pair.
          (SpatialCheck.Refuted(inferred, w),
           CheckDiagnosis(failures, Vector.empty, assumptions, corr,
             mirror :+ s"SOUNDNESS ALARM: SpatialType.leq proved inclusion, yet ${w.pretty} inhabits " +
               "the inferred type and not the declared one"))
        case None =>
          (SpatialCheck.Proved(inferred,
            CheckCertificate("SpatialType.leq = Shape.leqStrong × SpatialGamma.leqSpace (⇒ γ ⊆ γ)",
              inferred, declared, ChannelNames, assumptions, facts, corr)),
           CheckDiagnosis(Vector.empty, Vector.empty, assumptions, corr, mirror))
    else
      val rep = searchWitness(inferred, declared, search)
      rep.witness match
        case Some(w) => (SpatialCheck.Refuted(inferred, w),
                         CheckDiagnosis(failures, Vector.empty, assumptions, Some(rep), mirror))
        case None =>
          val chans = failures.map(_.channel.show).mkString("; ")
          val head =
            if rep.outOfScope then
              s"UNDECIDED: the sound abstract order rejected the declaration on [$chans], and the " +
                "witness search could not look — no space in its universe has enough paths to inhabit " +
                "the inferred type at all.  Raise WitnessSearch.maxPaths/maxLen"
            else if rep.completeOnUniverse then
              s"NOT PROVED and NOT refuted: the sound abstract order rejected the declaration on " +
                s"[$chans], but an EXHAUSTIVE search of ${rep.universe.spaceCount} concrete spaces " +
                s"found NO member of the inferred type outside the declared one" +
                (if failures.exists(_.sufficientOnly) then
                   " — and at least one failing channel's test is a SUFFICIENT CONDITION ONLY, so this " +
                     "is the order's documented incompleteness, not a violation"
                 else " — the bounded universe cannot see a witness, so nothing is claimed either way") +
                (if hintDepth(failures) > rep.universe.lens.hi then
                   s".  CAVEAT: the deepest failing channel sits at depth ${hintDepth(failures)}, DEEPER " +
                     s"than the length ceiling ${rep.universe.lens.hi} the search reached — raise " +
                     "WitnessSearch.maxLen to look there"
                 else "")
            else
              s"UNDECIDED: the sound abstract order rejected the declaration on [$chans], and the " +
                s"witness search stopped after ${rep.examined} of ${rep.universe.spaceCount} " +
                s"candidates (budget ${rep.budget}) without deciding"
          (SpatialCheck.Unknown(inferred, s"$head.  ${rep.show}"),
           CheckDiagnosis(failures, Vector.empty, assumptions, Some(rep), mirror))

  // ---- the routine check -------------------------------------------------------------------------

  /** THE ROUTINE CHECK — the operation review.md 1 says is missing.  Three-way, honest, and never
   *  turning the order's imprecision into a type error. */
  def checkRoutine(routine: Routine, signature: SpatialSignature,
                   routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                   search: WitnessSearch = WitnessSearch.default,
                   cfg: SpatialConfig = SpatialConfig.default,
                   corroborate: WitnessSearch = WitnessSearch.corroboration): SpatialCheck =
    report(routine, signature, routines, search, cfg, corroborate).check

  /** the same, plus the diagnosis and the decorated analysis both were computed from */
  def report(routine: Routine, signature: SpatialSignature,
             routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
             search: WitnessSearch = WitnessSearch.default,
             cfg: SpatialConfig = SpatialConfig.default,
             corroborate: WitnessSearch = WitnessSearch.corroboration): SpatialCheckReport =
    val (missingP, missingS) = signature.missing(routine)
    // ONE traversal: the decorated analysis IS the inference here, so the verdict and the per-node facts
    // an optimizer consumes cannot come from two different runs (review.md 4).
    val env = signature.env(routines, Set(routine.name))
    val analysis = SpatialAnalysis.of(routine.body, env, cfg)
    val inferred = analysis.root
    val assumptions = premises(routine, signature, routines, analysis, cfg, missingP, missingS)
    val facts = analysis.rootFacts

    val (verdict0, diag0) = types(inferred, signature.result, search, assumptions, facts, corroborate)
    // the per-node failing-channel sets, computed ONCE: `blameFor` used to re-run the whole order
    // comparison per (node, channel), which is the quadratic re-query pattern review.md 4 objects to.
    val perNode: Map[NodeId, Set[ResultChannel]] =
      if diag0.failures.isEmpty then Map.empty
      else analysis.nodes.iterator.map(n =>
        n.id -> SpatialChannels.orderFailures(n.result, signature.result).map(_.channel).toSet).toMap
    val blame = diag0.failures.map(_.channel).distinct
      .flatMap(c => blameFor(c, analysis, perNode, routine, routines))
    // A missing annotation never invalidates a proof — the parameter was analysed as ⊤, so a `Proved`
    // under it is STRONGER than the signature asks for.  It does make an `Unknown` actionable, so it is
    // named there (and it is always visible in the assumptions).
    val verdict = (verdict0, missingP.isEmpty && missingS.isEmpty) match
      case (SpatialCheck.Unknown(t, r), false) =>
        SpatialCheck.Unknown(t, s"$r  NOTE: paths [${missingP.map(_.s).mkString(",")}] and spaces " +
          s"[${missingS.map(_.s).mkString(",")}] are UNDECLARED and were analysed as ⊤; declaring them " +
          "is usually what makes a signature provable.")
      case (v, _) => v
    SpatialCheckReport(verdict, signature, analysis,
                       diag0.copy(blame = blame, assumptions = assumptions,
                                  notes = diag0.notes ++ analysis.notes))

  /** every premise the verdict rests on, gathered from the signature, the routine table and the
   *  decorated analysis — which is where the ⊤-producing occurrences become visible. */
  private def premises(routine: Routine, sig: SpatialSignature,
                       routines: PartialFunction[RoutinePtr, Routine], a: SpatialAnalysis,
                       cfg: SpatialConfig, missingP: Vector[PathRef],
                       missingS: Vector[SpaceMention]): Vector[SpatialAssumption] =
    val out = Vector.newBuilder[SpatialAssumption]
    out += SpatialAssumption.TransferSoundness
    out += SpatialAssumption.AnalysisBudgets(cfg)
    for m <- routine.mentions; t <- sig.spaces.get(m) do
      out += SpatialAssumption.InputSpaceAnnotation(m, t)
    for r <- routine.refs; t <- sig.paths.get(r) do out += SpatialAssumption.InputPathAnnotation(r, t)
    for m <- missingS do out += SpatialAssumption.MissingSpaceAnnotation(m)
    for r <- missingP do out += SpatialAssumption.MissingPathAnnotation(r)
    for n <- a.nodes do
      n.expression match
        case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => out += SpatialAssumption.OpaqueGrounded
        case Space.Call(rp, _, _) =>
          if rp == routine.name then out += SpatialAssumption.RecursionWidened(rp)
          else if !routines.isDefinedAt(rp) then out += SpatialAssumption.MissingRoutine(rp)
          else out += SpatialAssumption.RoutineBody(rp)
        case Space.Fixpoint(_, _, _) => out += SpatialAssumption.FixpointPostFixpoint
        case Space.Iteration(_, _, _, _) | Space.Fold(_, _, _, _, _, _, _) =>
          out += SpatialAssumption.HeadGroupUnion
        case _ => ()
      if n.observations.exists(_.cause == "budget") then out += SpatialAssumption.BudgetTop(n.id)
    out.result().distinct

  /** the SOURCE NODE for one channel, by the attribution rule stated on [[Blame]]. */
  private def blameFor(c: ResultChannel, a: SpatialAnalysis, perNode: Map[NodeId, Set[ResultChannel]],
                       routine: Routine,
                       routines: PartialFunction[RoutinePtr, Routine]): Vector[Blame] =
    val failing: Set[NodeId] = perNode.collect { case (id, cs) if cs.contains(c) => id }.toSet
    def chain(id: NodeId): Boolean =
      failing.contains(id) && id.parent.forall(p => !a.index.contains(p) || chain(p))
    val onChain = a.nodes.filter(n => chain(n.id))
    val hasChildOnChain = onChain.flatMap(_.id.parent).toSet
    val deepest = onChain.filter(n => !hasChildOnChain.contains(n.id))
    // an empty blame set is possible and honest: the channel can fail only at the root, when the
    // offending width is introduced by a transfer whose operands are each individually fine.
    (if deepest.nonEmpty then deepest else a.rootNode.toVector).map { n =>
      Blame(c, n.id, n.expression.show.take(70), n.observations.map(_.cause).distinct.mkString("|"),
            assumptionAt(n, routine, routines))
    }

  private def assumptionAt(n: NodeAnalysis, routine: Routine,
                           routines: PartialFunction[RoutinePtr, Routine]): SpatialAssumption =
    if n.observations.exists(_.cause == "budget") then SpatialAssumption.BudgetTop(n.id)
    else n.expression match
      case Space.Mention(m) => n.bindings.spaces.get(m) match
        case Some(t) => SpatialAssumption.InputSpaceAnnotation(m, t)
        case None => SpatialAssumption.MissingSpaceAnnotation(m)
      case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => SpatialAssumption.OpaqueGrounded
      case Space.Call(rp, _, _) =>
        if rp == routine.name then SpatialAssumption.RecursionWidened(rp)
        else if !routines.isDefinedAt(rp) then SpatialAssumption.MissingRoutine(rp)
        else SpatialAssumption.RoutineBody(rp)
      case Space.Fixpoint(_, _, _) => SpatialAssumption.FixpointPostFixpoint
      case Space.Iteration(_, _, _, _) | Space.Fold(_, _, _, _, _, _, _) =>
        SpatialAssumption.HeadGroupUnion
      case Space.Singleton(Path.Deref(pr)) =>
        n.bindings.opaque.get(pr) match
          case Some(k) => SpatialAssumption.InputPathAnnotation(pr, PathType.opaque(k))
          case None => n.bindings.paths.get(pr) match
            case Some(v) => SpatialAssumption.InputPathAnnotation(pr, PathType.known(v))
            case None => SpatialAssumption.MissingPathAnnotation(pr)
      case _ => SpatialAssumption.TransferSoundness
end SpatialCheck
