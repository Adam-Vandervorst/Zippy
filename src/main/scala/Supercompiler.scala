package morkl

import scala.collection.mutable

/** A positive supercompiler for the MORKL space/path algebra.
 *
 *  A *configuration* is a [[Space]] term whose free [[SpaceMention]]s and [[PathRef]]s
 *  are the inputs.  Supercompilation drives a configuration (meaning-preserving
 *  simplification via the algebraic laws + unfolding of routine calls, including
 *  self-calls), folds when a driven configuration is a renaming/instance of an
 *  ancestor, and generalizes (most-specific generalization) when the homeomorphic
 *  embedding whistle blows.  The finite process tree is residualized into a set of
 *  MORKL [[Routine]]s — the residual program.
 *
 *  This file is organized in layers:
 *    1. Matching   — canonicalization of bound names, substitution, free vars,
 *                    alpha-renaming, instance matching, homeomorphic embedding, msg.
 *    2. Driving    — one-step reduction of a configuration (Supercompiler.scala, part 2).
 *    3. Folding/Residualization (part 2).
 */
object Matching:
  import Space.*

  // ---- free variables -----------------------------------------------------

  /** Free space-mentions of a configuration (those not bound by an enclosing
   *  Iteration/Fold). */
  def freeMentions(s: Space): Set[SpaceMention] = freeMentionsLHS(s).toSet
  private def freeMentionsLHS(s: Space): mutable.LinkedHashSet[SpaceMention] =
    val acc = mutable.LinkedHashSet.empty[SpaceMention]
    def recp(p: Path, bound: Set[SpaceMention]): Unit = p match
      case Path.Concat(l, r) => recp(l, bound); recp(r, bound)
      case Path.GroundedSP(sp, _) => recs(sp, bound)
      case Path.GroundedPP(pp, _) => recp(pp, bound)
      case _ => ()
    def recs(x: Space, bound: Set[SpaceMention]): Unit = x match
      case Space.Mention(v) => if !bound(v) then acc += v
      case Space.Empty => ()
      case Space.Singleton(p) => recp(p, bound)
      case Space.Literal(_) => ()
      case Space.Call(_, refs, mentions) => refs.foreach(recp(_, bound)); mentions.foreach(recs(_, bound))
      case Space.Union(a, b) => recs(a, bound); recs(b, bound)
      case Space.Intersection(a, b) => recs(a, bound); recs(b, bound)
      case Space.Subtraction(a, b) => recs(a, bound); recs(b, bound)
      case Space.Restriction(a, b) => recs(a, bound); recs(b, bound)
      case Space.Raffination(a, b) => recs(a, bound); recs(b, bound)
      case Space.Composition(a, b) => recs(a, bound); recs(b, bound)
      case Space.Iteration(src, _, rest, body) => recs(src, bound); recs(body, bound + rest)
      case Space.Fixpoint(init, rec, body) => recs(init, bound); recs(body, bound + rec)
      case Space.Fold(src, init, _, _, rest, body, upd) =>
        recs(src, bound); recp(init, bound); recs(body, bound + rest); recp(upd, bound)
      case Space.Wrap(src, p) => recs(src, bound); recp(p, bound)
      case Space.Unwrap(src, p) => recs(src, bound); recp(p, bound)
      case Space.TailsUnion(src) => recs(src, bound)
      case Space.TailsIntersection(src) => recs(src, bound)
      case Space.GroundedPS(p, _) => recp(p, bound)
      case Space.GroundedSS(sp, _) => recs(sp, bound)
      case Space.Range(a, _, _) => recs(a, bound)
    recs(s, Set.empty)
    acc

  /** Free path-refs of a configuration (those not bound by an enclosing
   *  Iteration symbol / Fold acc+symbol). */
  def freeRefs(s: Space): Set[PathRef] = freeRefsLHS(s).toSet
  private def freeRefsLHS(s: Space): mutable.LinkedHashSet[PathRef] =
    val acc = mutable.LinkedHashSet.empty[PathRef]
    def recp(p: Path, bound: Set[PathRef]): Unit = p match
      case Path.Deref(pr) => if !bound(pr) then acc += pr
      case Path.Constant(_) => ()
      case Path.Concat(l, r) => recp(l, bound); recp(r, bound)
      case Path.GroundedSP(sp, _) => recs(sp, bound)
      case Path.GroundedPP(pp, _) => recp(pp, bound)
    def recs(x: Space, bound: Set[PathRef]): Unit = x match
      case Space.Mention(_) | Space.Empty | Space.Literal(_) => ()
      case Space.Singleton(p) => recp(p, bound)
      case Space.Call(_, refs, mentions) => refs.foreach(recp(_, bound)); mentions.foreach(recs(_, bound))
      case Space.Union(a, b) => recs(a, bound); recs(b, bound)
      case Space.Intersection(a, b) => recs(a, bound); recs(b, bound)
      case Space.Subtraction(a, b) => recs(a, bound); recs(b, bound)
      case Space.Restriction(a, b) => recs(a, bound); recs(b, bound)
      case Space.Raffination(a, b) => recs(a, bound); recs(b, bound)
      case Space.Composition(a, b) => recs(a, bound); recs(b, bound)
      case Space.Iteration(src, sym, _, body) => recs(src, bound); recs(body, bound + sym)
      case Space.Fixpoint(init, _, body) => recs(init, bound); recs(body, bound)  // rec is a mention, binds no refs
      case Space.Fold(src, init, acc2, sym, _, body, upd) =>
        recs(src, bound); recp(init, bound); recs(body, bound + acc2 + sym); recp(upd, bound + acc2 + sym)
      case Space.Wrap(src, p) => recs(src, bound); recp(p, bound)
      case Space.Unwrap(src, p) => recs(src, bound); recp(p, bound)
      case Space.TailsUnion(src) => recs(src, bound)
      case Space.TailsIntersection(src) => recs(src, bound)
      case Space.GroundedPS(p, _) => recp(p, bound)
      case Space.GroundedSS(sp, _) => recs(sp, bound)
      case Space.Range(a, _, _) => recs(a, bound)
    recs(s, Set.empty)
    acc

  /** Free mentions/refs in stable left-to-right encounter order (for residual params). */
  def freeMentionsV(s: Space): Vector[SpaceMention] = freeMentionsLHS(s).toVector
  def freeRefsV(s: Space): Vector[PathRef] = freeRefsLHS(s).toVector

  // ---- substitution --------------------------------------------------------

  /** Capture-avoiding simultaneous substitution — DELEGATED to [[Subst]], which is the single owner.
   *
   *  The implementation used to live here and was the only one of the tree's FOUR substitutions that
   *  was actually capture-avoiding; `Subst.scala`'s header lists the other three and what each got
   *  wrong.  It MOVED rather than being re-derived, because `SubstConformance` has been running a
   *  randomized differential against exactly this code (three real bugs found, per its header) and
   *  re-implementing it would discard that evidence.  This forwarder stays so the supercompiler's
   *  call sites read unchanged. */
  def subst(s: Space, sm: Map[SpaceMention, Space] = Map.empty, pm: Map[PathRef, Path] = Map.empty): Space =
    Subst(s, sm, pm)

  // ---- bound-name canonicalization -----------------------------------------

  private val BoundPrefix = "#"
  def isCanonical(name: String): Boolean = name.startsWith(BoundPrefix)

  /** Rename every binder-introduced name (Iteration symbol/rest, Fold acc/symbol/rest)
   *  to a deterministic, pre-order-numbered canonical name.  Two terms with the same
   *  binder structure get identical canonical bound names, so matching/embedding can
   *  treat bound occurrences as ordinary symbols and free occurrences as variables.
   *  Input parameter names never begin with [[BoundPrefix]], so they stay distinct. */
  def canon(s: Space): Space =
    var n = 0
    def freshS(): SpaceMention = { val r = SpaceMention(s"${BoundPrefix}s$n"); n += 1; r }
    def freshP(): PathRef = { val r = PathRef(s"${BoundPrefix}p$n"); n += 1; r }
    def recs(x: Space): Space = x match
      case Space.Iteration(src, sym, rest, body) =>
        val s2 = recs(src)
        val p = freshP().known(1); val r = if rest.sizeHint >= 0 then freshS().known(rest.sizeHint) else freshS()
        Space.Iteration(s2, p, r, recs(subst(body, Map(rest -> Space.Mention(r)), Map(sym -> Path.Deref(p)))))
      case Space.Fold(src, init, acc2, sym, rest, body, upd) =>
        val s2 = recs(src); val i2 = recp(init)
        val a = if acc2.lengthHint >= 0 then freshP().known(acc2.lengthHint) else freshP()
        val p = freshP().known(1)
        val r = if rest.sizeHint >= 0 then freshS().known(rest.sizeHint) else freshS()
        val pm = Map(acc2 -> Path.Deref(a), sym -> Path.Deref(p)); val smm = Map(rest -> Space.Mention(r))
        Space.Fold(s2, i2, a, p, r, recs(subst(body, smm, pm)), recp(subst2(upd, smm, pm)))
      case Space.Fixpoint(init, rec, body) =>
        val i2 = recs(init); val r = if rec.sizeHint >= 0 then freshS().known(rec.sizeHint) else freshS()
        Space.Fixpoint(i2, r, recs(subst(body, Map(rec -> Space.Mention(r)), Map.empty)))
      case Space.Mention(_) | Space.Empty | Space.Literal(_) => x
      case Space.Singleton(p) => Space.Singleton(recp(p))
      case Space.Call(r, refs, mentions) => Space.Call(r, refs.map(recp), mentions.map(recs))
      case Space.Union(a, b) => Space.Union(recs(a), recs(b))
      case Space.Intersection(a, b) => Space.Intersection(recs(a), recs(b))
      case Space.Subtraction(a, b) => Space.Subtraction(recs(a), recs(b))
      case Space.Restriction(a, b) => Space.Restriction(recs(a), recs(b))
      case Space.Raffination(a, b) => Space.Raffination(recs(a), recs(b))
      case Space.Composition(a, b) => Space.Composition(recs(a), recs(b))
      case Space.Wrap(src, p) => Space.Wrap(recs(src), recp(p))
      case Space.Unwrap(src, p) => Space.Unwrap(recs(src), recp(p))
      case Space.TailsUnion(src) => Space.TailsUnion(recs(src))
      case Space.TailsIntersection(src) => Space.TailsIntersection(recs(src))
      case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p), f)
      case Space.GroundedSS(sp, f) => Space.GroundedSS(recs(sp), f)
      case Space.Range(a, lo, hi) => Space.Range(recs(a), lo, hi)
    def recp(p: Path): Path = p match
      case Path.Concat(l, r) => Path.Concat(recp(l), recp(r))
      case Path.GroundedPP(pp, f) => Path.GroundedPP(recp(pp), f)
      case Path.GroundedSP(sp, f) => Path.GroundedSP(recs(sp), f)
      case _ => p
    // substitution inside a bare Path — [[Subst.path]], which is where the `Singleton` routing and
    // the reason for it (`Path.GroundedSP` carries a Space, so the space walker must see it) live.
    // The old local copy silently returned `p` unchanged if the walker had not preserved the
    // constructor; `Subst.path` raises instead, because a substitution that quietly did nothing is
    // the failure mode this whole file is about.
    def subst2(p: Path, sm: Map[SpaceMention, Space], pm: Map[PathRef, Path]): Path =
      Subst.path(p, sm, pm)
    recs(s)

  // ---- structural equality (after canon, plain ==) -------------------------

  def alphaEqual(a: Space, b: Space): Boolean = canon(a) == canon(b)

  // ---- alpha-renaming -------------------------------------------------------

  /** If `b` is `a` up to a consistent bijective renaming of free mentions/refs,
   *  return that renaming (a's vars -> b's vars).  Bound names are compared after
   *  canonicalization, so they must match structurally. */
  def renaming(a0: Space, b0: Space): Option[(Map[SpaceMention, SpaceMention], Map[PathRef, PathRef])] =
    val a = canon(a0); val b = canon(b0)
    val sm = mutable.Map.empty[SpaceMention, SpaceMention]
    val smR = mutable.Map.empty[SpaceMention, SpaceMention]
    val pm = mutable.Map.empty[PathRef, PathRef]
    val pmR = mutable.Map.empty[PathRef, PathRef]
    def bindS(x: SpaceMention, y: SpaceMention): Boolean =
      if isCanonical(x.s) || isCanonical(y.s) then x == y
      else (sm.get(x), smR.get(y)) match
        case (Some(y2), _) => y2 == y
        case (None, Some(_)) => false
        case (None, None) => sm(x) = y; smR(y) = x; true
    def bindP(x: PathRef, y: PathRef): Boolean =
      if isCanonical(x.s) || isCanonical(y.s) then x == y
      else (pm.get(x), pmR.get(y)) match
        case (Some(y2), _) => y2 == y
        case (None, Some(_)) => false
        case (None, None) => pm(x) = y; pmR(y) = x; true
    if goS(a, b, bindS, bindP) then Some((sm.toMap, pm.toMap)) else None

  private def goP(a: Path, b: Path, bindS: (SpaceMention, SpaceMention) => Boolean,
                  bindP: (PathRef, PathRef) => Boolean): Boolean = (a, b) match
    case (Path.Deref(x), Path.Deref(y)) => bindP(x, y)
    case (Path.Constant(p), Path.Constant(q)) => p == q
    case (Path.Concat(l1, r1), Path.Concat(l2, r2)) => goP(l1, l2, bindS, bindP) && goP(r1, r2, bindS, bindP)
    case (Path.GroundedPP(p1, f1), Path.GroundedPP(p2, f2)) => (f1 eq f2) && goP(p1, p2, bindS, bindP)
    case (Path.GroundedSP(s1, f1), Path.GroundedSP(s2, f2)) => (f1 eq f2) && goS(s1, s2, bindS, bindP)
    case _ => a == b

  private def goS(a: Space, b: Space, bindS: (SpaceMention, SpaceMention) => Boolean,
                  bindP: (PathRef, PathRef) => Boolean): Boolean = (a, b) match
    case (Space.Mention(x), Space.Mention(y)) => bindS(x, y)
    case (Space.Empty, Space.Empty) => true
    case (Space.Literal(x), Space.Literal(y)) => x == y
    case (Space.Singleton(p), Space.Singleton(q)) => goP(p, q, bindS, bindP)
    case (Space.Call(r1, rf1, m1), Space.Call(r2, rf2, m2)) =>
      r1 == r2 && rf1.length == rf2.length && m1.length == m2.length &&
        rf1.lazyZip(rf2).forall(goP(_, _, bindS, bindP)) && m1.lazyZip(m2).forall(goS(_, _, bindS, bindP))
    case (Space.Union(a1, b1), Space.Union(a2, b2)) => goS(a1, a2, bindS, bindP) && goS(b1, b2, bindS, bindP)
    case (Space.Intersection(a1, b1), Space.Intersection(a2, b2)) => goS(a1, a2, bindS, bindP) && goS(b1, b2, bindS, bindP)
    case (Space.Subtraction(a1, b1), Space.Subtraction(a2, b2)) => goS(a1, a2, bindS, bindP) && goS(b1, b2, bindS, bindP)
    case (Space.Restriction(a1, b1), Space.Restriction(a2, b2)) => goS(a1, a2, bindS, bindP) && goS(b1, b2, bindS, bindP)
    case (Space.Raffination(a1, b1), Space.Raffination(a2, b2)) => goS(a1, a2, bindS, bindP) && goS(b1, b2, bindS, bindP)
    case (Space.Composition(a1, b1), Space.Composition(a2, b2)) => goS(a1, a2, bindS, bindP) && goS(b1, b2, bindS, bindP)
    case (Space.Iteration(s1, y1, r1, b1), Space.Iteration(s2, y2, r2, b2)) =>
      goS(s1, s2, bindS, bindP) && bindP(y1, y2) && bindS(r1, r2) && goS(b1, b2, bindS, bindP)
    case (Space.Fold(s1, i1, a1, y1, r1, b1, u1), Space.Fold(s2, i2, a2, y2, r2, b2, u2)) =>
      goS(s1, s2, bindS, bindP) && goP(i1, i2, bindS, bindP) && bindP(a1, a2) && bindP(y1, y2) &&
        bindS(r1, r2) && goS(b1, b2, bindS, bindP) && goP(u1, u2, bindS, bindP)
    case (Space.GroundedSS(s1, f1), Space.GroundedSS(s2, f2)) => (f1 eq f2) && goS(s1, s2, bindS, bindP)
    case (Space.GroundedPS(p1, f1), Space.GroundedPS(p2, f2)) => (f1 eq f2) && goP(p1, p2, bindS, bindP)
    case (Space.Wrap(s1, p1), Space.Wrap(s2, p2)) => goS(s1, s2, bindS, bindP) && goP(p1, p2, bindS, bindP)
    case (Space.Unwrap(s1, p1), Space.Unwrap(s2, p2)) => goS(s1, s2, bindS, bindP) && goP(p1, p2, bindS, bindP)
    case (Space.TailsUnion(s1), Space.TailsUnion(s2)) => goS(s1, s2, bindS, bindP)
    case (Space.TailsIntersection(s1), Space.TailsIntersection(s2)) => goS(s1, s2, bindS, bindP)
    case (Space.Range(a1, l1, h1), Space.Range(a2, l2, h2)) => l1 == l2 && h1 == h2 && goS(a1, a2, bindS, bindP)
    case _ => a == b

  // ---- instance matching ----------------------------------------------------

  /** If `term` is an instance of `pattern` — i.e. there is a substitution θ of
   *  pattern's free mentions/refs such that `subst(pattern, θ) ≡ term` — return θ.
   *  Used for folding: a new configuration that is an instance of an ancestor folds
   *  to a call with θ as arguments.  Operates on canonicalized terms.
   *
   *  No occurs-check is performed, and that is intentional: a fold binds a parameter to a
   *  term that legitimately *contains that parameter* (e.g. `f(acc)` folds against
   *  `f(acc ∪ δ)` with `acc ↦ acc ∪ δ` — the recurrence).  θ is applied EXACTLY ONCE to
   *  build the residual call's arguments (never iterated), so the finite representation is
   *  exact and there is no cyclic substitution.  See `SCMatching.instanceOf` self-occurrence
   *  test. */
  def instanceOf(pattern0: Space, term0: Space): Option[(Map[SpaceMention, Space], Map[PathRef, Path])] =
    val pattern = canon(pattern0); val term = canon(term0)
    val sm = mutable.Map.empty[SpaceMention, Space]
    val pm = mutable.Map.empty[PathRef, Path]
    def bindMention(v: SpaceMention, t: Space): Boolean =
      if isCanonical(v.s) then t == Space.Mention(v)
      else sm.get(v) match { case Some(t2) => t2 == t; case None => sm(v) = t; true }
    def bindRef(v: PathRef, t: Path): Boolean =
      if isCanonical(v.s) then t == Path.Deref(v)
      else pm.get(v) match { case Some(t2) => t2 == t; case None => pm(v) = t; true }
    def mp(p: Path, t: Path): Boolean = p match
      case Path.Deref(v) if !isCanonical(v.s) => bindRef(v, t)
      case _ => (p, t) match
        case (Path.Deref(x), Path.Deref(y)) => x == y
        case (Path.Constant(a), Path.Constant(b)) => a == b
        case (Path.Concat(l1, r1), Path.Concat(l2, r2)) => mp(l1, l2) && mp(r1, r2)
        case (Path.GroundedPP(p1, f1), Path.GroundedPP(p2, f2)) => (f1 eq f2) && mp(p1, p2)
        case (Path.GroundedSP(s1, f1), Path.GroundedSP(s2, f2)) => (f1 eq f2) && ms(s1, s2)
        case _ => p == t
    def ms(p: Space, t: Space): Boolean = p match
      case Space.Mention(v) if !isCanonical(v.s) => bindMention(v, t)
      case _ => (p, t) match
        case (Space.Empty, Space.Empty) => true
        case (Space.Literal(a), Space.Literal(b)) => a == b
        case (Space.Singleton(a), Space.Singleton(b)) => mp(a, b)
        case (Space.Call(r1, rf1, m1), Space.Call(r2, rf2, m2)) =>
          r1 == r2 && rf1.length == rf2.length && m1.length == m2.length &&
            rf1.lazyZip(rf2).forall(mp) && m1.lazyZip(m2).forall(ms)
        case (Space.Union(a1, b1), Space.Union(a2, b2)) => ms(a1, a2) && ms(b1, b2)
        case (Space.Intersection(a1, b1), Space.Intersection(a2, b2)) => ms(a1, a2) && ms(b1, b2)
        case (Space.Subtraction(a1, b1), Space.Subtraction(a2, b2)) => ms(a1, a2) && ms(b1, b2)
        case (Space.Restriction(a1, b1), Space.Restriction(a2, b2)) => ms(a1, a2) && ms(b1, b2)
        case (Space.Raffination(a1, b1), Space.Raffination(a2, b2)) => ms(a1, a2) && ms(b1, b2)
        case (Space.Composition(a1, b1), Space.Composition(a2, b2)) => ms(a1, a2) && ms(b1, b2)
        case (Space.Iteration(s1, y1, r1, b1), Space.Iteration(s2, y2, r2, b2)) =>
          ms(s1, s2) && y1 == y2 && r1 == r2 && ms(b1, b2)
        case (Space.Fixpoint(i1, r1, b1), Space.Fixpoint(i2, r2, b2)) =>
          ms(i1, i2) && r1 == r2 && ms(b1, b2)
        case (Space.Fold(s1, i1, a1, y1, r1, b1, u1), Space.Fold(s2, i2, a2, y2, r2, b2, u2)) =>
          ms(s1, s2) && mp(i1, i2) && a1 == a2 && y1 == y2 && r1 == r2 && ms(b1, b2) && mp(u1, u2)
        case (Space.GroundedSS(s1, f1), Space.GroundedSS(s2, f2)) => (f1 eq f2) && ms(s1, s2)
        case (Space.GroundedPS(p1, f1), Space.GroundedPS(p2, f2)) => (f1 eq f2) && mp(p1, p2)
        case (Space.Wrap(s1, p1), Space.Wrap(s2, p2)) => ms(s1, s2) && mp(p1, p2)
        case (Space.Unwrap(s1, p1), Space.Unwrap(s2, p2)) => ms(s1, s2) && mp(p1, p2)
        case (Space.TailsUnion(s1), Space.TailsUnion(s2)) => ms(s1, s2)
        case (Space.TailsIntersection(s1), Space.TailsIntersection(s2)) => ms(s1, s2)
        case (Space.Range(a1, l1, h1), Space.Range(a2, l2, h2)) => l1 == l2 && h1 == h2 && ms(a1, a2)
        case _ => p == t
    if ms(pattern, term) then Some((sm.toMap, pm.toMap)) else None

  // ---- THE LABEL ALPHABET OF THE WHISTLE (plan.md 2E.3) --------------------------------------
  //
  // Kruskal's tree theorem (proofs/lean/Zippy/Whistle.lean#Zippy.Whistle.kruskal) makes the
  // homeomorphic embedding a well-quasi-order PROVIDED the relation on node LABELS is one.  Over a
  // finite alphabet, equality is.  `coupledS`/`coupledP` below — the coupling test `msg` uses — compare
  // four things by an equality over an UNBOUNDED set (canonical bound names, the full `RoutinePtr`,
  // `Range` bounds, closure identity), and with them the embedding was NOT a well-quasi-order: the
  // nested-`Iteration` family whose innermost `Mention` is `#s0`, `#s1`, `#s2`, … at successive depths
  // is an infinite antichain, so the whistle could stay silent forever and termination rested on the
  // caps alone.  `labelOf` is the alphabet the WHISTLE couples over instead ("decide and engineer
  // each", plan.md 2E.3):
  //
  //   Mention / Deref    ONE label per sort, bound or free.  Two variables of a sort always couple.
  //   Call               the ORIGINAL routine's name plus both arities.  A residual `f_sc7` is
  //                      labelled by its base `f`, so driving never mints a new label.
  //   Literal / Constant one atom each under `litAtoms = true` (the default; the theorem covers it);
  //                      by value under `litAtoms = false`, where the alphabet is NOT finite.
  //   Range              its bounds — finite per run only because no law manufactures new bounds,
  //                      which `SC.State.alphabetEscapes` checks at run time.
  //   Grounded*          the closure's identity, finite per run for the same reason.
  //   everything else    the constructor, whose arity is fixed.
  //
  // `msg` KEEPS the fine coupling: a generalization has to be instantiable back to both inputs, and
  // two different bound names or two different routines cannot share a skeleton leaf.  The whistle
  // is therefore coarser than the generalizer, and `SC.State.whistleFallbacks` counts the runs where
  // that gap showed (the whistle blew but `msg` found nothing to abstract).  `Whistle.lean`'s
  // termination theorem covers a run exactly when that count is 0 and no label escaped.
  enum Label:
    /** a fixed-arity constructor, by name */
    case Ctor(name: String)
    case LitAtom
    case LitVal(v: SpaceValue)
    case ConstAtom
    case ConstVal(v: PathValue)
    case MentionVar
    case DerefVar
    case CallL(base: String, refs: Int, mentions: Int)
    case RangeL(lo: Int, hi: Int)
    /** `f` is compared by REFERENCE (a function object's `equals` is identity), as `coupled*` did */
    case GroundedL(kind: String, f: AnyRef)

    /** the Lean rendering (`Zippy.Whistle.Label` constructors), for `WhistleTrace.lean` */
    def lean: String = this match
      case Ctor(n) => s"(.ctor \"$n\")"
      case LitAtom => "(.litAtom)"
      case LitVal(_) => "(.litVal)"        // the value is not reproducible across runs; atom-like
      case ConstAtom => "(.constAtom)"
      case ConstVal(_) => "(.constVal)"
      case MentionVar => "(.mentionVar)"
      case DerefVar => "(.derefVar)"
      case CallL(b, r, m) => s"(.call \"$b\" $r $m)"
      case RangeL(lo, hi) => s"(.range ($lo) ($hi))"
      case GroundedL(k, _) => s"(.grounded \"$k\")"

  private val ResidualSuffix = "_sc\\d+$".r
  /** the ORIGINAL routine a (possibly residual, possibly residual-of-residual) name descends from:
   *  `State.fresh` appends `_sc<n>` to the hint, which is the called routine's name. */
  def baseRoutineName(r: RoutinePtr): String =
    var n = r.s
    var m = ResidualSuffix.findFirstIn(n)
    while m.isDefined do
      n = n.substring(0, n.length - m.get.length)
      m = ResidualSuffix.findFirstIn(n)
    n

  /** the whistle's label of a node.  Total over both sorts, no catch-all: a new constructor is a
   *  compile error here, which is the point. */
  def labelOf(t: Space | Path, litAtoms: Boolean = true): Label = t match
    case Space.Empty => Label.Ctor("Empty")
    case Space.Literal(v) => if litAtoms then Label.LitAtom else Label.LitVal(v)
    case Space.Singleton(_) => Label.Ctor("Singleton")
    case Space.Call(r, refs, ms) => Label.CallL(baseRoutineName(r), refs.length, ms.length)
    case Space.Union(_, _) => Label.Ctor("Union")
    case Space.Intersection(_, _) => Label.Ctor("Intersection")
    case Space.Subtraction(_, _) => Label.Ctor("Subtraction")
    case Space.Restriction(_, _) => Label.Ctor("Restriction")
    case Space.Raffination(_, _) => Label.Ctor("Raffination")
    case Space.Composition(_, _) => Label.Ctor("Composition")
    case Space.Iteration(_, _, _, _) => Label.Ctor("Iteration")
    case Space.Fixpoint(_, _, _) => Label.Ctor("Fixpoint")
    case Space.Fold(_, _, _, _, _, _, _) => Label.Ctor("Fold")
    case Space.Wrap(_, _) => Label.Ctor("Wrap")
    case Space.Unwrap(_, _) => Label.Ctor("Unwrap")
    case Space.TailsUnion(_) => Label.Ctor("TailsUnion")
    case Space.TailsIntersection(_) => Label.Ctor("TailsIntersection")
    case Space.Range(_, lo, hi) => Label.RangeL(lo, hi)
    case Space.GroundedSS(_, f) => Label.GroundedL("SS", f)
    case Space.GroundedPS(_, f) => Label.GroundedL("PS", f)
    case Space.Mention(_) => Label.MentionVar
    case Path.Constant(v) => if litAtoms then Label.ConstAtom else Label.ConstVal(v)
    case Path.Concat(_, _) => Label.Ctor("Concat")
    case Path.Deref(_) => Label.DerefVar
    case Path.GroundedPP(_, f) => Label.GroundedL("PP", f)
    case Path.GroundedSP(_, f) => Label.GroundedL("SP", f)

  /** every label occurring in a term — the alphabet a run draws on */
  def labels(t: Space | Path, litAtoms: Boolean = true): Set[Label] =
    val acc = mutable.Set.empty[Label]
    def go(x: Space | Path): Unit =
      acc += labelOf(x, litAtoms)
      x match
        case sp: Space => childrenS(sp).foreach(go)
        case pt: Path => childrenP(pt).foreach(go)
    go(t); acc.toSet

  /** the label TREE of a term in Lean syntax — `Zippy.Whistle.Tree.node label kids` — which is what
   *  `WhistleTrace.lean` re-checks the Scala `embeds` verdicts against.  `toLabel` is the connection
   *  the plan names between the executable and the definition. */
  def toLabel(t: Space | Path, litAtoms: Boolean = true): String =
    val kids = t match
      case sp: Space => childrenS(sp)
      case pt: Path => childrenP(pt)
    s"(.node ${labelOf(t, litAtoms).lean} [${kids.map(toLabel(_, litAtoms)).mkString(", ")}])"

  // ---- homeomorphic embedding (the whistle) ---------------------------------
  //
  // obligation: terminating/REGISTRY.tsv O12a (drive steps are instances of the certified laws in
  // proofs/laws/), O12b (fold soundness — OPEN, it depends on the inline/beta obligation O6a), O12c
  // (msg correctness — a PROPERTY carried by SupercompilerTest) and O12d (this whistle is a
  // well-quasi-order — ADMITTED with the Kruskal citation, NOT machine-checked).  The registry keeps
  // those four rows visible precisely because two of them are not discharged.

  /** Homeomorphic embedding `a ⊴ b` on canonicalized configurations, coupling over [[labelOf]]: any
   *  two variables of a sort embed (bound or free), two calls couple by ORIGINAL routine and arities.
   *  The supercompiler's whistle: if an ancestor embeds in a descendant, generalize to ensure
   *  termination.  Proved a well-quasi-order in proofs/lean/Zippy/Whistle.lean (Kruskal from
   *  Higman) over the finite alphabet of a run; `SC.State.alphabetEscapes` is the run-time check
   *  that the alphabet stayed finite and `whistleFallbacks` that every blow was acted on.
   *
   *  `litAtoms` is a deliberate HEURISTIC, not "the" embedding.  With `litAtoms=true` (default)
   *  every literal/constant is one atom, so a configuration that grows a *static* literal
   *  accumulator trips the whistle and is generalized into a reusable loop instead of being
   *  unrolled to its answer.  The cost is potential precision loss / earlier generalization;
   *  with `litAtoms=false` the embedding is structural (literals couple only when equal), which
   *  fully evaluates static recursion but never generalizes it.  Both are sound; they trade
   *  residual *shape*.  (See `SCGeneralization` for tests of both modes.) */
  def embeds(a0: Space, b0: Space, litAtoms: Boolean = true): Boolean =
    val (a, b) = (canon(a0), canon(b0))
    val v = embedsS(a, b, litAtoms)
    WhistleTrace.note(a, b, litAtoms, v)
    v

  /** THE WHISTLE CORRESPONDENCE TRACE (plan.md 2E.3, the `Matching.toLabel` connection).  Every pair
   *  the whistle compared during a recorded run, with its verdict, rendered as label trees for
   *  `proofs/lean/Zippy/WhistleTrace.lean` to re-decide with `Zippy.Whistle.embedsB` — the function
   *  `embedsB_iff` proves equal to the relation `kruskal` is about.  A disagreement is a failing
   *  `lake build` on a real pair.  Bounded and deduplicated like `Subst.Trace`, for the same reasons. */
  object WhistleTrace:
    final case class Entry(a: Space, b: Space, litAtoms: Boolean, verdict: Boolean):
      /** grounded nodes carry closure identities that no Lean term reproduces; such pairs are recorded
       *  for the count but not emitted (LeanRender does the same for substitution triples) */
      def renderable: Boolean = !hasGrounded(a) && !hasGrounded(b)
    private def hasGrounded(s: Space): Boolean =
      Matching.labels(s).exists { case Label.GroundedL(_, _) => true; case _ => false }
    @volatile private var on = false
    private val seen = scala.collection.mutable.LinkedHashMap.empty[(Space, Space, Boolean), Entry]
    private var cap = 0
    private var dropped = 0
    def record(limit: Int)(body: => Unit): Vector[Entry] =
      synchronized { seen.clear(); cap = limit; dropped = 0; on = true }
      try body finally synchronized { on = false }
      synchronized { seen.values.toVector }
    def droppedCount: Int = synchronized(dropped)
    private[morkl] def note(a: Space, b: Space, litAtoms: Boolean, v: Boolean): Unit =
      if on then synchronized {
        val k = (a, b, litAtoms)
        if seen.contains(k) then ()
        else if seen.size >= cap then dropped += 1
        else seen(k) = Entry(a, b, litAtoms, v)
      }


  /** the children the embedding walks (binders' names are NOT children — both sides are `canon`ed) */
  def childrenOf(t: Space | Path): List[Space | Path] = t match
    case sp: Space => childrenS(sp)
    case pt: Path => childrenP(pt)

  private def childrenS(s: Space): List[Space | Path] = s match
    case Space.Singleton(p) => List(p)
    case Space.Call(_, refs, mentions) => refs.toList ++ mentions.toList
    case Space.Union(a, b) => List(a, b)
    case Space.Intersection(a, b) => List(a, b)
    case Space.Subtraction(a, b) => List(a, b)
    case Space.Restriction(a, b) => List(a, b)
    case Space.Raffination(a, b) => List(a, b)
    case Space.Composition(a, b) => List(a, b)
    case Space.Iteration(src, _, _, body) => List(src, body)
    case Space.Fixpoint(init, _, body) => List(init, body)
    case Space.Fold(src, init, _, _, _, body, upd) => List(src, init, body, upd)
    case Space.Wrap(src, p) => List(src, p)
    case Space.Unwrap(src, p) => List(src, p)
    case Space.TailsUnion(src) => List(src)
    case Space.TailsIntersection(src) => List(src)
    case Space.GroundedPS(p, _) => List(p)
    case Space.GroundedSS(sp, _) => List(sp)
    case Space.Range(a, _, _) => List(a)
    case _ => Nil

  private def childrenP(p: Path): List[Space | Path] = p match
    case Path.Concat(l, r) => List(l, r)
    case Path.GroundedPP(pp, _) => List(pp)
    case Path.GroundedSP(sp, _) => List(sp)
    case _ => Nil

  /** Coupling test: same top constructor with the same arity (ignoring leaf data).
   *  `litAtoms` selects the embedding heuristic (see [[embeds]]): when true (default), any
   *  literal/constant couples with any literal/constant (an atom-level abstraction that lets a
   *  growing *static* accumulator trip the whistle); when false, literals/constants couple only
   *  when equal (a precise, structural embedding). */
  private def coupledS(a: Space, b: Space, litAtoms: Boolean): Boolean = (a, b) match
    case (Space.Empty, Space.Empty) => true
    case (Space.Literal(x), Space.Literal(y)) => litAtoms || x == y
    case (Space.Singleton(_), Space.Singleton(_)) => true
    case (Space.Call(r1, rf1, m1), Space.Call(r2, rf2, m2)) => r1 == r2 && rf1.length == rf2.length && m1.length == m2.length
    case (Space.Union(_, _), Space.Union(_, _)) => true
    case (Space.Intersection(_, _), Space.Intersection(_, _)) => true
    case (Space.Subtraction(_, _), Space.Subtraction(_, _)) => true
    case (Space.Restriction(_, _), Space.Restriction(_, _)) => true
    case (Space.Raffination(_, _), Space.Raffination(_, _)) => true
    case (Space.Composition(_, _), Space.Composition(_, _)) => true
    case (Space.Iteration(_, _, _, _), Space.Iteration(_, _, _, _)) => true
    case (Space.Fixpoint(_, _, _), Space.Fixpoint(_, _, _)) => true
    case (Space.Fold(_, _, _, _, _, _, _), Space.Fold(_, _, _, _, _, _, _)) => true
    case (Space.Wrap(_, _), Space.Wrap(_, _)) => true
    case (Space.Unwrap(_, _), Space.Unwrap(_, _)) => true
    case (Space.TailsUnion(_), Space.TailsUnion(_)) => true
    case (Space.TailsIntersection(_), Space.TailsIntersection(_)) => true
    case (Space.Range(_, l1, h1), Space.Range(_, l2, h2)) => l1 == l2 && h1 == h2
    // grounded nodes couple only when they are the SAME host operation (closure identity);
    // their arguments may still be driven, but the function body is never inspected.
    case (Space.GroundedSS(_, f1), Space.GroundedSS(_, f2)) => f1 eq f2
    case (Space.GroundedPS(_, f1), Space.GroundedPS(_, f2)) => f1 eq f2
    case (Space.Mention(x), Space.Mention(y)) => x == y // canonical bound names
    case _ => false

  private def coupledP(a: Path, b: Path, litAtoms: Boolean): Boolean = (a, b) match
    case (Path.Constant(x), Path.Constant(y)) => litAtoms || x == y
    case (Path.Concat(_, _), Path.Concat(_, _)) => true
    case (Path.Deref(x), Path.Deref(y)) => x == y // canonical bound names
    case (Path.GroundedPP(_, f1), Path.GroundedPP(_, f2)) => f1 eq f2
    case (Path.GroundedSP(_, f1), Path.GroundedSP(_, f2)) => f1 eq f2
    case _ => false

  private def embed(a: Space | Path, b: Space | Path, litAtoms: Boolean): Boolean = (a, b) match
    case (as: Space, bs: Space) => embedsS(as, bs, litAtoms)
    case (ap: Path, bp: Path) => embedsP(ap, bp, litAtoms)
    case _ => false

  // THE WHISTLE COUPLES OVER `labelOf`, not over `coupled*` — see the alphabet section above.  A
  // `Call` label carries both arities, and every other label fixes its constructor's arity, so
  // `lazyZip(...).forall` runs over lists of EQUAL length whenever the labels are equal — which is
  // the `harity` hypothesis of `Zippy.Whistle.kruskal`, and why its couple rule is `List.Forall₂`.
  private def embedsS(a: Space, b: Space, litAtoms: Boolean): Boolean =
    val dive = childrenS(b).exists(c => embed(a, c, litAtoms))
    val couple = labelOf(a, litAtoms) == labelOf(b, litAtoms) &&
      childrenS(a).lazyZip(childrenS(b)).forall(embed(_, _, litAtoms))
    dive || couple

  private def embedsP(a: Path, b: Path, litAtoms: Boolean): Boolean =
    val dive = childrenP(b).exists(c => embed(a, c, litAtoms))
    val couple = labelOf(a, litAtoms) == labelOf(b, litAtoms) &&
      childrenP(a).lazyZip(childrenP(b)).forall(embed(_, _, litAtoms))
    dive || couple

  // ---- most specific generalization (anti-unification) ----------------------

  /** Result of msg: a generalized skeleton with fresh mention/ref holes, plus the
   *  two substitutions instantiating it back to the inputs. */
  case class Gen(skeleton: Space,
                 lsm: Map[SpaceMention, Space], lpm: Map[PathRef, Path],
                 rsm: Map[SpaceMention, Space], rpm: Map[PathRef, Path]):
    def isTrivial: Boolean = skeleton match { case Space.Mention(_) => true; case _ => false }

  /** Most specific generalization of two configurations (canonicalized).  Identical
   *  subterms are retained; differing positions become fresh holes recorded in the
   *  substitutions.  Common sub-differences are shared (a hole is reused when the same
   *  (left,right) pair recurs), keeping the generalization most specific. */
  def msg(a0: Space, b0: Space, litAtoms: Boolean = true): Gen =
    val a = canon(a0); val b = canon(b0)
    var n = 0
    val sHoles = mutable.LinkedHashMap.empty[(Space, Space), SpaceMention]
    val pHoles = mutable.LinkedHashMap.empty[(Path, Path), PathRef]
    def holeS(x: Space, y: Space): Space =
      Space.Mention(sHoles.getOrElseUpdate((x, y), { val m = SpaceMention(s"#g$n"); n += 1; m }))
    def holeP(x: Path, y: Path): Path =
      Path.Deref(pHoles.getOrElseUpdate((x, y), { val m = PathRef(s"#g$n"); n += 1; m }))
    def gp(x: Path, y: Path): Path =
      if coupledP(x, y, litAtoms) then (x, y) match
        case (Path.Concat(l1, r1), Path.Concat(l2, r2)) => Path.Concat(gp(l1, l2), gp(r1, r2))
        case (Path.Constant(a), Path.Constant(b)) => if a == b then x else holeP(x, y)
        case (Path.GroundedPP(p1, f1), Path.GroundedPP(p2, _)) => Path.GroundedPP(gp(p1, p2), f1)
        case (Path.GroundedSP(s1, f1), Path.GroundedSP(s2, _)) => Path.GroundedSP(gs(s1, s2), f1)
        case _ => x // equal leaf
      else holeP(x, y)
    def gs(x: Space, y: Space): Space =
      if coupledS(x, y, litAtoms) then (x, y) match
        case (Space.Singleton(p), Space.Singleton(q)) => Space.Singleton(gp(p, q))
        case (Space.Call(r, rf1, m1), Space.Call(_, rf2, m2)) =>
          Space.Call(r, rf1.lazyZip(rf2).map(gp), m1.lazyZip(m2).map(gs))
        case (Space.Fold(s1, i1, ac, sy, re, b1, u1), Space.Fold(s2, i2, _, _, _, b2, u2)) =>
          Space.Fold(gs(s1, s2), gp(i1, i2), ac, sy, re, gs(b1, b2), gp(u1, u2))
        case (Space.GroundedSS(s1, f1), Space.GroundedSS(s2, _)) => Space.GroundedSS(gs(s1, s2), f1)
        case (Space.GroundedPS(p1, f1), Space.GroundedPS(p2, _)) => Space.GroundedPS(gp(p1, p2), f1)
        case (Space.Union(a1, b1), Space.Union(a2, b2)) => Space.Union(gs(a1, a2), gs(b1, b2))
        case (Space.Intersection(a1, b1), Space.Intersection(a2, b2)) => Space.Intersection(gs(a1, a2), gs(b1, b2))
        case (Space.Subtraction(a1, b1), Space.Subtraction(a2, b2)) => Space.Subtraction(gs(a1, a2), gs(b1, b2))
        case (Space.Restriction(a1, b1), Space.Restriction(a2, b2)) => Space.Restriction(gs(a1, a2), gs(b1, b2))
        case (Space.Raffination(a1, b1), Space.Raffination(a2, b2)) => Space.Raffination(gs(a1, a2), gs(b1, b2))
        case (Space.Composition(a1, b1), Space.Composition(a2, b2)) => Space.Composition(gs(a1, a2), gs(b1, b2))
        case (Space.Iteration(s1, y, r, b1), Space.Iteration(s2, _, _, b2)) => Space.Iteration(gs(s1, s2), y, r, gs(b1, b2))
        case (Space.Fixpoint(i1, r, b1), Space.Fixpoint(i2, _, b2)) => Space.Fixpoint(gs(i1, i2), r, gs(b1, b2))
        case (Space.Wrap(s1, p1), Space.Wrap(s2, p2)) => Space.Wrap(gs(s1, s2), gp(p1, p2))
        case (Space.Unwrap(s1, p1), Space.Unwrap(s2, p2)) => Space.Unwrap(gs(s1, s2), gp(p1, p2))
        case (Space.TailsUnion(s1), Space.TailsUnion(s2)) => Space.TailsUnion(gs(s1, s2))
        case (Space.TailsIntersection(s1), Space.TailsIntersection(s2)) => Space.TailsIntersection(gs(s1, s2))
        case (Space.Range(a1, lo, hi), Space.Range(a2, _, _)) => Space.Range(gs(a1, a2), lo, hi)
        case (Space.Literal(a), Space.Literal(b)) => if a == b then x else holeS(x, y)
        case _ => x // Empty, equal Mention
      else holeS(x, y)
    val sk = gs(a, b)
    val lsm = sHoles.collect { case ((l, _), m) => m -> l }.toMap
    val rsm = sHoles.collect { case ((_, r), m) => m -> r }.toMap
    val lpm = pHoles.collect { case ((l, _), m) => m -> l }.toMap
    val rpm = pHoles.collect { case ((_, r), m) => m -> r }.toMap
    Gen(sk, lsm, lpm, rsm, rpm)
end Matching


/** The supercompiler proper: driving, folding, generalization, residualization.
 *
 *  Driving alternates two moves on a configuration:
 *    - REDUCE: apply MORKL's meaning-preserving algebraic laws (the `Lower` rule set)
 *      to a local normal form.  This subsumes partial evaluation (closed subspaces fold
 *      to literals, data-known iterations unroll, prefixes hoist, etc).
 *    - UNFOLD: replace a routine Call by the routine body with arguments substituted —
 *      *including self-calls*, which `Routine.optimized` deliberately refuses to do.
 *
 *  Each Call that we unfold becomes a *function node*.  When a later Call is an instance
 *  of an existing function node we FOLD (emit a recursive call to that node's residual
 *  routine).  When an ancestor function node is homeomorphically embedded in the current
 *  Call but is not an instance, the whistle blows and we GENERALIZE via msg, abstracting
 *  the growing sub-structure into fresh parameters.  The whistle guarantees the process
 *  tree is finite.  Residualization reads the process tree off as a set of [[Routine]]s.
 */
final case class Residual(top: Space, routines: Map[RoutinePtr, Routine]):
  def env: PartialFunction[RoutinePtr, Routine] = routines
  /** Run the original routine env to fixpoint-inline + optimize each residual routine. */
  def show: String =
    val rs = routines.values.toVector.sortBy(_.name.s).map(_.show).mkString("\n")
    s"top: ${top.show}\n$rs"

/** Size/shape metrics for a configuration or residual. */
case class SCStats(spaceNodes: Int, pathNodes: Int, literals: Int, mentions: Int, calls: Int):
  def total: Int = spaceNodes + pathNodes
  def compact: String = s"$total nodes (literals=$literals, mentions=$mentions, calls=$calls)"
object SCStats:
  def of(s: Space): SCStats =
    var sn, pn, lit, men, cal = 0
    def rp(p: Path): Unit = { pn += 1; p match
      case Path.Concat(l, r) => rp(l); rp(r)
      case Path.GroundedPP(pp, _) => rp(pp)
      case Path.GroundedSP(sp, _) => rs(sp)
      case _ => () }
    def rs(x: Space): Unit = { sn += 1; x match
      case Space.Mention(_) => men += 1
      case Space.Literal(_) => lit += 1
      case Space.Call(_, rf, m) => cal += 1; rf.foreach(rp); m.foreach(rs)
      case Space.Singleton(p) => rp(p)
      case Space.Union(a, b) => rs(a); rs(b)
      case Space.Intersection(a, b) => rs(a); rs(b)
      case Space.Subtraction(a, b) => rs(a); rs(b)
      case Space.Restriction(a, b) => rs(a); rs(b)
      case Space.Raffination(a, b) => rs(a); rs(b)
      case Space.Composition(a, b) => rs(a); rs(b)
      case Space.Iteration(src, _, _, b) => rs(src); rs(b)
      case Space.Fixpoint(init, _, b) => rs(init); rs(b)
      case Space.Fold(src, i, _, _, _, b, u) => rs(src); rp(i); rs(b); rp(u)
      case Space.Wrap(src, p) => rs(src); rp(p)
      case Space.Unwrap(src, p) => rs(src); rp(p)
      case Space.TailsUnion(src) => rs(src)
      case Space.TailsIntersection(src) => rs(src)
      case Space.GroundedPS(p, _) => rp(p)
      case Space.GroundedSS(sp, _) => rs(sp)
      case Space.Range(a, _, _) => rs(a)
      case Space.Empty => () }
    rs(s); SCStats(sn, pn, lit, men, cal)

/** Auditable account of one supercompilation run (cf. Track A's SupercompileReport, plus
 *  SC-specific counters and a compile-time-evaluation flag). */
case class SCReport(before: SCStats, after: SCStats, residualRoutines: Int,
                    reductions: Int, unfoldings: Int, folds: Int, whistles: Int, generalizations: Int,
                    converged: Boolean, compileTimeEvaluated: Boolean,
                    backendCompiled: Boolean, backendUnsupported: Vector[String],
                    compileMillis: Double = 0.0, phaseMillis: Map[String, Double] = Map.empty,
                    phaseImprovement: Map[String, Long] = Map.empty,
                    // ---- THE EXECUTABLE PREMISES of proofs/lean/Zippy/Supercompile.lean and Whistle.lean.
                    // Each is a premise of a Lean theorem, checked on THIS run; the theorem covers the
                    // run exactly when all four hold.  See `SC.State` for what each measures.
                    residualPositive: Boolean = false, productive: Boolean = false,
                    foldChecks: Int = 0, whistleFallbacks: Int = 0, alphabetEscapes: Int = 0):
  /** the run is inside what the Lean fold and whistle theorems cover */
  def leanCovered: Boolean = residualPositive && productive && whistleFallbacks == 0 && alphabetEscapes == 0
  /** The whole program reduced to its answer at compile time (no residual routines and the residual
   *  top is a constant) — nothing is left to run.  Reported explicitly. */
  def optimizedAway: Boolean = compileTimeEvaluated
  def summary: String =
    val mode = if !converged then "BUDGET-EXCEEDED — fell back to interpreting the original"
               else if optimizedAway then "OPTIMIZED AWAY — whole program evaluated at compile time (answer is a literal)"
               else if generalizations > 0 then "residual loop via generalization"
               else if folds > 0 then "residual recursion via folding"
               else "specialized / fused (no recursion)"
    val backend = if backendCompiled then "graph-lowered" else if backendUnsupported.nonEmpty then s"source-only (${backendUnsupported.distinct.mkString(",")})" else "source-only"
    s"$mode | ${before.total}->${after.total} nodes, $residualRoutines routines | " +
      s"unfold=$unfoldings fold=$folds whistle=$whistles gen=$generalizations reduce=$reductions | $backend | " +
      (if leanCovered then "lean-covered"
       else s"NOT lean-covered (positive=$residualPositive productive=$productive " +
            s"whistleFallbacks=$whistleFallbacks alphabetEscapes=$alphabetEscapes)")
  /** Per-pass compile-time accounting: time AND improvement (graph nodes removed) for each pass —
   *  supercompile, transpile, push_out, optimize_sharing.  Compile time is reported separately so it
   *  can be weighed against runtime (the supercompiler trades the former for the latter). */
  def timing: String =
    val parts = phaseMillis.toVector.sortBy(-_._2).map { (l, ms) =>
      val imp = phaseImprovement.get(l).filter(_ != 0).map(n => s", $n nodes").getOrElse("")
      f"$l ${ms}%.2fms$imp"
    }.mkString("; ")
    f"compile $compileMillis%.2fms" + (if parts.isEmpty then "" else s" [$parts]")

/** A supercompiled program: the residual plus its report and any operation-graph lowerings. */
case class SupercompiledProgram(residual: Residual, report: SCReport, graphs: Map[RoutinePtr, RecursiveOpGraph]):
  export residual.{top, routines, env}
  def evaluate(using pc: PathContext = PathContext.emptyMap, sc: SpaceContext = SpaceContextMap(Map.empty)): SpaceValue =
    eval(residual.top)(using pc, sc, residual.env)
  def show: String = s"${report.summary}\n${residual.show}"

object SC:
  import Space.*

  /** Meaning-preserving simplification laws used during driving (no Call inlining — the
   *  driver controls unfolding).  Named so a report can show which laws fired. */
  val sourceLaws: List[(String, Space => Space)] = List(
    "constant-ops" -> Lower.ConstantOps, "algebraic-identities" -> Lower.AlgebraicIdentities,
    "iterate-singleton-deref" -> Lower.IterateSingleton_Deref, "literal-space-ops" -> Lower.LiteralSpaceOps,
    "singleton-const-literal" -> Lower.SingletonConst_Literal, "concat-singleton-iter" -> Lower.ConcatSingleton_Iter,
    "iter-union-indep" -> Lower.IterUnion_Indep, "unwrap-merge" -> Lower.Unwrap_Merge,
    "wrap-iter" -> Lower.Wrap_Iter, "iter-ident" -> Lower.Iter_Ident,
    "concat-path" -> Lower.Concat_Path, "iterate-literal-union" -> Lower.IterateLiteral_Union,
    "unwrap-concat-unwraps" -> Lower.UnwrapConcat_Unwraps, "singleton-composition-wrap" -> Lower.SingletonComposition_Wrap,
    "singleton-space-op-path-op" -> Lower.SingletonSpaceOp_PathOp, "restriction-singleton-unwrap" -> Lower.SingletonRestriction_Unwrap,
    "iter-tails" -> Lower.Iter_Tails, "tailsunion-singleton" -> Lower.TailsUnion_Singleton,
    "range-singleton" -> Lower.Range_Singleton, "unwrap-wrap" -> Lower.Unwrap_Wrap,
    "iter-transpose-semijoin" -> Lower.IterWitness_TransposeSemiJoin,
    "iter-witness-head-narrow" -> Lower.IterWitness_HeadNarrow,
    "unwrap-push" -> Lower.UnwrapPush, "wrap-merge" -> Lower.WrapMerge,
    "restriction-push" -> Lower.RestrictionPush, "comp-wrap-assoc" -> Lower.CompWrapAssoc,
    "comp-assoc-right" -> Lower.CompAssocRight, "comp-lit-to-wraps" -> Lower.CompLitWraps,
    "unwrap-fuse-const" -> Lower.Unwrap_Merge,
    "singleton-constprefix-wrap" -> Lower.SingletonConstPrefix_Wrap,
    "iter-comp-right-hoist" -> Lower.IterCompRight_Hoist,
    "raffination-push" -> Lower.RaffinationPush,
    "raff-restrict-algebra" -> Lower.RaffRestrictAlgebra,
    "restrict-raff-wrap-both" -> Lower.RestrictRaffWrapBoth,
    "iter-setop-merge" -> Lower.IterSetOpMerge)
  val simplifyRules: List[Space => Space] = sourceLaws.map(_._2)
  /** THE GROUND LAWS: the two that EVALUATE a closed subterm (`Lower.ConstantOps` tries `eval` on every
   *  node, `Lower.LiteralSpaceOps` evaluates literal-operand algebra).  proofs/laws/REGISTRY.tsv files
   *  them as kind GROUND; `AlternativesCheck` holds this set to that table.  An exploration that must
   *  be evaluation-free (tasks.md B1) drives with `sourceLaws` minus these. */
  val groundLaws: Set[String] = Set("constant-ops", "literal-space-ops")
  def lawsWithout(names: Set[String]): List[(String, Space => Space)] = sourceLaws.filterNot((n, _) => names(n))

  /** Bounded fixpoint reduction.  The step cap turns an oscillating/non-terminating rule into a
   *  clear error; the wall-clock `deadline` stops it GRACEFULLY (returns the current normal form,
   *  sound since the laws are meaning-preserving).  Convergence is structural `==`, not `show`. */
  def reduce(s: Space, cap: Int = 100000, deadline: Deadline = Deadline.never): Space =
    reduceTraced(s, cap, deadline, record = false)._1

  /** ONE STEP of the reduction trace (plan.md 2A.3): the named law that fired, and the term before
   *  and after it.  A law is a whole-term congruence (`subs`), so ONE step may rewrite several
   *  positions at once; the certificate that discharges the step is the law's ∀-certificate in
   *  proofs/laws/REGISTRY.tsv, which covers every instance, and [[verifyTrace]] re-applies the law
   *  to `before` to check that `after` is exactly what it produces. */
  final case class Step(law: String, before: Space, after: Space)

  /** [[reduce]] with the per-step trace.  `record = false` is `reduce` itself (no allocation per
   *  step); the loop is ONE loop so the traced and untraced reductions cannot disagree. */
  def reduceTraced(s: Space, cap: Int = 100000, deadline: Deadline = Deadline.never,
                   record: Boolean = true, laws: List[(String, Space => Space)] = sourceLaws): (Space, Vector[Step]) =
    val steps = if record then Vector.newBuilder[Step] else null
    def round(x0: Space): Space =
      var x = x0
      for (name, f) <- laws do
        val y = f(x)
        if record && (y ne x) && y != x then steps += Step(name, x, y)
        x = y
      x
    var cur = s
    var nxt = round(cur)
    var rounds = 0
    while nxt != cur && !deadline.expired do
      rounds += 1
      if rounds > cap then sys.error(s"SC reduce did not converge within $cap rounds")
      cur = nxt; nxt = round(cur)
    (nxt, if record then steps.result() else Vector.empty)

  /** every step is a CHECKED LAW INSTANCE: its law is one of [[sourceLaws]] (hence has a registry
   *  row, `scripts/check_laws.py`), re-applying that law to `before` gives `after`, and consecutive
   *  steps compose (`after` of one is `before` of the next).  Returns the failures; empty is proof
   *  that the trace is an honest derivation from `steps.head.before` to `steps.last.after`. */
  def verifyTrace(steps: Vector[Step]): Vector[String] =
    val byName = sourceLaws.toMap
    val bad = Vector.newBuilder[String]
    for (st, i) <- steps.zipWithIndex do
      byName.get(st.law) match
        case None => bad += s"step $i: `${st.law}` is not a source law"
        case Some(f) => if f(st.before) != st.after then bad += s"step $i: re-applying `${st.law}` does not reproduce `after`"
      if i > 0 && steps(i - 1).after != st.before then bad += s"step $i: does not compose with step ${i - 1}"
    bad.result()

  // ---- CALL-POSITIVITY: the executable twin of `Zippy.Space.callPosB` (Supercompile.lean) --------
  //
  // The Lean fold theorem needs the residual system to be monotone and omega-continuous in the
  // valuation of the residual routines, and proves that from a syntactic discipline on where calls
  // may sit: only in positive positions, with call-free arguments, call-free iteration sources and
  // call-free fixpoints (Supercompile.lean's header says why each).  This is that discipline,
  // constructor for constructor, so a residual that passes it is one the theorem is about.
  def hasCall(t: Space | Path): Boolean = t match
    case _: Space.Call => true
    case sp: Space => Matching.childrenOf(sp).exists(hasCall)
    case pt: Path => Matching.childrenOf(pt).exists(hasCall)

  def callPositive(s: Space): Boolean = s match
    case Space.Empty | Space.Literal(_) | Space.Mention(_) => true
    case Space.Singleton(p) => !hasCall(p)
    case Space.Union(a, b) => callPositive(a) && callPositive(b)
    case Space.Intersection(a, b) => callPositive(a) && callPositive(b)
    case Space.Restriction(a, b) => callPositive(a) && callPositive(b)
    case Space.Composition(a, b) => callPositive(a) && callPositive(b)
    case Space.Subtraction(a, b) => callPositive(a) && !hasCall(b)
    case Space.Raffination(a, b) => callPositive(a) && !hasCall(b)
    case Space.Wrap(src, p) => callPositive(src) && !hasCall(p)
    case Space.Unwrap(src, p) => callPositive(src) && !hasCall(p)
    case Space.TailsUnion(src) => callPositive(src)
    case Space.TailsIntersection(src) => !hasCall(src)
    case Space.Range(x, _, _) => !hasCall(x)
    case Space.Call(_, refs, ms) => !refs.exists(hasCall) && !ms.exists(hasCall)
    case Space.Iteration(src, _, _, body) => !hasCall(src) && callPositive(body)
    case fx: Space.Fixpoint => !hasCall(fx)
    case fd: Space.Fold => !hasCall(fd)
    case Space.GroundedPS(p, _) => !hasCall(p)
    case Space.GroundedSS(x, _) => !hasCall(x)

  /** Configuration knobs.  `literalsAreAtoms` selects the embedding heuristic (see
   *  [[Matching.embeds]]); the count caps (maxNodes/maxDepth/maxReduce) turn whistle/reduce bugs
   *  into errors, not hangs.  `compileBudgetMs` is a *wall-clock* bound: a supercompiler trades
   *  compile time for run time, so compilation must itself be bounded — when the budget is exceeded
   *  the driver stops GRACEFULLY and falls back to the un-supercompiled program (reported with
   *  `converged = false`), rather than spending unbounded time.  The deadline is threaded through
   *  the WHOLE driver — `drive`, `reduce`, and `scCall`.  It defaults to a FINITE budget
   *  (a supercompiler should always be time-bounded); raise it for very large specializations. */
  case class Config(maxNodes: Int = 2000, maxDepth: Int = 400, generalize: Boolean = true,
                    literalsAreAtoms: Boolean = true, maxReduce: Int = 100000,
                    compileBudgetMs: Double = Config.DefaultBudgetMs,
                    /** record the typed proof trace of the run (tasks.md C3): one DAG per residual node */
                    trace: Boolean = false,
                    /** THE LAW TABLE THIS RUN DRIVES WITH (tasks.md B1): a subset of [[sourceLaws]].  Two runs
                     *  over two subsets reach two normal forms of the same program — two residual
                     *  ALTERNATIVES, each with its own law trace — which is how fusion, hoisting and
                     *  push choices are exposed instead of committed. */
                    laws: List[(String, Space => Space)] = sourceLaws,
                    /** UNROLL BEFORE FOLDING (tasks.md B1): the first `unroll` times a configuration would
                     *  fold to a node, unfold it once more instead.  0 is the ordinary fold-first driver. */
                    unroll: Int = 0)
  object Config:
    /** Default wall-clock compile budget (ms).  Finite by design — compilation must be bounded. */
    val DefaultBudgetMs: Double = 10000.0

  /** Thrown when [[Config.compileBudgetMs]] is exceeded mid-drive; caught in [[run]] to fall back. */
  object CompileBudgetExceeded extends RuntimeException("SC compile budget exceeded")

  private val Reserved = Set("#", "~")
  /** Enforce that no user free name uses a reserved prefix (#-canonical / ~-fresh), so generated
   *  names cannot collide with user names (addresses the string-scope brittleness). */
  def validate(conf: Space): Unit =
    val bad = (Matching.freeMentions(conf).map(_.s) ++ Matching.freeRefs(conf).map(_.s)).filter(n => Reserved.exists(n.startsWith))
    if bad.nonEmpty then sys.error(s"reserved name prefix(es) ${Reserved.mkString("/")} are not allowed in inputs: ${bad.mkString(", ")}")

  final class State(defs: PartialFunction[RoutinePtr, Routine], cfg: Config):
    var counter = 0
    var reductions, unfoldings, folds, whistles, generalizations = 0
    val deadline: Deadline = Deadline.inMillis(cfg.compileBudgetMs)
    var converged = true
    // ---- THE EXECUTABLE PREMISES (Supercompile.lean / Whistle.lean correspondence tables) ----
    /** folds whose instance substitution was re-applied ONCE and reproduced the folded call */
    var foldChecks = 0
    /** whistle blows `generalize` could not act on (msg found nothing to abstract, fell back to a
     *  node the ancestor embeds).  The termination theorem covers a run only when this is 0. */
    var whistleFallbacks = 0
    /** residual names whose body consumed one unfold of their own configuration BEFORE driving */
    val unfoldedNodes = mutable.Set.empty[RoutinePtr]
    /** B1: how many times each node's would-be folds were unrolled instead (bounded by `cfg.unroll`) */
    val unrolled = mutable.Map.empty[RoutinePtr, Int]
    var unrolls = 0
    /** the alphabet of the INPUTS — the finite label set Kruskal is applied to — and the labels the
     *  drive produced outside it */
    val alphabet0: Set[Matching.Label] = Set.empty // set by `run`
    var alphabetBase: Set[Matching.Label] = Set.empty
    val alphabetEscapes = mutable.Set.empty[Matching.Label]
    def noteAlphabet(c: Space): Unit =
      // only the UNBOUNDED kinds can escape: constructor tags, the two atoms and the two variable
      // labels are a fixed finite set by definition of `Label`, so Kruskal's alphabet already
      // contains them; what a drive could mint is a new routine base name, range bound, literal
      // value or closure identity.
      for l <- Matching.labels(c, cfg.literalsAreAtoms) if !alphabetBase(l) do l match
        case Matching.Label.Ctor(_) | Matching.Label.LitAtom | Matching.Label.ConstAtom
           | Matching.Label.MentionVar | Matching.Label.DerefVar => ()
        case other => alphabetEscapes += other
    /** every residual body (and the top) passes [[callPositive]] */
    def residualPositive(top: Space): Boolean =
      callPositive(top) && routines.values.forall(r => callPositive(r.body))
    /** every residual routine consumed exactly one unfold of its configuration before folding */
    def productive: Boolean = routines.keySet.forall(unfoldedNodes)
    // function nodes: (residual name, configuration at creation, ordered ref params, ordered mention params)
    val fnodes = mutable.ArrayBuffer.empty[(RoutinePtr, Space, Vector[PathRef], Vector[SpaceMention])]
    val routines = mutable.Map.empty[RoutinePtr, Routine]
    // ---- THE TYPED PROOF TRACE (tasks.md C3): every unfold, law step, fold and generalization ----
    val traceBuilder = new ProofTrace.Builder
    /** per residual node: the trace from one unfold of its configuration to its body */
    val traces = mutable.LinkedHashMap.empty[RoutinePtr, Int]
    /** the top-level drive's trace id (configuration → residual top) */
    var topTrace: Int = -1
    def nodeTable: ProofTrace.NodeTable = fnodes.iterator.map((g, c, refs, ments) => g -> (c, refs, ments)).toMap
    def traceOf(g: RoutinePtr): Option[ProofTrace.Dag] = traces.get(g).map(traceBuilder.dag)
    def topTraceDag: Option[ProofTrace.Dag] = if topTrace >= 0 then Some(traceBuilder.dag(topTrace)) else None

    def fresh(hint: String): RoutinePtr = { counter += 1; RoutinePtr(s"${hint}_sc$counter") }
    /** A COLLISION-SAFE CANONICAL IDENTITY for a residual node (tasks.md C2): the name carries a digest
     *  of the ALPHA-NORMALISED configuration and its parameter arity, so two nodes with the same
     *  configuration up to renaming have the same identity and two different configurations never
     *  share one — an integer counter alone is neither.  The counter is kept as a readable prefix
     *  (and as the tie-breaker no canonical digest should ever need). */
    def canonicalName(hint: String, c: Space): RoutinePtr =
      counter += 1
      val (refs, ments) = paramsOf(c)
      val canon = Matching.canon(c).toString + s"|${refs.length}/${ments.length}"
      val md = java.security.MessageDigest.getInstance("SHA-256").digest(canon.getBytes("UTF-8"))
      val digest = md.take(6).map(b => f"${b & 0xff}%02x").mkString
      RoutinePtr(s"${hint}_sc${counter}_$digest")
    def hintOf(c: Space): String = c match { case Space.Call(r, _, _) => r.s; case _ => "node" }
    def paramsOf(c: Space): (Vector[PathRef], Vector[SpaceMention]) = (Matching.freeRefsV(c), Matching.freeMentionsV(c))

    def callOf(g: RoutinePtr, refs: Vector[PathRef], ments: Vector[SpaceMention],
               sm: Map[SpaceMention, Space], pm: Map[PathRef, Path]): Space =
      Space.Call(g, refs.map(pr => pm.getOrElse(pr, Path.Deref(pr))), ments.map(m => sm.getOrElse(m, Space.Mention(m))))

    /** Unfold a single routine Call (incl. self-calls) with capture-avoiding substitution. */
    def unfold(c: Space.Call): Space =
      unfoldings += 1
      val r = defs(c.r)
      Matching.subst(r.body, sm = (r.mentions.iterator zip c.mentions.iterator).toMap,
                             pm = (r.refs.iterator zip c.refs.iterator).toMap)

    def callable(c: Space.Call): Boolean = defs.isDefinedAt(c.r)

    /** Drive: reduce, then supercompile every routine-call subterm bottom-up.  The compile deadline
     *  is checked at every driver step (here) and inside `reduce`/`scCall`, so the WHOLE driver is
     *  time-bounded; on expiry `scCall` raises CompileBudgetExceeded and `run` falls back. */
    def drive(s: Space, path: List[(Space, RoutinePtr)], depth: Int): Space = driveT(s, path, depth)._1

    /** `drive` with its trace: the law steps of the reduction, then every call replaced at its
     *  position (a fold, a new node or a generalization), as one composed step `s → result` */
    def driveT(s: Space, path: List[(Space, RoutinePtr)], depth: Int): (Space, Int) =
      if deadline.expired then throw CompileBudgetExceeded
      reductions += 1
      val (r, steps) = reduceTraced(s, cfg.maxReduce, deadline, record = cfg.trace, laws = cfg.laws)
      val ids = mutable.ArrayBuffer.empty[Int]
      if cfg.trace then for st <- steps do ids += traceBuilder.add(ProofTrace.lawNode(st.law, st.before, st.after))
      if !cfg.trace then
        (subs(r)(spost = { case c: Space.Call if callable(c) => scCall(c, path, depth)._1 }), -1)
      else
        // the calls, bottom-up and positionally, so every replacement is a recorded step of the whole term
        var cur = r
        def go(x: Space, pos: Vector[Int]): Space =
          val kids = ProofTrace.children(x)
          val rebuilt = if kids.isEmpty then x else ProofTrace.rebuild(x, kids.indices.toVector.map(i => go(kids(i), pos :+ i)))
          rebuilt match
            case c: Space.Call if callable(c) =>
              val whole = ProofTrace.replaceAt(cur, pos, c).getOrElse(cur)
              val (res, by) = scCall(c, path, depth)
              val next = ProofTrace.replaceAt(whole, pos, res).getOrElse(whole)
              if by >= 0 then ids += traceBuilder.add(ProofTrace.Node.Positional(whole, pos, next, by))
              cur = next
              res
            case other => other
        val out = go(r, Vector.empty)
        val tid = if ids.isEmpty then traceBuilder.add(ProofTrace.Node.AlphaEquivalence(s, out)) else traceBuilder.compose(ids.toVector, s, out)
        (out, tid)

    /** Supercompile one Call configuration: fold -> whistle/generalize -> new node.
     *
     *  FOLDING is global (against every function node, not only ancestors on the current
     *  path).  This is sound because each function node's routine is parameterized by exactly
     *  the free variables of its configuration, and a MORKL configuration denotes a pure
     *  function of its free variables; so an instance match yields a call with the correct
     *  argument substitution regardless of context.  Global memoization only ever increases
     *  sharing.  The whistle still uses the ancestor PATH (innermost first via `collectFirst`,
     *  so generalization is deterministic w.r.t. the most-recent embedding ancestor). */
    def scCall(c: Space.Call, path: List[(Space, RoutinePtr)], depth: Int): (Space, Int) =
      if deadline.expired then throw CompileBudgetExceeded
      if depth > cfg.maxDepth then sys.error(s"SC depth cap ${cfg.maxDepth} exceeded at ${c.show}")
      if fnodes.length > cfg.maxNodes then sys.error(s"SC node cap ${cfg.maxNodes} exceeded")
      noteAlphabet(c)
      val folded = fnodes.iterator.flatMap { case (g, gc, refs, ments) =>
        Matching.instanceOf(gc, c).map((g, refs, ments, gc, _))
      }.nextOption()
      folded match
        case Some((g, _, _, _, _)) if cfg.unroll > 0 && unrolled.getOrElse(g, 0) < cfg.unroll && callable(c) =>
          // B1: UNROLL INSTEAD OF FOLDING — one more unfold of this configuration, driven; the fold the
          // ordinary driver would have emitted happens one level deeper (the same node, now at its cap).
          // Semantically a definitional step (Drive.lean `unfold_step`), recorded as such.
          unrolled(g) = unrolled.getOrElse(g, 0) + 1
          unrolls += 1
          val u = unfold(c)
          val (body, bodyTrace) = driveT(u, path, depth + 1)
          val by = if cfg.trace then
            val d = defs(c.r)
            val un = traceBuilder.add(ProofTrace.Node.Unfold(c.r, c, d.body, d.mentions.zip(c.mentions).map((m, t) => m.s -> t), d.refs.zip(c.refs).map((p, t) => p.s -> t), u))
            traceBuilder.compose(Vector(un, bodyTrace), c, body)
          else -1
          (body, by)
        case Some((g, refs, ments, gc, (sm, pm))) =>
          // THE FOLD-SITE PREMISE, CHECKED: the instance substitution applied ONCE to the node's
          // configuration is the folded configuration.  `instanceOf`'s docstring argues this; the
          // Lean fold theorem's `fix` premise depends on it; so it is asserted per fold, not argued.
          val back = Matching.subst(gc, sm, pm)
          if !Matching.alphaEqual(back, c) then
            sys.error(s"SC fold premise violated: ${gc.show} under the instance substitution is " +
                      s"${back.show}, not the folded configuration ${c.show}")
          foldChecks += 1
          folds += 1
          val call = callOf(g, refs, ments, sm, pm)
          val by = if cfg.trace then traceBuilder.add(ProofTrace.Node.Fold(g, gc, sm.toVector.map((m, t) => m.s -> t).sortBy(_._1), pm.toVector.map((p, t) => p.s -> t).sortBy(_._1), c, call)) else -1
          (call, by)
        case None =>
          val whistler =
            if !cfg.generalize then None
            else path.collectFirst { case (pc, _) if Matching.embeds(pc, c, cfg.literalsAreAtoms) && Matching.instanceOf(pc, c).isEmpty => pc }
          whistler match
            case Some(pc) => whistles += 1; generalize(pc, c, path, depth)
            case None => makeNode(c, path, depth)

    def makeNode(c: Space.Call, path: List[(Space, RoutinePtr)], depth: Int): (Space, Int) =
      val (refs, ments) = paramsOf(c)
      val g = canonicalName(hintOf(c), c)
      fnodes += ((g, c, refs, ments))
      // ONE UNFOLD PER NODE, recorded before the body is driven: the productivity premise
      val unfolded = unfold(c)
      unfoldedNodes += g
      val (body, bodyTrace) = driveT(unfolded, (c, g) :: path, depth + 1)
      routines(g) = Routine(g, refs, ments, body)
      val call = Space.Call(g, refs.map(Path.Deref(_)), ments.map(Space.Mention(_)))
      if cfg.trace then
        val d = defs(c.r)
        val u = ProofTrace.Node.Unfold(c.r, c, d.body, d.mentions.zip(c.mentions).map((m, t) => m.s -> t), d.refs.zip(c.refs).map((p, t) => p.s -> t), unfolded)
        traces(g) = traceBuilder.compose(Vector(traceBuilder.add(u), bodyTrace), c, body)
        // the new node's call denotes its configuration: a fold with the identity instance
        val by = traceBuilder.add(ProofTrace.Node.Fold(g, c, Vector.empty, Vector.empty, c, call))
        (call, by)
      else (call, -1)

    /** Whistle response: most-specific-generalize the embedded ancestor against the current
     *  call (downward generalization), supercompile the more-general skeleton, then plug the
     *  driven hole-values back in.  The generalized skeleton, being strictly more general, is
     *  driven once and its recursive descendants fold to it. */
    def generalize(pc: Space, c: Space.Call, path: List[(Space, RoutinePtr)], depth: Int): (Space, Int) =
      val gen = Matching.msg(pc, c, cfg.literalsAreAtoms)
      gen.skeleton match
        case sk: Space.Call if !Matching.alphaEqual(sk, c) =>
          generalizations += 1
          val (residGen, skTrace) = scCall(sk, path, depth + 1)
          val driven = gen.rsm.toVector.sortBy(_._1.s).map((m, v) => { val (d, t) = driveT(v, path, depth + 1); (m, v, d, t) })
          val sm = driven.map((m, _, d, _) => m -> d).toMap
          val result = Matching.subst(residGen, sm, gen.rpm)
          val by = if cfg.trace then traceBuilder.add(ProofTrace.Node.Generalization(sk, gen.rsm.toVector.map((m, t) => m.s -> t).sortBy(_._1),
                     gen.rpm.toVector.map((p, t) => p.s -> t).sortBy(_._1), c, residGen, skTrace, driven.map((m, o, d, t) => (m.s, o, d, t)), result)) else -1
          (result, by)
        case _ =>
          // the whistle blew (coarse, label-based) but the generalizer (fine coupling) found nothing
          // to abstract: the path is extended by a node an ancestor embeds.  Counted, because the
          // termination theorem is about whistle-FREE paths and does not cover this run.
          whistleFallbacks += 1
          makeNode(c, path, depth)

  // ---- entry points ---------------------------------------------------------

  /** Every routine reachable from `conf` via `defs` — a self-contained env for the un-supercompiled
   *  fallback (so the residual still evaluates when the compile budget is exhausted). */
  def materialize(conf: Space, defs: PartialFunction[RoutinePtr, Routine]): Map[RoutinePtr, Routine] =
    val seen = mutable.Map.empty[RoutinePtr, Routine]
    def visit(s: Space): Unit =
      for rp <- collect(s)({ case Space.Call(r, _, _) => r })._1.map(_._2) if defs.isDefinedAt(rp) && !seen.contains(rp) do
        val r = defs(rp); seen(rp) = r; visit(r.body)
    visit(conf); seen.toMap

  /** Run the supercompiler and return both the residual and an instrumentation report.  If the
   *  compile-time budget is exceeded the driver stops and we fall back to interpreting the original
   *  program (env = every routine reachable from `conf`), marking the run as non-converged. */
  def run(conf: Space, defs: PartialFunction[RoutinePtr, Routine], cfg: Config = Config()): (Residual, State, Space) =
    validate(conf)
    val st = new State(defs, cfg)
    // the finite alphabet of THIS run: every label of the configuration and of every routine body
    // reachable from it (Kruskal is applied to it; `alphabetEscapes` is the run-time check)
    st.alphabetBase = Matching.labels(conf, cfg.literalsAreAtoms) ++
      materialize(conf, defs).values.flatMap(r => Matching.labels(r.body, cfg.literalsAreAtoms))
    val residual =
      try
        val (top, tid) = st.driveT(conf, Nil, 0)
        st.topTrace = tid
        Residual(top, st.routines.toMap)
      catch
        case CompileBudgetExceeded =>
          st.converged = false
          Residual(conf, materialize(conf, defs))
    (residual, st, conf)

  /** Supercompile a configuration; returns the residual (back-compatible). */
  def supercompile(conf: Space, defs: PartialFunction[RoutinePtr, Routine], cfg: Config = Config()): Residual =
    run(conf, defs, cfg)._1

  def supercompile(r: Routine, defs: PartialFunction[RoutinePtr, Routine], cfg: Config): Residual =
    supercompile(Space.Call(r.name, r.refs.map(Path.Deref(_)), r.mentions.map(Space.Mention(_))), defs, cfg)

  def supercompile(r: Routine, defs: PartialFunction[RoutinePtr, Routine]): Residual =
    supercompile(r, defs, Config())

/** Report-bearing public facade (cf. critique_on_b §"API and Integration Gaps").  Wraps the
 *  positive-supercompiler core [[SC]] with metrics, operation-graph lowering of the residual,
 *  backend-support accounting, and a compile-time-evaluation flag. */
object Supercompiler:
  import Space.*

  /** Node kinds the operation-graph backend (transpile/exec) cannot compile. */
  def backendUnsupported(s: Space): Vector[String] =
    val out = mutable.LinkedHashSet.empty[String]
    def rp(p: Path): Unit = p match
      case Path.Concat(l, r) => rp(l); rp(r)
      case Path.GroundedPP(pp, _) => out += "GroundedPP"; rp(pp)
      case Path.GroundedSP(sp, _) => out += "GroundedSP"; rs(sp)
      case _ => ()
    def rs(x: Space): Unit = x match
      case Space.GroundedPS(p, _) => out += "GroundedPS"; rp(p)
      case Space.GroundedSS(sp, _) => out += "GroundedSS"; rs(sp)
      case Space.Fold(src, i, _, _, _, b, u) => out += "Fold"; rs(src); rp(i); rs(b); rp(u)
      case Space.Singleton(p) => rp(p)
      case Space.Call(_, rf, m) => rf.foreach(rp); m.foreach(rs)
      case Space.Union(a, b) => rs(a); rs(b)
      case Space.Intersection(a, b) => rs(a); rs(b)
      case Space.Subtraction(a, b) => rs(a); rs(b)
      case Space.Restriction(a, b) => rs(a); rs(b)
      case Space.Raffination(a, b) => rs(a); rs(b)
      case Space.Composition(a, b) => rs(a); rs(b)
      case Space.Iteration(src, _, _, b) => rs(src); rs(b)
      case Space.Fixpoint(init, _, b) => rs(init); rs(b)   // backend-supported (lowers to a Fixpoint subgraph)
      case Space.Wrap(src, p) => rs(src); rp(p)
      case Space.Unwrap(src, p) => rs(src); rp(p)
      case Space.TailsUnion(src) => rs(src)
      case Space.TailsIntersection(src) => rs(src)
      case Space.Range(a, _, _) => rs(a)
      case Space.Mention(_) | Space.Empty | Space.Literal(_) => ()
    rs(s); out.toVector

  private def hasCall(s: Space): Boolean =
    val (cs, _) = collect(s)({ case _: Space.Call => () }); cs.nonEmpty

  private def lower(residual: Residual, prof: Profiler, budget: Deadline): Map[RoutinePtr, RecursiveOpGraph] =
    residual.routines.flatMap { (rp, r) =>
      if backendUnsupported(r.body).isEmpty then
        val g = prof.timed("transpile")(transpile(r))
        scala.util.Try(optimize(g, budget, prof)).orElse(scala.util.Try(optimize_sharing(g))).toOption.map(rp -> _)
      else None
    }

  private def report(conf: Space, st: SC.State, residual: Residual, buildGraph: Boolean,
                     prof: Profiler, budget: Deadline): (SCReport, Map[RoutinePtr, RecursiveOpGraph]) =
    val unsupported = residual.routines.values.toVector.flatMap(r => backendUnsupported(r.body)) ++ backendUnsupported(residual.top)
    val graphs = if buildGraph then lower(residual, prof, budget) else Map.empty
    val backendCompiled = buildGraph && unsupported.isEmpty && graphs.size == residual.routines.size
    val cte = residual.routines.isEmpty && !hasCall(residual.top)
    val rep = SCReport(SCStats.of(conf), SCStats.of(residual.top) , residual.routines.size,
      st.reductions, st.unfoldings, st.folds, st.whistles, st.generalizations,
      converged = st.converged, compileTimeEvaluated = cte, backendCompiled = backendCompiled,
      residualPositive = st.residualPositive(residual.top), productive = st.productive,
      foldChecks = st.foldChecks, whistleFallbacks = st.whistleFallbacks,
      alphabetEscapes = st.alphabetEscapes.size,
      backendUnsupported = unsupported.distinct, compileMillis = prof.totalMillis, phaseMillis = prof.millis,
      phaseImprovement = prof.counts)
    (rep, graphs)

  /** Supercompile a configuration (e.g. a routine call with some static arguments).  All compile
   *  phases (supercompile-drive, transpile, push_out, optimize_sharing) are timed into the report,
   *  and the whole pipeline is bounded by `cfg.compileBudgetMs` (driving stops and falls back; the
   *  shared deadline also caps the optimizer so total compile time stays within the budget). */
  def compileCall(conf: Space, defs: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                  cfg: SC.Config = SC.Config(), buildGraph: Boolean = true): SupercompiledProgram =
    val prof = Profiler.on
    val budget = Deadline.inMillis(cfg.compileBudgetMs)
    val (residual, st, _) = prof.timed("supercompile")(SC.run(conf, defs, cfg))
    val (rep, graphs) = report(conf, st, residual, buildGraph, prof, budget)
    SupercompiledProgram(residual, rep, graphs)

  /** Supercompile a routine via its parametric entry call. */
  def compileRoutine(r: Routine, defs: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                     cfg: SC.Config = SC.Config(), buildGraph: Boolean = true): SupercompiledProgram =
    compileCall(Space.Call(r.name, r.refs.map(Path.Deref(_)), r.mentions.map(Space.Mention(_))), defs, cfg, buildGraph)

  /** Specialize a routine to known static arguments, then supercompile. */
  def specialize(r: Routine, spaceArgs: Map[SpaceMention, Space] = Map.empty, pathArgs: Map[PathRef, Path] = Map.empty,
                 defs: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                 cfg: SC.Config = SC.Config(), buildGraph: Boolean = true): SupercompiledProgram =
    val mentions = r.mentions.map(m => spaceArgs.getOrElse(m, Space.Mention(m)))
    val refs = r.refs.map(pr => pathArgs.getOrElse(pr, Path.Deref(pr)))
    compileCall(Space.Call(r.name, refs, mentions), defs, cfg, buildGraph)
