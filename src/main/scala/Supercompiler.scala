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

  /** Capture-avoiding simultaneous substitution of free mentions and refs.  A binder
   *  (Iteration/Fold) shadows any substitution for the same name within its body; and if a
   *  replacement term would otherwise be captured by a binder (i.e. the binder name occurs
   *  free in the term being substituted in), the binder is alpha-renamed to a fresh name
   *  (prefix `~`, checked against all names in scope) before descending.  This is true
   *  hygiene, not merely shadow-awareness. */
  def subst(s: Space, sm: Map[SpaceMention, Space] = Map.empty, pm: Map[PathRef, Path] = Map.empty): Space =
    var fresh = 0
    def freshName(avoid: Set[String], kind: String): String =
      while avoid(s"~$kind$fresh") do fresh += 1
      val r = s"~$kind$fresh"; fresh += 1; r
    def rangeMentions(asm: Map[SpaceMention, Space], apm: Map[PathRef, Path]): Set[SpaceMention] =
      asm.valuesIterator.flatMap(freeMentions).toSet ++ apm.valuesIterator.flatMap(p => freeMentions(Space.Singleton(p))).toSet
    def rangeRefs(asm: Map[SpaceMention, Space], apm: Map[PathRef, Path]): Set[PathRef] =
      apm.valuesIterator.flatMap(p => freeRefs(Space.Singleton(p))).toSet ++ asm.valuesIterator.flatMap(freeRefs).toSet
    def recp(p: Path, sm: Map[SpaceMention, Space], pm: Map[PathRef, Path]): Path = p match
      case Path.Deref(pr) => pm.getOrElse(pr, p)
      case Path.Constant(_) => p
      case Path.Concat(l, r) => Path.Concat(recp(l, sm, pm), recp(r, sm, pm))
      case Path.GroundedPP(pp, f) => Path.GroundedPP(recp(pp, sm, pm), f)
      case Path.GroundedSP(sp, f) => Path.GroundedSP(recs(sp, sm, pm), f)
    def recs(x: Space, sm: Map[SpaceMention, Space], pm: Map[PathRef, Path]): Space = x match
      case Space.Mention(v) => sm.getOrElse(v, x)
      case Space.Empty | Space.Literal(_) => x
      case Space.Singleton(p) => Space.Singleton(recp(p, sm, pm))
      case Space.Call(r, refs, mentions) => Space.Call(r, refs.map(recp(_, sm, pm)), mentions.map(recs(_, sm, pm)))
      case Space.Union(a, b) => Space.Union(recs(a, sm, pm), recs(b, sm, pm))
      case Space.Intersection(a, b) => Space.Intersection(recs(a, sm, pm), recs(b, sm, pm))
      case Space.Subtraction(a, b) => Space.Subtraction(recs(a, sm, pm), recs(b, sm, pm))
      case Space.Restriction(a, b) => Space.Restriction(recs(a, sm, pm), recs(b, sm, pm))
      case Space.Raffination(a, b) => Space.Raffination(recs(a, sm, pm), recs(b, sm, pm))
      case Space.Composition(a, b) => Space.Composition(recs(a, sm, pm), recs(b, sm, pm))
      case Space.Iteration(src, sym, rest, body) =>
        val sm2 = sm - rest; val pm2 = pm - sym
        val capM = rangeMentions(sm2, pm2).contains(rest)
        val capP = rangeRefs(sm2, pm2).contains(sym)
        if capM || capP then
          val nr = if capM then SpaceMention(freshName(rangeMentions(sm2, pm2).map(_.s) ++ freeMentions(body).map(_.s), "m")) else rest
          val ns = if capP then PathRef(freshName(rangeRefs(sm2, pm2).map(_.s) ++ freeRefs(body).map(_.s), "p")) else sym
          val body1 = recs(body, if capM then Map(rest -> Space.Mention(nr)) else Map.empty, if capP then Map(sym -> Path.Deref(ns)) else Map.empty)
          Space.Iteration(recs(src, sm, pm), ns, nr, recs(body1, sm2, pm2))
        else Space.Iteration(recs(src, sm, pm), sym, rest, recs(body, sm2, pm2))
      case Space.Fixpoint(init, rec, body) =>
        val sm2 = sm - rec   // rec (a mention) shadows mention substitution in body; refs unaffected
        if rangeMentions(sm2, pm).contains(rec) then
          val nr = SpaceMention(freshName(rangeMentions(sm2, pm).map(_.s) ++ freeMentions(body).map(_.s), "m"))
          val body1 = recs(body, Map(rec -> Space.Mention(nr)), Map.empty)
          Space.Fixpoint(recs(init, sm, pm), nr, recs(body1, sm2, pm))
        else Space.Fixpoint(recs(init, sm, pm), rec, recs(body, sm2, pm))
      case Space.Fold(src, init, acc2, sym, rest, body, upd) =>
        val pm2 = pm - acc2 - sym; val sm2 = sm - rest
        // alpha-rename any of the three binders that a replacement would capture
        val capR = rangeMentions(sm2, pm2).contains(rest)
        val capA = rangeRefs(sm2, pm2).contains(acc2)
        val capS = rangeRefs(sm2, pm2).contains(sym)
        if capR || capA || capS then
          val bodyVars = freeMentions(body).map(_.s) ++ freeMentions(Space.Singleton(upd)).map(_.s)
          val refVars = freeRefs(body).map(_.s) ++ freeRefs(Space.Singleton(upd)).map(_.s)
          val nr = if capR then SpaceMention(freshName(rangeMentions(sm2, pm2).map(_.s) ++ bodyVars, "m")) else rest
          val na = if capA then PathRef(freshName(rangeRefs(sm2, pm2).map(_.s) ++ refVars, "p")) else acc2
          val nsy = if capS then PathRef(freshName(rangeRefs(sm2, pm2).map(_.s) ++ refVars, "p")) else sym
          val renS = if capR then Map(rest -> Space.Mention(nr)) else Map.empty[SpaceMention, Space]
          val renP = (if capA then Map(acc2 -> Path.Deref(na)) else Map.empty[PathRef, Path]) ++ (if capS then Map(sym -> Path.Deref(nsy)) else Map.empty)
          val body1 = recs(body, renS, renP)
          val upd1 = recp(upd, renS, renP)
          Space.Fold(recs(src, sm, pm), recp(init, sm, pm), na, nsy, nr, recs(body1, sm2, pm2), recp(upd1, sm2, pm2))
        else Space.Fold(recs(src, sm, pm), recp(init, sm, pm), acc2, sym, rest, recs(body, sm2, pm2), recp(upd, sm2, pm2))
      case Space.Wrap(src, p) => Space.Wrap(recs(src, sm, pm), recp(p, sm, pm))
      case Space.Unwrap(src, p) => Space.Unwrap(recs(src, sm, pm), recp(p, sm, pm))
      case Space.TailsUnion(src) => Space.TailsUnion(recs(src, sm, pm))
      case Space.TailsIntersection(src) => Space.TailsIntersection(recs(src, sm, pm))
      case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p, sm, pm), f)
      case Space.GroundedSS(sp, f) => Space.GroundedSS(recs(sp, sm, pm), f)
      case Space.Range(a, lo, hi) => Space.Range(recs(a, sm, pm), lo, hi)
    if sm.isEmpty && pm.isEmpty then s else recs(s, sm, pm)

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
        val p = freshP(); val r = freshS()
        Space.Iteration(s2, p, r, recs(subst(body, Map(rest -> Space.Mention(r)), Map(sym -> Path.Deref(p)))))
      case Space.Fold(src, init, acc2, sym, rest, body, upd) =>
        val s2 = recs(src); val i2 = recp(init)
        val a = freshP(); val p = freshP(); val r = freshS()
        val pm = Map(acc2 -> Path.Deref(a), sym -> Path.Deref(p)); val smm = Map(rest -> Space.Mention(r))
        Space.Fold(s2, i2, a, p, r, recs(subst(body, smm, pm)), recp(subst2(upd, smm, pm)))
      case Space.Fixpoint(init, rec, body) =>
        val i2 = recs(init); val r = freshS()
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
    // helper to substitute only inside an update Path before recursing
    def subst2(p: Path, sm: Map[SpaceMention, Space], pm: Map[PathRef, Path]): Path =
      subst(Space.Singleton(p), sm, pm) match { case Space.Singleton(q) => q; case _ => p }
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

  // ---- homeomorphic embedding (the whistle) ---------------------------------

  /** Homeomorphic embedding `a ⊴ b` on canonicalized configurations.  Free mentions/refs are
   *  universal variables (a variable embeds any variable of the same kind).  The supercompiler's
   *  whistle: if an ancestor embeds in a descendant, generalize to ensure termination.
   *
   *  `litAtoms` is a deliberate HEURISTIC, not "the" embedding.  With `litAtoms=true` (default)
   *  every literal/constant is one atom, so a configuration that grows a *static* literal
   *  accumulator trips the whistle and is generalized into a reusable loop instead of being
   *  unrolled to its answer.  The cost is potential precision loss / earlier generalization;
   *  with `litAtoms=false` the embedding is structural (literals couple only when equal), which
   *  fully evaluates static recursion but never generalizes it.  Both are sound; they trade
   *  residual *shape*.  (See `SCGeneralization` for tests of both modes.) */
  def embeds(a0: Space, b0: Space, litAtoms: Boolean = true): Boolean = embedsS(canon(a0), canon(b0), litAtoms)

  private def isVarS(s: Space): Boolean = s match { case Space.Mention(v) => !isCanonical(v.s); case _ => false }
  private def isVarP(p: Path): Boolean = p match { case Path.Deref(v) => !isCanonical(v.s); case _ => false }

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

  private def embedsS(a: Space, b: Space, litAtoms: Boolean): Boolean =
    if isVarS(a) && isVarS(b) then true
    else
      val dive = childrenS(b).exists(c => embed(a, c, litAtoms))
      val couple = coupledS(a, b, litAtoms) && childrenS(a).lazyZip(childrenS(b)).forall(embed(_, _, litAtoms))
      dive || couple

  private def embedsP(a: Path, b: Path, litAtoms: Boolean): Boolean =
    if isVarP(a) && isVarP(b) then true
    else
      val dive = childrenP(b).exists(c => embed(a, c, litAtoms))
      val couple = coupledP(a, b, litAtoms) && childrenP(a).lazyZip(childrenP(b)).forall(embed(_, _, litAtoms))
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
                    phaseImprovement: Map[String, Long] = Map.empty):
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
      s"unfold=$unfoldings fold=$folds whistle=$whistles gen=$generalizations reduce=$reductions | $backend"
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
    "range-singleton" -> Lower.Range_Singleton, "unwrap-wrap" -> Lower.Unwrap_Wrap)
  val simplifyRules: List[Space => Space] = sourceLaws.map(_._2)

  /** Bounded fixpoint reduction.  The step cap turns an oscillating/non-terminating rule into a
   *  clear error; the wall-clock `deadline` stops it GRACEFULLY (returns the current normal form,
   *  sound since the laws are meaning-preserving).  Convergence is structural `==`, not `show`. */
  def reduce(s: Space, cap: Int = 100000, deadline: Deadline = Deadline.never): Space =
    var cur = s
    var nxt = simplifyRules.foldLeft(cur)((x, f) => f(x))
    var rounds = 0
    while nxt != cur && !deadline.expired do
      rounds += 1
      if rounds > cap then sys.error(s"SC reduce did not converge within $cap rounds")
      cur = nxt; nxt = simplifyRules.foldLeft(cur)((x, f) => f(x))
    nxt

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
                    compileBudgetMs: Double = Config.DefaultBudgetMs)
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
    // function nodes: (residual name, configuration at creation, ordered ref params, ordered mention params)
    val fnodes = mutable.ArrayBuffer.empty[(RoutinePtr, Space, Vector[PathRef], Vector[SpaceMention])]
    val routines = mutable.Map.empty[RoutinePtr, Routine]

    def fresh(hint: String): RoutinePtr = { counter += 1; RoutinePtr(s"${hint}_sc$counter") }
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
    def drive(s: Space, path: List[(Space, RoutinePtr)], depth: Int): Space =
      if deadline.expired then throw CompileBudgetExceeded
      reductions += 1
      val r = reduce(s, cfg.maxReduce, deadline)
      subs(r)(spost = { case c: Space.Call if callable(c) => scCall(c, path, depth) })

    /** Supercompile one Call configuration: fold -> whistle/generalize -> new node.
     *
     *  FOLDING is global (against every function node, not only ancestors on the current
     *  path).  This is sound because each function node's routine is parameterized by exactly
     *  the free variables of its configuration, and a MORKL configuration denotes a pure
     *  function of its free variables; so an instance match yields a call with the correct
     *  argument substitution regardless of context.  Global memoization only ever increases
     *  sharing.  The whistle still uses the ancestor PATH (innermost first via `collectFirst`,
     *  so generalization is deterministic w.r.t. the most-recent embedding ancestor). */
    def scCall(c: Space.Call, path: List[(Space, RoutinePtr)], depth: Int): Space =
      if deadline.expired then throw CompileBudgetExceeded
      if depth > cfg.maxDepth then sys.error(s"SC depth cap ${cfg.maxDepth} exceeded at ${c.show}")
      if fnodes.length > cfg.maxNodes then sys.error(s"SC node cap ${cfg.maxNodes} exceeded")
      val folded = fnodes.iterator.flatMap { case (g, gc, refs, ments) =>
        Matching.instanceOf(gc, c).map((g, refs, ments, _))
      }.nextOption()
      folded match
        case Some((g, refs, ments, (sm, pm))) => folds += 1; callOf(g, refs, ments, sm, pm)
        case None =>
          val whistler =
            if !cfg.generalize then None
            else path.collectFirst { case (pc, _) if Matching.embeds(pc, c, cfg.literalsAreAtoms) && Matching.instanceOf(pc, c).isEmpty => pc }
          whistler match
            case Some(pc) => whistles += 1; generalize(pc, c, path, depth)
            case None => makeNode(c, path, depth)

    def makeNode(c: Space.Call, path: List[(Space, RoutinePtr)], depth: Int): Space =
      val (refs, ments) = paramsOf(c)
      val g = fresh(hintOf(c))
      fnodes += ((g, c, refs, ments))
      val body = drive(unfold(c), (c, g) :: path, depth + 1)
      routines(g) = Routine(g, refs, ments, body)
      Space.Call(g, refs.map(Path.Deref(_)), ments.map(Space.Mention(_)))

    /** Whistle response: most-specific-generalize the embedded ancestor against the current
     *  call (downward generalization), supercompile the more-general skeleton, then plug the
     *  driven hole-values back in.  The generalized skeleton, being strictly more general, is
     *  driven once and its recursive descendants fold to it. */
    def generalize(pc: Space, c: Space.Call, path: List[(Space, RoutinePtr)], depth: Int): Space =
      val gen = Matching.msg(pc, c, cfg.literalsAreAtoms)
      gen.skeleton match
        case sk: Space.Call if !Matching.alphaEqual(sk, c) =>
          generalizations += 1
          val residGen = scCall(sk, path, depth + 1)
          val sm = gen.rsm.view.mapValues(v => drive(v, path, depth + 1)).toMap
          Matching.subst(residGen, sm, gen.rpm)
        case _ => makeNode(c, path, depth)

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
    val residual =
      try Residual(st.drive(conf, Nil, 0), st.routines.toMap)
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
