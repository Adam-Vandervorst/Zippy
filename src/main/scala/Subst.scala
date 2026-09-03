package morkl

/** ==================================================================================================
 *  THE ONE SUBSTITUTION.  SIMULTANEOUS, CAPTURE-AVOIDING, TOTAL.
 *
 *  ==WHAT WAS WRONG: FOUR IMPLEMENTATIONS THAT DISAGREED==
 *  Substitution is the operation review item 3 is about, and the tree had four of it:
 *
 *    1. `Matching.subst` (Supercompiler.scala) — the only CAPTURE-AVOIDING one.  Simultaneous over
 *       both sorts, alpha-renames a binder whose name occurs free in a replacement, total over every
 *       constructor.  It was used only by the supercompiler.
 *    2. `EquivPipeline.substMention` — SHADOW-AWARE ONLY.  It stops descending when a binder rebinds
 *       the substituted name, which is necessary but not sufficient: it does NOT rename a binder that
 *       would CAPTURE a free name of the replacement.  `Iteration(_, y, rest, Mention(rest))` with
 *       `rest := Mention(rest0)` under a binder named `rest0` silently captures.
 *    3. `EquivPipeline.substPathRef` — shadow-aware only, AND its path walker ended in
 *       `case other => other`, so `Path.GroundedPP` and `Path.GroundedSP` were never descended: a
 *       path ref inside a grounded closure's ARGUMENT was never substituted at all.
 *    4. the blind `subs` rewrites (`MORKL.scala`'s `IterateLiteral_Union`,
 *       `IterateSingleton_Deref`, `asFixpointGeneral`'s inner `sub`; `SpatialRecursion`'s
 *       residualisation) — a generic tree walk with NO binder awareness whatsoever.  It substitutes
 *       into a binder's body regardless of shadowing, which is unsound in the other direction.
 *
 *  ==AND ONE-AT-A-TIME IS NOT SIMULTANEOUS==
 *  `EquivPipeline`'s `Lower.inline` bound its arguments in a loop:
 *
 *      for (mn, arg) <- mentionns zip args do b = substMention(b, mn, arg)
 *
 *  which is sequential composition, not simultaneous substitution, and they differ exactly when an
 *  ARGUMENT mentions a later FORMAL.  For a routine `g(a, b)` called as `g(b, a)`:
 *
 *      body = Union(Mention(a), Wrap(Mention(b), p))
 *      sequential:  a := b  ->  Union(Mention(b), Wrap(Mention(b), p))     -- both are now `b`
 *                   b := a  ->  Union(Mention(a), Wrap(Mention(a), p))     -- both are now `a`  WRONG
 *      simultaneous:          Union(Mention(b), Wrap(Mention(a), p))                            RIGHT
 *
 *  The arguments have been swapped into one variable.  `SubstCapture` pins this as `g(y,x)`.
 *
 *  ==WHAT THIS FILE IS==
 *  `Matching.subst`'s implementation, MOVED here and made the single owner.  It is moved rather than
 *  re-derived on purpose: it is the one of the four that was already right, it is total over every
 *  constructor, and `SubstConformance` has been running a randomized differential against it (finding
 *  three real bugs, per its header).  Re-implementing it would throw that evidence away.  Everything
 *  else now delegates:
 *
 *      Matching.subst                    -> Subst.apply            (the supercompiler's entry point)
 *      EquivPipeline.substMention        -> Subst.mention
 *      EquivPipeline.substPathRef        -> Subst.pathRef
 *      EquivPipeline's Lower.inline      -> Subst.apply, ONE call with BOTH maps (the g(y,x) fix)
 *      MORKL's IterateLiteral_Union      -> Subst.mention
 *      MORKL's IterateSingleton_Deref    -> Subst.mention
 *      MORKL's asFixpointGeneral `sub`   -> Subst.mention
 *      SpatialRecursion residualisation  -> Subst.apply
 *
 *  ==WHY THE HINTS ARE PRESERVED ACROSS A RENAME==
 *  `PathRef.lengthHint` and `SpaceMention.sizeHint` are author-supplied facts about the VALUE a name
 *  denotes, not about the name.  An alpha-rename that dropped them would silently weaken every size
 *  and length bound downstream of an inlined call, which is a soundness-adjacent regression that no
 *  equivalence test would see (the terms still denote the same thing; only the ANALYSIS gets worse).
 *  `keepP`/`keepM` carry them.
 *
 *  ==THE FRESH-NAME PREFIX==
 *  `~` — not a character any source program or any other pass uses, so a renamed binder cannot
 *  collide with a name the program chose, and a `~` in a rendered term is a visible marker that a
 *  capture was avoided there.  Freshness is checked against the replacements' free names AND the
 *  body's, so it is fresh for the whole scope and not merely unused in one of them.
 *  ================================================================================================== */
object Subst:
  import Matching.{freeMentions, freeRefs}

  /** ================================================================================================
   *  THE CORRESPONDENCE TRACE (plan.md 1E.2).
   *
   *  `1E.2` asks for "a Lean-checked TRACE of the production substitutions — `LeanRender` emits each
   *  `(term, substitution, result)` the Scala performed, Lean re-checks it.  Not a citation."  This
   *  is the recorder.  It is OFF unless a caller turns it on, and when off every hook below compiles
   *  to one static boolean load and a not-taken branch — the same shape as `EffortSink.armed`, and
   *  for the same reason: a correspondence check must not be able to cost anything in production.
   *
   *  ==WHAT A TRIPLE HAS TO CARRY, AND THE ONE THING THAT CANNOT BE CHECKED BY EQUALITY==
   *  The Lean substitution is parameterised by a `FreshSupply` and its theorems hold for every
   *  supply, on purpose.  The Scala mints `~m0`, `~m1`, … from a COUNTER that persists across one
   *  `apply` call and advances past every use, so the second fresh name in a call is `~m1` even when
   *  `~m0` is available for it.  That is a STATEFUL policy and no `Finset Name → Name` reproduces
   *  it, so a triple in which a fresh name was minted cannot be re-checked by exact equality against
   *  any Lean `FreshSupply`.
   *
   *  So each triple records whether a name was minted (`fresh`), and the two classes are checked
   *  differently and counted separately:
   *
   *    CLASS A, `fresh.isEmpty` — no capture was avoided, so the result is independent of the
   *      naming policy and Lean checks EXACT EQUALITY.  This is the strong check, and it covers
   *      totality, simultaneity and shadowing at every constructor the trace reaches.
   *    CLASS B, `fresh.nonEmpty` — a capture WAS avoided.  Emitted with its minted names recorded so
   *      the count is visible and the case is not silently dropped; exact equality is not asserted,
   *      for the reason above.  What covers this class instead is `SubstCapture` (Scala, 13 tests,
   *      open replacements at all six binders) and `substS_keeps_freeM` (Lean, capture avoidance over
   *      every constructor).  If class B is EMPTY in production, class A is the whole correspondence
   *      and the trace says so.
   *  ================================================================================================ */
  object Trace:
    /** one recorded substitution */
    final case class Entry(term: Space, mentions: Vector[(String, Space)],
                           paths: Vector[(String, Path)], result: Space,
                           fresh: Vector[String]):
      /** class A triples are the exactly-checkable ones; see [[Trace]]'s header */
      def exactlyCheckable: Boolean = fresh.isEmpty

    @volatile private var on = false
    private val seen = scala.collection.mutable.LinkedHashMap.empty[(Space, Vector[(String, Space)], Vector[(String, Path)]), Entry]
    private var cap = 0
    private var dropped = 0

    /** BOUNDED, and deduplicated by `(term, substitution)`.  The pipeline performs tens of thousands
     *  of substitutions on terms up to 1741 nodes; an unbounded trace would be a multi-megabyte
     *  artifact whose size says nothing.  Repeats of one triple add no information, and the drop
     *  count is reported so a truncated trace cannot look complete. */
    def record(limit: Int)(body: => Unit): Vector[Entry] =
      synchronized { seen.clear(); cap = limit; dropped = 0; on = true }
      try body finally synchronized { on = false }
      synchronized { seen.values.toVector }

    def droppedCount: Int = synchronized(dropped)

    private[morkl] def note(term: Space, sm: Map[SpaceMention, Space], pm: Map[PathRef, Path],
                            result: Space, fresh: Vector[String]): Unit =
      if on then synchronized {
        val k = (term, sm.toVector.map((m, t) => m.s -> t).sortBy(_._1),
                 pm.toVector.map((r, t) => r.s -> t).sortBy(_._1))
        if seen.contains(k) then ()
        else if seen.size >= cap then dropped += 1
        else seen(k) = Entry(term, k._2, k._3, result, fresh)
      }

    def isOn: Boolean = on

  /** THE substitution.  Simultaneous in both sorts, capture-avoiding, total.
   *
   *  A binder shadows any substitution for the same name within its scope; a binder whose name occurs
   *  free in a replacement is alpha-renamed to a fresh name before the descent.  With both maps empty
   *  it is the identity and returns `s` itself. */
  def apply(s: Space, mentions: Map[SpaceMention, Space] = Map.empty,
            paths: Map[PathRef, Path] = Map.empty): Space =
    if mentions.isEmpty && paths.isEmpty then s
    else if !Trace.isOn then go(s, mentions, paths)
    else
      // TRACED.  The minted-name list is collected by `go` and is what separates the two triple
      // classes; see `Trace`'s header.  The `isOn` test is outside the hot path so an untraced run
      // takes the same branch it always did.
      val minted = scala.collection.mutable.ArrayBuffer.empty[String]
      val r = go(s, mentions, paths, minted)
      Trace.note(s, mentions, paths, r, minted.toVector)
      r

  /** One space mention.  The single-name case of [[apply]]; kept as a name because the call sites
   *  that used `substMention` read better this way and because it documents that the single case is
   *  NOT a different algorithm. */
  def mention(s: Space, m: SpaceMention, r: Space): Space = apply(s, Map(m -> r))

  /** One path ref.  The single-name case of [[apply]] on the path side. */
  def pathRef(s: Space, pr: PathRef, arg: Path): Space = apply(s, Map.empty, Map(pr -> arg))

  /** Substitution inside a bare `Path`.
   *
   *  A `Path` has no space binders of its own, so this is the whole of it — but it must still go
   *  through the space walker, because `Path.GroundedSP` carries a `Space` that can contain binders.
   *  Routing it through `Singleton` is how `Matching.subst2` did it and is why `Path.GroundedSP`'s
   *  body gets the same treatment as any other space. */
  def path(p: Path, mentions: Map[SpaceMention, Space] = Map.empty,
           paths: Map[PathRef, Path] = Map.empty): Path =
    apply(Space.Singleton(p), mentions, paths) match
      case Space.Singleton(q) => q
      // unreachable: `Singleton` is preserved by every arm below.  Reported rather than silently
      // returning `p`, because a silent identity here is a substitution that did nothing.
      case other => throw new IllegalStateException(
        s"Subst.path: substituting inside a Singleton produced ${other.getClass.getSimpleName}; " +
        "the space walker must preserve the constructor it was given")

  // ================================================================================================
  // The implementation, moved verbatim in behaviour from `Matching.subst`.
  // ================================================================================================
  private def go(s0: Space, sm0: Map[SpaceMention, Space], pm0: Map[PathRef, Path],
                 minted: scala.collection.mutable.ArrayBuffer[String] = null): Space =
    var fresh = 0
    def freshName(avoid: Set[String], kind: String): String =
      while avoid(s"~$kind$fresh") do fresh += 1
      val r = s"~$kind$fresh"; fresh += 1
      if minted != null then minted += r
      r
    // renames preserve hints: a binder's lengthHint (an Iteration/Fold symbol is always a length-1
    // head, tagged at the rename site) and any author sizeHint carry over to the fresh name
    def keepP(f: PathRef, old: PathRef): PathRef = if old.lengthHint >= 0 then f.known(old.lengthHint) else f
    def keepM(f: SpaceMention, old: SpaceMention): SpaceMention = if old.sizeHint >= 0 then f.known(old.sizeHint) else f
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
          val nr = if capM then keepM(SpaceMention(freshName(rangeMentions(sm2, pm2).map(_.s) ++ freeMentions(body).map(_.s), "m")), rest) else rest
          val ns = if capP then PathRef(freshName(rangeRefs(sm2, pm2).map(_.s) ++ freeRefs(body).map(_.s), "p")).known(1) else sym
          val body1 = recs(body, if capM then Map(rest -> Space.Mention(nr)) else Map.empty, if capP then Map(sym -> Path.Deref(ns)) else Map.empty)
          Space.Iteration(recs(src, sm, pm), ns, nr, recs(body1, sm2, pm2))
        else Space.Iteration(recs(src, sm, pm), sym, rest, recs(body, sm2, pm2))
      case Space.Fixpoint(init, rec, body) =>
        val sm2 = sm - rec   // rec (a mention) shadows mention substitution in body; refs unaffected
        if rangeMentions(sm2, pm).contains(rec) then
          val nr = keepM(SpaceMention(freshName(rangeMentions(sm2, pm).map(_.s) ++ freeMentions(body).map(_.s), "m")), rec)
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
          val nr = if capR then keepM(SpaceMention(freshName(rangeMentions(sm2, pm2).map(_.s) ++ bodyVars, "m")), rest) else rest
          val na = if capA then keepP(PathRef(freshName(rangeRefs(sm2, pm2).map(_.s) ++ refVars, "p")), acc2) else acc2
          val nsy = if capS then PathRef(freshName(rangeRefs(sm2, pm2).map(_.s) ++ refVars, "p")).known(1) else sym
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
    recs(s0, sm0, pm0)
end Subst
