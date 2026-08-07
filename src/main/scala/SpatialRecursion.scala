package morkl

import scala.collection.immutable.SortedMap
import scala.collection.mutable

/** BOUNDED RECURSION — interprocedural routine SUMMARIES, a DECREASING path-length MEASURE, an
 *  explicit CALL-DEPTH BOUND derived from that measure plus a maximum input length, and
 *  RESIDUALISATION of the traversal into exactly that many specialised levels.  This is review.md
 *  finding 2: "if the maximum path length is four and a recursive routine consumes one item per
 *  call, eliminate recursion and specialize four levels".
 *
 *  ==NO EVALUATION==
 *  Nothing here calls `eval`/`evalI`/`evalT`/`exec*`.  Every fact comes from the term's syntax, the
 *  declared input types, the transfers of [[SpatialTyping]]/[[SpatialTypes]]/[[Shape]], and the
 *  fixed-point machinery below (docs/design_spatial_lattice.md §0).  `eval` appears only in the
 *  test suite, as ground truth.
 *
 *  ==THE FOUR PIECES==
 *
 *  1. SUMMARIES, memoised by `(RoutinePtr, abstract argument tuple)` ([[Key]]), solved by a
 *     WORKLIST to a fixed point with widening — not a fixed number of steps.  A summary maps
 *     abstract arguments to an abstract result.  The search strategy (join, widen after
 *     `widenAfter` updates, ⊤ after `maxUpdates`, ⊤ past `maxKeys`) is a heuristic; what makes the
 *     answer sound is the explicit POST-FIXED-POINT CERTIFICATION at the end
 *     ([[Summaries.certified]]): for every key in the table, re-deriving the body under the final
 *     table yields a type `⊑` the stored one.  Any post-fixed point of a sound abstract transfer
 *     over-approximates the concrete least fixed point, so the certification — not the schedule —
 *     is the licence.  A table that fails to certify is reported, never used.
 *
 *  2. A DECREASING MEASURE.  `μ(t) = t.len.hi` — the maximum number of path ITEMS the abstract
 *     type permits.  Two things are checked, and BOTH are required (see [[Decrease]] and
 *     [[DepthBound.NoBound]] for the failure reasons):
 *
 *       (M1) a STRUCTURAL witness that the recursive argument expression drops ≥1 item relative to
 *            the parameter: it is a `TailsUnion`/`TailsIntersection` of a subset of the parameter,
 *            an `Unwrap` of one by a path of ≥1 items, or the REST-MENTION of an enclosing
 *            `Iteration`/`Fold` whose source is a subset of the parameter.  "Subset of" is itself
 *            syntactic: `∩`, `∖`, `<|`, `\|`, `Range` and `∪`-of-subsets only ever delete paths, so
 *            they cannot lengthen one.
 *       (M2) a NUMERIC drop on the actual abstract types along the unrolled chain:
 *            `μ(a_{k+1}) ≤ μ(a_k) − 1` at every level (an empty `a_{k+1}` counts as a drop).
 *
 *     M2 is the load-bearing fact; M1 is the structural reason and rules out an accidental drop.
 *     From `μ(a_0) = L` and M2, `a_{L+1}` must be the empty type, so the search for a level whose
 *     SUMMARY is provably empty terminates by `L + 1` — that is the derived depth bound.
 *
 *  3. THE BOUND.  `maxCallDepth = k` is the FIRST level whose summary is provably empty, i.e. the
 *     level at which the call contributes nothing for every argument the chain admits.  With
 *     `μ(a_0) = 4` and one item consumed per call, a routine whose body is empty on a headless
 *     argument gives `k = 4` exactly.
 *
 *  4. RESIDUALISATION.  Levels `0 … k−1` are unrolled (hygienically: every binder of every spliced
 *     copy is alpha-renamed to a globally fresh name first, so an argument expression that mentions
 *     a loop binder — the common `Mention(rest)` case — cannot be captured) and the level-`k` call
 *     is replaced by `Empty`, justified by that provably-empty summary.  The result is a Call-free
 *     [[Routine]] wrapped in [[BoundedRecursion]], which carries the PRECONDITION it was derived
 *     under as data (like `SpatialTyping.SpecializedRoutine`) and decides an actual argument against
 *     it with [[BoundedRecursion.applicableTo]].  A conditional equivalence never looks
 *     unconditional.
 *
 *  ==WHY SUMMARIES ARE MAY-ONLY==
 *  Every summary is [[weaken]]ed: no MUST claim, every count lower bound 0.  Two reasons, both
 *  load-bearing.  (i) `Shape.union` / `SpatialTypes.join` are UNION TRANSFERS, not lattice joins;
 *  they are upper bounds of their operands only when `∅ ∈ γ` of each operand, which weakening
 *  guarantees.  (ii) γ of a weakened type is downward closed under subsets, which is what licenses
 *  binding an iteration's `rest` mention to (the weakening of) `TailsUnion(src)`: one head-group's
 *  tail-set is a SUBSET of the union of all of them.  The cost is that a summary can never say "the
 *  result is definitely non-empty"; the bound only needs upper facts.
 *
 *  ==WHAT IS AND IS NOT CLAIMED==
 *  The residual agrees with the original on every input SATISFYING the precondition and on which the
 *  original terminates.  For the recognised family termination is itself derived (the argument's
 *  maximum length strictly drops, so the argument reaches ∅ — a fixed point of the recursion — in
 *  ≤ L+1 steps).  Outside the precondition the residual may differ, which is exactly why the
 *  precondition is part of the artifact.  This has been checked differentially (see
 *  `SpatialRecursionCheck`), not proved. */
object SpatialRecursion:
  import Lower.{LenBounds, SizeBounds}

  /** the reserved prefix for placeholder mentions and freshened binders.  A body containing a free
   *  name with this prefix is REJECTED rather than silently mis-substituted (traps.md #7). */
  val Reserved = "#sr#"

  // ================================================================================================
  // 0.  weakening, the order, the join and the widening on the reduced product
  // ================================================================================================

  /** drop every count LOWER bound; the length support and every upper bound are kept.  Preserves the
   *  histogram's representation invariant: which lengths are tracked and which sit in the spill
   *  window is untouched. */
  def weakenLens(t: SpaceType): SpaceType =
    if t.isProvablyEmpty then SpaceType.empty
    else SpaceType(SortedMap.from(t.byLen.iterator.map((l, c) => l -> Ivl(0L, c.hi))),
                   Ivl(0L, t.rest.hi), t.restLens)

  /** the may-only projection of a spatial type — see the class comment for why every summary is one */
  def weaken(t: SpatialType): SpatialType =
    if t.isProvablyEmpty then SpatialType.empty
    else SpatialType(Shape.weaken(t.shape), weakenLens(t.lens))

  private def lenIn(x: LenBounds, y: LenBounds): Boolean =
    x.isEmpty || (!y.isEmpty && y.lo <= x.lo && x.hi <= y.hi)

  /** `γ(a) ⊆ γ(b)` on the histogram component.  Stronger than `SpaceType.within`, which compares
   *  UPPER ENVELOPES only and therefore does not imply γ-containment: `{len 1:[0,3], len 2:[0,3]}`
   *  is `within` `{rest [0,3] over lens 0..10}` yet admits six paths where the latter admits three.
   *  The total is compared explicitly here for exactly that reason. */
  def lensLeq(a: SpaceType, b: SpaceType): Boolean =
    if a.isProvablyEmpty then true
    else
      val ls = (a.byLen.keySet ++ b.byLen.keySet).toVector
      val (sa, sb) = (a.size, b.size)
      ls.forall(l => a.at(l).hi <= b.at(l).hi && a.at(l).lo >= b.at(l).lo) &&
        sa.hi <= sb.hi && sa.lo >= sb.lo && sa.loHeaded >= sb.loHeaded &&
        (a.rest.hi == 0 || (a.rest.hi <= b.rest.hi && !b.restLens.isEmpty &&
                            b.restLens.lo <= a.restLens.lo && a.restLens.hi <= b.restLens.hi)) &&
        lenIn(a.len, b.len)

  /** the order on the reduced product: `Shape.leq` on the shape (the same order that domain's own
   *  fixpoint check uses), [[lensLeq]] on the histogram, plus the REDUCED projections, since those
   *  are meets of both components and γ of the product constrains them directly. */
  def leq(a: SpatialType, b: SpatialType): Boolean =
    a.isProvablyEmpty ||
      (Shape.leq(a.shape, b.shape) && lensLeq(a.lens, b.lens) &&
        a.size.hi <= b.size.hi && a.size.lo >= b.size.lo && lenIn(a.len, b.len))

  /** an upper bound of both, used to accumulate the ascending chain.  Sound as an upper bound
   *  because both operands are may-only (see the class comment). */
  def join(a: SpatialType, b: SpatialType): SpatialType =
    if a.isProvablyEmpty then weaken(b)
    else if b.isProvablyEmpty then weaken(a)
    else weaken(SpatialType.reduce(SpatialType(Shape.union(a.shape, b.shape),
                                               SpatialTypes.join(a.lens, b.lens))))

  /** the WIDENING: open every count channel and every head set, keep the LENGTH SUPPORT (the fact
   *  the depth bound is derived from).  `Shape.widenShape` is the shape domain's own widening. */
  def widenType(t: SpatialType): SpatialType =
    if t.isProvablyEmpty then SpatialType.empty
    else
      val l = t.lens
      weaken(SpatialType(Shape.widenShape(t.shape),
        SpaceType(SortedMap.from(l.byLen.iterator.map((k, _) => k -> Ivl(0L, Ivl.INF))),
                  if l.rest.hi == 0 then Ivl.zero else Ivl(0L, Ivl.INF), l.restLens)))

  /** the MEASURE: how many path items the type permits at most.  `Ivl.INF` = unbounded; the empty
   *  type has no paths at all and is handled by [[SpatialType.isProvablyEmpty]], never by `μ`. */
  def measure(t: SpatialType): Long = if t.isProvablyEmpty then -1L else t.len.hi

  // ================================================================================================
  // 1.  abstract argument tuples and summary keys
  // ================================================================================================

  /** a path argument: its constant value when the term determines it (which lets a callee's shape
   *  transfers see the actual items), otherwise only its item-length interval */
  final case class PathArg(value: Option[PathValue], len: LenBounds):
    def show: String = value.map(p => "\"" + p.show + "\"").getOrElse(
      s"[${len.lo}, ${if len.hi == LenBounds.INF then "inf" else len.hi}]")
  object PathArg:
    def opaque(k: LenBounds): PathArg = PathArg(None, k)
    def known(p: PathValue): PathArg = PathArg(Some(p), LenBounds(p.items.length, p.items.length))

  /** the abstract argument tuple a summary is indexed by */
  final case class Args(mentions: Vector[SpatialType], paths: Vector[PathArg]):
    def show: String = s"(${paths.map(_.show).mkString(", ")}; ${mentions.map(_.show).mkString(", ")})"

  final case class Key(routine: RoutinePtr, args: Args):
    def show: String = s"${routine.s}${args.show}"

  /** canonical form of a type used inside a KEY: reduce, and collapse every provably-empty type to
   *  the single `⊥` so the memo table does not hold several spellings of ∅. */
  def keyType(t: SpatialType): SpatialType =
    val r = SpatialType.reduce(t)
    if r.isProvablyEmpty then SpatialType.empty else r

  // ================================================================================================
  // 2.  the worklist solver
  // ================================================================================================

  final case class Limits(maxKeys: Int = 400, maxUpdates: Int = 8, widenAfter: Int = 3,
                          maxRounds: Int = 20000, maxUnroll: Int = 32)

  /** The solved summary table.  `certified` is the POST-FIXED-POINT property, re-checked over the
   *  final table; only a certified table licenses anything. */
  final case class Summaries(table: Map[Key, SpatialType], certified: Boolean, note: String,
                             rounds: Int, updates: Int, widenedKeys: Int, toppedKeys: Int):
    def at(k: Key): SpatialType = table.getOrElse(k, SpatialType.top)
    def keys: Int = table.size
    def show: String =
      s"${table.size} keys, $rounds rounds, $updates updates, $widenedKeys widened, " +
      s"$toppedKeys ⊤-pinned, certified=$certified" + (if note.isEmpty then "" else s" ($note)")

  /** Solve the summaries reachable from `entry` to a certified post-fixed point (or report why not). */
  def summarise(entry: Key, routines: PartialFunction[RoutinePtr, Routine],
                limits: Limits = Limits()): Summaries =
    new Solver(routines, limits).solve(entry)

  private final class Solver(routines: PartialFunction[RoutinePtr, Routine], limits: Limits):
    private val cur = mutable.LinkedHashMap.empty[Key, SpatialType]
    private val ups = mutable.HashMap.empty[Key, Int]
    private val deps = mutable.HashMap.empty[Key, mutable.LinkedHashSet[Key]]
    private val queue = mutable.Queue.empty[Key]
    private val queued = mutable.HashSet.empty[Key]
    private var overflowed = false          // the key budget ran out: an unknown callee became ⊤
    private var escaped = false             // certification met a key the solve had not reached
    private var frozen = false              // no new keys (the certification sweep)
    private var rounds = 0
    private var updates = 0
    private var widened = 0
    private var topped = 0

    private def enqueue(k: Key): Unit = if !queued(k) then { queued += k; queue.enqueue(k) }

    /** the current value of a key.  A key not yet reached starts at `⊥` and is scheduled; once the
     *  key budget is gone (or during the certification sweep) an unreached key answers `⊤`, which
     *  is always a sound summary. */
    private def value(of: Key, from: Option[Key]): SpatialType =
      from.foreach(f => deps.getOrElseUpdate(of, mutable.LinkedHashSet.empty) += f)
      cur.get(of) match
        case Some(t) => t
        case None =>
          if frozen then { escaped = true; SpatialType.top }
          else if cur.size >= limits.maxKeys then { overflowed = true; SpatialType.top }
          else { cur(of) = SpatialType.empty; enqueue(of); SpatialType.empty }

    /** the abstract result of a routine BODY under the current table — the summary's transfer */
    def bodyType(key: Key): SpatialType =
      routines.lift(key.routine) match
        case None => SpatialType.top
        case Some(r) =>
          if r.mentions.length != key.args.mentions.length || r.refs.length != key.args.paths.length then
            SpatialType.top
          else
            val env = entryEnv(r, key.args)
            val sc = new BodyScan(routines, k => value(k, Some(key)))
            val rewritten = sc.rewrite(r.body, env)
            weaken(SpatialType.reduce(
              SpatialTyping.infer(rewritten, env.copy(spaces = env.spaces ++ sc.bindings))))

    def solve(entry: Key): Summaries =
      value(entry, None)
      while queue.nonEmpty && rounds < limits.maxRounds do
        rounds += 1
        val k = queue.dequeue(); queued -= k
        if cur.contains(k) then
          val old = cur(k)
          val nw = bodyType(k)
          if !leq(nw, old) then
            updates += 1
            val n = ups.getOrElse(k, 0) + 1
            ups(k) = n
            val j = join(old, nw)
            val next =
              if n >= limits.maxUpdates then { topped += 1; SpatialType.top }
              else if n >= limits.widenAfter then { widened += 1; widenType(j) }
              else j
            cur(k) = next
            deps.get(k).foreach(_.foreach(enqueue))
      val exhausted = queue.nonEmpty
      // ---- CERTIFICATION: the post-fixed-point property, re-checked over the FINAL table --------
      frozen = true
      val snapshot = cur.keys.toVector
      var bad = 0
      for k <- snapshot do
        if !leq(bodyType(k), cur(k)) then bad += 1
      val notes = Vector(
        if exhausted then s"round budget ${limits.maxRounds} exhausted" else "",
        if overflowed then s"key budget ${limits.maxKeys} exhausted (unreached callees answered ⊤)" else "",
        if escaped then "certification reached a key the solve had not" else "",
        if bad > 0 then s"$bad keys are not post-fixed points" else "").filter(_.nonEmpty)
      Summaries(cur.toMap, bad == 0 && !escaped && !exhausted, notes.mkString("; "),
                rounds, updates, widened, topped)
  end Solver

  /** the entry environment of a routine body: parameters bound to the abstract arguments.  A path
   *  parameter with a known value is `paths` (so the shape transfers see the items); one with only a
   *  length bound is `opaque`, exactly as `SpatialTyping`'s own `Call` arm binds them. */
  private def entryEnv(r: Routine, args: Args): SpatialTyping.Env =
    val known = r.refs.indices.iterator.collect {
      case i if args.paths(i).value.isDefined => r.refs(i) -> args.paths(i).value.get }.toMap
    val opaque = r.refs.indices.iterator.collect {
      case i if args.paths(i).value.isEmpty => r.refs(i) -> args.paths(i).len }.toMap
    SpatialTyping.Env(spaces = r.mentions.zip(args.mentions).toMap, paths = known,
                      lenv = SpatialEnv(), opaque = opaque)

  // ================================================================================================
  // 3.  the body scan: local binder environments, call-site argument types, Call elimination
  // ================================================================================================

  final case class Site(routine: RoutinePtr, args: Args)

  /** Rewrites a routine body into a Call-FREE term by replacing every `Call` with a placeholder
   *  mention bound to that call's summary, and records each call site's abstract arguments.
   *
   *  The only binder logic duplicated here is what a call's ARGUMENTS need: `SpatialTyping.infer`
   *  binds the loop variables itself when it analyses the rewritten (Call-free) term.  An
   *  `Iteration`/`Fold` `rest` mention is bound to `weaken(type of TailsUnion(src))`: one head
   *  group's tail-set is a SUBSET of the union of all of them, and γ of a weakened type is downward
   *  closed under subsets, so that is a sound over-approximation of every group.  A `Fixpoint`'s
   *  recursive mention is bound to ⊤ — no claim. */
  private final class BodyScan(routines: PartialFunction[RoutinePtr, Routine],
                               resolve: Key => SpatialType):
    val bindings = mutable.LinkedHashMap.empty[SpaceMention, SpatialType]
    private val siteBuf = Vector.newBuilder[Site]
    private var n = 0
    def sites: Vector[Site] = siteBuf.result()

    private def fresh(): SpaceMention = { n += 1; SpaceMention(Reserved + "ph" + n) }

    def typeOf(e: Space, env: SpatialTyping.Env): SpatialType =
      keyType(SpatialTyping.infer(e, env.copy(spaces = env.spaces ++ bindings)))

    private def constPathOf(p: Path, env: SpatialTyping.Env): Option[PathValue] = p match
      case Path.Constant(pv) => Some(pv)
      case Path.Deref(pr) => if env.opaque.contains(pr) then None else env.paths.get(pr)
      case Path.Concat(l, r) =>
        for a <- constPathOf(l, env); b <- constPathOf(r, env) yield PathValue(a.items ++ b.items)
      case _ => None

    private def pathLenOf(p: Path, env: SpatialTyping.Env): LenBounds = p match
      case Path.Constant(pv) => LenBounds(pv.items.length, pv.items.length)
      case Path.Deref(pr) => env.opaque.get(pr) match
        case Some(k) => k
        case None => env.paths.get(pr) match
          case Some(pv) => LenBounds(pv.items.length, pv.items.length)
          case None => if pr.lengthHint >= 0 then LenBounds(pr.lengthHint, pr.lengthHint)
                       else LenBounds.unknown
      case Path.Concat(l, r) =>
        val (a, b) = (pathLenOf(l, env), pathLenOf(r, env))
        LenBounds(Ivl.add(a.lo, b.lo), Ivl.add(a.hi, b.hi))
      case _ => LenBounds.unknown

    private def pathArgOf(p: Path, env: SpatialTyping.Env): PathArg =
      constPathOf(p, env) match
        case Some(pv) => PathArg.known(pv)
        case None => PathArg.opaque(pathLenOf(p, env))

    private def iterEnv(env: SpatialTyping.Env, src: Space, sym: PathRef, rest: SpaceMention,
                        extra: Map[PathRef, LenBounds]): SpatialTyping.Env =
      val restT = weaken(typeOf(Space.TailsUnion(src), env))
      env.copy(spaces = if rest.s == "_" then env.spaces else env.spaces + (rest -> restT),
               paths = env.paths - sym,
               opaque = env.opaque ++ extra + (sym -> LenBounds(1, 1)))

    def rewritePath(p: Path, env: SpatialTyping.Env): Path = p match
      case Path.Concat(l, r) => Path.Concat(rewritePath(l, env), rewritePath(r, env))
      case Path.GroundedPP(q, f) => Path.GroundedPP(rewritePath(q, env), f)
      case Path.GroundedSP(q, f) => Path.GroundedSP(rewrite(q, env), f)
      case _ => p

    def rewrite(s: Space, env: SpatialTyping.Env): Space = s match
      case Space.Call(rp, refs, mentions) =>
        val margs = mentions.map(m => rewrite(m, env))
        val rargs = refs.map(p => rewritePath(p, env))
        val args = Args(margs.map(m => typeOf(m, env)), rargs.map(p => pathArgOf(p, env)))
        siteBuf += Site(rp, args)
        val t = if routines.isDefinedAt(rp) then resolve(Key(rp, args)) else SpatialType.top
        val ph = fresh()
        bindings(ph) = t
        Space.Mention(ph)
      case Space.Iteration(src, sym, rest, body) =>
        val s2 = rewrite(src, env)
        Space.Iteration(s2, sym, rest, rewrite(body, iterEnv(env, s2, sym, rest, Map.empty)))
      case Space.Fold(src, init, acc, sym, rest, body, upd) =>
        val s2 = rewrite(src, env)
        val benv = iterEnv(env, s2, sym, rest, Map(acc -> LenBounds.unknown))
        Space.Fold(s2, rewritePath(init, env), acc, sym, rest,
                   rewrite(body, benv), rewritePath(upd, benv))
      case Space.Fixpoint(init, recm, body) =>
        val i2 = rewrite(init, env)
        Space.Fixpoint(i2, recm,
                       rewrite(body, env.copy(spaces = env.spaces + (recm -> SpatialType.top))))
      case Space.Union(a, b) => Space.Union(rewrite(a, env), rewrite(b, env))
      case Space.Intersection(a, b) => Space.Intersection(rewrite(a, env), rewrite(b, env))
      case Space.Subtraction(a, b) => Space.Subtraction(rewrite(a, env), rewrite(b, env))
      case Space.Restriction(a, b) => Space.Restriction(rewrite(a, env), rewrite(b, env))
      case Space.Raffination(a, b) => Space.Raffination(rewrite(a, env), rewrite(b, env))
      case Space.Composition(a, b) => Space.Composition(rewrite(a, env), rewrite(b, env))
      case Space.Wrap(a, p) => Space.Wrap(rewrite(a, env), rewritePath(p, env))
      case Space.Unwrap(a, p) => Space.Unwrap(rewrite(a, env), rewritePath(p, env))
      case Space.TailsUnion(a) => Space.TailsUnion(rewrite(a, env))
      case Space.TailsIntersection(a) => Space.TailsIntersection(rewrite(a, env))
      case Space.Range(a, lo, hi) => Space.Range(rewrite(a, env), lo, hi)
      case Space.Singleton(p) => Space.Singleton(rewritePath(p, env))
      case Space.GroundedPS(p, f) => Space.GroundedPS(rewritePath(p, env), f)
      case Space.GroundedSS(a, f) => Space.GroundedSS(rewrite(a, env), f)
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => s
  end BodyScan

  // ================================================================================================
  // 4.  syntactic call inventory and name hygiene
  // ================================================================================================

  /** every `Call` node in a term, INCLUDING those nested inside path expressions (via
   *  `GroundedSP`), separated so a residual can be certified Call-free. */
  def callSites(s: Space): (Vector[Space.Call], Vector[Space.Call]) =
    val inSpace = Vector.newBuilder[Space.Call]
    val inPath = Vector.newBuilder[Space.Call]
    def gs(x: Space, viaPath: Boolean): Unit =
      x match
        case c @ Space.Call(_, refs, mentions) =>
          if viaPath then inPath += c else inSpace += c
          refs.foreach(gp(_, true)); mentions.foreach(gs(_, viaPath))
        case Space.Union(a, b) => gs(a, viaPath); gs(b, viaPath)
        case Space.Intersection(a, b) => gs(a, viaPath); gs(b, viaPath)
        case Space.Subtraction(a, b) => gs(a, viaPath); gs(b, viaPath)
        case Space.Restriction(a, b) => gs(a, viaPath); gs(b, viaPath)
        case Space.Raffination(a, b) => gs(a, viaPath); gs(b, viaPath)
        case Space.Composition(a, b) => gs(a, viaPath); gs(b, viaPath)
        case Space.Wrap(a, p) => gs(a, viaPath); gp(p, viaPath)
        case Space.Unwrap(a, p) => gs(a, viaPath); gp(p, viaPath)
        case Space.TailsUnion(a) => gs(a, viaPath)
        case Space.TailsIntersection(a) => gs(a, viaPath)
        case Space.Range(a, _, _) => gs(a, viaPath)
        case Space.Singleton(p) => gp(p, viaPath)
        case Space.GroundedPS(p, _) => gp(p, viaPath)
        case Space.GroundedSS(a, _) => gs(a, viaPath)
        case Space.Iteration(a, _, _, b) => gs(a, viaPath); gs(b, viaPath)
        case Space.Fixpoint(a, _, b) => gs(a, viaPath); gs(b, viaPath)
        case Space.Fold(a, i, _, _, _, b, u) => gs(a, viaPath); gp(i, viaPath); gs(b, viaPath); gp(u, viaPath)
        case Space.Empty | Space.Mention(_) | Space.Literal(_) => ()
    def gp(p: Path, viaPath: Boolean): Unit = p match
      case Path.Concat(l, r) => gp(l, viaPath); gp(r, viaPath)
      case Path.GroundedPP(q, _) => gp(q, viaPath)
      case Path.GroundedSP(q, _) => gs(q, true)
      case _ => ()
    gs(s, false)
    (inSpace.result(), inPath.result())

  /** is the term free of `Call` nodes anywhere (space positions and path positions alike)? */
  def isCallFree(s: Space): Boolean =
    val (a, b) = callSites(s); a.isEmpty && b.isEmpty

  /** every name the term mentions or binds — used to reject a body that already uses [[Reserved]] */
  private def usesReserved(s: Space): Boolean =
    var hit = false
    def chk(x: String): Unit = if x.startsWith(Reserved) then hit = true
    def gs(x: Space): Unit = x match
      case Space.Mention(m) => chk(m.s)
      case Space.Union(a, b) => gs(a); gs(b)
      case Space.Intersection(a, b) => gs(a); gs(b)
      case Space.Subtraction(a, b) => gs(a); gs(b)
      case Space.Restriction(a, b) => gs(a); gs(b)
      case Space.Raffination(a, b) => gs(a); gs(b)
      case Space.Composition(a, b) => gs(a); gs(b)
      case Space.Wrap(a, p) => gs(a); gp(p)
      case Space.Unwrap(a, p) => gs(a); gp(p)
      case Space.TailsUnion(a) => gs(a)
      case Space.TailsIntersection(a) => gs(a)
      case Space.Range(a, _, _) => gs(a)
      case Space.Singleton(p) => gp(p)
      case Space.GroundedPS(p, _) => gp(p)
      case Space.GroundedSS(a, _) => gs(a)
      case Space.Call(_, refs, mentions) => refs.foreach(gp); mentions.foreach(gs)
      case Space.Iteration(a, sym, rest, b) => chk(sym.s); chk(rest.s); gs(a); gs(b)
      case Space.Fixpoint(a, recm, b) => chk(recm.s); gs(a); gs(b)
      case Space.Fold(a, i, acc, sym, rest, b, u) =>
        chk(acc.s); chk(sym.s); chk(rest.s); gs(a); gp(i); gs(b); gp(u)
      case Space.Empty | Space.Literal(_) => ()
    def gp(p: Path): Unit = p match
      case Path.Deref(pr) => chk(pr.s)
      case Path.Concat(l, r) => gp(l); gp(r)
      case Path.GroundedPP(q, _) => gp(q)
      case Path.GroundedSP(q, _) => gs(q)
      case Path.Constant(_) => ()
    gs(s)
    hit

  /** HYGIENIC copy: every binder of `s` renamed to a globally fresh [[Reserved]] name, hints
   *  preserved, the throwaway binder `_` left alone.  Splicing an unrolled level substitutes the
   *  parameters by argument expressions that routinely mention a LOOP BINDER (`Mention(rest)`); done
   *  on a body whose own binders keep their names, that substitution is captured and silently wrong
   *  (traps.md #7).  Freshening first makes capture impossible. */
  def alphaFresh(s: Space, ctr: java.util.concurrent.atomic.AtomicInteger): Space =
    def newRef(pr: PathRef): PathRef =
      if pr.s == "_" then pr
      else
        val f = PathRef(Reserved + "p" + ctr.incrementAndGet())
        if pr.lengthHint >= 0 then f.known(pr.lengthHint) else f
    def newMention(m: SpaceMention): SpaceMention =
      if m.s == "_" then m
      else
        val f = SpaceMention(Reserved + "m" + ctr.incrementAndGet())
        if m.sizeHint >= 0 then f.known(m.sizeHint) else f
    def bindP(a: PathRef, b: PathRef): Map[PathRef, PathRef] = if a.s == "_" then Map.empty else Map(a -> b)
    def bindS(a: SpaceMention, b: SpaceMention): Map[SpaceMention, SpaceMention] =
      if a.s == "_" then Map.empty else Map(a -> b)
    def rp(p: Path, sm: Map[SpaceMention, SpaceMention], pm: Map[PathRef, PathRef]): Path = p match
      case Path.Deref(pr) => pm.get(pr).map(Path.Deref(_)).getOrElse(p)
      case Path.Constant(_) => p
      case Path.Concat(l, r) => Path.Concat(rp(l, sm, pm), rp(r, sm, pm))
      case Path.GroundedPP(q, f) => Path.GroundedPP(rp(q, sm, pm), f)
      case Path.GroundedSP(q, f) => Path.GroundedSP(rs(q, sm, pm), f)
    def rs(x: Space, sm: Map[SpaceMention, SpaceMention], pm: Map[PathRef, PathRef]): Space = x match
      case Space.Mention(m) => sm.get(m).map(Space.Mention(_)).getOrElse(x)
      case Space.Iteration(src, sym, rest, body) =>
        val sym2 = newRef(sym); val rest2 = newMention(rest)
        Space.Iteration(rs(src, sm, pm), sym2, rest2,
                        rs(body, sm ++ bindS(rest, rest2), pm ++ bindP(sym, sym2)))
      case Space.Fold(src, init, acc, sym, rest, body, upd) =>
        val acc2 = newRef(acc); val sym2 = newRef(sym); val rest2 = newMention(rest)
        val pm2 = pm ++ bindP(acc, acc2) ++ bindP(sym, sym2)
        val sm2 = sm ++ bindS(rest, rest2)
        Space.Fold(rs(src, sm, pm), rp(init, sm, pm), acc2, sym2, rest2,
                   rs(body, sm2, pm2), rp(upd, sm2, pm2))
      case Space.Fixpoint(init, recm, body) =>
        val recm2 = newMention(recm)
        Space.Fixpoint(rs(init, sm, pm), recm2, rs(body, sm ++ bindS(recm, recm2), pm))
      case Space.Union(a, b) => Space.Union(rs(a, sm, pm), rs(b, sm, pm))
      case Space.Intersection(a, b) => Space.Intersection(rs(a, sm, pm), rs(b, sm, pm))
      case Space.Subtraction(a, b) => Space.Subtraction(rs(a, sm, pm), rs(b, sm, pm))
      case Space.Restriction(a, b) => Space.Restriction(rs(a, sm, pm), rs(b, sm, pm))
      case Space.Raffination(a, b) => Space.Raffination(rs(a, sm, pm), rs(b, sm, pm))
      case Space.Composition(a, b) => Space.Composition(rs(a, sm, pm), rs(b, sm, pm))
      case Space.Wrap(a, p) => Space.Wrap(rs(a, sm, pm), rp(p, sm, pm))
      case Space.Unwrap(a, p) => Space.Unwrap(rs(a, sm, pm), rp(p, sm, pm))
      case Space.TailsUnion(a) => Space.TailsUnion(rs(a, sm, pm))
      case Space.TailsIntersection(a) => Space.TailsIntersection(rs(a, sm, pm))
      case Space.Range(a, lo, hi) => Space.Range(rs(a, sm, pm), lo, hi)
      case Space.Singleton(p) => Space.Singleton(rp(p, sm, pm))
      case Space.GroundedPS(p, f) => Space.GroundedPS(rp(p, sm, pm), f)
      case Space.GroundedSS(a, f) => Space.GroundedSS(rs(a, sm, pm), f)
      case Space.Call(rpn, refs, mentions) =>
        Space.Call(rpn, refs.map(rp(_, sm, pm)), mentions.map(rs(_, sm, pm)))
      case Space.Empty | Space.Literal(_) => x
    rs(s, Map.empty, Map.empty)

  // ================================================================================================
  // 5.  the decreasing measure — the exact structural condition
  // ================================================================================================

  /** THE STRUCTURAL WITNESS that a recursive argument drops at least one path item.  Every case is
   *  a length fact about the operator, not about the analysis:
   *   - `Tails`: `TailsUnion`/`TailsIntersection` remove exactly the head item (`sp_tails_shift`);
   *   - `Unwrap`: dropping a prefix of ≥ `items` items removes that many (`sp_unwrap_shift`);
   *   - `IterationRest`: a rest-set element is a source path minus its single head (`sp_iter_head_one`). */
  enum Decrease:
    case Tails(param: SpaceMention)
    case Unwrap(param: SpaceMention, items: Long)
    case IterationRest(param: SpaceMention, rest: SpaceMention)
    case Bottom
    def show: String = this match
      case Tails(m) => s"tails of a subset of S\"${m.s}\" (one item per call)"
      case Unwrap(m, k) => s"unwrap of a subset of S\"${m.s}\" by a path of ≥ $k items"
      case IterationRest(m, r) => s"the rest-set S\"${r.s}\" of an iteration over a subset of S\"${m.s}\""
      case Bottom => "the empty space"

  /** is `e` a SUBSET of `m`'s denotation by syntax alone?  `∩`, `∖`, `<|`, `\\|` and `Range` only
   *  ever delete paths, and a union of subsets is a subset — so none of these can lengthen a path.
   *  This is the "length-non-increasing" side condition of every case in [[decreaseOf]]. */
  def subsetOf(e: Space, m: SpaceMention): Boolean = e match
    case Space.Mention(x) => x == m
    case Space.Empty => true
    case Space.Literal(SpaceValue(ps)) => ps.isEmpty
    case Space.Restriction(x, _) => subsetOf(x, m)
    case Space.Raffination(x, _) => subsetOf(x, m)
    case Space.Subtraction(x, _) => subsetOf(x, m)
    case Space.Range(x, _, _) => subsetOf(x, m)
    case Space.Intersection(x, y) => subsetOf(x, m) || subsetOf(y, m)
    case Space.Union(x, y) => subsetOf(x, m) && subsetOf(y, m)
    case _ => false

  /** the structural decrease witness for the recursive argument `e` against parameter `m`, given the
   *  rest-binders in scope at the call (`rest ↦ the iteration/fold source`) and the item-length
   *  bounds of the path refs in scope.  `None` = no witness; the caller must then report `NoBound`. */
  def decreaseOf(e: Space, m: SpaceMention, rests: Map[SpaceMention, Space],
                 refLens: Map[PathRef, LenBounds]): Option[Decrease] = e match
    case Space.Empty => Some(Decrease.Bottom)
    case Space.TailsUnion(x) if subsetOf(x, m) => Some(Decrease.Tails(m))
    case Space.TailsIntersection(x) if subsetOf(x, m) => Some(Decrease.Tails(m))
    case Space.Unwrap(x, p) if subsetOf(x, m) =>
      val k = SpatialTypes.pathLen(p, SpatialEnv(paths = refLens))
      if k.lo >= 1 then Some(Decrease.Unwrap(m, k.lo)) else None
    case Space.Mention(r) if rests.get(r).exists(src => subsetOf(src, m)) =>
      Some(Decrease.IterationRest(m, r))
    case Space.Restriction(x, _) => decreaseOf(x, m, rests, refLens)
    case Space.Raffination(x, _) => decreaseOf(x, m, rests, refLens)
    case Space.Subtraction(x, _) => decreaseOf(x, m, rests, refLens)
    case Space.Range(x, _, _) => decreaseOf(x, m, rests, refLens)
    case Space.Intersection(x, y) =>
      decreaseOf(x, m, rests, refLens).orElse(decreaseOf(y, m, rests, refLens))
    case Space.Union(x, y) =>
      for a <- decreaseOf(x, m, rests, refLens); _ <- decreaseOf(y, m, rests, refLens) yield a
    case _ => None

  /** find the unique self-call and the binder context at its position */
  private def locateSelf(body: Space, self: RoutinePtr)
      : Option[(Space.Call, Map[SpaceMention, Space], Map[PathRef, LenBounds])] =
    var found: Option[(Space.Call, Map[SpaceMention, Space], Map[PathRef, LenBounds])] = None
    def gs(x: Space, rests: Map[SpaceMention, Space], refs: Map[PathRef, LenBounds]): Unit = x match
      case c @ Space.Call(rp, _, ms) =>
        if rp == self && found.isEmpty then found = Some((c, rests, refs))
        ms.foreach(gs(_, rests, refs))
      case Space.Union(a, b) => gs(a, rests, refs); gs(b, rests, refs)
      case Space.Intersection(a, b) => gs(a, rests, refs); gs(b, rests, refs)
      case Space.Subtraction(a, b) => gs(a, rests, refs); gs(b, rests, refs)
      case Space.Restriction(a, b) => gs(a, rests, refs); gs(b, rests, refs)
      case Space.Raffination(a, b) => gs(a, rests, refs); gs(b, rests, refs)
      case Space.Composition(a, b) => gs(a, rests, refs); gs(b, rests, refs)
      case Space.Wrap(a, _) => gs(a, rests, refs)
      case Space.Unwrap(a, _) => gs(a, rests, refs)
      case Space.TailsUnion(a) => gs(a, rests, refs)
      case Space.TailsIntersection(a) => gs(a, rests, refs)
      case Space.Range(a, _, _) => gs(a, rests, refs)
      case Space.GroundedSS(a, _) => gs(a, rests, refs)
      case Space.Iteration(src, sym, rest, b) =>
        gs(src, rests, refs)
        gs(b, if rest.s == "_" then rests else rests + (rest -> src), refs + (sym -> LenBounds(1, 1)))
      case Space.Fold(src, _, acc, sym, rest, b, _) =>
        gs(src, rests, refs)
        gs(b, if rest.s == "_" then rests else rests + (rest -> src),
           refs + (sym -> LenBounds(1, 1)) + (acc -> LenBounds.unknown))
      case Space.Fixpoint(init, _, b) => gs(init, rests, refs); gs(b, rests, refs)
      case _ => ()
    gs(body, Map.empty, Map.empty)
    found

  // ================================================================================================
  // 6.  the depth bound and the residual
  // ================================================================================================

  /** The CONDITIONAL artifact.  `precondition` is the input type the bound depended on; without it
   *  the residual is not equivalent to the original (review.md 5), so it travels with it and
   *  [[applicableTo]] decides an actual argument tuple against it. */
  final case class BoundedRecursion(routine: RoutinePtr,
                                    precondition: Map[SpaceMention, SpatialType],
                                    pathPrecondition: Map[PathRef, LenBounds],
                                    decreasingParam: SpaceMention,
                                    witness: Decrease,
                                    inputMaxLen: Long,
                                    measureBound: Long,
                                    maxCallDepth: Int,
                                    lenChain: Vector[Long],
                                    argChain: Vector[SpatialType],
                                    emptyLevelSummary: SpatialType,
                                    summary: SpatialType,
                                    residual: Routine,
                                    facts: Vector[Fact],
                                    summaries: Summaries):
    /** the residual contains no `Call` at all — checked, not assumed */
    def callFree: Boolean = isCallFree(residual.body)
    /** may this residual be used for these actual arguments?  Full γ-membership, never the weaker
     *  envelope check: admitting an argument outside the precondition installs a conditionally-valid
     *  body on an input that violates the condition. */
    def applicableTo(args: Map[SpaceMention, SpaceValue]): Boolean =
      precondition.forall((m, t) => args.get(m).exists(v => SpatialTyping.gammaMember(v, t)))
    /** the same artifact in the type system's own guarded-specialisation shape */
    def specialized: SpatialTyping.SpecializedRoutine =
      SpatialTyping.SpecializedRoutine(precondition, residual, facts)
    def show: String =
      s"${routine.s}: maxCallDepth=$maxCallDepth (measure bound ${measureBound}, input maxLen " +
      s"$inputMaxLen) via ${witness.show}; μ chain ${lenChain.mkString(" -> ")}; " +
      s"level-$maxCallDepth summary ⊥; residual ${if callFree then "Call-free" else "STILL HAS CALLS"}; " +
      s"summaries ${summaries.show}"

  enum DepthBound:
    case Bounded(result: BoundedRecursion)
    case NoBound(reason: String)
    def bounded: Option[BoundedRecursion] = this match
      case Bounded(r) => Some(r)
      case NoBound(_) => None
    /** why no bound was derived — `None` when one was */
    def noBoundReason: Option[String] = this match
      case Bounded(_) => None
      case NoBound(r) => Some(r)

  /** DERIVE the call-depth bound and residualise.  Returns `NoBound(reason)` — never a guess —
   *  whenever any of the checked conditions fails.
   *
   *  The conditions, in the order they are checked:
   *   1. the routine is in `routines`, and neither it nor the residual uses the [[Reserved]] prefix;
   *   2. the body contains EXACTLY ONE call to the routine itself, no call to any other routine, and
   *      no call inside a path expression (so the residual can be Call-free);
   *   3. every path argument of the self-call is passed through unchanged, and exactly one mention
   *      argument differs from its parameter — the CHANGING parameter, on which the measure runs;
   *   4. the declared input type bounds that parameter's maximum path length (`μ(a_0) = L ≠ ∞`),
   *      and `L + 1` is within the unrolling budget;
   *   5. the summaries solve to a CERTIFIED post-fixed point;
   *   6. at every level `μ` drops by ≥ 1 (M2) and the structural witness (M1) exists;
   *   7. some level `k ≤ L + 1` has a provably-empty summary. */
  def residualise(rp: RoutinePtr, routines: PartialFunction[RoutinePtr, Routine],
                  spaces: Map[SpaceMention, SpatialType] = Map.empty,
                  paths: Map[PathRef, LenBounds] = Map.empty,
                  limits: Limits = Limits()): DepthBound =
    import DepthBound.{Bounded, NoBound}
    routines.lift(rp) match
      case None => NoBound(s"routine ${rp.s} is not in the routine table")
      case Some(r) =>
        if usesReserved(r.body) then NoBound(s"the body of ${rp.s} uses the reserved name prefix $Reserved")
        else
          val (inSpace, inPath) = callSites(r.body)
          val selfs = inSpace.filter(_.r == rp)
          val others = inSpace.filterNot(_.r == rp)
          if inPath.nonEmpty then NoBound("a Call appears inside a path expression; the residual could not be Call-free")
          else if selfs.size != 1 then
            NoBound(s"expected exactly one self-recursive call in ${rp.s}, found ${selfs.size}")
          else if others.nonEmpty then
            NoBound(s"the body of ${rp.s} calls ${others.map(_.r.s).distinct.mkString(", ")}; " +
                    "residualising only the self-recursion would not be Call-free")
          else
            val call = selfs.head
            if call.refs.length != r.refs.length || call.mentions.length != r.mentions.length then
              NoBound("the self-call's arity does not match the routine's signature")
            else if r.refs.indices.exists(i => call.refs(i) != Path.Deref(r.refs(i))) then
              NoBound("the self-call does not pass its path arguments through unchanged")
            else
              val changing = r.mentions.indices.filter(i => call.mentions(i) != Space.Mention(r.mentions(i)))
              if changing.size != 1 then
                NoBound(s"expected exactly one changing mention argument, found ${changing.size}")
              else
                val ci = changing.head
                val param = r.mentions(ci)
                locateSelf(r.body, rp) match
                  case None => NoBound("could not locate the self-call")
                  case Some((_, rests, binderLens)) =>
                    // the declared path precondition is visible to M1 too: a routine path parameter
                    // typed "≥ 1 item" licenses the unwrap witness exactly as a `lengthHint` does
                    val refLens = paths ++ binderLens
                    decreaseOf(call.mentions(ci), param, rests, refLens) match
                      case None =>
                        NoBound(s"no structural decrease witness (M1) for the recursive argument of " +
                                s"S\"${param.s}\": ${safeShow(call.mentions(ci))}")
                      case Some(w) => withWitness(rp, r, call, ci, param, w, routines, spaces, paths, limits)

  private def withWitness(rp: RoutinePtr, r: Routine, call: Space.Call, ci: Int, param: SpaceMention,
                          w: Decrease, routines: PartialFunction[RoutinePtr, Routine],
                          spaces: Map[SpaceMention, SpatialType], paths: Map[PathRef, LenBounds],
                          limits: Limits): DepthBound =
    import DepthBound.{Bounded, NoBound}
    val a0 = Args(r.mentions.map(m => keyType(spaces.getOrElse(m, SpatialType.top))),
                  r.refs.map(pr => PathArg.opaque(paths.getOrElse(pr, LenBounds.unknown))))
    val t0 = a0.mentions(ci)
    if t0.isProvablyEmpty then
      NoBound(s"the declared input type for S\"${param.s}\" is the empty space; nothing to residualise")
    else
      val L = measure(t0)
      if L == LenBounds.INF then
        NoBound(s"the declared input type for S\"${param.s}\" does not bound the maximum path " +
                s"length (μ = ∞); no call-depth bound follows from the measure")
      else
        val measureBound = L + 1
        if measureBound > limits.maxUnroll then
          NoBound(s"the measure bound ${measureBound} exceeds the unrolling budget ${limits.maxUnroll}")
        else
          val sums = summarise(Key(rp, a0), routines, limits)
          if !sums.certified then
            NoBound(s"the summary table did not certify as a post-fixed point: ${sums.note}")
          else
            // ---- the abstract argument chain, checked for the numeric drop (M2) at every level ---
            def step(a: Args): Option[Args] =
              routines.lift(rp).flatMap { rr =>
                val env = entryEnv(rr, a)
                val sc = new BodyScan(routines, k => sums.at(k))
                sc.rewrite(rr.body, env)
                sc.sites.find(_.routine == rp).map(_.args)
              }
            val chain = mutable.ArrayBuffer(a0)
            val lens = mutable.ArrayBuffer(L)
            var k = -1
            var failure: Option[String] = None
            var j = 0
            while k < 0 && failure.isEmpty do
              val aj = chain(j)
              val sj = sums.at(Key(rp, aj))
              if sj.isProvablyEmpty then k = j
              else if j > measureBound then
                failure = Some(s"no level at or below the measure bound ${measureBound} has a " +
                               s"provably-empty summary (level $j summary ${sj.show})")
              else step(aj) match
                case None => failure = Some(s"the self-call disappeared from the body at level $j")
                case Some(nxt) =>
                  val prevT = aj.mentions(ci)
                  val nxtT = nxt.mentions(ci)
                  val (mp, mn) = (measure(prevT), measure(nxtT))
                  if prevT.isProvablyEmpty then
                    failure = Some(s"the base case (an empty argument) does not have a provably-empty " +
                                   s"summary: ${sj.show}")
                  else if !nxtT.isProvablyEmpty && mn > mp - 1 then
                    failure = Some(s"the recursive argument does not provably drop a path item at " +
                                   s"level $j: μ $mp -> $mn (M2 failed)")
                  else
                    chain += nxt; lens += mn; j += 1
            failure match
              case Some(why) => NoBound(why)
              case None =>
                val ctr = new java.util.concurrent.atomic.AtomicInteger(0)
                val body = unroll(r, rp, k, ctr)
                val residual = Routine(rp, r.refs, r.mentions, body)
                if !isCallFree(body) then
                  NoBound(s"the unrolled residual still contains a Call (internal invariant broken)")
                else
                  val summary = sums.at(Key(rp, a0))
                  Bounded(BoundedRecursion(
                    routine = rp,
                    precondition = r.mentions.iterator.filter(spaces.contains).map(m => m -> keyType(spaces(m))).toMap,
                    pathPrecondition = paths,
                    decreasingParam = param,
                    witness = w,
                    inputMaxLen = L,
                    measureBound = measureBound,
                    maxCallDepth = k,
                    lenChain = lens.toVector,
                    argChain = chain.toVector.map(_.mentions(ci)),
                    emptyLevelSummary = sums.at(Key(rp, chain(k))),
                    summary = summary,
                    residual = residual,
                    facts = Fact.from(summary),
                    summaries = sums))

  /** unroll `k` specialised levels; the level-`k` call becomes `Empty` (its summary is ⊥) */
  private def unroll(r: Routine, self: RoutinePtr, k: Int,
                     ctr: java.util.concurrent.atomic.AtomicInteger): Space =
    def level(j: Int): Space =
      if j >= k then Space.Empty
      else
        val inner = level(j + 1)
        subs(r.body)(spost = {
          case Space.Call(`self`, refs, mentions) => splice(inner, r, refs, mentions, ctr)
        })
    level(0)

  /** substitute a routine's parameters by the call's argument expressions, hygienically */
  private def splice(u: Space, r: Routine, refs: Vector[Path], mentions: Vector[Space],
                     ctr: java.util.concurrent.atomic.AtomicInteger): Space =
    val fresh = alphaFresh(u, ctr)
    val mmap = r.mentions.zip(mentions).toMap
    val pmap = r.refs.zip(refs).toMap
    subs(fresh)(spost = { case Space.Mention(m) if mmap.contains(m) => mmap(m) },
                ppost = { case Path.Deref(pr) if pmap.contains(pr) => pmap(pr) })

  private def safeShow(s: Space): String =
    try s.show.replace('\n', ' ').take(160) catch case _: Throwable => s.toString.take(160)

  // ================================================================================================
  // 7.  input-type annotations
  // ================================================================================================

  /** THE ANNOTATION the depth bound is derived from: "every path has between `lo` and `hi` items,
   *  any number of them".  The shape component claims nothing (⊤); the histogram carries the length
   *  window, which is what `μ` reads.  γ = the spaces whose every path has a length in `[lo, hi]`. */
  def lengthAnnotation(lo: Long, hi: Long): SpatialType =
    if hi < lo then SpatialType.empty
    else SpatialType(Shape.top, SpaceType.closed((lo to hi).map(l => l -> Ivl.unknown)*))

  /** the same, capped at `n` paths */
  def lengthAnnotation(lo: Long, hi: Long, maxPaths: Long): SpatialType =
    if hi < lo || maxPaths <= 0 then SpatialType.empty
    else SpatialType(Shape.top, SpaceType.closed((lo to hi).map(l => l -> Ivl(0, maxPaths))*))
end SpatialRecursion
