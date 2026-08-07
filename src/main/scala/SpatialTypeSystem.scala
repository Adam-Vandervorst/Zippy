package morkl

/** THE SPATIAL TYPE — a reduced product of the SHAPE (a bounded abstract trie, [[Shape]]) and the
 *  LENGTH-INDEXED COUNTS ([[SpaceType]]), analysed together and reduced against each other.
 *
 *  Why a product rather than either alone: the histogram knows how many paths of each length a
 *  space holds but cannot tell `{a.0,a.1,a.2,a.3}` from `{a.0,b.0,c.0,d.0}`; the trie knows the
 *  heads and prefixes but is capped in depth and width, so beyond the cap the histogram is the only
 *  thing still saying anything.  Each component bounds the other — the shape's head count bounds an
 *  iteration's group count, the shape's implied size and lengths meet the histogram's — and
 *  [[SpatialType.reduce]] applies that in both directions after every transfer.
 *
 *  Facts are exposed as VALIDATED PROPOSITIONS ([[Fact]]), never as raw numbers: `len.lo >= 3` on
 *  the empty space is `INF >= 3`, which would "prove" three extractable items from nothing.  Each
 *  proposition encodes the conjunction its meaning requires, once. */
final case class SpatialType(shape: Shape, lens: SpaceType):
  import Lower.{LenBounds, SizeBounds}
  def size: SizeBounds =
    val a = lens.size; val b = shape.size
    val lo = a.lo max b.lo
    SizeBounds(lo, a.loHeaded max (if shape.eps.mayBe then Ivl.relu(b.lo - 1) else b.lo), a.hi min b.hi)
  def len: LenBounds =
    val a = lens.len; val b = shape.lens
    if a.isEmpty || b.isEmpty then LenBounds.empty else LenBounds(a.lo max b.lo, a.hi min b.hi)
  def isProvablyEmpty: Boolean = lens.isProvablyEmpty || shape.definitelyEmpty || size.hi == 0
  /** the DISTINCT-head count — the group count of an iteration, invisible to the histogram */
  def headCount: Ivl = Ivl(shape.headCount.lo, shape.headCount.hi min size.hi)
  def show: String = s"shape ${shape.show}  lens ${lens.show}"

object SpatialType:
  import Lower.{LenBounds, SizeBounds}
  val top: SpatialType = SpatialType(Shape.top, SpaceType.unknown)
  val empty: SpatialType = SpatialType(Shape.empty, SpaceType.empty)
  def of(v: SpaceValue): SpatialType = SpatialType(Shape.of(v), SpaceType.of(v))

  /** REDUCE the two components against each other: whatever one proves constrains the other. */
  def reduce(t: SpatialType): SpatialType =
    if t.shape.definitelyEmpty || t.lens.isProvablyEmpty then empty
    else
      // the shape's implied total caps every length class (no class exceeds the whole space)
      val cap = t.shape.size.hi
      val lens2 =
        if cap == Ivl.INF then t.lens
        else SpaceType(scala.collection.immutable.SortedMap.from(
                         t.lens.byLen.map((l, c) => l -> Ivl(c.lo, c.hi min cap))),
                       Ivl(t.lens.rest.lo, t.lens.rest.hi min cap), t.lens.restLens)
      SpatialType(t.shape, lens2)

/** A validated proposition about a space — the safe API an optimizer should consume.  Each case
 *  bundles the conjunction its meaning requires, so a client cannot read `len.lo` off an empty
 *  space and conclude something about paths that do not exist. */
enum Fact:
  case DefinitelyEmpty
  case DefinitelyNonEmpty
  case MinimumCardinality(k: Long)          // at least k paths, AND the space is non-empty
  case MaximumCardinality(k: Long)
  case AllPathsHaveAtLeast(items: Long)     // every path has ≥ items items, AND ≥1 path exists
  case MaximumPathLength(items: Long)
  case ExactHeadSet(heads: Set[PathItem])   // the head set is EXACTLY this: closed AND all must
  case HeadSetWithin(heads: Set[PathItem])  // the head set is a subset of this (closed, some may)
  case MinimumHeadCount(k: Long)            // ≥ k distinct heads, so an iteration definitely runs
  case MaximumHeadCount(k: Long)
  case PrefixAbsent(prefix: List[PathItem]) // no path starts with this prefix
  def show: String = toString

object Fact:
  /** everything this type licenses, each with its precondition already discharged */
  def from(t: SpatialType): Vector[Fact] =
    val out = Vector.newBuilder[Fact]
    val sz = t.size; val ln = t.len
    if t.isProvablyEmpty then out += Fact.DefinitelyEmpty
    else
      if sz.lo >= 1 then out += Fact.DefinitelyNonEmpty
      if sz.lo >= 1 then out += Fact.MinimumCardinality(sz.lo)
      if sz.hi != Ivl.INF then out += Fact.MaximumCardinality(sz.hi)
      // a length claim is only meaningful once the space is known non-empty
      if sz.lo >= 1 && !ln.isEmpty && ln.lo >= 1 then out += Fact.AllPathsHaveAtLeast(ln.lo)
      if !ln.isEmpty && ln.hi != LenBounds.INF then out += Fact.MaximumPathLength(ln.hi)
      if t.shape.headsClosed then
        val live = t.shape.heads.keySet.filter(h => t.shape.heads(h).possiblyNonEmpty)
        // "EXACTLY these heads" needs every one of them to be MUST-present; otherwise the closed
        // head set only bounds the head set from above.
        if live.forall(h => t.shape.heads(h).definitelyNonEmpty) then out += Fact.ExactHeadSet(live)
        else out += Fact.HeadSetWithin(live)
      val hc = t.headCount
      if hc.lo >= 1 then out += Fact.MinimumHeadCount(hc.lo)
      if hc.hi != Ivl.INF then out += Fact.MaximumHeadCount(hc.hi)
    out.result()
  private val LenBounds = Lower.LenBounds

/** The analysis over the reduced product.  Same discipline as [[SpatialTypes]]: no evaluation, only
 *  the term's syntax, the declared input types, and the transfers.
 *
 *  The shape transfers are documented, with their may/must justification, in the table at the top of
 *  SpatialShape.scala.  Real transfers: Empty, Literal, Singleton, Union, Intersection, Subtraction,
 *  Restriction, Raffination, Wrap, Unwrap, TailsUnion, TailsIntersection, Composition, Range,
 *  Iteration, Fold, Fixpoint, Call, Mention — including the non-constant-path arms of `Singleton`,
 *  `Wrap` and `Unwrap`, which stay informative as long as the path's LENGTH is bounded.
 *  Degraded to ⊤, and only these: `GroundedPS`/`GroundedSS` (an arbitrary Scala function), a `Call`
 *  whose routine is absent from the table or already on the call stack, an `Unwrap` by a path of
 *  unbounded length, a `Mention` with no declared type, a `Fixpoint` with no verified post-fixpoint,
 *  and anything reached after the node budget runs out. */
object SpatialTyping:
  import Lower.{LenBounds, SizeBounds}

  /** input types for the shape domain: shapes for mentions, KNOWN VALUES for path refs (an
   *  iteration binds its head symbol to a concrete item, which is what lets the body distinguish
   *  one head from another).  `opaque` are refs that ARE bound but whose value is unknown — an
   *  iteration head of an untracked group, a fold accumulator — carrying only a length bound.  They
   *  must shadow any outer binding, or a body would read a stale constant. */
  final case class Env(spaces: Map[SpaceMention, SpatialType] = Map.empty,
                       paths: Map[PathRef, PathValue] = Map.empty,
                       lenv: SpatialEnv = SpatialEnv(),
                       opaque: Map[PathRef, Lower.LenBounds] = Map.empty):
    def lengths: SpatialEnv = lenv.copy(spaces = spaces.view.mapValues(_.lens).toMap,
                                        paths = paths.view.mapValues(p => LenBounds(p.items.length, p.items.length)).toMap
                                                  ++ lenv.paths ++ opaque)

  /** the analysis is linear in the term, but `Iteration`/`Fold` fork per head group and `Fixpoint`
   *  iterates, so the product is bounded by an explicit node budget rather than by hope.  Running
   *  out yields ⊤, which is always sound. */
  private final class Budget(var left: Int):
    def spend(): Boolean = { left -= 1; left > 0 }

  def infer(s: Space): SpatialType = infer(s, Env())
  /** Analyse the shape ONCE over the term, analyse the length/count component once, and reduce the
   *  two at the root.  An earlier draft re-ran the whole histogram analysis at every node, which is
   *  quadratic and overflowed the stack on corpus terms. */
  def infer(s: Space, env: Env): SpatialType =
    val b = new Budget(200000)
    SpatialType.reduce(SpatialType(goShape(s, env, 0)(using b), SpatialTypes.infer(s, env.lengths)))

  /** just the shape component (used by the differential operator matrix) */
  def shapeOf(s: Space, env: Env = Env()): Shape = goShape(s, env, 0)(using new Budget(200000))

  /** the constant value of a path expression, when the term and the env determine it */
  private def constPath(p: Path, env: Env): Option[List[PathItem]] = p match
    case Path.Constant(pv) => Some(pv.items)
    case Path.Deref(pr) => if env.opaque.contains(pr) then None else env.paths.get(pr).map(_.items)
    case Path.Concat(l, r) => for a <- constPath(l, env); b <- constPath(r, env) yield a ++ b
    case _ => None

  /** the ITEM-length interval of a path expression under the shape env.  Annotations
   *  (`PathRef.lengthHint`) and declared entries are trusted exactly as `SpatialTypes.pathLen`
   *  trusts them — see docs/design_spatial_lattice.md §0 for why that is a legitimate source. */
  private def pathLenOf(p: Path, env: Env): LenBounds = p match
    case Path.Constant(pv) => LenBounds(pv.items.length, pv.items.length)
    case Path.Deref(pr) => env.opaque.get(pr) match
      case Some(k) => k
      case None => env.paths.get(pr) match
        case Some(pv) => LenBounds(pv.items.length, pv.items.length)
        case None => env.lenv.paths.getOrElse(pr,
          if pr.lengthHint >= 0 then LenBounds(pr.lengthHint, pr.lengthHint) else LenBounds.unknown)
    case Path.Concat(l, r) =>
      val (a, b) = (pathLenOf(l, env), pathLenOf(r, env))
      LenBounds(Ivl.add(a.lo, b.lo), Ivl.add(a.hi, b.hi))
    case _ => LenBounds.unknown

  private def goShape(s: Space, env: Env, depth: Int)(using b: Budget): Shape =
    if depth > 48 || !b.spend() then Shape.top
    else
      def rec(x: Space) = goShape(x, env, depth + 1)
      s match
        case Space.Empty => Shape.empty
        case Space.Literal(v) => Shape.of(v)
        case Space.Singleton(p) => constPath(p, env) match
          case Some(items) => Shape.ofPath(PathValue(items))
          case None => Shape.oneUnknownPath(pathLenOf(p, env))   // exactly ONE path, content unknown
        case Space.Union(a, bb) => Shape.union(rec(a), rec(bb))
        case Space.Intersection(a, bb) => Shape.inter(rec(a), rec(bb))
        case Space.Subtraction(a, bb) => Shape.sub(rec(a), rec(bb))
        case Space.Restriction(a, bb) => Shape.restrict(rec(a), rec(bb))
        // x \| y = x ∖ (x <| y).  Sound because `restrict`'s must under-approximates the true
        // restriction (so subtracting it never removes a member that survives) and its may
        // over-approximates it (so the must that survives is a genuine must).
        case Space.Raffination(a, bb) => val x = rec(a); Shape.sub(x, Shape.restrict(x, rec(bb)))
        case Space.Wrap(a, p) => constPath(p, env) match
          case Some(items) => Shape.wrap(items, rec(a))
          case None => Shape.wrapUnknown(pathLenOf(p, env), rec(a))
        case Space.Unwrap(a, p) => constPath(p, env) match
          case Some(items) => Shape.unwrap(items, rec(a))   // proves absent prefixes
          case None => Shape.unwrapUnknown(pathLenOf(p, env), rec(a))
        case Space.TailsUnion(a) => Shape.tailsUnion(rec(a))
        case Space.TailsIntersection(a) => Shape.tailsInter(rec(a))
        case Space.Composition(a, bb) => Shape.comp(rec(a), rec(bb))
        case Space.Mention(m) => env.spaces.get(m).map(_.shape).getOrElse(Shape.top)

        case Space.Range(x, lo, hi) =>
          val src = rec(x)
          val sz = src.size
          val whole = (lo == 0 && hi == 0) ||
            (sz.lo == sz.hi && sz.hi != Ivl.INF && sz.hi <= Int.MaxValue &&
              RangeBounds.normalize(sz.hi.toInt, lo, hi) == (0, sz.hi.toInt))
          Shape.range(src, windowWidth(sz, lo, hi), whole)

        case Space.Iteration(src, sym, rest, body) =>
          // THE shape payoff: the group count is the number of DISTINCT HEADS, not the path count,
          // and each group is analysed with its head bound to that item and `rest` bound to that
          // head's tail-set.  `{a.0,a.1,a.2,a.3}` has ONE group and `{a.0,b.0,c.0,d.0}` has FOUR —
          // indistinguishable to a length histogram.
          groupUnion(rec(src), env, sym, rest, body, depth, Map.empty)

        case Space.Fold(src, _, acc, sym, rest, body, _) =>
          // the same head-group union, but the ACCUMULATOR is opaque: its value depends on the
          // group order and on `update`, neither of which this domain models.  A body that does not
          // read the accumulator therefore keeps full precision, and one that does degrades exactly
          // where it reads it.  The accumulator's own contribution to the RESULT is nil — `Fold`
          // returns the union of the bodies, not the accumulator.
          groupUnion(rec(src), env, sym, rest, body, depth, Map(acc -> LenBounds.unknown))

        case Space.Fixpoint(init, recm, body) => fixpoint(init, recm, body, env, depth)

        case Space.Call(rp, refs, mentions) =>
          val table = env.lenv.routines
          if table.isDefinedAt(rp) && !env.lenv.active(rp) then
            val Routine(_, refns, mentionns, cbody) = table(rp)
            // INTERPROCEDURAL: a routine body denotes a function of its parameters, so analysing it
            // with the parameters bound to the ARGUMENT shapes is sound, must channels included.
            // The callee scope starts empty — inheriting the caller's bindings would let a body read
            // a mention it does not have.
            val argShapes = mentionns.zip(mentions.map(m => SpatialType(rec(m), SpaceType.unknown))).toMap
            val argPathsAll = refns.zip(refs.map(p => constPath(p, env) -> pathLenOf(p, env)))
            val known = argPathsAll.collect { case (n, (Some(items), _)) => n -> PathValue(items) }.toMap
            val opaque = argPathsAll.collect { case (n, (None, k)) => n -> k }.toMap
            val callee = Env(spaces = argShapes, paths = known, opaque = opaque,
                             lenv = env.lenv.copy(spaces = Map.empty, paths = Map.empty,
                                                  active = env.lenv.active + rp))
            goShape(cbody, callee, depth + 1)
          else Shape.top

        // an arbitrary Scala function: NOTHING is claimed
        case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => Shape.top

  /** the head-group union shared by `Iteration` and `Fold`.  A group whose head is only MAY-present
   *  need not run, so its body cannot contribute must information; a MUST-present head's group DOES
   *  run and contributes fully.  An open head set adds ONE extra weakened body, analysed with the
   *  head symbol opaque (length 1 — `sp_iter_head_one`) and `rest` bound to the weakened
   *  `otherTail`; without that arm the whole transfer had to degrade to ⊤. */
  private def groupUnion(x: Shape, env: Env, sym: PathRef, rest: SpaceMention, body: Space,
                         depth: Int, extraOpaque: Map[PathRef, LenBounds])(using b: Budget): Shape =
    if x.definitelyEmpty || x.headCount.hi == 0 then Shape.empty
    else
      def bind(head: Option[PathItem], tail: Shape): Env =
        val base = env.copy(spaces = env.spaces + (rest -> SpatialType(tail, SpaceType.unknown)),
                            opaque = env.opaque ++ extraOpaque)
        head match
          case Some(h) => base.copy(paths = base.paths + (sym -> PathValue(List(h))),
                                    opaque = base.opaque - sym)
          case None => base.copy(paths = base.paths - sym,
                                 opaque = base.opaque + (sym -> LenBounds(1, 1)))
      val parts = Vector.newBuilder[Shape]
      for (h, tail) <- x.heads.toVector if tail.possiblyNonEmpty do
        val bs = goShape(body, bind(Some(h), tail), depth + 1)
        parts += (if tail.definitelyNonEmpty then bs else Shape.weaken(bs))
      if x.others.hi > 0 then
        val ot = Shape.weaken(x.otherTail.getOrElse(Shape.top))
        val bs = goShape(body, bind(None, ot), depth + 1)
        // there may be up to `others.hi` untracked groups, and the result is the union of ALL of
        // them.  One body shape bounds ONE group; unioning an unknown number of sets each admitted
        // by it is only sound once the count channels are opened (`openCounts`).  Adding the arm
        // once, weakened, was a soundness bug — found by the nested operator matrix on
        // `Fold(GroundedSS(…), …, Wrap(rest, acc), …)`, where two head groups each produced one head
        // and the transfer claimed at most one.
        parts += (if x.others.hi <= 1 then Shape.weaken(bs) else Shape.openCounts(bs))
      val ps = parts.result()
      if ps.isEmpty then Shape.empty else ps.reduce((p, q) => Shape.union(p, q))

  /** FIXPOINT — Kleene iteration over shapes.
   *
   *  ==THE CONCRETE OPERATOR (MORKL.scala:235)==
   *  {{{ cur₀ = init;  cur_{k+1} = F(cur_k);  acc₀ = cur₀;  acc_{k+1} = acc_k ∪ cur_{k+1} }}}
   *  and the RESULT is `acc`, while the recursive mention is bound to `cur` — the LAST iterate, not
   *  the accumulation.  Two distinct obligations follow, and conflating them was a real unsoundness:
   *
   *  (1) EVERY ITERATE must be admitted by one candidate `c`.  That needs `c` to be an upper bound in
   *      the ORDER: `init ⊑ c` and `F#(c) ⊑ c`.  The previous version ascended with [[Shape.union]],
   *      which is the transfer for the set operation `A ∪ B` — it keeps the left operand's MUST
   *      claims (sound for a union, since `A ∪ B ⊇ A`) and ADDS the untracked-head counts.  Neither
   *      holds for a value drawn from one side, so `union` is not a join and the chain claimed musts
   *      no single iterate has.  Witness (delta-debugged from 71 raw cases):
   *      {{{ Singleton("c.b.b").fix(k){TailsIntersection(k)}
   *          eval    = {b, b.b, c.b.b, ε}
   *          claimed = shape {b·{b·{ε?}}, c·{b·{b·{ε!}}}}  —  eps = No, so ε was PROVED absent }}}
   *      The chain now ascends with [[Shape.lub]] and every iterate is kept MAY-ONLY
   *      ([[Shape.weaken]]).  May-only is what makes the whole argument close: for a may-only `c`,
   *      `γ_may(c) = γ(c)`, so [[Shape.leq]] — which is a γ_may order and ignores must channels — is
   *      exactly the right certificate, while the body is still analysed by the ordinary transfers in
   *      the STRONG reading they are sound in.  A must-consuming transfer (`sub`, `tailsInter`,
   *      raffination) is NOT sound when its input is read may-only, so this direction is the only one
   *      available; see the KNOWN-OPEN note in build.log.
   *
   *  (2) THE RESULT is an unbounded UNION of iterates, and `γ(c)` is not union-closed: `{a}` and
   *      `{b}` can both be in `γ({+[0,1] more})` while `{a,b}` is not.  What survives an arbitrary
   *      union of members of `γ(c)` is exactly [[Shape.openCounts]] — ε stays absent if it was absent
   *      in every iterate (union-closed), a CLOSED head set stays closed (union-closed), an open one
   *      loses its count, and the per-head summaries recurse.  So the accumulation is bounded by
   *      `openCounts(c)`.
   *
   *  MUST comes from `init` ALONE — `acc ⊇ eval(init)` always, and nothing else is guaranteed (the
   *  body may contribute nothing) — hence the final `union(i0, openCounts(c))`, where `union` is
   *  legitimately the set-union transfer this time. */
  private def fixpoint(init: Space, recm: SpaceMention, body: Space, env: Env, depth: Int)
                      (using b: Budget): Shape =
    val i0 = goShape(init, env, depth + 1)
    val w0 = Shape.weaken(i0)
    def step(t: Shape): Shape =
      Shape.weaken(goShape(body, env.copy(spaces = env.spaces + (recm -> SpatialType(t, SpaceType.unknown))),
                           depth + 1))
    var t = w0
    var k = 0
    var ok = false
    while k < 8 && !ok do
      val j = Shape.lub(t, step(t))
      if Shape.leq(j, t) then ok = true
      else { t = if k >= 4 then Shape.widenShape(j) else j; k += 1 }
    // the certificate, re-checked on the accepted candidate; widen once and retry if it fails
    def certified(c: Shape): Boolean = Shape.leq(step(c), c) && Shape.leq(w0, c)
    val cand = if ok && certified(t) then Some(t)
               else { val w = Shape.widenShape(t); if certified(w) then Some(w) else None }
    cand match
      case Some(c) => Shape.union(i0, Shape.openCounts(c))
      case None => Shape.union(i0, Shape.top)   // no certified post-fixpoint ⇒ ⊤ for the accumulation
    end match

  /** an upper bound on how many paths a `Range(_, start, end)` window keeps, from the source's SHAPE
   *  size and the static arithmetic of [[RangeBounds.normalize]].  Windows whose width depends on the
   *  (unknown) source size fall back to that size. */
  private def windowWidth(src: Ivl, start: Int, end: Int): Long =
    val static: Long =
      if start == 0 && end == 0 then Ivl.INF
      else if end > 0 && start > 0 then Ivl.relu(end.toLong - start.toLong)
      else if end > 0 && start == 0 then end.toLong
      else if end < 0 && start < 0 then Ivl.relu(end.toLong - start.toLong)
      else if end == 0 && start < 0 then -start.toLong
      else Ivl.INF
    static min src.hi

  // ---- the consumer-facing entry points ---------------------------------------------------------
  /** every validated proposition the analysis licenses about `s` under `env` */
  def facts(s: Space, env: Env = Env()): Vector[Fact] = Fact.from(infer(s, env))

  /** A specialisation carries its PRECONDITION as data.  `eliminateIn` used to hand back a bare
   *  `Routine` with the same name, so nothing stopped a caller installing a conditionally-valid
   *  body as a general replacement (review.md 5).  A `SpecializedRoutine` cannot be mistaken for
   *  one: the environment it assumed is attached, and [[satisfies]] decides an actual input against
   *  it, which is what a guarded dispatcher needs. */
  final case class SpecializedRoutine(precondition: Map[SpaceMention, SpatialType],
                                      residual: Routine, facts: Vector[Fact]):
    /** may this specialisation be used for these actual arguments?  Decided with the EXACT predicate
     *  [[gammaMember]], not the weaker [[satisfies]] envelope: a dispatcher that admits an argument
     *  outside the precondition installs a conditionally-valid body on an input that violates the
     *  condition, which is the failure review.md 5 is about. */
    def applicableTo(args: Map[SpaceMention, SpaceValue]): Boolean =
      precondition.forall((m, t) => args.get(m).exists(v => SpatialTyping.gammaMember(v, t)))

  /** does a concrete space satisfy an abstract type?  (the missing `SpaceValue satisfies SpaceType`
   *  operation a runtime dispatcher would be built from)
   *
   *  The SHAPE half is exact — it is full γ-membership ([[Shape.contains]]).  The HISTOGRAM half is
   *  an ENVELOPE check: it verifies every class the value actually populates plus the totals, but it
   *  does not verify a per-class LOWER bound for a class the value leaves empty.  That gap is real
   *  and is exhibited by `SpatialLawCheck`; [[gammaMember]] is the version without it, and it is
   *  what the corpus soundness gate uses. */
  def satisfies(v: SpaceValue, t: SpatialType): Boolean =
    val n = v.paths.size.toLong
    val sz = t.size
    val byLen = v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap
    sz.lo <= n && n <= sz.hi &&
      byLen.forall((l, c) => { val i = t.lens.at(l); i.lo <= c && c <= i.hi }) &&
      byLen.keys.forall(l => { val b = t.len; !b.isEmpty && b.lo <= l && l <= b.hi }) &&
      Shape.contains(t.shape, v)

  /** FULL γ-membership on the reduced product: `Shape.contains` on the shape (all four channels) and
   *  the representation invariant of the histogram (every tracked class brackets the real count,
   *  every untracked length sits inside the spill window, and the spill total is in `rest`).  This
   *  is the predicate the corpus gate asserts; it is equivalent to `SpatialGamma.gamma` and is
   *  duplicated here so this file's gate does not depend on a file it does not own. */
  def gammaMember(v: SpaceValue, t: SpatialType): Boolean =
    Shape.contains(t.shape, v) && histogramMember(v, t.lens) && {
      val n = v.paths.size.toLong; val sz = t.size
      sz.lo <= n && n <= sz.hi
    } && {
      val b = t.len
      v.paths.forall(p => !b.isEmpty && b.lo <= p.items.length && p.items.length <= b.hi)
    }

  private def histogramMember(v: SpaceValue, t: SpaceType): Boolean =
    val cnt: Map[Long, Long] = v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap
    val trackedOk = t.byLen.forall { (l, c) => val k = cnt.getOrElse(l, 0L); c.lo <= k && k <= c.hi }
    if !trackedOk then false
    else
      val residual = cnt.filter((l, _) => !t.byLen.contains(l))
      val lensOk = residual.forall { (l, k) =>
        k == 0L || (t.rest.hi > 0 && !t.restLens.isEmpty && t.restLens.lo <= l && l <= t.restLens.hi) }
      var tot = 0L
      for (_, k) <- residual do tot = Ivl.add(tot, k)
      lensOk && t.rest.lo <= tot && tot <= t.rest.hi
end SpatialTyping
