package morkl

/** SPATIAL TYPES — abstract interpretation of a Space as a LENGTH-INDEXED count domain, from
 *  input types to an output type.  This is the unifying tier above the two projections:
 *
 *    - [[SpaceType.size]] (sum the per-length count intervals) is a size bound — the domain of
 *      `Lower.sizeBounds` / `SizeZ3`;
 *    - [[SpaceType.len]] (the support hull) is a path-length bound — the domain of
 *      `Lower.lenBounds` / `LenZ3`.
 *
 *  Keeping counts PER LENGTH is what makes both sharper than either alone: a restriction by a
 *  length-3 prefix set annihilates the length-2 paths (a path cannot start with a longer prefix)
 *  while leaving longer classes intact, and `TailsUnion` then shifts the surviving classes down
 *  by exactly one item.  It is also what makes the `s || g` control-flow derivation come out
 *  exactly (see `SpatialTypeCheck`), and it supersedes the partial `otypes`/`itypes` experiment
 *  with a total, sound analysis.
 *
 *  Soundness statement: for `t = SpatialTypes.infer(s, env)` and any binding of the free
 *  mentions/refs consistent with `env`,
 *
 *      ∀ L: t.at(L).lo ≤ |{p ∈ eval(s) : |p| = L}| ≤ t.at(L).hi
 *
 *  — the count of paths of each length is bracketed, hence so are the size and length
 *  projections.  Unknowns (free mention with no env entry, Call, Grounded) widen to "any number
 *  of paths at any length"; every transfer below is a true cardinality fact about the operator.
 *
 *  Representation: counts for the lengths in `byLen`, plus a single `rest` bucket covering ALL
 *  other lengths (those in `restLens`).  `rest == Ivl.zero` therefore means "the support is
 *  exactly `byLen`'s keys" — the closed case that carries the most information.  Widening keeps
 *  `byLen` under [[SpatialTypes.MaxClasses]] entries and lengths under [[SpatialTypes.MaxLen]]
 *  by spilling classes into `rest`, which only ever loosens. */
final case class Ivl(lo: Long, hi: Long):
  def isZero: Boolean = hi == 0
  def show: String = s"[$lo, ${if hi == Ivl.INF then "inf" else hi}]"
object Ivl:
  val INF: Long = Long.MaxValue
  val zero: Ivl = Ivl(0, 0)
  val unknown: Ivl = Ivl(0, INF)
  def add(a: Long, b: Long): Long = if a == INF || b == INF then INF else { val s = a + b; if s < 0 then INF else s }
  def mul(a: Long, b: Long): Long = if a == 0 || b == 0 then 0 else if a == INF || b == INF || a > INF / b then INF else a * b
  def relu(a: Long): Long = if a < 0 then 0 else a

/** A length-indexed count abstraction of a set of paths (see [[SpatialTypes]]). */
final case class SpaceType(byLen: scala.collection.immutable.SortedMap[Long, Ivl], rest: Ivl, restLens: Lower.LenBounds):
  import Lower.{LenBounds, SizeBounds}

  /** count interval for paths of exactly length `l` */
  def at(l: Long): Ivl = byLen.getOrElse(l, if rest.hi > 0 && !restLens.isEmpty && restLens.lo <= l && l <= restLens.hi then Ivl(0, rest.hi) else Ivl.zero)

  /** lengths that may carry a path */
  def support: Vector[Long] = byLen.iterator.collect { case (l, c) if c.hi > 0 => l }.toVector

  def isProvablyEmpty: Boolean = support.isEmpty && rest.hi == 0

  /** PROJECTION 1 — the size interval: classes are disjoint, so counts add. */
  def size: SizeBounds =
    var lo = 0L; var hi = 0L
    for (l, c) <- byLen do { lo = Ivl.add(lo, c.lo); hi = Ivl.add(hi, c.hi) }
    lo = Ivl.add(lo, rest.lo); hi = Ivl.add(hi, rest.hi)
    // headed = every path of length ≥ 1 (only length 0 is ε, and it can hold at most one path)
    val loHeaded = Ivl.relu(lo - (if at(0).hi > 0 then 1 else 0))
    SizeBounds(lo, loHeaded, hi)

  /** PROJECTION 2 — the ∀-path length interval (`lo > hi` marks the provably-empty space). */
  def len: LenBounds =
    val s = support
    if s.isEmpty && rest.hi == 0 then LenBounds.empty
    else
      val trackedLo = if s.isEmpty then LenBounds.INF else s.min
      val trackedHi = if s.isEmpty then 0L else s.max
      if rest.hi == 0 then LenBounds(trackedLo, trackedHi)
      else LenBounds(trackedLo min restLens.lo, if restLens.hi == LenBounds.INF then LenBounds.INF else trackedHi max restLens.hi)

  /** upper-envelope subsumption (`this` fits inside `that`) — the post-fixpoint check. */
  def within(that: SpaceType): Boolean =
    val ls = (byLen.keySet ++ that.byLen.keySet).toVector
    ls.forall(l => at(l).hi <= that.at(l).hi) && rest.hi <= that.rest.hi &&
      (rest.hi == 0 || (!that.restLens.isEmpty && that.restLens.lo <= restLens.lo && restLens.hi <= that.restLens.hi))

  def show: String =
    val cs = byLen.iterator.map((l, c) => s"len $l: ${c.show}").mkString("; ")
    val r = if rest.hi == 0 then "" else s"; other lens [${restLens.lo}, ${if restLens.hi == Lower.LenBounds.INF then "inf" else restLens.hi}]: ${rest.show}"
    s"{$cs$r}"

object SpaceType:
  import Lower.LenBounds
  private def sorted(m: Iterable[(Long, Ivl)]): scala.collection.immutable.SortedMap[Long, Ivl] =
    scala.collection.immutable.SortedMap.from(m.filter(_._2.hi > 0))

  val empty: SpaceType = SpaceType(sorted(Nil), Ivl.zero, LenBounds.empty)
  val unknown: SpaceType = SpaceType(sorted(Nil), Ivl.unknown, LenBounds.unknown)
  /** exactly `n` paths, all of length `l` */
  def exact(l: Long, n: Long): SpaceType = SpaceType(sorted(List(l -> Ivl(n, n))), Ivl.zero, LenBounds.empty)
  /** closed support: the given classes and nothing else */
  def closed(cs: (Long, Ivl)*): SpaceType = SpaceType(sorted(cs), Ivl.zero, LenBounds.empty)
  def of(v: SpaceValue): SpaceType =
    closed(v.paths.groupBy(_.items.length.toLong).view.mapValues(ps => Ivl(ps.size, ps.size)).toSeq*)
  /** at most `n` paths, lengths anywhere in `b` (the shape of an unwrap/restriction result) */
  def bounded(b: LenBounds, n: Long): SpaceType =
    if b.isEmpty || n == 0 then empty else SpaceType(sorted(Nil), Ivl(0, n), b)
  /** EXACTLY `n` paths whose lengths lie in `b` but are not individually known — a singleton over
   *  an unknown-length path is this, not `bounded`: the count is certain even when the class is not. */
  def boundedExact(b: LenBounds, n: Long): SpaceType =
    if b.isEmpty then empty else SpaceType(sorted(Nil), Ivl(n, n), b)

/** The abstract environment: input types for space mentions, path-length types for refs, and the
 *  routine table so `Call` nodes can be analysed INTERPROCEDURALLY (parameters bound to the
 *  argument types) instead of widening to ⊤.  `active` is the call stack: a routine already being
 *  analysed is not re-entered, so recursion degrades to ⊤ rather than diverging. */
final case class SpatialEnv(spaces: Map[SpaceMention, SpaceType] = Map.empty,
                            paths: Map[PathRef, Lower.LenBounds] = Map.empty,
                            routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                            active: Set[RoutinePtr] = Set.empty):
  def +(kv: (SpaceMention, SpaceType)): SpatialEnv = copy(spaces = spaces + kv)
  def withPath(kv: (PathRef, Lower.LenBounds)): SpatialEnv = copy(paths = paths + kv)

object SpatialTypes:
  import Lower.{LenBounds, SizeBounds}
  import scala.collection.immutable.SortedMap
  val MaxClasses = 24
  val MaxLen = 8192

  /** widen: keep the map small and the lengths bounded by spilling classes into `rest` */
  private def normalize(t: SpaceType): SpaceType =
    val live = t.byLen.filter(_._2.hi > 0)
    val (keep, spill) =
      if live.size <= MaxClasses && live.keysIterator.forall(_ <= MaxLen) then (live, Map.empty[Long, Ivl])
      else
        val over = live.filter((l, _) => l > MaxLen)
        val under = live.filter((l, _) => l <= MaxLen)
        // spill the smallest-count classes first (they carry least information)
        val extra = if under.size <= MaxClasses then Map.empty[Long, Ivl]
                    else under.toVector.sortBy(_._2.hi).take(under.size - MaxClasses).toMap
        (under.filter((l, _) => !extra.contains(l)), over ++ extra)
    if spill.isEmpty then SpaceType(SortedMap.from(keep), t.rest, t.restLens)
    else
      val lo = spill.keysIterator.min min (if t.rest.hi > 0 then t.restLens.lo else LenBounds.INF)
      val hi = spill.keysIterator.max max (if t.rest.hi > 0 then t.restLens.hi else 0L)
      var cLo = t.rest.lo; var cHi = t.rest.hi
      for (_, c) <- spill do { cLo = Ivl.add(cLo, c.lo); cHi = Ivl.add(cHi, c.hi) }
      SpaceType(SortedMap.from(keep), Ivl(cLo, cHi), LenBounds(lo, hi))

  private def lensOf(a: SpaceType, b: SpaceType): Vector[Long] = (a.byLen.keySet ++ b.byLen.keySet).toVector.sorted
  private def build(cs: Iterable[(Long, Ivl)], rest: Ivl, restLens: LenBounds): SpaceType =
    normalize(SpaceType(SortedMap.from(cs.filter(_._2.hi > 0)), rest, if rest.hi == 0 then LenBounds.empty else restLens))
  private def restUnion(a: SpaceType, b: SpaceType): (Ivl, LenBounds) =
    val c = Ivl(a.rest.lo max b.rest.lo, Ivl.add(a.rest.hi, b.rest.hi))
    if c.hi == 0 then (Ivl.zero, LenBounds.empty)
    else
      val lo = (if a.rest.hi > 0 then a.restLens.lo else LenBounds.INF) min (if b.rest.hi > 0 then b.restLens.lo else LenBounds.INF)
      val hi = (if a.rest.hi > 0 then a.restLens.hi else 0L) max (if b.rest.hi > 0 then b.restLens.hi else 0L)
      (c, LenBounds(lo, hi))

  /** The join (⊔) — the Union transfer and the Fixpoint iteration step.
   *
   *  When BOTH sides have a closed support the per-length sum is exact bookkeeping.  When either
   *  side has a spill bucket it must NOT be materialised into the output's tracked classes *and*
   *  left in the output's rest: those are the same paths, and counting them twice inflates the size
   *  projection (it turned the certified `s || g` bracket [2, 5] into [2, 11]).  The representation
   *  invariant says rest counts exactly the paths at UNTRACKED lengths, so with a spill present we
   *  collapse to one bucket carrying the summed totals and the hull of both length ranges. */
  def join(a: SpaceType, b: SpaceType): SpaceType =
    if a.rest.hi == 0 && b.rest.hi == 0 then
      build(lensOf(a, b).map(l => l -> Ivl(a.at(l).lo max b.at(l).lo, Ivl.add(a.at(l).hi, b.at(l).hi))), Ivl.zero, LenBounds.empty)
    else
      val (sa, sb) = (a.size, b.size)
      val (la, lb) = (a.len, b.len)
      SpaceType(SortedMap.from(Nil), Ivl(sa.lo max sb.lo, Ivl.add(sa.hi, sb.hi)),
                if la.isEmpty then lb else if lb.isEmpty then la else LenBounds(la.lo min lb.lo, la.hi max lb.hi))

  def infer(s: Space): SpaceType = infer(s, SpatialEnv())
  def infer(s: Space, env: SpatialEnv): SpaceType = go(s, env, 0)

  /** RELATIONAL layer: is `y ⊆ x` derivable syntactically?  Certified by
   *  `proofs/spatial/sp_subsume_syntactic.smt2` (∩/∖/<|/\\| are all ⊆ their left operand, each
   *  operand ⊆ their union) plus transitivity.  This is the one piece a purely per-length count
   *  domain cannot see, and it is exactly where `SizeZ3`'s relational facts used to win: with
   *  `y ⊆ x` the union ABSORBS (`x ∪ y = x`), the meet COLLAPSES (`x ∩ y = y`) and the difference
   *  becomes an exact per-class subtraction — see `sp_subsume_ops.smt2`. */
  def subsumes(x: Space, y: Space): Boolean =
    x == y || (y match
      case Space.Empty => true
      case Space.Literal(SpaceValue(ps)) if ps.isEmpty => true
      case Space.Intersection(a, b) => subsumes(x, a) || subsumes(x, b)
      case Space.Subtraction(a, _) => subsumes(x, a)
      case Space.Restriction(a, _) => subsumes(x, a)
      case Space.Raffination(a, _) => subsumes(x, a)
      case Space.Range(a, _, _) => subsumes(x, a)
      case Space.Union(a, b) => subsumes(x, a) && subsumes(x, b)
      case _ => false) ||
    (x match                                        // x grows: y ⊆ x₀ ⊆ x
      case Space.Union(a, b) => subsumes(a, y) || subsumes(b, y)
      case _ => false)

  /** `{x <| y, x \| y}` partition x (`sp_partition_restrict_raff.smt2`), so their union is x
   *  EXACTLY — the per-class analogue of SizeZ3's partitionPair rule. */
  private def partitionOf(a: Space, b: Space): Option[Space] = (a, b) match
    case (Space.Restriction(x1, y1), Space.Raffination(x2, y2)) if x1 == x2 && y1 == y2 => Some(x1)
    case (Space.Raffination(x1, y1), Space.Restriction(x2, y2)) if x1 == x2 && y1 == y2 => Some(x1)
    case _ => None

  /** ITEM-length interval of a path expression under the env (hints and env entries trusted). */
  def pathLen(p: Path, env: SpatialEnv): LenBounds = p match
    case Path.Deref(pr) =>
      env.paths.getOrElse(pr, if pr.lengthHint >= 0 then LenBounds(pr.lengthHint, pr.lengthHint) else LenBounds.unknown)
    case Path.Constant(pv) => LenBounds(pv.items.length, pv.items.length)
    case Path.Concat(l, r) =>
      val (a, b) = (pathLen(l, env), pathLen(r, env))
      LenBounds(Ivl.add(a.lo, b.lo), Ivl.add(a.hi, b.hi))
    case _ => LenBounds.unknown

  private def go(s: Space, env: SpatialEnv, depth: Int): SpaceType =
    if depth > 64 then SpaceType.unknown else goStructural(s, env, depth)

  private def goStructural(s: Space, env: SpatialEnv, depth: Int): SpaceType =
    def rec(x: Space) = go(x, env, depth + 1)
    s match
      case Space.Empty => SpaceType.empty
      case Space.Literal(v) => SpaceType.of(v)
      case Space.Singleton(p) =>                                  // exactly ONE path, always
        val k = pathLen(p, env)
        if k.lo == k.hi then SpaceType.exact(k.lo, 1) else SpaceType.boundedExact(k, 1)

      // RELATIONAL cases first (certified in proofs/spatial/sp_subsume_*.smt2) — these are the
      // shapes a per-length count domain would otherwise over-estimate by double counting.
      case Space.Union(a, b) if subsumes(a, b) => rec(a)              // b ⊆ a ⟹ a ∪ b = a
      case Space.Union(a, b) if subsumes(b, a) => rec(b)
      case Space.Union(a, b) if partitionOf(a, b).isDefined => rec(partitionOf(a, b).get)
      case Space.Intersection(a, b) if subsumes(a, b) => rec(b)       // b ⊆ a ⟹ a ∩ b = b
      case Space.Intersection(a, b) if subsumes(b, a) => rec(a)
      case Space.Subtraction(a, b) if subsumes(b, a) =>               // a ⊆ b ⟹ a ∖ b = ∅
        SpaceType.empty
      case Space.Restriction(a, b) if a == b => rec(a)                // x <| x = x (sp_restrict_self)
      case Space.Raffination(a, b) if a == b => SpaceType.empty       // x \| x = ∅

      case Space.Union(a, b) => join(rec(a), rec(b))

      case Space.Intersection(a, b) =>
        val (x, y) = (rec(a), rec(b))
        val (r, rl) =
          if x.rest.hi == 0 || y.rest.hi == 0 then (Ivl.zero, LenBounds.empty)
          else (Ivl(0, x.rest.hi min y.rest.hi), LenBounds(x.restLens.lo max y.restLens.lo, x.restLens.hi min y.restLens.hi))
        build(lensOf(x, y).map(l => l -> Ivl(0, x.at(l).hi min y.at(l).hi)), r, rl)

      case Space.Subtraction(a, b) =>
        val (x, y) = (rec(a), rec(b))
        build(x.byLen.map((l, c) => l -> Ivl(Ivl.relu(c.lo - y.at(l).hi), c.hi)),
              Ivl(Ivl.relu(x.rest.lo - y.rest.hi), x.rest.hi), x.restLens)

      case Space.Restriction(xs, ys) =>
        val (x, y) = (rec(xs), rec(ys))
        // a kept path HAS a prefix in y, so its length is ≥ the shortest prefix length
        if y.isProvablyEmpty then SpaceType.empty
        else
          val minPre = y.len.lo
          build(x.byLen.map((l, c) => l -> (if l < minPre then Ivl.zero else Ivl(0, c.hi))),
                Ivl(0, x.rest.hi), LenBounds(x.restLens.lo max minPre, x.restLens.hi))

      case Space.Raffination(xs, ys) =>
        val (x, y) = (rec(xs), rec(ys))
        // x \ (x <| y): a path SHORTER than the shortest prefix of y can never be restricted away
        if y.isProvablyEmpty then x
        else
          val minPre = y.len.lo
          build(x.byLen.map((l, c) => l -> (if l < minPre then c else Ivl(0, c.hi))), Ivl(0, x.rest.hi), x.restLens)

      case Space.Composition(a, b) =>
        val (x, y) = (rec(a), rec(b))
        if x.isProvablyEmpty || y.isProvablyEmpty then SpaceType.empty
        else
          val acc = collection.mutable.Map.empty[Long, Ivl]
          for (la, ca) <- x.byLen; (lb, cb) <- y.byLen do
            val l = la + lb
            val add = Ivl.mul(ca.hi, cb.hi)
            // for a FIXED left path r ↦ l·r is injective (and symmetrically), so each pair
            // independently witnesses max(ca.lo, cb.lo) distinct results; different pairs can
            // collide, so take the max across pairs rather than the sum
            val lo = if ca.lo >= 1 && cb.lo >= 1 then ca.lo max cb.lo else 0L
            val prev = acc.getOrElse(l, Ivl.zero)
            acc(l) = Ivl(prev.lo max lo, Ivl.add(prev.hi, add))
          val anyRest = x.rest.hi > 0 || y.rest.hi > 0
          val (r, rl) =
            if !anyRest then (Ivl.zero, LenBounds.empty)
            else
              val xs2 = x.size; val ys2 = y.size
              (Ivl(0, Ivl.mul(xs2.hi, ys2.hi)), LenBounds(Ivl.add(x.len.lo, y.len.lo), Ivl.add(x.len.hi, y.len.hi)))
          build(acc, r, rl)

      case Space.Wrap(src, p) =>                                  // ≡ Composition(Singleton p, src)
        val x = rec(src); val k = pathLen(p, env)
        if x.isProvablyEmpty then SpaceType.empty
        else if k.lo == k.hi then                                 // exact shift: wrap is a bijection
          build(x.byLen.map((l, c) => (l + k.lo) -> c), x.rest, LenBounds(Ivl.add(x.restLens.lo, k.lo), Ivl.add(x.restLens.hi, k.lo)))
        else rec(Space.Composition(Space.Singleton(p), src))

      case Space.Unwrap(src, p) =>
        val x = rec(src); val k = pathLen(p, env)
        if x.isProvablyEmpty then SpaceType.empty
        else if k.lo == k.hi then                                 // keep those with the prefix, drop |p|
          build(x.byLen.collect { case (l, c) if l >= k.lo => (l - k.lo) -> Ivl(0, c.hi) },
                Ivl(0, x.rest.hi), LenBounds(Ivl.relu(x.restLens.lo - k.lo), if x.restLens.hi == LenBounds.INF then LenBounds.INF else x.restLens.hi - k.lo))
        else SpaceType.bounded(Lower.lenBounds(s), x.size.hi)

      case Space.TailsUnion(src) =>
        val x = rec(src)
        // one tail per HEADED source path, deduped by tag: ≥1 whenever the class is nonempty
        // (for the spilled bucket only when EVERY length in it is headed — a bucket that may hold
        //  ε cannot promise a tail; this is the precision the single rest bucket costs us)
        val restLo = if x.rest.lo >= 1 && !x.restLens.isEmpty && x.restLens.lo >= 1 then 1L else 0L
        build(x.byLen.collect { case (l, c) if l >= 1 => (l - 1) -> Ivl(if c.lo >= 1 then 1 else 0, c.hi) },
              Ivl(restLo, x.rest.hi), LenBounds(Ivl.relu(x.restLens.lo - 1), if x.restLens.hi == LenBounds.INF then LenBounds.INF else Ivl.relu(x.restLens.hi - 1)))

      case Space.TailsIntersection(src) =>
        val x = rec(src)
        build(x.byLen.collect { case (l, c) if l >= 1 => (l - 1) -> Ivl(0, c.hi) },
              Ivl(0, x.rest.hi), LenBounds(Ivl.relu(x.restLens.lo - 1), if x.restLens.hi == LenBounds.INF then LenBounds.INF else Ivl.relu(x.restLens.hi - 1)))

      case Space.Range(xs, a, b) =>
        val x = rec(xs)
        if a == 0 && b == 0 then x
        else
          val w = Lower.sizeBounds(s).hi                            // the window (already computed there)
          build(x.byLen.map((l, c) => l -> Ivl(0, c.hi min w)), Ivl(0, x.rest.hi min w), x.restLens)

      case Space.Iteration(src, sym, rest, body) =>
        val x = rec(src)
        val sb = Lower.sizeBounds(src)
        if x.isProvablyEmpty || x.len.hi == 0 then SpaceType.empty  // no HEADED path ⇒ no groups
        else
          val benv = env.withPath(sym -> LenBounds(1, 1))           // an iteration head is ONE item
            .copy(spaces = if rest.s == "_" then env.spaces else env.spaces + (rest -> tailsOf(x)))
          val bt = go(body, benv, depth + 1)
          val groupsHi = sb.hi                                       // ≤ one group per source path
          val runs = sb.loHeaded >= 1                                // ≥1 headed source path ⇒ ≥1 group
          scaleUnion(bt, if runs then 1L else 0L, groupsHi)

      case Space.Fold(src, _, acc, sym, rest, body, _) =>
        val x = rec(src)
        val sb = Lower.sizeBounds(src)
        if x.isProvablyEmpty || x.len.hi == 0 then SpaceType.empty
        else
          val benv = env.withPath(sym -> LenBounds(1, 1))
            .copy(spaces = if rest.s == "_" then env.spaces else env.spaces + (rest -> tailsOf(x)))
          scaleUnion(go(body, benv, depth + 1), 0L, sb.hi)           // accumulator unknown ⇒ no lower

      case Space.Fixpoint(init, recm, body) =>
        val i0 = rec(init)
        // Kleene iteration with widening, then a POST-FIXPOINT check: if F(T) ⊑ T then lfp ⊑ T.
        var t = i0
        var k = 0
        var ok = false
        while k < 6 && !ok do
          val f = go(body, env + (recm -> t), depth + 1)
          val j = join(t, f)
          if j.within(t) then ok = true
          else
            t = if k >= 2 then widenCounts(j) else j                 // widen counts, keep the support
            k += 1
        val verified = ok || go(body, env + (recm -> t), depth + 1).within(t)
        if verified then
          // the result contains init and is contained in t: keep t's envelope, init's lower bounds
          build(t.byLen.map((l, c) => l -> Ivl(i0.at(l).lo, c.hi)), Ivl(0, t.rest.hi), t.restLens)
        else
          val lb = Lower.lenBounds(s)
          if lb.isEmpty then SpaceType.empty else SpaceType(SortedMap.from(Nil), Ivl(i0.size.lo, Ivl.INF), lb)

      // an explicit input type wins; otherwise honour the mention's `sizeHint` contract (exactly
      // that many paths, at lengths we know nothing about) — the same hint tier-1 sizeBounds trusts
      case Space.Mention(m) => env.spaces.getOrElse(m,
        if m.sizeHint >= 0 then SpaceType.boundedExact(LenBounds.unknown, m.sizeHint) else SpaceType.unknown)

      // INTERPROCEDURAL: analyse the callee's body with its parameters bound to the argument types.
      // Sound because a routine body denotes a function of its parameters; `active` stops recursion
      // (a recursive callee falls through to ⊤ below rather than diverging).
      case Space.Call(rp, refs, mentions) if env.routines.isDefinedAt(rp) && !env.active(rp) =>
        val Routine(_, refns, mentionns, body) = env.routines(rp)
        val callee = SpatialEnv(
          spaces = mentionns.zip(mentions.map(m => go(m, env, depth + 1))).toMap,
          paths = refns.zip(refs.map(p => pathLen(p, env))).toMap,
          routines = env.routines, active = env.active + rp)
        go(body, callee, depth + 1)

      case Space.Call(_, _, _) | Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => SpaceType.unknown

  private def widenCounts(t: SpaceType): SpaceType =
    SpaceType(SortedMap.from(t.byLen.map((l, c) => l -> Ivl(c.lo, Ivl.INF))),
              if t.rest.hi == 0 then Ivl.zero else Ivl(t.rest.lo, Ivl.INF), t.restLens)

  /** the tail-set type of one head-group: each tail is a source path minus its single head item */
  private def tailsOf(x: SpaceType): SpaceType =
    build(x.byLen.collect { case (l, c) if l >= 1 => (l - 1) -> Ivl(0, c.hi) },
          Ivl(0, x.rest.hi), LenBounds(Ivl.relu(x.restLens.lo - 1), if x.restLens.hi == LenBounds.INF then LenBounds.INF else Ivl.relu(x.restLens.hi - 1)))

  /** a union of between `gLo` and `gHi` copies of `t` (per-group bodies of an iteration/fold) */
  private def scaleUnion(t: SpaceType, gLo: Long, gHi: Long): SpaceType =
    if gHi == 0 then SpaceType.empty
    else build(t.byLen.map((l, c) => l -> Ivl(if gLo >= 1 then c.lo else 0L, Ivl.mul(c.hi, gHi))),
               Ivl(if gLo >= 1 then t.rest.lo else 0L, Ivl.mul(t.rest.hi, gHi)), t.restLens)

  // ---- projections, clamped by the dedicated analyses ------------------------------------------
  /** the size projection, intersected with the tier-1 size analysis (never worse than either) */
  def sizeOf(s: Space, env: SpatialEnv = SpatialEnv()): SizeBounds =
    val t = infer(s, env).size
    val b = Lower.sizeBounds(s)
    SizeBounds(t.lo max b.lo, t.loHeaded max b.loHeaded, t.hi min b.hi)

  /** the length projection, intersected with the tier-1 length analysis */
  def lenOf(s: Space, env: SpatialEnv = SpatialEnv()): LenBounds =
    val t = infer(s, env).len
    val b = Lower.lenBounds(s)
    if t.isEmpty || b.isEmpty then LenBounds.empty else LenBounds(t.lo max b.lo, t.hi min b.hi)

  /** The sharpest sound answers available: the spatial projection meet the dedicated tiers.
   *  The analyses are INCOMPARABLE in general — spatial wins on per-length reasoning (a
   *  restriction that annihilates a length class, wrap/tails class shifts), `SizeZ3` wins on
   *  relational set facts across siblings (inclusion–exclusion `|a∪b| = |a|+|b|−|a∩b|`, subset
   *  saturation, partition equalities), which a per-length count domain cannot express.  Meeting
   *  them is sound (both over-approximate the same value) and dominates each, so these are what a
   *  consumer should use; they also make "the spatial projection falls within the z3 bounds" hold
   *  by construction. */
  def bestSize(s: Space, env: SpatialEnv = SpatialEnv(), timeoutSec: Int = 8): SizeBounds =
    val a = sizeOf(s, env)
    if !SizeZ3.available then a
    else
      val (z, st) = SizeZ3.boundsWithStatus(s, timeoutSec)
      if st != SizeZ3.Status.Solved then a
      else SizeBounds(a.lo max z.lo, a.loHeaded max z.loHeaded, a.hi min z.hi)

  def bestLen(s: Space, env: SpatialEnv = SpatialEnv(), timeoutSec: Int = 8): LenBounds =
    val a = lenOf(s, env)
    if !LenZ3.available then a
    else
      val (z, st) = LenZ3.boundsWithStatus(s, timeoutSec)
      if st != SizeZ3.Status.Solved || z.isEmpty || a.isEmpty then a
      else LenBounds(a.lo max z.lo, a.hi min z.hi)
end SpatialTypes
