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
 *  of paths at any length".  Each transfer is INTENDED to be a true cardinality fact about its
 *  operator; three of them (∪, ∩, ∖) have that checked in `proofs/spatial/lat_transfer_sound.smt2`
 *  and the rest are supported by the path lemmas in §5 of docs/design_spatial_lattice.md plus the
 *  differential suites — no mechanical link ties a transfer here to an obligation there.
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
  /** exactly `n` paths, all of length `l` (routed through the widening: a length-9000 constant
   *  used to keep a tracked key above `MaxLen`, contradicting the class comment) */
  def exact(l: Long, n: Long): SpaceType =
    SpatialTypes.widen(SpaceType(sorted(List(l -> Ivl(n, n))), Ivl.zero, LenBounds.empty))
  /** Closed support: the given classes and nothing else.  Routed through the analysis' widening so
   *  the documented class cap actually holds — a literal (or a declared input type) with more than
   *  `MaxClasses` distinct lengths used to build an oversized map that bypassed `normalize`. */
  def closed(cs: (Long, Ivl)*): SpaceType =
    SpatialTypes.widen(SpaceType(sorted(cs), Ivl.zero, LenBounds.empty))
  def of(v: SpaceValue): SpaceType =
    closed(v.paths.groupBy(_.items.length.toLong).view.mapValues(ps => Ivl(ps.size, ps.size)).toSeq*)
  /** at most `n` paths, lengths anywhere in `b` (the shape of an unwrap/restriction result) */
  def bounded(b: LenBounds, n: Long): SpaceType =
    if b.isEmpty || n == 0 then empty else SpatialTypes.widen(SpaceType(sorted(Nil), Ivl(0, n), b))
  /** EXACTLY `n` paths whose lengths lie in `b` but are not individually known — a singleton over
   *  an unknown-length path is this, not `bounded`: the count is certain even when the class is not. */
  def boundedExact(b: LenBounds, n: Long): SpaceType =
    if b.isEmpty then empty else SpatialTypes.widen(SpaceType(sorted(Nil), Ivl(n, n), b))

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

  /** THE LENGTH-SIDE `TailsUnion` TRANSFER, as a function rather than only as a `case` arm.
   *
   *  Extracted because `SpatialCost.ChainCost.leafEnv` needs it to iterate the PER-LEVEL FIBER
   *  BOUND down a rest-chain nest: each level's `rest` is a group of the previous
   *  level's tails, so the bound is `tailsUnion` applied once per level.  Re-deriving the shift
   *  there would be a second copy of the arithmetic, which is exactly the kind of duplication that
   *  drifts — `windowWidthOf` was one and it was unsound.
   *
   *  One tail per HEADED source path, deduped by tag: `>= 1` whenever the class is non-empty.  For
   *  the spilled bucket only when EVERY length in it is headed — a bucket that may hold ε cannot
   *  promise a tail, which is the precision the single rest bucket costs. */
  private[morkl] def tailsUnionLens(x: SpaceType): SpaceType =
    val restLo = if x.rest.lo >= 1 && !x.restLens.isEmpty && x.restLens.lo >= 1 then 1L else 0L
    build(
      x.byLen.collect { case (l, c) if l >= 1 => (l - 1) -> Ivl(if c.lo >= 1 then 1 else 0, c.hi) },
      Ivl(restLo, x.rest.hi),
      LenBounds(Ivl.relu(x.restLens.lo - 1),
                if x.restLens.hi == LenBounds.INF then LenBounds.INF
                else Ivl.relu(x.restLens.hi - 1)))
  /** THE MAY-ONLY LENGTH TYPE — the length half of the FIBER BOUND, in ONE place.
   *
   *  One head group's tails are a SUBSET of the level's tails-union, so the union's UPPER bounds hold
   *  of the group and its LOWER bounds do not: `Literal({a, b.a})`'s tails-union has a path of length
   *  0 and one of length 1, and head `a`'s group has only the length-0 one.  Keeping the lower bounds
   *  made the reduced product contradict itself — `SpatialType.reduce`'s `constrainShape` typed 11
   *  corpus terms DEFINITELY EMPTY against non-empty values (`SpatialAnalysisCheck`, three distinct
   *  operator families) — which is the same mistake, on the other channel, that `Shape.weaken` exists
   *  to prevent on the shape side.
   *
   *  It is shared by `SpatialTyping.groupUnion` (the decorated analysis' binder) and
   *  `SpatialCost.mayOnlyType` (the cost model's) so the two cannot drift: they are the same claim
   *  about the same relationship. */
  private[morkl] def mayOnlyLens(x: SpaceType): SpaceType =
    build(x.byLen.map((l, c) => l -> Ivl(0, c.hi)), Ivl(0, x.rest.hi), x.restLens)

  /** the fiber's length type: one group's tails, bounded above by the tails-union and claiming no
   *  lower bound at all.  This is the composition the two binders both want. */
  private[morkl] def fiberLens(x: SpaceType): SpaceType = mayOnlyLens(tailsUnionLens(x))

  val MaxClasses = 24
  val MaxLen = 8192

  /** the public widening: spill to keep the caps, then enforce the disjointness invariant */
  private[morkl] def widen(t: SpaceType): SpaceType = disjoin(normalize(t))

  /** spill classes into `rest` to keep the map small and the lengths bounded */
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
    disjoin(normalize(SpaceType(SortedMap.from(cs.filter(_._2.hi > 0)), rest,
                                if rest.hi == 0 then LenBounds.empty else restLens)))

  /** ENFORCE THE REPRESENTATION INVARIANT: the spill bucket counts the paths at lengths NOT in
   *  `byLen`, so `restLens` must not cover a tracked length.  `at` and `size` both rely on that —
   *  `at(l)` answers from the tracked class alone — so an overlap makes the per-length claim FALSE,
   *  not merely imprecise: a transfer can route part of a length's paths into the spill (composition
   *  puts every rest-involving product there) while the tracked class counts only the rest.
   *
   *  Any tracked class the spill range covers is therefore folded INTO the spill.  Counts are
   *  combined with `max` on the lower end, not `+`: if the buckets did overlap, the two claims may
   *  describe the same paths, and only the maximum is guaranteed.  Precision is lost exactly where
   *  widening had already given up (a type only has a spill once it exceeded `MaxClasses`/`MaxLen`),
   *  so terms under the caps — every cornerstone and every corpus program — are unaffected. */
  private def disjoin(t: SpaceType): SpaceType =
    if t.rest.hi == 0 || t.restLens.isEmpty then t
    else
      val (overlap, keep) = t.byLen.partition((l, _) => t.restLens.lo <= l && l <= t.restLens.hi)
      if overlap.isEmpty then t
      else
        var lo = t.rest.lo
        var hi = t.rest.hi
        for (_, c) <- overlap do { lo = lo max c.lo; hi = Ivl.add(hi, c.hi) }
        SpaceType(SortedMap.from(keep), Ivl(lo, hi),
                  LenBounds(t.restLens.lo min overlap.keysIterator.min, t.restLens.hi max overlap.keysIterator.max))
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
        // The SPILL lower bound has to discount every subtrahend path that could sit at one of the
        // lengths the bucket covers -- including one in a TRACKED class of `y`.  Using only
        // `y.rest.hi` ignored those, so e.g. `(A \ A)` with `A`'s count in the spill kept a lower
        // bound of |A| on an empty result (witness: `(hunt$rec(;$s0) \ $s0)` with `$s0 = {ε}`
        // inferred size.lo = 1 -> DefinitelyNonEmpty for eval = ∅; also
        // `((s0 ∪ TU(L)) \ TU(L))` -> lo 2, and `(Singleton(?p) \ L{17 paths})` -> lo 1).
        // Tracked classes keep their own exact discount (`y.at(l).hi`); only the bucket needs the
        // window sum, because it does not know which lengths its paths occupy.
        val win = x.restLens
        val yInWindow: Long =
          if x.rest.lo == 0 || win.isEmpty then 0L
          else
            var tot = 0L
            for (l, c) <- y.byLen if win.lo <= l && l <= win.hi do tot = Ivl.add(tot, c.hi)
            if y.rest.hi > 0 && !y.restLens.isEmpty && y.restLens.lo <= win.hi && win.lo <= y.restLens.hi
            then Ivl.add(tot, y.rest.hi) else tot
        build(x.byLen.map((l, c) => l -> Ivl(Ivl.relu(c.lo - y.at(l).hi), c.hi)),
              Ivl(Ivl.relu(x.rest.lo - yInWindow), x.rest.hi), x.restLens)

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

      case Space.TailsUnion(src) => tailsUnionLens(rec(src))

      case Space.TailsIntersection(src) =>
        val x = rec(src)
        build(x.byLen.collect { case (l, c) if l >= 1 => (l - 1) -> Ivl(0, c.hi) },
              Ivl(0, x.rest.hi), LenBounds(Ivl.relu(x.restLens.lo - 1), if x.restLens.hi == LenBounds.INF then LenBounds.INF else Ivl.relu(x.restLens.hi - 1)))

      case Space.Range(xs, a, b) =>
        val x = rec(xs)
        if a == 0 && b == 0 then x
        else
          // THE WINDOW'S CARDINALITY, BOTH ENDPOINTS.  `SpatialTyping.windowCard` lifts
          // `RangeBounds.normalize` over the SOURCE'S OWN size interval and is exact (45367
          // (bound-pair, size-interval) lifts at two magnitudes, checked against `normalize` itself
          // in `src/test/scala/RangeCardCheck.scala`).  It is MET with the tier-1 syntactic bound
          // rather than replacing it: the two are computed from different information — tier-1 from
          // the term's syntax, this from the histogram just derived for `xs` — and neither subsumes
          // the other.
          val sz = x.size
          val card = SpatialTyping.windowCard(Ivl(sz.lo, sz.hi), a, b)
          val w = Lower.sizeBounds(s).hi min card.hi
          // ==A LOWER BOUND NEEDS A CLASS TO ATTRIBUTE IT TO==
          // `card.lo` bounds the window's TOTAL cardinality, and a positional window may draw its
          // paths from any length class, so no individual class gets a must-count from it in
          // general — which is why every class below is `Ivl(0, ...)` and was before.  There is one
          // case where the attribution is forced: when the source's support is a SINGLE class and
          // there is no spill (`rest.hi == 0`), every surviving path has that length, so the whole
          // of `card.lo` lands there.  Anything weaker than that side condition would claim a must
          // for a class the window can miss entirely.
          val sup = x.support
          val single = sup.length == 1 && x.rest.hi == 0
          def loAt(l: Long, cHi: Long): Long =
            if single && sup.head == l then card.lo min cHi else 0L
          build(x.byLen.map((l, c) => l -> Ivl(loAt(l, c.hi), c.hi min w)),
                Ivl(0, x.rest.hi min w), x.restLens)

      case Space.Iteration(src, sym, rest, body) =>
        val x = rec(src)
        // the group count comes from the SPATIAL source type met with the baseline: using only
        // `Lower.sizeBounds(src)` threw away a declared input type, so iterating over a mention
        // typed "exactly two length-1 paths" still reported [0, inf)
        val sb = meetSize(x.size, Lower.sizeBounds(src, envSizes(env), env.routines, env.active))
        if x.isProvablyEmpty || x.len.hi == 0 then SpaceType.empty  // no HEADED path ⇒ no groups
        else
          val benv = env.withPath(sym -> LenBounds(1, 1))           // an iteration head is ONE item
            .copy(spaces = if rest.s == "_" then env.spaces else env.spaces + (rest -> tailsOf(x)))
          val bt = go(body, benv, depth + 1)
          val groupsHi = sb.hi                                       // ≤ one group per source path
          val runs = sb.loHeaded >= 1                                // ≥1 headed source path ⇒ ≥1 group
          reduceTotal(scaleUnion(bt, if runs then 1L else 0L, groupsHi),
                      Lower.sizeBounds(s, envSizes(env), env.routines, env.active))

      case Space.Fold(src, _, acc, sym, rest, body, _) =>
        val x = rec(src)
        val sb = meetSize(x.size, Lower.sizeBounds(src, envSizes(env), env.routines, env.active))
        if x.isProvablyEmpty || x.len.hi == 0 then SpaceType.empty
        else
          val benv = env.withPath(sym -> LenBounds(1, 1))
            .copy(spaces = if rest.s == "_" then env.spaces else env.spaces + (rest -> tailsOf(x)))
          reduceTotal(scaleUnion(go(body, benv, depth + 1), 0L, sb.hi),   // accumulator unknown ⇒ no lower
                      Lower.sizeBounds(s, envSizes(env), env.routines, env.active))

      case Space.Fixpoint(init, recm, body) =>
        val i0 = rec(init)
        // The concrete fixpoint returns the UNION of all iterates, so the check has to hold for the
        // union, not just for one application: `join(t, F#(t)) ⊑ t`.  Since `join`'s per-class upper
        // ADDS counts, a finite-count candidate can only satisfy that when the body contributes
        // nothing — every other case must have its counts widened to ∞ first.  Earlier this held
        // only as a side effect of the widening schedule (widenCounts kicked in at k ≥ 2), which is
        // exactly the kind of accidental soundness the review warned about; it is now required
        // explicitly.  The SUPPORT (which lengths occur) is what survives widening, and that is the
        // real result here — the reachable-state-space fixpoints are length-homogeneous.
        var t = i0
        var k = 0
        var ok = false
        while k < 6 && !ok do
          val f = go(body, env + (recm -> t), depth + 1)
          val j = join(t, f)
          if j.within(t) then ok = true
          else
            t = if k >= 2 then widenCounts(j) else j
            k += 1
        // re-verify on the UNION, and if a finite-count candidate cannot carry it, widen and retry
        def unionClosed(c: SpaceType): Boolean = join(c, go(body, env + (recm -> c), depth + 1)).within(c)
        val (cand, verified) =
          if ok || unionClosed(t) then (t, true)
          else
            val w = widenCounts(t)
            if unionClosed(w) then (w, true) else (w, false)
        if verified then
          // the result contains init and is contained in cand: cand's envelope, init's lower bounds
          build(cand.byLen.map((l, c) => l -> Ivl(i0.at(l).lo, c.hi)), Ivl(0, cand.rest.hi), cand.restLens)
        else
          // no verified post-fixpoint ⇒ counts unbounded, but keep every length fact the supplied
          // env and routine table still justify (the old fallback recomputed lenBounds with an
          // EMPTY env, discarding exactly the information the caller had provided).
          val lb = Lower.lenBounds(s, envLens(env), env.paths, env.routines, env.active)
          val hull = if lb.isEmpty then i0.len else if i0.len.isEmpty then lb
                     else LenBounds(lb.lo min i0.len.lo, lb.hi max i0.len.hi)
          if hull.isEmpty then SpaceType.empty
          else SpaceType(SortedMap.from(Nil), Ivl(i0.size.lo, Ivl.INF), hull)

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

      // ==A RECURSIVE CALLEE'S SUMMARY ON THE LENGTH SIDE TOO ==
      //
      // `active(rp)` stops the interprocedural descent above, and this arm returned
      // `SpaceType.unknown` — no claim about the length histogram OR the cardinality of a recursive
      // call's result.  `SpatialRecursion` solves both halves at once (its table holds
      // `SpatialType`s), so the length half is one field of the same certified answer.
      //
      // THE ARGUMENTS ARE BUILT FROM WHAT THIS SIDE HAS, which is less than the shape side has: a
      // mention argument's SHAPE is not available here, so it goes in as ⊤ with the length half
      // filled.  That is a sound argument tuple and it is a DIFFERENT key from the shape side's, so
      // the two consult different summaries and neither is degraded by the other.  A key the solve
      // does not reach yields `None` and this arm keeps its `unknown`.
      case Space.Call(rp, refs, mentions) if env.routines.isDefinedAt(rp) =>
        val argTypes = mentions.map(m => SpatialType(Shape.top, go(m, env, depth + 1)))
        // OPAQUE, always: `SpatialEnv` carries `paths: Map[PathRef, LenBounds]` and no path VALUES,
        // so a constant argument cannot be recognised here even when the shape side recognises it.
        val pathArgs = refs.map(p => SpatialRecursion.PathArg.opaque(pathLen(p, env)))
        if depth > 8 then SpaceType.unknown        // a solve per level of an open nest is not worth it
        else SpatialRecursion.summaryAt(rp, SpatialRecursion.argsOf(argTypes, pathArgs), env.routines)
               .map(_.lens).getOrElse(SpaceType.unknown)

      case Space.Call(_, _, _) | Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => SpaceType.unknown

  /** both are sound bounds on the same count, so the meet is sound and at least as tight */
  private def meetSize(a: SizeBounds, b: SizeBounds): SizeBounds =
    SizeBounds(a.lo max b.lo, a.loHeaded max b.loHeaded, a.hi min b.hi)

  /** REDUCE the histogram against a sound bound on its TOTAL.  No class can hold more than the whole
   *  space, so every class upper is capped by `total.hi`; when only one class is live that makes the
   *  reduction exact.  Without this the product was unreduced and `infer(...).size` could be 64x
   *  looser than `sizeOf(...)` on the very same term — a four-deep rest-chained iteration reported
   *  [0, 256] where the tier-1 head-partition law already knew [0, 4]. */
  private def reduceTotal(t: SpaceType, total: SizeBounds): SpaceType =
    if total.hi == Ivl.INF then t
    else SpaceType(SortedMap.from(t.byLen.map((l, c) => l -> Ivl(c.lo, c.hi min total.hi))),
                   Ivl(t.rest.lo, t.rest.hi min total.hi), t.restLens)

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

  // ---- intermediate-space elimination ----------------------------------------------------------
  /** A named fact the abstract interpretation established, and what it let us delete. */
  final case class Removed(fact: String, subterm: String, nodes: Int)
  /** The residual program plus the facts that justify it. */
  final case class Elimination(residual: Space, removed: Vector[Removed]):
    def nodesRemoved: Int = removed.map(_.nodes).sum

  private def nodeCount(sp: Space): Int = 1 + SizeZ3.children(sp).map(nodeCount).sum

  /** ELIMINATE INTERMEDIATE SPACES from a function body, using ONLY facts this abstract
   *  interpretation derives from the function's ANNOTATED INPUTS.
   *
   *  Nothing here evaluates a subterm: a subterm is deleted when its inferred spatial type is
   *  `⊥` (no class can hold a path), which the transfers derive from the term's syntax, the
   *  annotations in `env`, and the certified relational laws.  Deleting it removes the whole
   *  computation that produced it — the point of the exercise — and the ordinary `Lower` laws then
   *  propagate `Empty` through its parents (`x ∪ ∅ = x`, `∅ · y = ∅`, …).
   *
   *  CONTRACT: the residual agrees with the original on every input SATISFYING `env`.  With an empty
   *  `env` the annotations are vacuous, so the rewrite is unconditional; with annotations the result
   *  is a SPECIALISATION and is only valid where they hold.  This is strictly stronger than the
   *  syntactic `Lower.SizeEmpty` law, which sees only `sizeBounds(sp).hi == 0`: the spatial tier also
   *  proves emptiness from length-disjointness (`{len 10} ∩ {len 15}`), from restriction
   *  annihilation (every path shorter than the shortest prefix), and from a declared input type. */
  def eliminate(s: Space, env: SpatialEnv): Elimination =
    val out = Vector.newBuilder[Removed]
    def go2(sp: Space, e: SpatialEnv, depth: Int): Space =
      if depth > 64 then sp
      else if sp != Space.Empty && infer(sp, e).isProvablyEmpty then
        out += Removed("provably-empty", sp.show.take(90), nodeCount(sp))
        Space.Empty
      else sp match
        case Space.Union(a, b) => Space.Union(go2(a, e, depth + 1), go2(b, e, depth + 1))
        case Space.Intersection(a, b) => Space.Intersection(go2(a, e, depth + 1), go2(b, e, depth + 1))
        case Space.Subtraction(a, b) => Space.Subtraction(go2(a, e, depth + 1), go2(b, e, depth + 1))
        case Space.Restriction(a, b) => Space.Restriction(go2(a, e, depth + 1), go2(b, e, depth + 1))
        case Space.Raffination(a, b) => Space.Raffination(go2(a, e, depth + 1), go2(b, e, depth + 1))
        case Space.Composition(a, b) => Space.Composition(go2(a, e, depth + 1), go2(b, e, depth + 1))
        case Space.Wrap(a, p) => Space.Wrap(go2(a, e, depth + 1), p)
        case Space.Unwrap(a, p) => Space.Unwrap(go2(a, e, depth + 1), p)
        case Space.TailsUnion(a) => Space.TailsUnion(go2(a, e, depth + 1))
        case Space.TailsIntersection(a) => Space.TailsIntersection(go2(a, e, depth + 1))
        case Space.Range(a, x, y) => Space.Range(go2(a, e, depth + 1), x, y)
        case Space.Iteration(src, sym, rest, body) =>
          // the body sees the loop's bindings, exactly as the analysis binds them
          val benv = e.withPath(sym -> LenBounds(1, 1))
            .copy(spaces = if rest.s == "_" then e.spaces else e.spaces + (rest -> tailsOf(infer(src, e))))
          Space.Iteration(go2(src, e, depth + 1), sym, rest, go2(body, benv, depth + 1))
        case Space.Fold(src, init, acc, sym, rest, body, upd) =>
          val benv = e.withPath(sym -> LenBounds(1, 1))
            .copy(spaces = if rest.s == "_" then e.spaces else e.spaces + (rest -> tailsOf(infer(src, e))))
          Space.Fold(go2(src, e, depth + 1), init, acc, sym, rest, go2(body, benv, depth + 1), upd)
        case Space.Fixpoint(init, recm, body) =>
          // the recursive mention is only ⊤-bound here: the accumulated type is not available to a
          // one-pass rewrite, and assuming anything stronger would not be justified
          val benv = e.copy(spaces = e.spaces - recm)
          Space.Fixpoint(go2(init, e, depth + 1), recm, go2(body, benv, depth + 1))
        case other => other                       // Call bodies belong to their own routine
    val r = go2(s, env, 0)
    Elimination(r, out.result())

  /** the same, on a FUNCTION: annotate the parameters, get a specialised routine plus its facts */
  def eliminateIn(r: Routine, env: SpatialEnv): (Routine, Vector[Removed]) =
    val e = eliminate(r.body, env)
    (Routine(r.name, r.refs, r.mentions, e.residual), e.removed)

  // ---- projections, clamped by the dedicated analyses ------------------------------------------
  // Every one of these passes the caller's ROUTINE TABLE down to the tier-1/z3 analyses.  Not doing
  // so silently discarded the interprocedural information the caller supplied, so a "sharpest
  // answer" could be LOOSER than plain `Lower.sizeBounds(s, rc)` — see the review.  Declared input
  // TYPES still reach only the spatial tier: the other two take mention bounds through their own
  // env, so `envSizes`/`envLens` translate what is translatable (a `SpaceType` down to its size and
  // length projections) instead of dropping it.
  private def envSizes(env: SpatialEnv): Map[SpaceMention, SizeBounds] =
    env.spaces.view.mapValues(_.size).toMap
  private def envLens(env: SpatialEnv): Map[SpaceMention, LenBounds] =
    env.spaces.view.mapValues(_.len).toMap

  /** the size projection, intersected with the tier-1 size analysis (never worse than either) */
  def sizeOf(s: Space, env: SpatialEnv = SpatialEnv()): SizeBounds =
    val t = infer(s, env).size
    val b = Lower.sizeBounds(s, envSizes(env), env.routines, Set.empty)
    SizeBounds(t.lo max b.lo, t.loHeaded max b.loHeaded, t.hi min b.hi)

  /** the length projection, intersected with the tier-1 length analysis */
  def lenOf(s: Space, env: SpatialEnv = SpatialEnv()): LenBounds =
    val t = infer(s, env).len
    val b = Lower.lenBounds(s, envLens(env), env.paths, env.routines, Set.empty)
    if t.isEmpty || b.isEmpty then LenBounds.empty else LenBounds(t.lo max b.lo, t.hi min b.hi)

  /** The sharpest sound answers available: the spatial projection meet the dedicated tiers.
   *  The analyses are INCOMPARABLE in general — spatial wins on per-length reasoning (a
   *  restriction that annihilates a length class, wrap/tails class shifts), `SizeZ3` wins on
   *  relational set facts across siblings (inclusion–exclusion `|a∪b| = |a|+|b|−|a∩b|`, subset
   *  saturation, partition equalities), which a per-length count domain cannot express.  Meeting
   *  them is sound (both over-approximate the same value) and dominates each, so these are what a
   *  consumer should use; they also make "the spatial projection falls within the z3 bounds" hold
   *  by construction. */
  /** a z3 answer is usable when it was fully solved OR partly solved — a `PartiallySolved` result
   *  has baseline endpoints where an objective failed and optimal ones elsewhere, so it still
   *  dominates the baseline and meeting with it can only tighten.  Discarding it threw away real
   *  information. */
  private def usable(st: SizeZ3.Status): Boolean = st match
    case SizeZ3.Status.Solved | SizeZ3.Status.PartiallySolved(_) => true
    case _ => false

  def bestSize(s: Space, env: SpatialEnv = SpatialEnv(), timeoutSec: Int = 8): SizeBounds =
    val a = sizeOf(s, env)
    if !SizeZ3.available then a
    else
      val (z, st) = SizeZ3.boundsWithStatus(s, timeoutSec, env.routines)
      if !usable(st) then a
      else SizeBounds(a.lo max z.lo, a.loHeaded max z.loHeaded, a.hi min z.hi)

  def bestLen(s: Space, env: SpatialEnv = SpatialEnv(), timeoutSec: Int = 8): LenBounds =
    val a = lenOf(s, env)
    if !LenZ3.available then a
    else
      val (z, st) = LenZ3.boundsWithStatus(s, timeoutSec, env.routines)
      if !usable(st) || z.isEmpty || a.isEmpty then a
      else LenBounds(a.lo max z.lo, a.hi min z.hi)
end SpatialTypes
