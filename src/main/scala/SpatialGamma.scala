package morkl

/** THE SEMANTIC LAYER OF THE SPATIAL DOMAIN — γ, α, the order that IS γ-containment, the lattice
 *  join, and the OPERATOR TABLE that drives the simulation squares.
 *
 *  review.md 6 asks for the law family the corpus is missing:
 *
 *      eval(s, concreteEnv) ∈ γ(infer(s, abstractEnv))          -- per-operator simulation
 *      γ(a op# b) ⊇ γ(a) op γ(b)                                 -- local soundness of a transfer
 *      specialize(s, facts) ≡ s under facts                      -- conditional rewrite
 *
 *  None of those can even be *stated* until γ is a concrete, total, executable predicate on the
 *  actual abstract carrier ([[SpatialType]] = [[Shape]] × [[SpaceType]]).  That is what this file
 *  provides; `SpatialLawCheck` is the executable checker and `proofs/spatial-semantic/` holds the
 *  finite-first-order fragments discharged by z3.
 *
 *  ==NO EVALUATION==
 *  Nothing here calls `eval`/`evalI`/`evalT`/`exec*`.  γ is a *predicate on a value that the caller
 *  already has*, not a way to obtain one; α abstracts a value the caller already has.  Neither is
 *  reachable from any transfer in `SpatialTypes`/`SpatialTyping`, and the operator table below is
 *  data (constructors), not an interpreter.  The only place evaluation happens is the *test*, which
 *  is allowed to use it as ground truth.
 *
 *  ==WHAT γ MEANS HERE==
 *  Two readings of the shape component are provided, because the code is ambiguous about which one
 *  it implements and the difference is exactly where the must/may bugs live:
 *
 *    - [[gammaShape]] (STRONG): `eps = Must` means ε really is a member, a tracked head whose child
 *      forces ε means that path really is present, and `others.lo` is a real lower bound on the
 *      number of untracked heads.  This is the reading `Shape.restrict` needs (`prefixes.eps.mustBe
 *      ⇒ result = x`) and the one `Shape.of` produces for a literal.
 *    - [[gammaShapeMay]] (WEAK, = strong γ of [[weakenAll]]): every Must is demoted to May and every
 *      `others.lo` to 0.  This is the reading the class comment on `Shape.definitelyNonEmpty`
 *      claims ("V1 IS MAY-ONLY"), and it is what `Fact`, `headCount`, `mayHavePrefix` and
 *      `isProvablyEmpty` actually consume.
 *
 *  `SpatialLawCheck` reports both, separately, per operator.  A transfer that is sound for the weak
 *  reading but not the strong one is not "nearly sound": it means the Must channel leaks and must
 *  not be consumed. */
object SpatialGamma:
  import scala.collection.immutable.SortedMap
  import Lower.{LenBounds, SizeBounds}

  // ==============================================================================================
  // 1. CONCRETIZATION
  // ==============================================================================================

  /** γ for the LENGTH-INDEXED COUNT component.
   *
   *  `v ∈ γ(t)` iff every tracked class brackets the concrete count of paths of that length, every
   *  concrete length is either tracked or inside the spill window, and the TOTAL count at untracked
   *  lengths lies in the spill interval.  This is the representation invariant `SpaceType.at` and
   *  `SpaceType.size` already assume (see the `disjoin` comment in SpatialTypes.scala) read as a
   *  membership predicate. */
  def gammaSpace(t: SpaceType, v: SpaceValue): Boolean =
    val cnt: Map[Long, Long] =
      v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap
    val trackedOk = t.byLen.forall { (l, c) => val n = cnt.getOrElse(l, 0L); c.lo <= n && n <= c.hi }
    if !trackedOk then false
    else
      val residual = cnt.filter((l, _) => !t.byLen.contains(l))
      val lensOk = residual.forall { (l, n) =>
        n == 0L || (t.rest.hi > 0 && !t.restLens.isEmpty && t.restLens.lo <= l && l <= t.restLens.hi) }
      var tot = 0L
      for (_, n) <- residual do tot = Ivl.add(tot, n)
      lensOk && t.rest.lo <= tot && tot <= t.rest.hi

  /** γ for the SHAPE component, STRONG reading (Must is a real must). Total: the recursion is on
   *  the finite `Shape` tree; the guard is belt-and-braces against a cyclic hand-built shape. */
  def gammaShape(sh: Shape, v: SpaceValue): Boolean = gammaShape(sh, v, 64)
  private def gammaShape(sh: Shape, v: SpaceValue, d: Int): Boolean =
    if d <= 0 then true
    else
      val hasEps = v.paths.contains(PathValue(Nil))
      val epsOk = sh.eps match
        case Presence.No => !hasEps
        case Presence.Must => hasEps
        case Presence.May => true
      if !epsOk then false
      else
        val groups: Map[PathItem, SpaceValue] =
          v.paths.iterator.collect { case PathValue(h :: t) => (h, PathValue(t)) }
            .toVector.groupMap(_._1)(_._2).view.mapValues(ts => SpaceValue(ts.toSet)).toMap
        val tracked = groups.filter((h, _) => sh.heads.contains(h))
        val untracked = groups.filter((h, _) => !sh.heads.contains(h))
        val n = untracked.size.toLong
        sh.others.lo <= n && n <= sh.others.hi &&
          tracked.forall((h, tv) => gammaShape(sh.heads(h), tv, d - 1)) &&
          // a tracked head that is concretely ABSENT still has to be admitted by its child: this is
          // where `Shape.of({a})`'s "the path a is present" claim is checked
          sh.heads.forall((h, c) => tracked.contains(h) || gammaShape(c, SpaceValue(Set.empty), d - 1)) &&
          (sh.otherTail match
            case Some(ot) => untracked.forall((_, tv) => gammaShape(ot, tv, d - 1))
            case None => true)

  /** drop EVERY must claim from a shape, at every depth: `Must ↦ May`, `others.lo ↦ 0`.  The
   *  code's own `Shape.weaken` stops at `MaxDepth` and keeps `definitelyEmpty` nodes intact; this
   *  one is total, because γ must be. */
  def weakenAll(s: Shape): Shape = weakenAll(s, 64)
  private def weakenAll(s: Shape, d: Int): Shape =
    if d <= 0 then Shape.top
    else Shape(if s.eps == Presence.Must then Presence.May else s.eps,
               SortedMap.from(s.heads.view.mapValues(weakenAll(_, d - 1))),
               Ivl(0, s.others.hi), s.otherTail.map(weakenAll(_, d - 1)))

  /** γ for the shape, WEAK (may-only) reading. */
  def gammaShapeMay(sh: Shape, v: SpaceValue): Boolean = gammaShape(weakenAll(sh), v)

  /** γ for the reduced product — the predicate review.md 6 asks for. */
  def gamma(t: SpatialType): SpaceValue => Boolean =
    v => gammaShape(t.shape, v) && gammaSpace(t.lens, v)
  /** the may-only variant (shape Musts demoted; the histogram is unchanged) */
  def gammaMay(t: SpatialType): SpaceValue => Boolean =
    v => gammaShapeMay(t.shape, v) && gammaSpace(t.lens, v)

  // ==============================================================================================
  // 2. ABSTRACTION
  // ==============================================================================================

  /** the POINT abstraction — exactly what the analysis uses for a `Literal`. */
  def alpha(v: SpaceValue): SpatialType = SpatialType.of(v)

  /** the SET abstraction α : ℘(SpaceValue) → SpatialType, the lub of the point abstractions.  This
   *  is the α of the Galois connection; `alpha` above is its restriction to singletons.  An empty
   *  set has no least abstraction in a domain without a syntactic ⊥, so it maps to `SpaceType.empty`
   *  paired with `Shape.empty` (γ = {∅}), which is the least element that is actually representable
   *  — stated, not hidden, because it makes α(∅) NOT the true bottom. */
  def alphaSet(vs: Iterable[SpaceValue]): SpatialType =
    if vs.isEmpty then SpatialType.empty
    else vs.iterator.map(alpha).reduce(lub)

  // ==============================================================================================
  // 3. THE LATTICE JOIN  (NOT SpatialTypes.join — see the note)
  // ==============================================================================================

  /** THE LUB.  `SpatialTypes.join` is *not* this: it is the UNION TRANSFER (per class it takes
   *  `lo = max(lo_a, lo_b)` and `hi = hi_a + hi_b`, which is right for `|A ∪ B|` and wrong for a
   *  join — `γ(a) ⊄ γ(join(a,b))` whenever `lo_b > lo_a`).  The `Fixpoint` transfer's
   *  `join(t, F#(t)).within(t)` check therefore compares against a union, which is what the
   *  concrete `Fixpoint` accumulates, so the usage is coherent; but the name in
   *  docs/design_spatial_lattice.md §2 ("join/meet are the lub/glb") does not describe the code's
   *  `join`.  See `proofs/spatial-semantic/gsem_join_not_lub.smt2`. */
  def lub(a: SpatialType, b: SpatialType): SpatialType =
    SpatialType(lubShape(a.shape, b.shape), lubSpace(a.lens, b.lens))

  /** the shape lub.  There is exactly ONE implementation and it lives in the domain that owns the
   *  carrier ([[Shape.lub]]) — the `Fixpoint` transfer needs the same join this file's laws check, and
   *  two spellings of a join is how the two-orders confusion above got in in the first place.  Its
   *  channel-by-channel justification is on `Shape.lub`; the essentials: `others` takes the MAX of the
   *  two uppers and no lower bound (`U_result(V) ⊆ U_side(V)`), the ε channel becomes `May` unless the
   *  two agree, and `otherTail` must admit both sides' summaries.  `Shape.mk` re-establishes the
   *  MAY-ONLY `otherTail` invariant every transfer in SpatialShape.scala relies on
   *  (`proofs/spatial-semantic/gsem_l2_union_sound.smt2` is refuted without it: an untracked head of
   *  one operand need not be present in the other, so a Must in the summary would be attributed to a
   *  head whose tail-set is empty on that side). */
  def lubShape(a: Shape, b: Shape): Shape = Shape.lub(a, b)

  /** the histogram lub.  Only the classes tracked on BOTH sides keep exact per-class information
   *  (elsewhere one side's count is hidden inside a spill aggregate); everything else is folded
   *  into one residual bucket whose interval is derived from the two size projections. */
  def lubSpace(a: SpaceType, b: SpaceType): SpaceType =
    if a.rest.hi == 0 && b.rest.hi == 0 then
      val keys = (a.byLen.keySet ++ b.byLen.keySet).toVector
      SpatialTypes.widen(SpaceType(SortedMap.from(keys.map { l =>
        val (x, y) = (a.at(l), b.at(l)); l -> Ivl(x.lo min y.lo, x.hi max y.hi) }),
        Ivl.zero, LenBounds.empty))
    else
      val keys = (a.byLen.keySet intersect b.byLen.keySet).toVector
      val kept = keys.map { l => val (x, y) = (a.at(l), b.at(l)); l -> Ivl(x.lo min y.lo, x.hi max y.hi) }
      def outside(t: SpaceType): Ivl =
        var loK = 0L; var hiK = 0L
        for l <- keys do { val c = t.at(l); loK = Ivl.add(loK, c.lo); hiK = Ivl.add(hiK, c.hi) }
        val s = t.size
        val lo = if s.lo == Ivl.INF || hiK == Ivl.INF then 0L else Ivl.relu(s.lo - hiK)
        val hi = if s.hi == Ivl.INF then Ivl.INF else Ivl.relu(s.hi - loK)
        Ivl(lo, hi)
      val (oa, ob) = (outside(a), outside(b))
      val r = Ivl(oa.lo min ob.lo, oa.hi max ob.hi)
      def win(t: SpaceType): LenBounds =
        val ls = t.byLen.keysIterator.filter(l => !keys.contains(l) && t.at(l).hi > 0).toVector
        val lo0 = if t.rest.hi > 0 then t.restLens.lo else LenBounds.INF
        val hi0 = if t.rest.hi > 0 then t.restLens.hi else 0L
        if ls.isEmpty then LenBounds(lo0, hi0) else LenBounds(lo0 min ls.min, hi0 max ls.max)
      val (wa, wb) = (win(a), win(b))
      val w = if wa.isEmpty then wb else if wb.isEmpty then wa else LenBounds(wa.lo min wb.lo, wa.hi max wb.hi)
      if r.hi == 0 then SpatialTypes.widen(SpaceType(SortedMap.from(kept), Ivl.zero, LenBounds.empty))
      else SpatialTypes.widen(SpaceType(SortedMap.from(kept), r, if w.isEmpty then LenBounds.unknown else w))

  // ==============================================================================================
  // 4. THE ORDER
  // ==============================================================================================

  /** `leq(a, b)` ⇒ `γ(a) ⊆ γ(b)`.  This is the domain order *as γ-containment*, decided
   *  structurally: no upper-envelope shortcut, both endpoints of every class, the spill aggregate
   *  in both directions, and the shape's ε/head/`others`/`otherTail` channels.
   *
   *  It is SOUND (the implication above is what `SpatialLawCheck` checks exhaustively on a finite
   *  universe of concrete values) and INCOMPLETE: it does not attempt the integer-partition
   *  reasoning that would be needed to decide containment exactly when a spill bucket on one side
   *  faces tracked classes on the other.  `SpatialLawCheck` measures the incompleteness against
   *  [[gammaLeqOn]], which decides containment EXACTLY on a finite universe.
   *
   *  ==HOW `SpaceType.within` DIFFERS==
   *  `within` compares UPPER envelopes only (`at(l).hi ≤ that.at(l).hi`, `rest.hi ≤ that.rest.hi`)
   *  and ignores every lower bound.  So `within` is strictly weaker than `leq` and does NOT imply
   *  γ-containment: `{len 1: [0,3]}.within({len 1: [2,5]})` holds, yet the concrete value ∅ is in
   *  γ of the first and not of the second.  (`proofs/spatial/sp_gamma_order.smt2` already refutes
   *  the envelope-only reading for a single interval; `gsem_within_not_containment.smt2` restates
   *  it for the class-indexed type with a spill bucket, and `SpatialLawCheck` exhibits the concrete
   *  witness.)  `within` is used only as the `Fixpoint` post-fixpoint test, where the lower bounds
   *  are re-supplied from `init` — so what it licenses is the upper half, exactly as
   *  docs/design_spatial_lattice.md §4 says. */
  def leq(a: SpatialType, b: SpatialType): Boolean =
    leqShape(a.shape, b.shape) && leqSpace(a.lens, b.lens)

  def leqSpace(a: SpaceType, b: SpaceType): Boolean =
    val keys = (a.byLen.keySet ++ b.byLen.keySet).toVector
    val pointwise = keys.forall { l => val (x, y) = (a.at(l), b.at(l)); y.lo <= x.lo && x.hi <= y.hi }
    // every length a permits outside the tracked keys is inside b's spill window
    val windowOk =
      a.rest.hi == 0 || a.restLens.isEmpty ||
        (b.rest.hi > 0 && !b.restLens.isEmpty && b.restLens.lo <= a.restLens.lo && a.restLens.hi <= b.restLens.hi)
    // the aggregate at lengths b does NOT track
    var hiOut = if a.rest.hi > 0 then a.rest.hi else 0L
    var loOut = 0L
    for (l, c) <- a.byLen if !b.byLen.contains(l) do
      hiOut = Ivl.add(hiOut, c.hi); loOut = Ivl.add(loOut, c.lo)
    val aggOk = hiOut <= b.rest.hi && b.rest.lo <= loOut
    pointwise && windowOk && aggOk

  def leqShape(a: Shape, b: Shape): Boolean = leqShape(a, b, 32)
  private def leqShape(a: Shape, b: Shape, d: Int): Boolean =
    if d <= 0 then b.isTop
    else if b.isTop then true
    else
      val epsOk = b.eps == Presence.May || b.eps == a.eps
      val keys = a.heads.keySet ++ b.heads.keySet
      val childOk = keys.forall(h => leqShape(a.under(h), b.under(h), d - 1))
      // heads untracked in b: a's own extra tracked heads, plus a's untracked ones
      val hiOut = Ivl.add(a.heads.count((h, t) => !b.heads.contains(h) && t.possiblyNonEmpty).toLong, a.others.hi)
      val cntOk = b.others.lo == 0 && hiOut <= b.others.hi
      val tailOk = b.otherTail match
        case None => true
        case Some(bt) =>
          a.heads.forall((h, t) => b.heads.contains(h) || !t.possiblyNonEmpty || leqShape(t, bt, d - 1)) &&
            (a.others.hi == 0 || leqShape(a.otherTail.getOrElse(Shape.top), bt, d - 1))
      epsOk && childOk && cntOk && tailOk

  // ==============================================================================================
  // 5. EXACT γ-CONTAINMENT ON A FINITE UNIVERSE
  // ==============================================================================================

  /** every path over `items` of at most `maxLen` items */
  def allPaths(items: Vector[PathItem], maxLen: Int): Vector[PathValue] =
    var acc = Vector(PathValue(Nil))
    var cur = Vector(PathValue(Nil))
    for _ <- 1 to maxLen do
      cur = cur.flatMap(p => items.map(i => PathValue(p.items :+ i)))
      acc = acc ++ cur
    acc

  /** ALL space values over that path set — the finite universe on which γ-containment is DECIDED
   *  exactly (no envelope shortcut, no sampling).  `|U| = 2^|paths|`, so keep it small:
   *  `universe(Vector("a","b"), 2)` is 2^7 = 128 values. */
  def universe(items: Vector[PathItem], maxLen: Int): Vector[SpaceValue] =
    allPaths(items, maxLen).toSet.subsets().map(SpaceValue.apply).toVector

  /** EXACT γ-containment restricted to `u`: `∀ v ∈ u. v ∈ γ(a) ⇒ v ∈ γ(b)`.  A `false` here is a
   *  genuine refutation of containment; a `true` is containment *on that universe*. */
  def gammaLeqOn(u: Vector[SpaceValue])(a: SpatialType, b: SpatialType): Boolean =
    val ga = gamma(a); val gb = gamma(b)
    u.forall(v => !ga(v) || gb(v))
  def gammaLeqWitness(u: Vector[SpaceValue])(a: SpatialType, b: SpatialType): Option[SpaceValue] =
    val ga = gamma(a); val gb = gamma(b)
    u.find(v => ga(v) && !gb(v))

  // ==============================================================================================
  // 6. THE OPERATOR TABLE — one list driving the checks AND the report
  // ==============================================================================================

  /** binder names used by the binder-carrying operators.  Distinct from the operand names so a
   *  generated body can mention both. */
  val bindSym: PathRef = PathRef("h$")
  val bindRest: SpaceMention = SpaceMention("r$")
  val bindAcc: PathRef = PathRef("acc$")
  val bindRec: SpaceMention = SpaceMention("rec$")
  /** operand slots */
  val opSpaces: Vector[SpaceMention] = Vector("s$0", "s$1").map(SpaceMention.apply)
  val opPaths: Vector[PathRef] = Vector("p$0", "p$1").map(PathRef.apply)

  enum BodyKind:
    case NoBody, Iter, Fold, Fix
  /** One operator of the Space algebra: how many space operands and path operands it takes, what
   *  kind of body (if any) it binds, and how to build the node.  EVERY constructor of `Space` has a
   *  row; `SpatialLawCheck` iterates this table for the simulation squares and prints one line per
   *  row, so a new operator cannot be added to the language without showing up unchecked. */
  final case class Op(name: String, arity: Int, pathArity: Int, body: BodyKind,
                      build: (Vector[Space], Vector[Path], Space) => Space)

  private def P(i: Int)(ps: Vector[Path]): Path = ps(i)

  val ops: Vector[Op] = Vector(
    Op("Empty", 0, 0, BodyKind.NoBody, (_, _, _) => Space.Empty),
    Op("Mention", 1, 0, BodyKind.NoBody, (xs, _, _) => xs(0)),
    Op("Singleton", 0, 1, BodyKind.NoBody, (_, ps, _) => Space.Singleton(ps(0))),
    Op("Union", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Union(xs(0), xs(1))),
    Op("Intersection", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Intersection(xs(0), xs(1))),
    Op("Subtraction", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Subtraction(xs(0), xs(1))),
    Op("Restriction", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Restriction(xs(0), xs(1))),
    Op("Raffination", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Raffination(xs(0), xs(1))),
    Op("Composition", 2, 0, BodyKind.NoBody, (xs, _, _) => Space.Composition(xs(0), xs(1))),
    Op("Wrap", 1, 1, BodyKind.NoBody, (xs, ps, _) => Space.Wrap(xs(0), ps(0))),
    Op("Unwrap", 1, 1, BodyKind.NoBody, (xs, ps, _) => Space.Unwrap(xs(0), ps(0))),
    Op("TailsUnion", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.TailsUnion(xs(0))),
    Op("TailsIntersection", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.TailsIntersection(xs(0))),
    Op("Range", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.Range(xs(0), 0, 2)),
    Op("RangeNeg", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.Range(xs(0), -2, 0)),
    Op("RangeExact", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.Range(xs(0), 2, 3)),
    Op("Iteration", 1, 0, BodyKind.Iter, (xs, _, b) => Space.Iteration(xs(0), bindSym, bindRest, b)),
    Op("Fold", 1, 1, BodyKind.Fold, (xs, ps, b) =>
      Space.Fold(xs(0), ps(0), bindAcc, bindSym, bindRest, b, Path.Concat(Path.Deref(bindAcc), Path.Deref(bindSym)))),
    Op("Fixpoint", 1, 0, BodyKind.Fix, (xs, _, b) => Space.Fixpoint(xs(0), bindRec, b)),
    Op("Call", 2, 1, BodyKind.NoBody, (xs, ps, _) => Space.Call(callee, Vector(ps(0)), xs)),
    Op("GroundedPS", 0, 1, BodyKind.NoBody, (_, ps, _) => Space.GroundedPS(ps(0), groundedPS)),
    Op("GroundedSS", 1, 0, BodyKind.NoBody, (xs, _, _) => Space.GroundedSS(xs(0), groundedSS)))

  /** the callee used by the `Call` row: a fixed, deterministic two-parameter routine.  Its body is
   *  an ordinary term, so the interprocedural transfer has something to analyse. */
  val callee: RoutinePtr = RoutinePtr("gsem$callee")
  val calleeRefs: Vector[PathRef] = Vector(PathRef("q$0"))
  val calleeMentions: Vector[SpaceMention] = Vector(SpaceMention("m$0"), SpaceMention("m$1"))
  val calleeRoutine: Routine = Routine(callee, calleeRefs, calleeMentions,
    Space.Union(Space.Wrap(Space.Mention(calleeMentions(0)), Path.Deref(calleeRefs(0))),
                Space.TailsUnion(Space.Mention(calleeMentions(1)))))
  val routineTable: PartialFunction[RoutinePtr, Routine] = { case `callee` => calleeRoutine }

  /** deterministic grounded functions for the two opaque rows (compared by closure identity by the
   *  rest of the engine, so they must be stable `val`s) */
  val groundedPS: PathValue => SpaceValue =
    (p: PathValue) => SpaceValue(p.items.indices.map(i => PathValue(p.items.take(i + 1))).toSet)
  val groundedSS: SpaceValue => SpaceValue =
    (s: SpaceValue) => SpaceValue(s.paths.map(p => PathValue(p.items.reverse)))
end SpatialGamma
