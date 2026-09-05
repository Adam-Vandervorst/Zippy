package morkl

/** SPATIAL FACTS — the DERIVED layer over the existing carriers.
 *
 *  This file introduces NO new abstract domain.  Every quantity below is a projection of the two
 *  components that already exist:
 *
 *    - the length-indexed histogram [[SpaceType]] (SpatialTypes.scala) supplies `E_d`;
 *    - the bounded abstract trie [[Shape]] (SpatialShape.scala) supplies `K_d` and the per-prefix
 *      fiber envelopes;
 *    - [[SpatialType]] is the reduced product, and the two are reduced against each other AT EVERY
 *      DEPTH here (both directions — see [[SpatialFacts.degreeAt]]), which is strictly more than
 *      `SpatialType.reduce`'s single root-level cap.
 *
 *  ==THE TWO QUANTITIES==
 *  For a depth `d` and a concrete `V ∈ γ(t)`:
 *
 *    `E_d(V) = |{p ∈ V : |p| ≥ d}|`          — the paths that reach depth `d`
 *    `K_d(V) = |{take(p, d) : p ∈ V, |p| ≥ d}|` — the DISTINCT length-`d` prefixes
 *
 *  Every qualifying path lies in exactly one prefix fiber, so `0 ≤ K_d ≤ E_d` and `E_d > 0 ⇒
 *  K_d ≥ 1`.  `K_d` is exactly `ITrie.prefixCount(d)`, and `1 + Σ_{d≥1} K_d` is exactly
 *  `ITrie.nodeCount` — both identities are checked against the real trie in `SpatialFactsCheck`.
 *
 *  ==NO EVALUATION==
 *  Nothing here calls `eval`/`evalI`/`evalT`/`exec*`.  [[SpatialFacts.chainBound]] calls
 *  `SpatialTyping.infer`, which is analysis; the only concrete values this file ever produces come
 *  from a shape that already pins one down ([[SpatialFacts.exactValue]]), and that value is checked
 *  against γ rather than obtained by running anything.
 *
 *  ==CONTRADICTIONS ARE REPORTED, NOT REPAIRED==
 *  `K_d.lo > K_d.hi` after the reduction means the two components describe no common concrete value:
 *  the hand-built (or inconsistent) [[SpatialType]] is UNINHABITED.  Swapping or widening the
 *  endpoints would turn an uninhabited contract into an inhabited one, so every reducing entry point
 *  returns `Either[SpatialContradiction, _]`.  Note carefully that "the type is uninhabited" is NOT
 *  `Fact.DefinitelyEmpty` ("the space is ∅", a perfectly inhabited claim); the two are deliberately
 *  different values. */

/** The two components of a [[SpatialType]] disagree at `depth`: no concrete space satisfies both.
 *  Reported, never repaired — see the file header. */
final case class SpatialContradiction(depth: Int, prefixes: Ivl, paths: Ivl, why: String):
  def show: String = s"inconsistent spatial product at depth $depth: prefixes ${prefixes.show}, paths ${paths.show} ($why)"

/** The per-depth degree record: how many distinct prefixes of length `depth` a space admits (`K_d`),
 *  how many paths reach that depth (`E_d`), and the envelopes on the SMALLEST and LARGEST suffix
 *  fiber below one of those prefixes.  Fiber envelopes are intervals BRACKETING the concrete
 *  `min f_i` / `max f_i`, not bounds on an individual fiber; both collapse to `[0,0]` when the
 *  space may be free of qualifying paths. */
final case class DepthDegree(depth: Int, prefixes: Ivl, paths: Ivl, minFiber: Ivl, maxFiber: Ivl):
  /** exactly one prefix, so a `d`-level iteration nest has a single innermost group */
  def singlePrefix: Boolean = prefixes.lo == 1 && prefixes.hi == 1
  /** every fiber is a singleton: the suffix group is one value, which licenses an inlined body */
  def singletonFibers: Boolean = maxFiber.hi == 1 && minFiber.lo >= 1
  def show: String =
    s"d=$depth  K=${prefixes.show}  E=${paths.show}  minFiber=${minFiber.show}  maxFiber=${maxFiber.show}"

/** The whole prefix profile of one type.  `degrees(d).depth == d`.
 *
 *  `truncated` says the profile stopped at [[SpatialFacts.Config.maxProfileDepth]] rather than at a
 *  proved maximum path length: BELOW the last entry nothing is known, and the accessors say so by
 *  returning `Ivl.unknown` instead of `Ivl.zero`.  Reading a truncated profile as "no deeper
 *  prefixes" is the one way to make this record unsound, so the distinction is in the data. */
final case class PrefixProfile(degrees: Vector[DepthDegree], truncated: Boolean):
  def lastDepth: Int = degrees.length - 1
  def at(d: Int): Option[DepthDegree] = if d >= 0 && d < degrees.length then Some(degrees(d)) else None
  private def beyond: Ivl = if truncated then Ivl.unknown else Ivl.zero
  def prefixes(d: Int): Ivl = at(d).map(_.prefixes).getOrElse(beyond)
  def paths(d: Int): Ivl = at(d).map(_.paths).getOrElse(beyond)

  /** `Σ_{i=1..through} K_i` — the number of loop-frame entries a `through`-level rest-chained
   *  iterator nest performs.  This is a STRUCTURAL IDENTITY, not an estimate: each depth-`i+1`
   *  prefix has exactly one depth-`i` parent, so the frames add up over the levels. */
  def frameEntries(through: Int): Ivl = fold(through)(prefixes)
  /** `Σ_{i=1..through} E_i` — the reference evaluator's `groupMap` visits (it regroups the whole
   *  surviving path set at every level, not just the distinct prefixes). */
  def groupingVisits(through: Int): Ivl = fold(through)(paths)
  /** `Π_{i=1..through} K_i` — the per-level PRODUCT.  Provided only so a caller can see what it is
   *  being spared: it is not tight (`N²` where the truth is `2N`) and it is not even SOUND as a
   *  frame count (`K_1 = 1, K_2 = N` gives `N` where the truth is `N+1`).  Never use it as a bound. */
  def naiveProductBound(through: Int): Ivl =
    var lo = 1L; var hi = 1L
    for d <- 1 to through do
      val i = prefixes(d); lo = Ivl.mul(lo, i.lo); hi = Ivl.mul(hi, i.hi)
    Ivl(lo, hi)

  private def fold(through: Int)(f: Int => Ivl): Ivl =
    var lo = 0L; var hi = 0L
    for d <- 1 to through do
      val i = f(d); lo = Ivl.add(lo, i.lo); hi = Ivl.add(hi, i.hi)
    Ivl(lo, hi)

  def show: String = degrees.map(_.show).mkString("\n") + (if truncated then "\n  (truncated)" else "")

/** The longest prefix EVERY path of a non-empty member must start with.
 *
 *  `items` is empty when nothing is shared.  The claim is universally quantified over the paths of a
 *  member, so it is VACUOUS on `∅` — that precondition is carried in the value rather than left to
 *  the caller: `definitelyPresent` says the space is also proved non-empty, which is what a
 *  zipper pre-focus needs before it may assume the spine exists. */
final case class CommonPrefix(items: List[PathItem], definitelyPresent: Boolean):
  def path: PathValue = PathValue(items)
  def nonTrivial: Boolean = items.nonEmpty
  def show: String = s"${if items.isEmpty then "ε" else items.mkString(".")}${if definitelyPresent then " (present)" else " (vacuous on ∅)"}"

/** the candidate ADT, DERIVED AS DATA.  Nothing here is wired into a backend —
 *  that is another agent's integration surface; these are the justified candidates it can consume. */
enum SpatialSpecialization:
  /** unroll the trie/recursive traversal completely through `maxDepth`, with the per-depth fan-out
   *  the unroller needs to size its code */
  case TrieUnroll(maxDepth: Int, profile: Vector[DepthDegree])
  /** every path shares this spine: a zipper may descend to it once instead of per path */
  case ZipperPrefocus(prefix: PathValue)
  /** the type pins down exactly one concrete space, so the whole subterm folds to a constant */
  case GraphConstantFold(value: SpaceValue)
  def show: String = this match
    case TrieUnroll(d, p) => s"TrieUnroll(maxDepth=$d, ${p.size} levels)"
    case ZipperPrefocus(p) => s"ZipperPrefocus(${p.show})"
    case GraphConstantFold(v) => s"GraphConstantFold(${v.pretty})"

/** A candidate plus the reason it is licensed and the validated propositions it rests on.  The
 *  `evidence` is [[Fact]] values, not raw endpoints, so a consumer cannot re-derive a bound from an
 *  empty space (the trap `Fact` exists to close). */
final case class SpecializationCandidate(spec: SpatialSpecialization, why: String, evidence: Vector[Fact]):
  def show: String = s"${spec.show} — $why"

/** One level of a rest-chained iterator nest: the head symbol it binds and the rest-set mention. */
final case class IterLink(head: PathRef, rest: SpaceMention)

/** `Iteration(src, h₁, r₁, Iteration(r₁, h₂, r₂, … leaf))` — the shape of a full-path iterator.
 *  Recognised syntactically; the bound is computed by [[SpatialFacts.chainBound]]. */
final case class RestChain(source: Space, links: Vector[IterLink], leaf: Space):
  def depth: Int = links.size

object RestChain:
  /** peel a maximal rest-chained nest.  `None` when `s` is not an `Iteration` at all. */
  def recognize(s: Space): Option[RestChain] = s match
    case Space.Iteration(src, h, rest, body) =>
      val links = Vector.newBuilder[IterLink]
      links += IterLink(h, rest)
      var previous = rest
      var cur = body
      var peeling = true
      while peeling do
        cur match
          case Space.Iteration(Space.Mention(m), h2, rest2, body2) if m == previous =>
            links += IterLink(h2, rest2)
            previous = rest2
            cur = body2
          case _ => peeling = false
      Some(RestChain(src, links.result(), cur))
    case _ => None

  /** every space mention occurring in a term (used only by the `readsRest` guard) */
  private[morkl] def mentionsOf(s: Space): Set[SpaceMention] =
    val out = collection.mutable.Set.empty[SpaceMention]
    def go(x: Space): Unit = x match
      case Space.Mention(m) => out += m
      case _ => SizeZ3.children(x).foreach(go)
    go(s)
    out.toSet

/** The POINTWISE bound for a rest-chained iterator nest (whispers §4).  The headline numbers are
 *  `frameEntries = Σ K_i` and `leafInvocations = K_d` — never a product of per-level maxima. */
final case class ChainBound(depth: Int,
                            sourceType: SpatialType,
                            leafType: SpatialType,
                            profile: PrefixProfile,
                            leafInvocations: Ivl,
                            frameEntries: Ivl,
                            groupingVisits: Ivl,
                            naiveProductBound: Ivl,
                            resultCardinality: Ivl,
                            framesSym: Sym,
                            naiveSym: Sym):
  def show: String =
    s"chain d=$depth  leafInvocations=${leafInvocations.show}  frames=${frameEntries.show} (${framesSym.show})  " +
    s"refVisits=${groupingVisits.show}  naiveProduct=${naiveProductBound.show} (${naiveSym.show})  " +
    s"result=${resultCardinality.show}"

object SpatialFacts:
  import Lower.LenBounds

  /** ONE configuration value for every budget this file spends (the review asks for exactly
   *  that, per stage; this is the stage it can be done in without touching another file). */
  final case class Config(maxProfileDepth: Int = 64,
                          maxUnrollDepth: Int = 8,
                          maxUnrollNodes: Long = 4096L,
                          maxPrefixLength: Int = 64)
  val defaults: Config = Config()

  // ================================================================================================
  // 1.  E_d — paths that reach depth d, from the HISTOGRAM
  // ================================================================================================

  private def plus(a: Ivl, b: Ivl): Ivl = Ivl(Ivl.add(a.lo, b.lo), Ivl.add(a.hi, b.hi))
  private def divFloor(n: Long, d: Long): Long = if n == Ivl.INF then Ivl.INF else n / d
  private def ceilDiv(n: Long, d: Long): Long =
    if n == Ivl.INF then Ivl.INF else if n <= 0 then 0L else 1L + (n - 1L) / d

  /** `E_d`: the number of concrete paths with at least `d` items.
   *
   *  Tracked length classes are disjoint (the `disjoin` invariant in SpatialTypes.scala), so the
   *  classes at `len ≥ d` contribute BOTH endpoints.  The spill bucket is the load-bearing part:
   *  it counts an unknown distribution of `[rest.lo, rest.hi]` paths over the lengths in `restLens`,
   *  so it contributes
   *
   *    - nothing at all when `restLens.hi < d` (no possible rest length reaches `d`);
   *    - its FULL interval when `restLens.lo ≥ d` (every possible rest length reaches `d`);
   *    - only its UPPER endpoint otherwise.
   *
   *  Adding `rest.lo` merely because `restLens.hi ≥ d` is UNSOUND: the required rest paths may all
   *  sit in the short part of the window.  `SpatialFactsCheck` carries the counterexample
   *  (`rest = [2,2]`, `restLens = [0,3]`, `V = {ε, a}`, `d = 2`: the truth is 0, the unsound
   *  formula claims ≥ 2). */
  def pathsAtDepth(t: SpaceType, d: Int): Ivl =
    require(d >= 0, s"depth must be non-negative, got $d")
    var out = Ivl.zero
    for (len, count) <- t.byLen if len >= d do out = plus(out, count)
    val spill =
      if t.rest.hi == 0 || t.restLens.isEmpty || t.restLens.hi < d then Ivl.zero
      else if t.restLens.lo >= d then t.rest
      else Ivl(0, t.rest.hi)
    plus(out, spill)

  // ================================================================================================
  // 2.  K_d — distinct prefixes of length d, from the SHAPE
  // ================================================================================================

  /** `K_d` read off the trie alone, before the reduction against the histogram.
   *
   *  At depth 0 there is one prefix (`ε`) iff the space is non-empty.  At depth 1 every untracked
   *  head is one prefix, and channel (c) of γ brackets their number by `others`, so BOTH endpoints
   *  survive.  BELOW depth 1 `otherTail` is a PER-UNTRACKED-HEAD may-only summary: it admits each
   *  untracked head's tail-set separately, so `others.hi` heads × `perHead.hi` prefixes is a sound
   *  upper bound and there is NO positive lower bound (the summary carries no must claim — `mk`
   *  weakens it, and `Shape.under` weakens it again).
   *
   *  Reading `otherTail` as one GLOBAL tail set would understate the upper bound: with
   *  `others = [2,2]` and a summary admitting `{x}`, the value `{a.x, b.x}` has TWO distinct
   *  length-2 prefixes while the global reading allows one.  `SpatialFactsCheck` carries that
   *  regression. */
  def rawPrefixesAt(s: Shape, d: Int): Ivl =
    require(d >= 0, s"depth must be non-negative, got $d")
    if d == 0 then
      if s.definitelyEmpty then Ivl.zero
      else if s.definitelyNonEmpty then Ivl(1, 1)
      else Ivl(0, 1)
    else
      var tracked = Ivl.zero
      for (_, child) <- s.heads do tracked = plus(tracked, rawPrefixesAt(child, d - 1))
      val untracked =
        if s.others.hi == 0 then Ivl.zero
        else if d == 1 then s.others
        else
          val perHead = rawPrefixesAt(Shape.weaken(s.otherTail.getOrElse(Shape.top)), d - 1)
          Ivl(0, Ivl.mul(s.others.hi, perHead.hi))
      plus(tracked, untracked)

  /** The per-prefix fiber envelope at depth `d`, available only while the head set is CLOSED at
   *  every level above `d`: then the depth-`d` nodes are exactly the possible prefixes, and each
   *  node's implied cardinality is exactly its fiber's size (every path in a depth-`d` subtree has
   *  at least `d` items).  `Some(Vector((size, mustBePresent)))`, or `None` once an open head set
   *  makes the node set unenumerable. */
  private def closedFibers(s: Shape, d: Int): Option[Vector[(Ivl, Boolean)]] =
    if s.definitelyEmpty then Some(Vector.empty)
    else if d == 0 then Some(Vector((s.size, s.definitelyNonEmpty)))
    else if !s.headsClosed then None
    else
      val out = Vector.newBuilder[(Ivl, Boolean)]
      var ok = true
      for (_, c) <- s.heads if ok do
        closedFibers(c, d - 1) match
          case Some(v) => out ++= v
          case None => ok = false
      if ok then Some(out.result()) else None

  /** what the shape says about `E_d` and about the fiber extremes, when [[closedFibers]] applies */
  private final case class FiberEnvelope(eLo: Long, eHi: Long, minHi: Long, maxLo: Long, maxHi: Long)
  private val openEnvelope = FiberEnvelope(0L, Ivl.INF, Ivl.INF, 0L, Ivl.INF)
  private def fiberEnvelope(s: Shape, d: Int): FiberEnvelope =
    closedFibers(s, d) match
      case None => openEnvelope
      case Some(fs) =>
        var eLo = 0L; var eHi = 0L
        var minHi = Ivl.INF; var maxLo = 0L; var maxHi = 0L
        for (sz, must) <- fs do
          eHi = Ivl.add(eHi, sz.hi)
          maxHi = maxHi max sz.hi
          if must then
            eLo = Ivl.add(eLo, sz.lo)
            // a definitely-present fiber bounds the minimum from above and the maximum from below
            minHi = minHi min sz.hi
            maxLo = maxLo max sz.lo
        FiberEnvelope(eLo, eHi, minHi, maxLo, maxHi)

  // ================================================================================================
  // 3.  THE REDUCTION — both directions, at every depth
  // ================================================================================================

  /** `K_d`, reduced against `E_d`.
   *
   *  `K_d ≤ E_d` (fibers are disjoint and non-empty) and `E_d > 0 ⇒ K_d ≥ 1`.  A `Left` means the
   *  two components describe no common concrete value; it is never repaired. */
  def prefixesAt(t: SpatialType, d: Int): Either[SpatialContradiction, Ivl] =
    degreeAt(t, d).map(_.prefixes)

  /** `E_d`, reduced against the shape.  The histogram's own answer, met with `Σ` of the closed
   *  fiber envelope and raised by `K_d`'s lower bound (each prefix carries at least one path). */
  def pathsAt(t: SpatialType, d: Int): Either[SpatialContradiction, Ivl] =
    degreeAt(t, d).map(_.paths)

  /** THE reduced per-depth record.  Every direction of the reduction, spelled out:
   *
   *    E.lo ← max(E.lo, Σ must-present fiber lows, K_raw.lo)   shape ⇒ histogram, and K ≤ E
   *    E.hi ← min(E.hi, Σ all fiber highs)                     shape ⇒ histogram
   *    K.lo ← max(K_raw.lo, [E.lo > 0])                        histogram ⇒ shape
   *    K.hi ← min(K_raw.hi, E.hi)                              K ≤ E
   *
   *  followed by the pigeonhole fiber envelopes, met with whatever the closed shape knows directly.
   *  This is PER DEPTH, which is what makes it worth doing separately from `SpatialType.reduce`:
   *  the reducer works on the whole-type projections (total count, length hull, ε, level shape),
   *  while a disagreement about how many paths reach depth `d` — and about how they are distributed
   *  over the depth-`d` prefixes — is only visible once `d` is fixed.  The depth-2 case in
   *  `SpatialFactsCheck` is exactly that: both projections agree, the depth-2 degree does not. */
  def degreeAt(t: SpatialType, d: Int): Either[SpatialContradiction, DepthDegree] =
    require(d >= 0, s"depth must be non-negative, got $d")
    val e0 = pathsAtDepth(t.lens, d)
    val k0 = rawPrefixesAt(t.shape, d)
    val env = fiberEnvelope(t.shape, d)

    val e = Ivl((e0.lo max env.eLo) max k0.lo, e0.hi min env.eHi)
    if e.lo > e.hi then
      return Left(SpatialContradiction(d, k0, e0,
        s"paths-at-depth brackets cross after reduction: ${e.show}"))
    val k = Ivl(k0.lo max (if e.lo > 0 then 1L else 0L), k0.hi min e.hi)
    if k.lo > k.hi then
      return Left(SpatialContradiction(d, k0, e0,
        s"prefix brackets cross after reduction: ${k.show}"))

    // ---- fiber envelopes.  f_1..f_K are the POSITIVE fiber sizes with Σ f_i = E.
    //   minFiber ≥ 1                        (a fiber is non-empty by construction)
    //   minFiber ≤ ⌊E / K⌋ ≤ ⌊E.hi / max(1, K.lo)⌋      (the minimum is at most the average)
    //   maxFiber ≥ ⌈E / K⌉ ≥ ⌈E.lo / K.hi⌉              (the maximum is at least the average)
    //   maxFiber ≤ E − K + 1 ≤ E.hi − max(1, K.lo) + 1  (every other fiber holds at least one path)
    val kLo1 = k.lo max 1L
    val minLo = if k.lo >= 1 then 1L else 0L
    val pigeonMinHi = if e.hi == 0 then 0L else divFloor(e.hi, kLo1)
    val pigeonMaxLo =
      if e.lo == 0 then 0L
      else if k.hi == Ivl.INF then 1L
      else ceilDiv(e.lo, k.hi max 1L) max 1L
    val pigeonMaxHi = if e.hi == 0 then 0L else if e.hi == Ivl.INF then Ivl.INF else e.hi - kLo1 + 1L

    val maxHi = if e.hi == 0 then 0L else pigeonMaxHi min env.maxHi
    val maxLo = if e.hi == 0 then 0L else pigeonMaxLo max env.maxLo
    val minHi = if e.hi == 0 then 0L else (pigeonMinHi min env.minHi) min maxHi
    // Crossed fiber envelopes are the same kind of evidence as crossed prefix counts: both endpoints
    // bracket the same concrete quantity, so an empty meet proves there is no such quantity.  Widening
    // the interval here would hide it, which is exactly what must not happen.
    if maxLo > maxHi then
      return Left(SpatialContradiction(d, k, e, s"largest-fiber brackets cross: [$maxLo, $maxHi]"))
    if minLo > minHi then
      return Left(SpatialContradiction(d, k, e, s"smallest-fiber brackets cross: [$minLo, $minHi]"))
    Right(DepthDegree(d, k, e, Ivl(minLo, minHi), Ivl(maxLo, maxHi)))

  /** the first depth at which the two components contradict each other, if any.  A `Some` PROVES
   *  the type uninhabited (`γ(t) = ∅`) given that both components are individually sound — which
   *  makes this a live soundness probe on the existing transfers, not only an input validator. */
  def contradiction(t: SpatialType, cfg: Config = defaults): Option[SpatialContradiction] =
    profile(t, cfg).left.toOption

  /** the depth range the profile and the contradiction scan cover: the MAX of the two components'
   *  length hulls, NOT their meet.  A disagreement typically lives at a depth the meet has already
   *  excluded — the shape proves there is no length-2 prefix while the histogram insists on a
   *  length-3 path, so `t.len` is the crossed interval `[3,1]` and a meet-driven scan stops at 1,
   *  one depth short of the contradiction. */
  private def scanDepth(t: SpatialType, cfg: Config): Int =
    def hullHi(b: LenBounds): Long = if b.isEmpty then 0L else b.hi
    val hi = hullHi(t.lens.len) max hullHi(t.shape.lens)
    if hi == LenBounds.INF then cfg.maxProfileDepth else (hi min cfg.maxProfileDepth.toLong).toInt

  /** the whole profile, `d = 0 .. min(maxPathLength, cfg.maxProfileDepth)`.  A provably empty space
   *  yields the single honest entry `K_0 = E_0 = [0,0]` rather than an empty vector, so a consumer
   *  reading `degrees(0)` never has to special-case it. */
  def profile(t: SpatialType, cfg: Config = defaults): Either[SpatialContradiction, PrefixProfile] =
    val last = scanDepth(t, cfg)
    val out = Vector.newBuilder[DepthDegree]
    var d = 0
    while d <= last do
      degreeAt(t, d) match
        case Left(c) => return Left(c)
        case Right(g) => out += g
      d += 1
    // truncation is decided by the REDUCED maximum path length: past it there provably are no
    // prefixes, so a profile that reaches it is complete even when one component alone said ∞.
    val reduced = t.len
    val truncated = !reduced.isEmpty && (reduced.hi == LenBounds.INF || reduced.hi > last)
    Right(PrefixProfile(out.result(), truncated))

  /** Logical `ITrie` nodes, including the always-present root: `nodes = 1 + Σ_{d≥1} K_d`.  That is
   *  an EXACT identity for a concrete trie (checked against `ITrie.nodeCount`), so this replaces the
   *  cost model's `Meas.nodes = size * len` — which throws away every bit of prefix sharing —
   *  whenever a `SpatialType` is available.  `size * len + 1` remains the fallback upper when the
   *  profile is truncated. */
  def trieNodes(t: SpatialType, cfg: Config = defaults): Either[SpatialContradiction, Ivl] =
    profile(t, cfg).map { p =>
      if t.isProvablyEmpty then Ivl(1, 1)   // ITrie.empty is one root object
      else
        val known = p.frameEntries(p.lastDepth)
        val lo = Ivl.add(1L, known.lo)
        val hi =
          if !p.truncated then Ivl.add(1L, known.hi)
          else if t.len.hi == LenBounds.INF then Ivl.INF
          else Ivl.add(1L, Ivl.mul(t.size.hi, t.len.hi))
        Ivl(lo, hi max lo)
    }

  /** THE NODES THAT HAVE AT LEAST ONE CHILD — `I = Σ_{d≥0} I_d`, where `I_d` is the number of
   *  distinct depth-`d` prefixes that some path STRICTLY extends.
   *
   *  WHY IT IS A DIFFERENT QUANTITY FROM [[trieNodes]], AND WHY IT NEEDS ITS OWN LOWER ENDPOINT.
   *  `ITrie.compositionR` calls the one allocation site `ITrie.node` at exactly the nodes of its LEFT
   *  operand that fall through both `{ε}` fast paths, i.e. at exactly the nodes with a child: a LEAF
   *  terminal takes `rIdent(RIGHT)` and grafts `b` by pointer without allocating anything.  `N(a)`
   *  over-counts that set by the leaf count, and on a full-width fixture the leaves ARE almost the
   *  whole trie (64 of 73), so `N(a)` is not merely loose — it is not a lower bound on the allocation
   *  at all.  This is the count that is.
   *
   *  ==THE LOWER ENDPOINT (LESSON 9: every input here is read in the direction that weakens it)==
   *  Write `L_d` for the depth-`d` LEAVES.  A leaf at depth `d` is a path of length EXACTLY `d`
   *  (a node with no child that is not terminal cannot exist in a trie: it holds nothing), and the
   *  paths of length exactly `d` are `E_d − E_{d+1}`, so `L_d ≤ E_d − E_{d+1}`.  Every depth-`d`
   *  prefix is a leaf or an interior node, so
   *
   *      I_d = K_d − L_d ≥ K_d − (E_d − E_{d+1}) ≥ K_d.lo − E_d.hi + E_{d+1}.lo
   *
   *  — `K_d` read at its LOW end, `E_d` at its HIGH end and `E_{d+1}` at its LOW end, which is the
   *  only reading of the three that is sound simultaneously for one concrete member.  Clamped at 0 per
   *  depth (a negative term is no information, not a credit against another level) and skipped
   *  entirely when `E_d.hi` is `∞`.
   *
   *  ==THE UPPER ENDPOINT==  `I_d ≤ K_d` (an interior node is a prefix) and `I_d ≤ K_{d+1}` (distinct
   *  interior nodes own disjoint, non-empty sets of depth-`d+1` child prefixes), so `I_d ≤ min` of the
   *  two.  Past a TRUNCATED profile `prefixes` answers `Ivl.unknown`, so the min degrades to `K_d.hi`
   *  and nothing unsound is read into the tail.
   *
   *  The empty space has no node with a child, hence `[0,0]` — NOT the `[1,1]` of [[trieNodes]], whose
   *  one node is the childless root. */
  def interiorNodes(t: SpatialType, cfg: Config = defaults): Either[SpatialContradiction, Ivl] =
    profile(t, cfg).map { p =>
      if t.isProvablyEmpty then Ivl(0, 0)
      else
        var lo = 0L
        var hi = 0L
        var d = 0
        while d <= p.lastDepth do
          val k = p.prefixes(d)
          val e = p.paths(d)
          val eNext = p.paths(d + 1)
          val kNext = p.prefixes(d + 1)
          hi = Ivl.add(hi, k.hi min kNext.hi)
          if e.hi < Ivl.INF then
            val leavesHi = e.hi - (eNext.lo min e.hi)          // >= L_d, and never negative
            if k.lo > leavesHi then lo = Ivl.add(lo, k.lo - leavesHi)
          d += 1
        Ivl(lo, hi max lo)
    }

  // ================================================================================================
  // 4.  COMMON PREFIXES AND SAFE EXTRACTION
  // ================================================================================================

  /** The longest constant prefix every path of a non-empty member must start with.
   *
   *  A level extends the prefix exactly when `ε` is impossible there (no path ends at this node),
   *  the head set is CLOSED (no untracked head could differ), and exactly one tracked head may be
   *  live.  All three are may-channel facts, so the conclusion is a ∀-path MAY fact and is vacuous
   *  on `∅` — hence [[CommonPrefix.definitelyPresent]], which adds the must-non-emptiness a zipper
   *  pre-focus needs before assuming the spine exists. */
  def commonPrefix(t: SpatialType, cfg: Config = defaults): CommonPrefix =
    val out = List.newBuilder[PathItem]
    var cur = t.shape
    var steps = 0
    var done = t.isProvablyEmpty
    while !done && steps < cfg.maxPrefixLength do
      val live = cur.heads.iterator.filter(_._2.possiblyNonEmpty).toVector
      if cur.eps != Presence.No || !cur.headsClosed || live.size != 1 then done = true
      else
        out += live.head._1
        cur = live.head._2
        steps += 1
    val items = out.result()
    CommonPrefix(items, definitelyPresent = items.nonEmpty && t.size.lo >= 1)

  /** the dead promise, discharged from the outside: `Fact.PrefixAbsent` is public
   *  but `Fact.from` cannot emit it (a prefix has to be SUPPLIED).  This is the query that can. */
  def prefixAbsent(t: SpatialType, prefix: List[PathItem]): Option[Fact] =
    if t.isProvablyEmpty || !t.shape.mayHavePrefix(prefix) then Some(Fact.PrefixAbsent(prefix)) else None

  /** may some path start with `prefix`?  `false` is a PROOF of absence (the negation of the above). */
  def mayHavePrefix(t: SpatialType, prefix: List[PathItem]): Boolean = prefixAbsent(t, prefix).isEmpty

  /** Is `items` successive item-extractions safe on EVERY path of this space?
   *
   *  Cardinality and path length are deliberately separate: `MinimumCardinality(3)` says three paths
   *  exist, `AllPathsHaveAtLeast(3)` says each path supports three extractions, and only the latter
   *  removes three item-existence checks.  The `size.lo ≥ 1` conjunct is what stops `len.lo` on the
   *  empty space (`LenBounds.empty.lo == INF`) from "proving" any number of extractions. */
  def canExtractEveryPath(t: SpatialType, items: Long): Boolean =
    items >= 0 && t.size.lo >= 1 && !t.len.isEmpty && t.len.lo >= items

  // ================================================================================================
  // 5.  EXACT VALUES  (the requirement: "exact paths at known positions where available")
  // ================================================================================================

  /** The single concrete space this type admits, when the shape pins one down: every level has a
   *  decided `ε`, a closed head set, and a definitely-present, itself-exact child under every
   *  tracked head.  The candidate is then checked against FULL γ-membership, so a histogram that
   *  disagrees yields `None` rather than a value outside the type. */
  def exactValue(t: SpatialType): Option[SpaceValue] =
    shapeExact(t.shape, Shape.MaxDepth + 8)
      .map(ps => SpaceValue(ps))
      .filter(v => SpatialTyping.gammaMember(v, t))

  private def shapeExact(s: Shape, budget: Int): Option[Set[PathValue]] =
    if s.definitelyEmpty then Some(Set.empty)
    else if budget <= 0 || s.others.hi != 0 then None
    else
      val base = s.eps match
        case Presence.Must => Some(Set(PathValue(Nil)))
        case Presence.No => Some(Set.empty[PathValue])
        case Presence.May => None
      base.flatMap { b =>
        var acc = b
        var ok = true
        for (h, c) <- s.heads if ok do
          if !c.definitelyNonEmpty then ok = false
          else
            shapeExact(c, budget - 1) match
              case Some(ts) if ts.nonEmpty => acc = acc ++ ts.map(x => PathValue(h :: x.items))
              case _ => ok = false
        if ok then Some(acc) else None
      }

  // ================================================================================================
  // 6.  POINTWISE BOUNDS FOR NESTED ITERATORS  (whispers §4)
  // ================================================================================================

  /** The pointwise bound for a recognised rest-chain.
   *
   *  Requires (a) an EXACT full path length equal to the nest depth — otherwise a shorter path is
   *  exhausted early and the leaf is not a per-source-path map — and (b) that the leaf reads none of
   *  the chain's rest mentions, because a leaf that reads an outer rest set AGGREGATES siblings and
   *  is then not pointwise at all.  Head refs are fine: on a full-length chain they name the items
   *  of the one source path, so the leaf is analysed with them opaque at length 1.
   *
   *  The symbolic pair is the headline: `frames = d·N` (degree 1) against the per-level product
   *  `N^d` (degree `d`), because `K_i ≤ E_i ≤ N` at every level and `K_d = N` exactly when every
   *  path has length `d`. */
  def chainBound(chain: RestChain, env: SpatialTyping.Env, n: Sym = Sym.v("N"),
                 cfg: Config = defaults): Either[String, ChainBound] =
    val d = chain.depth
    if d < 1 then Left("not an iterator nest")
    else
      val sourceT = SpatialTyping.infer(chain.source, env)
      val ln = sourceT.len
      if ln.isEmpty || ln.lo != d.toLong || ln.hi != d.toLong then
        Left(s"source path length ${ln.lo}..${ln.hi} is not exactly the nest depth $d")
      else if RestChain.mentionsOf(chain.leaf).exists(chain.links.map(_.rest).toSet) then
        Left("the leaf reads a rest set of the chain, so it aggregates siblings and is not pointwise")
      else
        val leafEnv = env.copy(paths = env.paths -- chain.links.map(_.head),
                               opaque = env.opaque ++ chain.links.map(_.head -> LenBounds(1, 1)))
        val leafT = SpatialTyping.infer(chain.leaf, leafEnv)
        profile(sourceT, cfg) match
          case Left(c) => Left(c.show)
          case Right(p) =>
            val leafInv = p.prefixes(d)
            // Union collapses outputs from different source paths, so positivity is the only generic
            // lower bound; an injectivity law (see PatternImage) may strengthen it separately.
            val lo = if sourceT.size.lo >= 1 && leafT.size.lo >= 1 then 1L else 0L
            val hi = Ivl.mul(leafInv.hi, leafT.size.hi)
            Right(ChainBound(d, sourceT, leafT, p, leafInv,
                             p.frameEntries(d), p.groupingVisits(d), p.naiveProductBound(d),
                             Ivl(lo, hi), Sym.c(d.toLong) * n, n ** Sym.c(d.toLong)))

  // ================================================================================================
  // 7.  SPECIALIZATION CANDIDATES
  // ================================================================================================

  /** Derive the backend-facing candidates this type licenses.  DATA only: nothing here rewrites a
   *  term, chooses a backend, or touches the lowering pipeline. */
  def specializations(t: SpatialType, cfg: Config = defaults): Vector[SpecializationCandidate] =
    val out = Vector.newBuilder[SpecializationCandidate]
    val evidence = Fact.from(t)

    exactValue(t).foreach { v =>
      out += SpecializationCandidate(SpatialSpecialization.GraphConstantFold(v),
        s"the shape pins down exactly one space (${v.paths.size} paths) and γ-membership confirms it",
        evidence)
    }

    val cp = commonPrefix(t, cfg)
    if cp.nonTrivial then
      out += SpecializationCandidate(SpatialSpecialization.ZipperPrefocus(cp.path),
        s"every path starts with ${cp.show}; descend the spine once instead of per path",
        evidence)

    val ln = t.len
    if !ln.isEmpty && ln.hi != LenBounds.INF && ln.hi <= cfg.maxUnrollDepth then
      profile(t, cfg).foreach { p =>
        val nodes = Ivl.add(1L, p.frameEntries(p.lastDepth).hi)
        if !p.truncated && nodes <= cfg.maxUnrollNodes then
          // only the levels a path can actually reach: the scan may run past the reduced maximum
          // length, and an unroller has no business emitting code for provably empty levels
          out += SpecializationCandidate(
            SpatialSpecialization.TrieUnroll(ln.hi.toInt, p.degrees.take(ln.hi.toInt + 1)),
            s"maximum path length ${ln.hi} with at most $nodes logical trie nodes: the traversal unrolls completely",
            evidence)
      }
    out.result()

end SpatialFacts

// ==================================================================================================
// CORRELATED PATH SHAPES  (whispers §5) — a REFINEMENT OVERLAY, not a replacement for Shape
// ==================================================================================================

/** `Shape` cannot say that an output item is `x + 1` where `x` is an extracted input coordinate:
 *  `PathItem` is a `String` and putting arithmetic in it would change the carrier.  This overlay
 *  says it alongside, as a set of SUBSTITUTIONS.  Erasing the overlay must always leave the
 *  ordinary `SpatialType` sound — nothing here participates in γ.
 *
 *  The hard part is the difference between "different for the same input" and "globally disjoint
 *  images".  `x` and `x + 1` differ under every fixed binding, but their images collide between
 *  adjacent inputs, so only the STRONGER relation licenses multiplying lower cardinalities. */
enum ItemPattern:
  case Constant(value: PathItem)
  /** rendered as a length-prefixed namespace plus the affine integer value */
  case AffineInt(namespace: String, variable: String, offset: Int, minimum: Int, maximum: Int)
  case Unknown(label: String)

object ItemPattern:
  // Length-prefixing keeps two namespaces disjoint even when one textually prefixes the other.
  private def prefix(namespace: String): String = s"${namespace.length}:$namespace:"
  def encode(namespace: String, value: Long): PathItem = prefix(namespace) + value.toString
  def decode(namespace: String, value: PathItem): Option[Long] =
    val p = prefix(namespace)
    if value.startsWith(p) then value.drop(p.length).toLongOption else None

  private def satWidth(lo: Int, hi: Int): Long = if hi < lo then 0L else Ivl.add(hi.toLong - lo.toLong, 1L)

  def choices(p: ItemPattern): Long = p match
    case Constant(_) => 1L
    case AffineInt(_, _, _, lo, hi) => satWidth(lo, hi)
    case Unknown(_) => Ivl.INF

  def instantiate(p: ItemPattern, env: Map[String, Int]): Option[PathItem] = p match
    case Constant(v) => Some(v)
    case AffineInt(ns, x, off, lo, hi) =>
      env.get(x).filter(v => lo <= v && v <= hi).map(v => encode(ns, v.toLong + off.toLong))
    case Unknown(_) => None

  private def imageInterval(p: ItemPattern): Option[(String, Long, Long)] = p match
    case AffineInt(ns, _, off, lo, hi) => Some((ns, lo.toLong + off.toLong, hi.toLong + off.toLong))
    case _ => None

  /** the two sets of possible rendered items cannot overlap under ANY bindings */
  def globallyDisjoint(a: ItemPattern, b: ItemPattern): Boolean = (a, b) match
    case (Constant(x), Constant(y)) => x != y
    case _ => (imageInterval(a), imageInterval(b)) match
      case (Some((na, alo, ahi)), Some((nb, blo, bhi))) => na != nb || ahi < blo || bhi < alo
      case (Some((ns, lo, hi)), None) => b match
        case Constant(v) => decode(ns, v).forall(k => k < lo || k > hi)
        case _ => false
      case (None, Some(_)) => globallyDisjoint(b, a)
      case _ => false

  /** different whenever both are evaluated under the SAME variable binding — strictly weaker than
   *  [[globallyDisjoint]], and the two must never be exchanged */
  def differentAtSameBinding(a: ItemPattern, b: ItemPattern): Boolean = (a, b) match
    case (AffineInt(na, xa, oa, _, _), AffineInt(nb, xb, ob, _, _)) if na == nb && xa == xb && oa != ob => true
    case _ => globallyDisjoint(a, b)

final case class PathPattern(items: Vector[ItemPattern]):
  def instantiate(env: Map[String, Int]): Option[PathValue] =
    val xs = items.map(ItemPattern.instantiate(_, env))
    if xs.forall(_.nonEmpty) then Some(PathValue(xs.flatten.toList)) else None

  /** equality of output paths implies equality of every key variable (each appears in some position,
   *  and `ItemPattern.encode` is injective in `(namespace, value)`) */
  def injectiveIn(keyVariables: Set[String]): Boolean =
    keyVariables.forall { x =>
      items.exists {
        case ItemPattern.AffineInt(_, `x`, _, _, _) => true
        case _ => false
      }
    }

  /** one globally-disjoint coordinate proves the two path images globally disjoint */
  def globallyDisjoint(that: PathPattern): Boolean =
    items.size != that.items.size ||
      items.indices.exists(i => ItemPattern.globallyDisjoint(items(i), that.items(i)))

/** a cardinality plus the alternative path patterns a position may emit */
final case class PatternStratum(cardinality: Ivl, alternatives: Vector[PathPattern]):
  /** a sound distinct-head upper bound: overlaps between alternatives only make it smaller */
  def headGroupsUpper: Long =
    val choices = alternatives.foldLeft(0L) { (n, p) =>
      Ivl.add(n, p.items.headOption.map(ItemPattern.choices).getOrElse(0L))
    }
    cardinality.hi min choices

object PatternImage:
  /** `q` pointwise output alternatives for every one of `inputs` inputs.
   *
   *  The upper bound is always `q·N`.  The LOWER bound `q·N` needs BOTH proofs: pairwise global
   *  disjointness of the alternatives (no collision within one input) and injectivity in a key that
   *  identifies the input (no collision between inputs).  An empty key set is accepted only when
   *  there is at most one input. */
  def cardinality(inputs: Ivl, inputKeyVariables: Set[String], outputs: Vector[PathPattern]): Ivl =
    val q = outputs.size.toLong
    val hi = Ivl.mul(inputs.hi, q)
    val perInputDistinct =
      outputs.indices.forall(i => outputs.indices.forall(j => i >= j || outputs(i).globallyDisjoint(outputs(j))))
    val crossInputDistinct =
      inputs.hi <= 1 || (inputKeyVariables.nonEmpty && outputs.forall(_.injectiveIn(inputKeyVariables)))
    if perInputDistinct && crossInputDistinct then Ivl(Ivl.mul(inputs.lo, q), hi)
    else Ivl(if inputs.lo > 0 && q > 0 then 1L else 0L, hi)
