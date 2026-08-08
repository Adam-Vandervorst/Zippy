package morkl

/** ==============================================================================================
 *  RELATIONAL FRONTIER COST — review.md item 2.
 *
 *  `SpatialCost`'s merge bounds are SIZE-ONLY: `merge2(a,b) = 3(N(a)+N(b))` for `touch` and
 *  `tighter(N(a),N(b))` for `alloc`.  Both discard the control state of the persistent algorithms.
 *  The `touch` one is not merely loose, it has the WRONG SLOPE: it is linear in the operand that the
 *  algorithm never descends into.  Restriction of a million-node space by one length-`d` prefix is
 *  `Θ(d)` and the size-only model calls it `Θ(10^6)`.  `min(N(L),N(R))` is a ceiling on the number of
 *  paired logical nodes, not the parameter itself.
 *
 *  ==THE PARAMETER==
 *  For restriction review.md defines it exactly; this file generalises it to the whole ring.  Write
 *  `X_u` for the subtrie of `X` at prefix `u` (present iff some `X`-path starts with `u`):
 *
 *  {{{
 *  Q(X,Y) = { u | X_u and Y_u both exist, and — for the PRUNED ops — no proper prefix v of u
 *                 has terminal(Y_v) }                          the PAIRED-PREFIX FRONTIER
 *  A(X,Y) = { u in Q(X,Y) | terminal(Y_u) is false }           the ACTIVE frontier
 *  T(X,Y) = Q(X,Y) \ A(X,Y)                                    the TERMINAL-PREFIX ACCEPTS
 *  J(X,Y) = Patricia nodes visited matching the child maps at the nodes of A(X,Y)
 *  }}}
 *
 *  Every ring operation performs `Θ(|Q| + J)` counted descents and allocates one fresh node per
 *  element of its rebuild frontier (`|A|` for the pruned ops, `|Q|` for the merges).  Branches
 *  present on only one side are attached, kept or rejected BY POINTER and are never visited; a
 *  terminal prefix accepts `X_u` whole.  Hence, and these are the claims the suite asserts:
 *
 *    - restriction by `{ε}` is CONSTANT with zero allocation (`|Q| = 1`, `A = ∅`, `J = 0`);
 *    - restriction by one present prefix of length `d` is `Θ(d)` with a `d`-node spine, INDEPENDENT
 *      of the millions of nodes below the matched prefix;
 *    - a head-disjoint intersection/restriction rejects at the root;
 *    - `{ε}·B` is constant and returns `B` by pointer;
 *    - two occurrences of the SAME node are the `same` case: constant, zero allocation.
 *
 *  ==WHERE THE NUMBERS COME FROM==
 *  Three sources, met against each other, weakest last:
 *
 *   1. EXACT VALUES.  When `SpatialFacts.exactValue` pins both operands, the algebraic result case is
 *      computed by set arithmetic on the two concrete values — no bound, the answer.
 *   2. THE PREFIX PROFILES (`SpatialFacts.profile`: `K_d` distinct depth-`d` prefixes, `E_d` paths
 *      reaching depth `d`).  A paired depth-`d` prefix is a depth-`d` prefix of BOTH operands, so
 *      `|Q_d| ≤ min(K_d(X), K_d(Y))` — a MINIMUM, at every depth, which is where the slope comes
 *      from.  Terminal depth-`d` prefixes of `Y` are exactly its length-`d` paths, `E_d − E_{d+1}`,
 *      so `|A_d| ≤ min(K_d(X), K_d(Y) − (E_d − E_{d+1}))` and `|T_d| ≤ min(K_d(X), E_d − E_{d+1})`.
 *      This is depth-indexed and reaches `SpatialFacts.Config.maxProfileDepth`, so it sees prefixes
 *      far below the shape domain's four tracked levels.
 *   3. THE RELATIONAL SHAPE WALK.  A simultaneous descent of the two `Shape`s, carrying a
 *      multiplicity interval per reachable shape-pair.  This is the only source that can see
 *      DISJOINTNESS (a head tracked on one side and provably absent on the other kills the whole
 *      pair, and with it every deeper pair) and MUST-terminality (`Presence.Must` on the right
 *      proves an accept and prunes).  It is exact where the shapes are exact and closed.
 *
 *  The coarse size ceiling survives ONLY as the last resort, and when it is used
 *  [[FrontierSummary.fallback]] says so, so a consumer can tell a real frontier bound from a
 *  fallback.  [[FrontierSummary.syms]] hands a symbolic consumer the min-gated form rather than the
 *  `merge2` sum even in the fallback case, because `min` is the structurally licensed combination.
 *
 *  ==WHICH PROGRAM IS BEING PRICED==
 *  The case-returning persistent algebra — `Trie.unionR`/`intersectionR`/`subtractionR`/
 *  `restrictionR`/`raffinationR`/`compositionR` (Trie.scala:159-365), the algebra review.md item 1
 *  calls the one that matters — and the interned `ITrie`/`IntTrieOps` descent that implements the same
 *  frontier over Patricia child maps.  The two differ by an ADDITIVE CONSTANT PER OPERATION:
 *  `ITrie.union` allocates its root node even when the case-returning form returns `Identity`, so
 *  where this file reports `rebuilt = 0` the interned form allocates 1.  [[FrontierConfig.interned]]
 *  switches that constant on.  Cost estimates belong on the OPTIMIZED program (the user's third
 *  steer): [[SpatialFrontier.summarize]] is meant to be run over `Routine.optimized`'s body, whose
 *  spatial hook has already replaced proved-empty occurrences by `Space.Empty` and pinned occurrences
 *  by their `Literal` — which is exactly what turns the generic four-case answer into a named
 *  whole-subtree case here.
 *
 *  ==NO EVALUATION==
 *  Nothing here calls `eval`/`evalI`/`evalT`/`exec*`.  Every number comes from the decorated
 *  analysis' per-node `SpatialType`s, from `SpatialFacts`' profile/exact-value queries, and from the
 *  structural laws documented on `Trie.AlgebraicResult`.  The exact-value branch does SET ARITHMETIC
 *  on values `SpatialFacts.exactValue` already produced from a shape — the same standing that
 *  `SpatialFacts.exactValue` itself has, and no trie is ever built or run.
 *  ============================================================================================== */

/** The per-node outcome of a ring operation RELATIVE to its operands — the analysis-side mirror of
 *  `Trie.AlgebraicResult` (Trie.scala:129-132).  A summary carries the SET of cases that may hold;
 *  `{Left}` alone is a proof that the result IS the left operand, hence zero allocation and no
 *  rebuild anywhere above it (identity propagation).  `{Left, Right}` is `Identity(BOTH)`: the two
 *  operands denote the same set.  `Empty` takes precedence over identity when everything is empty,
 *  the ring.rs convention `Trie` follows. */
enum FrontierCase:
  case Empty, Left, Right, Bespoke
  def show: String = this match
    case Empty => "∅"
    case Left => "=L"
    case Right => "=R"
    case Bespoke => "fresh"

object FrontierCase:
  val all: Vector[FrontierCase] = Vector(Empty, Left, Right, Bespoke)
  val any: Set[FrontierCase] = all.toSet
  def show(cs: Set[FrontierCase]): String =
    if cs.isEmpty then "⊥" else all.iterator.filter(cs.contains).map(_.show).mkString("|")
  /** does this case set PROVE the result is an operand (or empty), i.e. nothing is rebuilt? */
  def isIdentity(cs: Set[FrontierCase]): Boolean = cs.nonEmpty && !cs.contains(Bespoke)

/** Which side gates the Patricia descent.  `Symmetric`: either child map may be the small one and
 *  the merge follows it (`unionTries`/`intersectTries` keep the other side's subtree by pointer on a
 *  prefix mismatch).  `RightGated`: only the right operand's keys are ever searched for, so the
 *  visit count is independent of the left fan-out (`restrictTries`, `diffTries`). */
enum FrontierGate:
  case Symmetric, RightGated

/** THE PER-OPERATION FRONTIER RULES — review.md item 2's table, encoded.  `frontier` names the
 *  quantity that actually controls the work and `wholeSubtree` names the case the size-only bound
 *  loses. */
enum FrontierOp:
  case Union, Intersection, Subtraction, Restriction, Raffination, Composition, FixpointUnion

  def frontier: String = this match
    case Union => "common-prefix / Patricia join frontier Q(A,B)"
    case Intersection => "common-prefix frontier Q(A,B), until mismatch"
    case Subtraction => "right-supported common-prefix frontier Q(A,B)"
    case Restriction => "Q(X,P) pruned at terminal prefixes; rebuild frontier A(X,P)"
    case Raffination => "Q(X,Y) pruned at terminal prefixes, fused with the subtraction"
    case Composition => "nodes of the left, plus the merge frontiers at its terminal grafts"
    case FixpointUnion => "the CHANGED frontier of each iterate"

  def wholeSubtree: String = this match
    case Union => "non-overlapping branches are attached unchanged; subset is an identity"
    case Intersection => "disjoint branches are rejected; a contained operand is returned"
    case Subtraction => "missing right branches return the whole left subtree; disjoint subtraction is left identity"
    case Restriction => "a terminal prefix accepts X_u by pointer; a missing prefix rejects X_u without visiting it"
    case Raffination => "a terminal prefix DROPS X_u without visiting it; ε ∈ Y annihilates"
    case Composition => "every graft reuses the same right subtrie; {ε}·B is constant-time"
    case FixpointUnion => "absorbed iterates and unchanged subtries require no rebuild"

  /** does a terminal right prefix PRUNE the descent (accept/drop the whole left subtrie)? */
  def prunes: Boolean = this == Restriction || this == Raffination
  def gate: FrontierGate = this match
    case Subtraction | Restriction | Raffination => FrontierGate.RightGated
    case _ => FrontierGate.Symmetric
  /** structural law: `a ∖ b == b` forces `b ⊆ a∖b`, so `b == ∅` and then `a == ∅` — which is
   *  `Empty`, not `Identity(RIGHT)`.  Same for raffination (Trie.scala:108-111, 118-119). */
  def mayBeRight: Boolean = this != Subtraction && this != Raffination
  def show: String = toString

/** WHERE A COMPONENT'S BOUND CAME FROM, weakest last.  Anything at or below [[NodeCeiling]] is a
 *  FALLBACK: it is a ceiling on the frontier rather than the frontier, and [[FrontierSummary.fallback]]
 *  is then non-empty. */
enum FrontierSource:
  case Exact, Relational, Profile, NodeCeiling, SizeCeiling
  def isFallback: Boolean = this == NodeCeiling || this == SizeCeiling
  def rank: Int = ordinal
  def show: String = toString

/** THE DEPTH-INDEXED FRONTIER.  `paired(d)` is `|Q_d|`, `active(d)` is `|A_d|`, `accepts(d)` is
 *  `|T_d|`, and `fanLeft/fanRight(d)` bound the child-map fan-out summed over the active depth-`d`
 *  nodes — the input to `J`.  `truncated` says nothing is known below `paired.length - 1`, which is
 *  the ONLY way to misread this record: past the end the counts are unknown, not zero. */
final case class DepthFrontier(paired: Vector[Ivl], active: Vector[Ivl], accepts: Vector[Ivl],
                               fanLeft: Vector[Ivl], fanRight: Vector[Ivl], truncated: Boolean):
  def depth: Int = paired.length - 1
  private def sum(v: Vector[Ivl]): Ivl =
    var lo = 0L; var hi = 0L
    for i <- v do { lo = Ivl.add(lo, i.lo); hi = Ivl.add(hi, i.hi) }
    if truncated then Ivl(lo, Ivl.INF) else Ivl(lo, hi)
  def pairedTotal: Ivl = sum(paired)
  def activeTotal: Ivl = sum(active)
  def acceptTotal: Ivl = sum(accepts)
  def show: String =
    val rows = paired.indices.iterator
      .filter(d => paired(d).hi > 0 || active(d).hi > 0 || accepts(d).hi > 0)
      .map(d => s"    d=$d  Q=${paired(d).show} A=${active(d).show} T=${accepts(d).show}").mkString("\n")
    (if rows.isEmpty then "    (no paired prefix at any depth)" else rows) +
      (if truncated then "\n    (truncated: nothing known below d=" + depth + ")" else "")

object DepthFrontier:
  def zero(d: Int): DepthFrontier =
    val z = Vector.fill(d + 1)(Ivl.zero)
    DepthFrontier(z, z, z, z, z, truncated = false)

/** The symbolic projection a `Sym`-valued consumer (`SpatialCost`) needs.  `fallback` is honest: when
 *  the frontier could not be bounded numerically the descent bound is the caller's own coarse sum,
 *  but the REBUILD bound is still the min-gated `tighter(N(L), N(R))` rather than the sum, because
 *  that combination is licensed structurally (a rebuilt node is a paired node, hence a node of both
 *  operands) and not by measurement. */
final case class FrontierSyms(descents: Sym, rebuilt: Sym, patricia: Sym, fallback: Boolean)

/** THE BINARY SUMMARY review.md item 2 asks for.
 *
 *  `descents` is `Θ(|Q| + J)` — the counted per-node entries into the algebra.  `rebuilt` is the
 *  fresh-node bound: `|A|` for the pruned ops, `|Q|` for the merges, `0` whenever `cases` proves an
 *  identity.  `accepts` is the terminal-prefix accept count (whole left subtries taken by pointer),
 *  `reuse` the whole-subtree attach/keep/reject count (one-sided branches never visited). */
final case class FrontierSummary(op: FrontierOp,
                                 cases: Set[FrontierCase],
                                 depth: DepthFrontier,
                                 descents: Ivl,
                                 patricia: Ivl,
                                 rebuilt: Ivl,
                                 accepts: Ivl,
                                 reuse: Ivl,
                                 source: FrontierSource,
                                 fallback: Option[String],
                                 notes: Vector[String] = Vector.empty):
  def isFallback: Boolean = fallback.nonEmpty
  /** the result IS an operand (or empty): zero allocation, and the identity propagates to the parent */
  def identity: Boolean = FrontierCase.isIdentity(cases)
  /** THE STRUCTURAL WHOLE-SUBTREE CLAIM: nothing below the root is paired and nothing is rebuilt.
   *  This is accept-by-pointer, disjoint-reject and `a eq b`.  It is not the same as constant time —
   *  discovering that two head SETS are disjoint still costs one comparison of the two head sets — so
   *  it is stated separately from [[constant]]. */
  def rootOnly: Boolean = !isFallback && !depth.truncated && rebuilt.hi == 0 && depth.pairedTotal.hi <= 1
  /** does the model PROVE the operation constant-time and allocation-free?  [[rootOnly]] plus a
   *  bounded root comparison (a fast path, or two child maps of bounded fan-out). */
  def constant: Boolean = rootOnly && descents.hi <= FrontierConfig.ConstantDescents
  /** does the model bound the work by the path DEPTH rather than by either operand's size? */
  def depthOnly(depthBudget: Long): Boolean =
    !isFallback && depthBudget < Ivl.INF &&
      descents.hi <= Ivl.mul(FrontierConfig.DepthSlack, Ivl.add(depthBudget, 1L))

  def syms(nodesLeft: Sym, nodesRight: Sym, coarse: => Sym): FrontierSyms =
    def num(i: Ivl): Sym = if i.hi >= Ivl.INF then Sym.Inf else Sym.c(i.hi)
    if !isFallback then FrontierSyms(num(descents), num(rebuilt), num(patricia), fallback = false)
    else FrontierSyms(coarse, Sym.tighter(nodesLeft, nodesRight),
                      Sym.tighter(Sym.c(2) * (nodesLeft + nodesRight), coarse), fallback = true)

  def show: String =
    val f = fallback.map(r => s"  FALLBACK($r)").getOrElse("")
    s"${op.show}  cases ${FrontierCase.show(cases)}  |Q|=${depth.pairedTotal.show} " +
      s"|A|=${depth.activeTotal.show} accepts=${accepts.show} reuse=${reuse.show}\n" +
      s"    descents=${descents.show} patricia=${patricia.show} rebuilt=${rebuilt.show} " +
      s"src=${source.show}$f\n" +
      s"    frontier: ${op.frontier}\n" +
      s"    whole-subtree: ${op.wholeSubtree}\n" + depth.show +
      (if notes.isEmpty then "" else notes.map("\n    ! " + _).mkString)

/** Budgets and the two Patricia constants.  Constant factors, not slopes — the user's first steer —
 *  so they are named and loose rather than tuned. */
final case class FrontierConfig(facts: SpatialFacts.Config = SpatialConfig.default.facts,
                                /** shape-pairs the relational walk may carry at one depth */
                                maxFrames: Int = 512,
                                /** depths the walk descends (the profile reaches further on its own) */
                                maxWalkDepth: Int = 64,
                                /** price the INTERNED `ITrie` algebra instead of the case-returning
                                 *  `Trie` one.  `ITrie` has no `Identity` result to propagate, so it
                                 *  REBUILDS ITS WHOLE FRONTIER where `Trie` reuses the argument
                                 *  object — `|A|` against `0`, a slope difference — plus one root
                                 *  node and one op entry per operation. */
                                interned: Boolean = false,
                                /** paths an operand may hold before [[SpatialFacts.exactValue]] is
                                 *  skipped.  Pinning a value is `O(|v|)` and it only ever buys a
                                 *  TIGHTER answer, so declining it on a large operand costs
                                 *  precision and never soundness — and keeps this query off the
                                 *  quadratic path a hot `Routine.optimized` hook cannot afford. */
                                maxExactPaths: Long = 256L)

object FrontierConfig:
  val default: FrontierConfig = FrontierConfig()
  val interned: FrontierConfig = FrontierConfig(interned = true)
  /** big-endian Patricia over `Int` keys: a chain of single-side `Bin` descents is at most this long,
   *  which is what makes a right-gated merge independent of the LEFT fan-out. */
  val PatriciaBits: Long = 33L
  /** `descents.hi` at or below this counts as constant-time: the root entry, plus the Patricia
   *  comparison of two child maps of bounded fan-out (`2·(1+1)` visits for two single-key maps). */
  val ConstantDescents: Long = 8L
  /** slack on the depth-only predicate: the per-level constant of one descent plus its Patricia chain */
  val DepthSlack: Long = 4L * PatriciaBits

object SpatialFrontier:
  import FrontierCase.{Empty as CEmpty, Left as CLeft, Right as CRight, Bespoke as CBespoke}

  // ================================================================================================
  // 0.  saturating interval arithmetic
  // ================================================================================================
  private def satSub(a: Long, b: Long): Long =
    if a >= Ivl.INF then Ivl.INF else if b >= a then 0L else a - b
  private def clamp(lo: Long, hi: Long): Ivl = if lo > hi then Ivl(hi, hi) else Ivl(lo, hi)
  private def meet(a: Ivl, b: Ivl): Ivl = clamp(a.lo max b.lo, a.hi min b.hi)
  private def minI(a: Ivl, b: Ivl): Ivl = Ivl(a.lo min b.lo, a.hi min b.hi)
  private def addI(a: Ivl, b: Ivl): Ivl = Ivl(Ivl.add(a.lo, b.lo), Ivl.add(a.hi, b.hi))
  /** `a − b` on counts of the SAME population, so the endpoints cross */
  private def subI(a: Ivl, b: Ivl): Ivl = clamp(satSub(a.lo, b.hi), satSub(a.hi, b.lo))
  private def sumI(v: IterableOnce[Ivl]): Ivl =
    var lo = 0L; var hi = 0L
    for i <- v.iterator do { lo = Ivl.add(lo, i.lo); hi = Ivl.add(hi, i.hi) }
    Ivl(lo, hi)

  // ================================================================================================
  // 1.  THE PROFILE SOURCE — K_d, E_d, terminal-prefix counts, logical node counts
  // ================================================================================================

  /** One operand's depth-indexed facts, read from `SpatialFacts.profile` (`K_d`) and the histogram
   *  (`E_d`).  `terminal(d) = E_d − E_{d+1}` is EXACTLY the number of length-`d` paths, hence exactly
   *  the number of TERMINAL depth-`d` prefixes — the quantity restriction prunes on.  `nodes` is
   *  `1 + Σ_{d≥1} K_d`, the exact logical `ITrie` node count. */
  private final case class Side(k: Vector[Ivl], e: Vector[Ivl], truncated: Boolean,
                                nodes: Ivl, size: Ivl, len: Ivl, epsOnly: Boolean,
                                provablyEmpty: Boolean, certainlyNonEmpty: Boolean,
                                /** the prefix EVERY path of a non-empty member starts with */
                                common: List[PathItem],
                                exact: Option[Set[PathValue]],
                                shape: Shape, contradiction: Boolean):
    def kAt(d: Int): Ivl = if d < k.length then k(d) else if truncated then Ivl.unknown else Ivl.zero
    def eAt(d: Int): Ivl = if d < e.length then e(d) else if truncated then Ivl.unknown else Ivl.zero
    /** terminal depth-`d` prefixes = paths of length exactly `d` */
    def terminalAt(d: Int): Ivl = meet(subI(eAt(d), eAt(d + 1)), kAt(d))
    def nonTerminalAt(d: Int): Ivl = subI(kAt(d), terminalAt(d))
    def lastDepth: Int = k.length - 1

  private def side(t: SpatialType, cfg: FrontierConfig): Side =
    val exact =
      if t.size.hi > cfg.maxExactPaths then None else SpatialFacts.exactValue(t).map(_.paths)
    // an exact value refines the shape to a CLOSED, DECIDED one; that is what makes the relational
    // walk exact rather than merely sound.  `Shape.of` is a projection of a value, never a run.
    val sh = exact.map(ps => Shape.of(SpaceValue(ps))).getOrElse(t.shape)
    val sz = Ivl(t.size.lo, t.size.hi)
    val ln = if t.len.isEmpty then Ivl.zero else Ivl(t.len.lo, t.len.hi)
    SpatialFacts.profile(t, cfg.facts) match
      case Left(_) =>
        Side(Vector(Ivl.unknown), Vector(Ivl.unknown), truncated = true, Ivl.unknown, sz, ln,
             epsOnly = false, provablyEmpty = false, certainlyNonEmpty = false, Nil, exact, sh,
             contradiction = true)
      case Right(p) =>
        val last = p.lastDepth
        val ks = Vector.tabulate(last + 1)(d => t.prefixesAt(d))
        val es = Vector.tabulate(last + 2)(d => t.pathsAtDepth(d))
        val nodes = SpatialFacts.trieNodes(t, cfg.facts).getOrElse(Ivl.unknown)
        // `{ε}` — the degenerate operand every named whole-subtree case turns on
        val epsOnly = !t.isProvablyEmpty && t.size.lo >= 1 && !t.len.isEmpty && t.len.hi == 0
        Side(ks, es, p.truncated, nodes, sz, ln, epsOnly, t.isProvablyEmpty, t.size.lo >= 1,
             SpatialFacts.commonPrefix(t, cfg.facts).items, exact, sh, contradiction = false)

  // ================================================================================================
  // 2.  THE RELATIONAL SHAPE WALK — the only source that sees disjointness and must-terminality
  // ================================================================================================

  /** One reachable shape-pair at one depth, with the interval of paired prefixes it stands for.  Two
   *  frames with the same pair are MERGED (their multiplicities add), which is what keeps the walk
   *  bounded on an open shape whose `otherTail` summary is the same at every untracked head. */
  private final case class Frame(x: Shape, y: Shape, lo: Long, hi: Long)

  private final case class Walk(paired: Vector[Ivl], active: Vector[Ivl], accepts: Vector[Ivl],
                               fanLeft: Vector[Ivl], fanRight: Vector[Ivl],
                               definiteReuse: Long, exhausted: Boolean, informative: Boolean)

  /** A simultaneous descent of the two shapes.  At a frame the RIGHT operand's `eps` decides the
   *  split for a pruned op: `Must` proves an accept and stops the descent (the whole left subtrie is
   *  taken by pointer), `No` proves the pair active, `May` contributes to both upper bounds and to
   *  neither lower bound.  A head tracked on one side whose counterpart is provably absent
   *  (`headsClosed` and untracked) contributes a DEFINITE whole-subtree reuse and no child frame —
   *  that is disjoint-reject, and it is invisible to any size-only bound. */
  private def walk(x0: Shape, y0: Shape, prunes: Boolean, cfg: FrontierConfig): Walk =
    val paired = Vector.newBuilder[Ivl]; val active = Vector.newBuilder[Ivl]
    val accepts = Vector.newBuilder[Ivl]
    val fanL = Vector.newBuilder[Ivl]; val fanR = Vector.newBuilder[Ivl]
    var reuse = 0L
    var exhausted = false
    var frames: Vector[Frame] =
      if x0.definitelyEmpty || y0.definitelyEmpty then Vector.empty
      else Vector(Frame(x0, y0, if x0.definitelyNonEmpty && y0.definitelyNonEmpty then 1L else 0L, 1L))
    var d = 0
    while frames.nonEmpty && d <= cfg.maxWalkDepth do
      paired += sumI(frames.map(f => Ivl(f.lo, f.hi)))
      // the accept / active split, per frame, on the RIGHT operand's ε presence
      accepts += sumI(frames.map { f =>
        if !prunes then Ivl.zero
        else Ivl(if f.y.eps == Presence.Must then f.lo else 0L,
                 if f.y.eps.mayBe then f.hi else 0L) })
      val actives = frames.map { f =>
        val alive = !prunes || f.y.eps != Presence.Must
        Ivl(if !prunes || f.y.eps == Presence.No then f.lo else 0L, if alive then f.hi else 0L) }
      active += sumI(actives)
      // child-map fan-out at the ACTIVE nodes: the input to J
      fanL += sumI(frames.iterator.zip(actives.iterator).map { (f, a) =>
        if a.hi == 0 then Ivl.zero else Ivl(0L, Ivl.mul(a.hi, f.x.headCount.hi)) })
      fanR += sumI(frames.iterator.zip(actives.iterator).map { (f, a) =>
        if a.hi == 0 then Ivl.zero else Ivl(0L, Ivl.mul(a.hi, f.y.headCount.hi)) })

      val next = Vector.newBuilder[Frame]
      for f <- frames do
        // a MUST-terminal right prefix accepts and does not descend; a MAY-terminal one may not
        // prune, so the upper bound descends while the lower bound gives up its claim
        if !prunes || f.y.eps != Presence.Must then
          val childLo = if !prunes || f.y.eps == Presence.No then f.lo else 0L
          val xLive = f.x.heads.iterator.filter(_._2.possiblyNonEmpty).toVector
          val yLive = f.y.heads.iterator.filter(_._2.possiblyNonEmpty).toVector
          for (k, xc) <- xLive do
            f.y.heads.get(k) match
              case Some(yc) if yc.possiblyNonEmpty =>
                val lo = if childLo > 0 && xc.definitelyNonEmpty && yc.definitelyNonEmpty then childLo else 0L
                next += Frame(xc, yc, lo, f.hi)
              case _ =>
                if f.y.headsClosed then reuse = Ivl.add(reuse, f.lo)     // provably absent: rejected whole
                else next += Frame(xc, f.y.under(k), 0L, f.hi)
          for (k, yc) <- yLive if !f.x.heads.contains(k) do
            if f.x.headsClosed then reuse = Ivl.add(reuse, f.lo)
            else next += Frame(f.x.under(k), yc, 0L, f.hi)
          // untracked on BOTH sides: one summary frame with the paired multiplicity
          if !f.x.headsClosed && !f.y.headsClosed then
            val m = Ivl.mul(f.hi, f.x.others.hi min f.y.others.hi)
            if m > 0 then next += Frame(Shape.weaken(f.x.otherTail.getOrElse(Shape.top)),
                                        Shape.weaken(f.y.otherTail.getOrElse(Shape.top)), 0L, m)
      // merge equal pairs so an open shape does not explode the frame set
      val merged = next.result().groupBy(f => (f.x, f.y)).iterator
        .map { case ((x, y), fs) => Frame(x, y, fs.map(_.lo).foldLeft(0L)(Ivl.add),
                                          fs.map(_.hi).foldLeft(0L)(Ivl.add)) }.toVector
      if merged.size > cfg.maxFrames then { exhausted = true; frames = Vector.empty }
      else frames = merged.filter(f => f.hi > 0)
      d += 1
    if d > cfg.maxWalkDepth && frames.nonEmpty then exhausted = true
    val ps = paired.result()
    // a walk that only ever saw ⊤ knows nothing the profile does not
    Walk(ps, active.result(), accepts.result(), fanL.result(), fanR.result(), reuse, exhausted,
         informative = ps.nonEmpty && !(x0.isTop && y0.isTop))

  // ================================================================================================
  // 3.  THE ALGEBRAIC RESULT CASES
  // ================================================================================================

  /** the exact result of one ring operation on two CONCRETE values — set arithmetic, no trie, no run */
  private def applyExact(op: FrontierOp, a: Set[PathValue], b: Set[PathValue]): Set[PathValue] =
    def extendsSome(p: PathValue): Boolean =
      b.exists(q => q.items.length <= p.items.length && p.items.startsWith(q.items))
    op match
      case FrontierOp.Union | FrontierOp.FixpointUnion => a ++ b
      case FrontierOp.Intersection => a.intersect(b)
      case FrontierOp.Subtraction => a.diff(b)
      case FrontierOp.Restriction => a.filter(extendsSome)
      case FrontierOp.Raffination => a.filterNot(extendsSome)
      case FrontierOp.Composition =>
        for p <- a; q <- b yield PathValue(p.items ++ q.items)

  private def exactCases(op: FrontierOp, a: Set[PathValue], b: Set[PathValue]): Set[FrontierCase] =
    val r = applyExact(op, a, b)
    if r.isEmpty then Set(CEmpty)
    else
      var cs = Set.empty[FrontierCase]
      if r == a then cs += CLeft
      if r == b && op.mayBeRight then cs += CRight
      if cs.isEmpty then Set(CBespoke) else cs

  /** the cases that MAY hold, from the structural laws plus whatever the two types prove.  All four
   *  is always sound; every removal below is a named law from `Trie.AlgebraicResult`'s inventory. */
  private def abstractCases(op: FrontierOp, l: Side, r: Side, shared: Boolean,
                            headDisjoint: Boolean): Set[FrontierCase] =
    import FrontierOp.*
    val base = if op.mayBeRight then FrontierCase.any else FrontierCase.any - CRight
    if l.provablyEmpty && r.provablyEmpty then Set(CEmpty)
    else if shared then op match
      case Union | Intersection | Restriction | FixpointUnion => Set(CLeft, CRight)
      case Subtraction | Raffination => Set(CEmpty)
      case Composition => base
    else op match
      case Union | FixpointUnion =>
        if l.provablyEmpty then Set(CRight) else if r.provablyEmpty then Set(CLeft)
        else if headDisjoint then Set(CBespoke) else base
      case Intersection =>
        if l.provablyEmpty || r.provablyEmpty || headDisjoint then Set(CEmpty) else base
      case Subtraction =>
        if l.provablyEmpty then Set(CEmpty)
        else if r.provablyEmpty || headDisjoint then Set(CLeft) else base
      case Restriction =>
        if l.provablyEmpty || r.provablyEmpty then Set(CEmpty)
        else if headDisjoint then Set(CEmpty)
        else if r.epsOnly then Set(CLeft)                      // ε prefixes everything: all of X kept
        // A COVERING PREFIX: some right path is a prefix of the prefix EVERY left path starts with,
        // so every left path is kept and the whole left space is accepted.  `CommonPrefix` is vacuous
        // on ∅, hence the `Empty` alternative when the left is not proved non-empty.
        else if covers(l, r) then (if l.certainlyNonEmpty then Set(CLeft) else Set(CEmpty, CLeft))
        else base
      case Raffination =>
        if l.provablyEmpty then Set(CEmpty)
        else if r.epsOnly then Set(CEmpty)                     // ε prefixes everything: all of X dropped
        else if covers(l, r) then Set(CEmpty)                  // every left path extends a right prefix
        else if r.provablyEmpty || headDisjoint then Set(CLeft)
        else base
      case Composition =>
        if l.provablyEmpty || r.provablyEmpty then Set(CEmpty)
        else if r.epsOnly then (if l.epsOnly then Set(CLeft, CRight) else Set(CLeft))
        else if l.epsOnly then Set(CRight)
        else base

  /** DOES THE RIGHT OPERAND COVER THE LEFT?  Some pinned right path is a prefix of the constant
   *  prefix every left path must start with, so EVERY left path extends it.  This is the structural
   *  law behind "a terminal prefix accepts `X_u`" applied at the root: restriction keeps all of `X`
   *  and raffination drops all of it, with zero allocation either way. */
  private def covers(l: Side, r: Side): Boolean =
    l.common.nonEmpty && r.exact.exists(_.exists(q => l.common.startsWith(q.items)))

  /** HEAD DISJOINTNESS from the two shapes: every head one side may have, the other provably lacks.
   *  This is the root-level disjoint-reject, and it needs closed head sets on both sides. */
  private def headDisjoint(a: Shape, b: Shape): Boolean =
    a.headsClosed && b.headsClosed && a.eps != Presence.Must && b.eps != Presence.Must && {
      val ah = a.heads.iterator.filter(_._2.possiblyNonEmpty).map(_._1).toSet
      val bh = b.heads.iterator.filter(_._2.possiblyNonEmpty).map(_._1).toSet
      (ah intersect bh).isEmpty
    }

  // ================================================================================================
  // 4.  THE ENTRY POINTS
  // ================================================================================================

  /** `same`: do the two operands evaluate to the SAME OBJECT, so the pointer-identity short circuit
   *  fires (`Trie.unionR`'s `a eq b`, `ITrie.union`'s `a eq b`)?
   *
   *  Structural equality of two `Space` terms proves they denote the same SET — which already gives
   *  `Identity(BOTH)` in the case-returning algebra — but NOT that one object is reached twice: two
   *  separate `Singleton` evaluations build two tries.  The three cases below do share the object:
   *  a repeated `Mention` resolves through the same context entry, a repeated `Literal` through the
   *  identity-keyed `literalTrie`/`iLiteral` cache, and `Empty` is a process-wide `val`.  A DAG-shaped
   *  optimized/supercompiled residual shares more than this, which is why [[binary]] also takes an
   *  explicit `shared` flag. */
  def sameObject(l: Space, r: Space): Boolean = (l, r) match
    case (Space.Mention(a), Space.Mention(b)) => a == b
    case (Space.Literal(a), Space.Literal(b)) => a eq b
    case (Space.Empty, Space.Empty) => true
    case _ => false

  /** the `FrontierOp` of a binary ring node, if it is one */
  def opOf(s: Space): Option[FrontierOp] = s match
    case Space.Union(_, _) => Some(FrontierOp.Union)
    case Space.Intersection(_, _) => Some(FrontierOp.Intersection)
    case Space.Subtraction(_, _) => Some(FrontierOp.Subtraction)
    case Space.Restriction(_, _) => Some(FrontierOp.Restriction)
    case Space.Raffination(_, _) => Some(FrontierOp.Raffination)
    case Space.Composition(_, _) => Some(FrontierOp.Composition)
    case _ => None

  /** THE BINARY SUMMARY.  `shared` asserts the two operands are the same object at run time (see
   *  [[sameObject]]); it is a fast-path claim, so passing `false` only loses tightness. */
  def binary(op: FrontierOp, left: SpatialType, right: SpatialType, shared: Boolean = false,
             cfg: FrontierConfig = FrontierConfig.default): FrontierSummary =
    val l = side(left, cfg)
    val r = side(right, cfg)
    val hd = headDisjoint(l.shape, r.shape)
    val exact = for a <- l.exact; b <- r.exact yield exactCases(op, a, b)
    val cases = exact.getOrElse(abstractCases(op, l, r, shared, hd))
    val notes = Vector.newBuilder[String]
    if exact.isDefined then notes += "both operands pinned to exact values: the case is computed, not bounded"
    if hd then notes += "head-disjoint at the root: " + op.wholeSubtree
    if shared then notes += "shared representation: the pointer-identity short circuit fires"
    if l.contradiction || r.contradiction then
      notes += "an operand's spatial product is contradictory (uninhabited type): no frontier derived"
    if cfg.interned then
      notes += "priced for the INTERNED ITrie algebra: +1 node and +1 descent, it has no Identity case"

    // ---- the three constant-time short circuits, before any frontier is computed ----------------
    val shortCircuit: Option[String] =
      if shared then Some("a eq b")
      else if l.provablyEmpty || r.provablyEmpty then
        // every op has an explicit empty guard on at least one side; union/subtraction return the
        // other operand by pointer, the rest return `empty`
        Some("provably empty operand")
      else if op.prunes && r.epsOnly then Some("ε ∈ right: the whole left space is accepted/dropped by pointer")
      else if op == FrontierOp.Composition && (l.epsOnly || r.epsOnly) then Some("{ε} is the composition unit")
      else None
    if shortCircuit.isDefined && !l.contradiction && !r.contradiction then
      val extra = if cfg.interned then 1L else 0L
      // THE FRONTIER OF A SHORT CIRCUIT is the ROOT PAIR AND NOTHING ELSE: the operation is entered,
      // the guard fires, no child map is ever matched.  It is 0 when an operand is empty — the empty
      // guard answers before any pair exists at all.
      val rootPaired = if l.provablyEmpty || r.provablyEmpty then Ivl.zero else Ivl(1, 1)
      // `ε ∈ right` accepts X_u whole; `a eq b` answers before the ε test, so it accepts nothing
      val acc = if !shared && op.prunes && r.epsOnly && !l.provablyEmpty then Ivl(1, 1) else Ivl.zero
      val z = Vector(Ivl.zero)
      return FrontierSummary(op, cases,
                             DepthFrontier(Vector(rootPaired), Vector(Ivl(0L, satSub(rootPaired.hi, acc.lo))),
                                           Vector(acc), z, z, truncated = false),
                             descents = Ivl(1L, Ivl.add(1L, extra)),
                             patricia = Ivl.zero,
                             rebuilt = Ivl(0L, extra),
                             accepts = acc,
                             reuse = if l.provablyEmpty || r.provablyEmpty then Ivl.zero else Ivl(1, 1),
                             source = if exact.isDefined then FrontierSource.Exact else FrontierSource.Relational,
                             fallback = None,
                             notes = notes.result() :+ s"short circuit: ${shortCircuit.get}")

    if op == FrontierOp.Composition then compositionSummary(l, r, cases, notes.result(), cfg)
    else mergeSummary(op, l, r, cases, hd, notes.result(), cfg)

  /** The frontier of a MERGE (union / intersection / subtraction / restriction / raffination /
   *  fixpoint-union): the paired-prefix frontier, pruned at terminal right prefixes where the op
   *  prunes, met against the per-depth `min(K_d(L), K_d(R))` ceiling. */
  private def mergeSummary(op: FrontierOp, l: Side, r: Side, cases: Set[FrontierCase],
                           hd: Boolean, notes0: Vector[String], cfg: FrontierConfig): FrontierSummary =
    val w = walk(l.shape, r.shape, op.prunes, cfg)
    val dMax = (l.lastDepth max r.lastDepth) max (w.paired.length - 1)
    // TRUNCATION IS A PROPERTY OF THE PROFILES, NOT OF THE WALK.  A truncated profile on ONE side is
    // harmless: `min(K_d(L), K_d(R))` is zero past the other side's maximum depth, so the frontier is
    // still bounded.  Only when NEITHER side bounds its depth is there no frontier bound at all.
    val truncated = l.truncated && r.truncated

    // a walk that ran out of frames simply stops informing: past its last recorded depth it claims
    // nothing (`Ivl.unknown` meets away), so exhaustion costs tightness and never soundness
    def walkAt(v: Vector[Ivl], d: Int): Ivl =
      if d < v.length then v(d) else if w.exhausted then Ivl.unknown else Ivl.zero
    val useWalk = w.informative

    val paired = Vector.tabulate(dMax + 1) { d =>
      val ceiling = Ivl(0L, minI(l.kAt(d), r.kAt(d)).hi)
      if useWalk then meet(walkAt(w.paired, d), ceiling) else ceiling }
    val accepts = Vector.tabulate(dMax + 1) { d =>
      if !op.prunes then Ivl.zero
      else
        val ceiling = Ivl(0L, minI(l.kAt(d), r.terminalAt(d)).hi)
        val c = meet(ceiling, paired(d))
        if useWalk then meet(walkAt(w.accepts, d), c) else c }
    val active = Vector.tabulate(dMax + 1) { d =>
      if !op.prunes then paired(d)
      else
        val ceiling = Ivl(0L, minI(l.kAt(d), r.nonTerminalAt(d)).hi)
        val c = meet(meet(ceiling, paired(d)), subI(paired(d), accepts(d)))
        if useWalk then meet(walkAt(w.active, d), c) else c }
    // the child-map fan-out at the active nodes: each child of an active depth-d prefix is a
    // depth-(d+1) prefix of that operand, and distinct active parents have distinct children
    val fanL = Vector.tabulate(dMax + 1) { d =>
      val ceiling = Ivl(0L, minI(l.kAt(d + 1), Ivl(0L, Ivl.mul(active(d).hi, Ivl.INF))).hi)
      if useWalk then meet(walkAt(w.fanLeft, d), ceiling) else ceiling }
    val fanR = Vector.tabulate(dMax + 1) { d =>
      val ceiling = Ivl(0L, minI(r.kAt(d + 1), Ivl(0L, Ivl.mul(active(d).hi, Ivl.INF))).hi)
      if useWalk then meet(walkAt(w.fanRight, d), ceiling) else ceiling }

    val depth = DepthFrontier(paired, active, accepts, fanL, fanR, truncated)
    val qTot = depth.pairedTotal
    val aTot = depth.activeTotal
    val tTot = meet(depth.acceptTotal, Ivl(0L, r.size.hi))   // an accept consumes a distinct right path

    // ---- J: the Patricia frontier -------------------------------------------------------------
    // Bound 1 (always): a simultaneous descent visits at most the nodes of both Patricia trees, and a
    //   tree over k keys has at most 2k-1 nodes  ->  2 (fanL + fanR).
    // Bound 2 (gated): only the GATING side's keys are ever searched for, and between two of its
    //   nodes the descent can take at most `PatriciaBits` single-side steps  ->
    //   2 * PatriciaBits * (gatingFan + |A|).  This is the bound that is INDEPENDENT of the other
    //   operand's fan-out, and it is what makes restriction by a length-d prefix Θ(d).
    val fanLTot = sumI(fanL); val fanRTot = sumI(fanR)
    val bothBound = Ivl.mul(2L, Ivl.add(fanLTot.hi, fanRTot.hi))
    val gateFan = op.gate match
      case FrontierGate.RightGated => fanRTot.hi
      case FrontierGate.Symmetric => fanLTot.hi min fanRTot.hi
    val gatedBound = Ivl.mul(Ivl.mul(2L, FrontierConfig.PatriciaBits), Ivl.add(gateFan, aTot.hi))
    val jHi = if truncated then Ivl.INF else bothBound min gatedBound
    val patricia = Ivl(0L, jHi)

    val identity = FrontierCase.isIdentity(cases)
    val extra = if cfg.interned then 1L else 0L
    // THE ASYMPTOTIC DIFFERENCE BETWEEN THE TWO BACKENDS.  The case-returning algebra propagates
    // `Identity` to the root and allocates NOTHING (Trie.scala:333-336); the interned one has no
    // `Identity` to return, so it rebuilds its whole frontier — `0` against `|A|`, which is a SLOPE
    // difference and not a constant.  review.md item 2, last sentence of the restriction paragraph.
    val rebuiltCore =
      if identity && !cfg.interned then Ivl.zero else if op.prunes then aTot else qTot
    val rebuilt = Ivl(rebuiltCore.lo, Ivl.add(rebuiltCore.hi, extra))
    val descents = Ivl(qTot.lo max 1L, Ivl.add(Ivl.add(qTot.hi, jHi), extra))

    // ---- source / fallback --------------------------------------------------------------------
    val exactBoth = l.exact.isDefined && r.exact.isDefined
    var source =
      if exactBoth && !truncated then FrontierSource.Exact
      else if useWalk && !truncated then FrontierSource.Relational
      else if !truncated then FrontierSource.Profile
      else FrontierSource.NodeCeiling
    var fallback: Option[String] = None
    var notes = notes0
    var out = (descents, rebuilt, patricia)
    if truncated then
      // LAST RESORT.  The frontier is a subset of both operands' node sets, so `min(N(L),N(R))` is
      // still a sound ceiling on it — that is a structural law, not a measurement — and it is
      // MARKED, so a consumer can tell it from a real frontier bound.
      val ceil = minI(l.nodes, r.nodes)
      if ceil.hi < Ivl.INF then
        source = FrontierSource.NodeCeiling
        fallback = Some(s"depth profile truncated; ceiling min(N(L),N(R)) = ${ceil.hi}")
        val j = Ivl.mul(2L, Ivl.add(l.nodes.hi, r.nodes.hi))
        out = (Ivl(1L, Ivl.add(Ivl.add(ceil.hi, j), extra)),
               Ivl(0L, if identity && !cfg.interned then extra else Ivl.add(ceil.hi, extra)),
               Ivl(0L, j))
      else
        source = FrontierSource.SizeCeiling
        fallback = Some("neither operand has a bounded node count: no frontier bound exists")
        out = (Ivl.unknown, if identity && !cfg.interned then Ivl(0L, extra) else Ivl.unknown,
               Ivl.unknown)
      notes = notes :+ ("frontier not derivable: " + fallback.get)

    FrontierSummary(op, cases, depth, out._1, out._3, out._2, tTot,
                    reuse = Ivl(w.definiteReuse, if truncated then Ivl.INF else Ivl.add(fanLTot.hi, fanRTot.hi)),
                    source = source, fallback = fallback, notes = notes)

  /** COMPOSITION.  The left operand's nodes are the frontier (each is entered once and rebuilt —
   *  review.md item 4's correction to `Trie.scala:294-304`: a single depth-`d` path has ONE terminal
   *  but the code rebuilds its `d`-node spine), plus one union frontier per NON-LEAF terminal of the
   *  left.  A LEAF terminal grafts `B` by pointer and costs nothing, which is why a single-path left
   *  operand composes in `Θ(|p|)` with zero extra allocation. */
  private def compositionSummary(l: Side, r: Side, cases: Set[FrontierCase], notes0: Vector[String],
                                 cfg: FrontierConfig): FrontierSummary =
    // a non-leaf terminal at depth d is a length-d path with an extension; distinct ones have
    // distinct depth-(d+1) children, so their count is at most min(terminal_d, K_{d+1})
    val nonLeaf =
      if l.truncated then Ivl.unknown
      else sumI((0 to l.lastDepth).map(d => Ivl(0L, minI(l.terminalAt(d), l.kAt(d + 1)).hi)))
    val paired = Vector.tabulate(l.lastDepth + 1)(d => l.kAt(d))
    val z = Vector.fill(l.lastDepth + 1)(Ivl.zero)
    val depth = DepthFrontier(paired, paired, z, z, z, l.truncated)
    val identity = FrontierCase.isIdentity(cases)
    val extra = if cfg.interned then 1L else 0L
    val graft = Ivl.mul(nonLeaf.hi, minI(l.nodes, r.nodes).hi)
    val notes =
      notes0 :+ (if nonLeaf.hi == 0 then "every terminal of the left is a LEAF: every graft reuses B by pointer"
                 else s"up to ${if nonLeaf.hi >= Ivl.INF then "inf" else nonLeaf.hi} non-leaf grafts, each a union against B")
    if l.truncated || l.nodes.hi >= Ivl.INF then
      FrontierSummary(FrontierOp.Composition, cases, depth, Ivl.unknown,
                      Ivl.unknown, if identity then Ivl(0L, extra) else Ivl.unknown, Ivl.zero,
                      Ivl(0L, Ivl.INF), FrontierSource.SizeCeiling,
                      Some("the left operand has no bounded node count: no graft frontier exists"), notes)
    else
      val rebuilt = if identity then Ivl(0L, extra) else Ivl(0L, Ivl.add(Ivl.add(l.nodes.hi, graft), extra))
      val descents = Ivl(1L, Ivl.add(Ivl.add(l.nodes.hi, Ivl.add(graft, l.size.hi)), extra))
      FrontierSummary(FrontierOp.Composition, cases, depth, descents, Ivl(0L, graft), rebuilt,
                      accepts = Ivl.zero,
                      reuse = Ivl(satSub(l.size.lo, nonLeaf.hi), l.size.hi),
                      source = if l.exact.isDefined && r.exact.isDefined then FrontierSource.Exact
                               else FrontierSource.Profile,
                      fallback = None, notes = notes)

  /** FIXPOINT-UNION — the CHANGED frontier of one iterate against the accumulator.  `absorbed`
   *  asserts the iterate adds nothing (`nxt ⊆ acc`, the union is `Identity(LEFT)`), which is what
   *  makes the terminating round free of rebuilds; `shared` asserts `nxt eq acc`, the `eq`
   *  convergence signal `evalT` checks before the structural comparison. */
  def fixpointUnion(acc: SpatialType, iterate: SpatialType, shared: Boolean = false,
                    absorbed: Boolean = false,
                    cfg: FrontierConfig = FrontierConfig.default): FrontierSummary =
    val s = binary(FrontierOp.FixpointUnion, acc, iterate, shared, cfg)
    if !absorbed || s.identity then s
    else s.copy(cases = Set(CLeft),
                rebuilt = Ivl(0L, if cfg.interned then 1L else 0L),
                notes = s.notes :+ "iterate ABSORBED: the union is Identity(LEFT), nothing is rebuilt")

  /** the same frontier repeated over a round count — the fixpoint's whole cost */
  def scaled(s: FrontierSummary, rounds: Ivl): FrontierSummary =
    def m(i: Ivl): Ivl = Ivl(Ivl.mul(i.lo, rounds.lo), Ivl.mul(i.hi, rounds.hi))
    s.copy(descents = m(s.descents), patricia = m(s.patricia), rebuilt = m(s.rebuilt),
           accepts = m(s.accepts), reuse = m(s.reuse),
           notes = s.notes :+ s"scaled by ${rounds.show} rounds")

  // ================================================================================================
  // 5.  THE DECORATED-ANALYSIS ENTRY POINT
  // ================================================================================================

  /** The summary of the binary ring node at `id`, read from the DECORATED SIBLING FACTS — the two
   *  children's already-computed `SpatialType`s at their own `NodeId`s, under their own binder
   *  environments — and never from a fresh `SpatialTyping.infer`.  `None` when `id` is absent, is not
   *  a binary ring node, or a child was not decorated (the analysis stopped recording). */
  def atNode(a: SpatialAnalysis, id: NodeId,
             cfg: FrontierConfig = FrontierConfig.default): Option[FrontierSummary] =
    for
      n <- a.at(id)
      op <- opOf(n.expression)
      lc <- a.at(id.child(0))
      rc <- a.at(id.child(1))
    yield
      val shared = sameObject(lc.expression, rc.expression)
      val s = binary(op, lc.result, rc.result, shared, cfg)
      if lc.expression == rc.expression && !shared then
        s.copy(notes = s.notes :+ "structurally equal operands (same SET, but two objects unless the residual shares them)")
      else s

  /** every binary ring node of a decorated term, parents before children.  Run this over
   *  `Routine.optimized`'s body: the spatial hook has already turned proved-empty and pinned
   *  occurrences into `Empty`/`Literal`, which is what promotes a generic four-case answer into a
   *  named whole-subtree case. */
  def summarize(a: SpatialAnalysis,
                cfg: FrontierConfig = FrontierConfig.default): Vector[(NodeId, FrontierSummary)] =
    a.nodes.flatMap(n => atNode(a, n.id, cfg).map(n.id -> _))

  /** the report the calibration suite publishes */
  def report(rows: Vector[(NodeId, FrontierSummary)]): String =
    if rows.isEmpty then "(no binary ring node)"
    else rows.map((id, s) => s"${id.show}  ${s.show}").mkString("\n")
