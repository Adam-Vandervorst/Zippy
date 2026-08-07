package morkl

import scala.collection.immutable.SortedMap

/** ==============================================================================================
 *  SYMBOLIC COST — a cost algebra over the spatial facts (review.md finding 3).
 *
 *  The point of this file is the distinction review.md 3 says the repository keeps losing:
 *  **result cardinality is not evaluation cost**.  Cardinality (and path length, and head count)
 *  are the *inputs* here.  What is computed is a cost VECTOR per AST node with three separate
 *  components — `work` (elementary operand/node visits), `alloc` (paths or trie nodes actually
 *  materialised) and `rounds` (loop head-groups and fixpoint rounds entered) — expressed in a
 *  SYMBOLIC algebra over size variables, so `N`, `N log N`, `N²` and `2^N` stay distinct instead of
 *  all collapsing onto one `INF` sentinel.
 *
 *  The same facts drive FOUR backend cost instances, one per executable, each in a COLD and a WARM
 *  phase, each returning a LOWER/UPPER [[CostInterval]] rather than a bare worst case:
 *
 *  | instance          | executable                        | calibrated against               |
 *  |-------------------|-----------------------------------|----------------------------------|
 *  | [[ReferenceCost]] | `eval` (MORKL.scala)              | counted events, `touch` excepted (no oracle) |
 *  | [[TrieCostModel]] | `evalI` (IntTrie.scala)           | counted events, all four components |
 *  | [[GraphCost]]     | `execT` (GraphExec.scala)         | counted events, all four components |
 *  | [[ZipperCost]]    | `execZ` (Zipper.scala)            | counted events, `evalI` fallback INCLUDED |
 *
 *  They disagree, and the disagreement is what makes this a cost model rather than a second size
 *  bound: a trie intersection can skip a provably disjoint subtrie, an `Unwrap` shares the focused
 *  subtrie instead of rebuilding a set, `execT` allocates one frame per loop node while `execZ`
 *  allocates none but re-reads each node once per fused layer, and `execZ` stops being `execZ` at all
 *  on control flow (it hands the subterm to `evalI`, and this file prices it that way).
 *
 *  STANDING INVARIANT (docs/design_spatial_lattice.md §0): NO EVALUATION.  Nothing here calls
 *  `eval`/`evalI`/`evalT`/`exec*`.  Every input fact comes from the term's syntax, the declared
 *  annotations, or a read-only query to `SpatialTypes` / `SpatialTyping` / `SpatialFacts` / `Lower`.
 *
 *  WHAT IS AND IS NOT ESTABLISHED (review.md finding 2, then item 1).  ALL FOUR cost components —
 *  `work`, `alloc`, `rounds` AND `touch` — are DEFINED BY COUNTED EVENTS ([[EffortComponent]]), so
 *  their tightness is measurable and is measured: `SpatialEventsCheck` publishes containment
 *  (`lower ≤ actual ≤ upper`), median/p95/worst slack per component and per backend over the fuzzer
 *  corpus and the cornerstones, and GATES the p95 and the worst case.  `touch` became measurable when
 *  IntTrie.scala / IntTrieOps.scala were instrumented: it is the per-node descent inside the trie
 *  algebra ([[EffortEvent.TrieNodeVisit]] + [[EffortEvent.PatriciaVisit]]).
 *
 *  THE ONE REMAINING EXCEPTION, declared in the model rather than filtered in the harness:
 *  [[ReferenceCost]] overrides [[CostModel.touchNoOracle]].  `eval` works over
 *  `scala.collection.immutable.Set[PathValue]`, performs no `ITrie` work at all, and the `Set`
 *  internals (hash probes, bucket copies) are standard-library code with no hooks — so the reference
 *  backend's `touch` is a MODEL with no oracle, validated only by the SECONDARY rank-correlation
 *  trend in `SpatialCostCheck`.  `SpatialEventsCheck` asserts that this is the ONLY such exception, so
 *  the exclusion list cannot grow silently.
 *
 *  THE TOUCH LOWER ENDPOINT IS 0 BY CONSTRUCTION.  The fast paths inside `ITrie`/`IntMap` — pointer
 *  identity, a prefix mismatch that prunes a whole Patricia branch, an empty operand — can eliminate
 *  essentially every internal visit, so no positive LOWER bound on counted `touch` is claimed;
 *  [[SpatialCost.analyze]] zeroes it. Per-operator constants remain a model read off the executors'
 *  code — what is now checked is that the model BRACKETS what the executors actually do.
 *  ============================================================================================== */

/** A symbolic non-negative quantity.
 *
 *  DOMAIN.  Every [[Sym.Var]] ranges over the reals `≥ 2`.  That is the assumption which makes the
 *  syntactic [[Sym.dominates]] test sound (every atom, `Log` included, is then `≥ 1`, so adding a
 *  factor or raising an exponent can only increase a monomial).  `Log` is base 2. */
enum Sym:
  case Const(n: Long)
  case Var(name: String)
  case Add(terms: Vector[Sym])
  case Mul(factors: Vector[Sym])
  case Pow(base: Sym, exp: Sym)
  case Max(alts: Vector[Sym])
  case Log(arg: Sym)
  /** the algebra's top — used ONLY where a quantity is genuinely unknowable (a grounded closure's
   *  output size), never as a stand-in for "large" */
  case Inf

  def +(o: Sym): Sym = Sym.normalize(Sym.Add(Vector(this, o)))
  def *(o: Sym): Sym = Sym.normalize(Sym.Mul(Vector(this, o)))
  def **(o: Sym): Sym = Sym.normalize(Sym.Pow(this, o))
  /** the pointwise maximum (a join, not a sum) */
  infix def lub(o: Sym): Sym = Sym.normalize(Sym.Max(Vector(this, o)))
  def show: String = Sym.render(this)

/** The asymptotic projection of a [[Sym]]: `expFactors` counts symbolic-exponent factors (`2^N`),
 *  `degree` is the total polynomial degree of the dominant monomial, `logs` its log factors.
 *  Compared lexicographically, which is exactly `2^N > N² > N log N > N > log N > 1`. */
final case class BigO(expFactors: Int, degree: Int, logs: Int) extends Ordered[BigO]:
  def compare(that: BigO): Int =
    val a = Integer.compare(expFactors, that.expFactors)
    if a != 0 then a
    else
      val b = Integer.compare(degree, that.degree)
      if b != 0 then b else Integer.compare(logs, that.logs)
  def show: String =
    if this == BigO.inf then "inf"
    else if this == BigO.zero then "0"
    else if expFactors > 0 then (if expFactors == 1 then "2^n" else s"2^(${expFactors}n)")
    else
      val d = degree match { case 0 => "" ; case 1 => "n" ; case k => s"n^$k" }
      val l = logs match { case 0 => "" ; case 1 => "log n" ; case k => s"log^$k n" }
      val parts = Vector(d, l).filter(_.nonEmpty)
      if parts.isEmpty then "1" else parts.mkString(" ")

object BigO:
  /** strictly below every non-zero class: the quantity is identically 0 */
  val zero: BigO = BigO(-1, 0, 0)
  val const: BigO = BigO(0, 0, 0)
  val inf: BigO = BigO(Int.MaxValue, 0, 0)
  def max(a: BigO, b: BigO): BigO = if a >= b then a else b

object Sym:
  val INF: Long = Long.MaxValue
  val zero: Sym = Const(0)
  val one: Sym = Const(1)

  def v(name: String): Sym = Var(name)
  def c(n: Long): Sym = if n >= INF then Inf else if n <= 0 then Const(0) else Const(n)
  def log(a: Sym): Sym = normalize(Log(a))
  def sum(xs: Iterable[Sym]): Sym = normalize(Add(xs.toVector))
  def prod(xs: Iterable[Sym]): Sym = normalize(Mul(xs.toVector))
  def maxOf(xs: Sym*): Sym = normalize(Max(xs.toVector))

  private def satAdd(a: Long, b: Long): Long =
    if a >= INF || b >= INF then INF else { val s = a + b; if s < 0 then INF else s }
  private def satMul(a: Long, b: Long): Long =
    if a == 0 || b == 0 then 0 else if a >= INF || b >= INF || a > INF / b then INF else a * b
  private def satPow(b: Long, e: Long): Long =
    if e <= 0 then 1 else if b == 0 then 0 else if b == 1 then 1
    else
      var acc = 1L; var i = 0L
      while i < e && acc < INF do { acc = satMul(acc, b); i += 1 }
      acc
  /** ⌈log₂ n⌉, floored at 1 so a folded `Log` still respects the `atom ≥ 1` domain (only loosens) */
  private def ceilLog2(n: Long): Long =
    if n <= 2 then 1L
    else
      var k = 0L; var p = 1L
      while p < n do { p = satMul(p, 2); k += 1 }
      k

  // ---- rendering (also the canonical key for atoms) ---------------------------------------------
  private[morkl] def render(e: Sym): String = e match
    case Const(n) => n.toString
    case Inf => "inf"
    case Var(x) => x
    case Log(a) => s"log(${render(a)})"
    case Max(as) => as.map(render).mkString("max(", ", ", ")")
    case Pow(b, x) => s"${atomStr(b)}^${atomStr(x)}"
    case Mul(fs) => fs.map(atomStr).mkString("*")
    case Add(ts) => ts.map(render).mkString(" + ")
  private def atomStr(e: Sym): String = e match
    case Add(_) | Mul(_) => s"(${render(e)})"
    case _ => render(e)

  // ---- the polynomial normal form --------------------------------------------------------------
  // A normalised Sym is a SUM of monomials; a monomial is a coefficient times a product of ATOMS
  // raised to integer exponents.  An atom is a Var, a Log, a Pow with a non-constant exponent, a
  // Max, or (only past the distribution cap) an opaque product — never an Add.  Atoms are keyed by
  // their rendering, which is canonical because they are themselves normalised.
  private type Mono = SortedMap[String, (Sym, Int)]
  private val unit: Mono = SortedMap.empty[String, (Sym, Int)]
  private final case class P(inf: Boolean, ts: Map[Mono, Long])
  private val pZero = P(false, Map.empty)
  private val pInf = P(true, Map.empty)
  private def pConst(n: Long): P = if n >= INF then pInf else if n <= 0 then pZero else P(false, Map(unit -> n))
  private def pAtom(a: Sym): P = P(false, Map(SortedMap(render(a) -> (a, 1)) -> 1L))

  private def addP(x: P, y: P): P =
    if x.inf || y.inf then pInf
    else
      var out = x.ts
      var over = false
      for (m, c) <- y.ts do
        val nc = satAdd(out.getOrElse(m, 0L), c)
        if nc >= INF then over = true
        out = out.updated(m, nc)
      if over then pInf else P(false, out.filter(_._2 != 0L))

  private def mulMono(a: Mono, b: Mono): Mono =
    var out = a
    for (k, (atom, e)) <- b do
      out = out.updated(k, out.get(k) match { case Some((at, e0)) => (at, e0 + e); case None => (atom, e) })
    out

  private def mulP(x: P, y: P): P =
    if (!x.inf && x.ts.isEmpty) || (!y.inf && y.ts.isEmpty) then pZero   // 0 · anything (even ⊤) = 0
    else if x.inf || y.inf then pInf
    else if x.ts.size.toLong * y.ts.size.toLong > 512L then
      pAtom(Mul(Vector(fromP(x), fromP(y)).sortBy(render)))              // distribution cap: keep opaque
    else
      var out = pZero
      var over = false
      for (ma, ca) <- x.ts; (mb, cb) <- y.ts do
        val cc = satMul(ca, cb)
        if cc >= INF then over = true
        else out = addP(out, P(false, Map(mulMono(ma, mb) -> cc)))
      if over || out.inf then pInf else out

  private def powP(b: Sym, e: Sym): P =
    val nb = normalize(b); val ne = normalize(e)
    (nb, ne) match
      case (_, Const(0)) => pConst(1)
      case (_, Const(1)) => toP(nb)
      case (Const(0), _) => pZero
      case (Const(1), _) => pConst(1)
      case (Inf, _) => pInf
      case (_, Inf) => pInf
      case (Const(m), Const(k)) => pConst(satPow(m, k))
      case (_, Const(k)) if k >= 2 =>
        val pb = toP(nb)
        if pb.inf then pInf
        else if pb.ts.size == 1 then
          // a single monomial raised to a constant: multiply the exponents (keeps `fromP ∘ toP`
          // idempotent for large exponents, which repeated multiplication would not)
          val (m, cf) = pb.ts.head
          val cc = satPow(cf, k)
          if cc >= INF || k > 1000000L then pInf
          else
            var mm: Mono = unit
            var bad = false
            for (key, (a, ex)) <- m do
              val ne2 = ex.toLong * k
              if ne2 > Int.MaxValue.toLong then bad = true else mm = mm.updated(key, (a, ne2.toInt))
            if bad then pInf else P(false, Map(mm -> cc))
        else if k <= 12 then
          var acc = pb; var i = 1L
          while i < k do { acc = mulP(acc, pb); i += 1 }
          acc
        else pAtom(Pow(nb, Const(k)))
      case _ => pAtom(Pow(nb, ne))

  private def logP(a: Sym): P = normalize(a) match
    case Inf => pInf
    case Const(n) => pConst(ceilLog2(n))
    case x => pAtom(Log(x))

  private def maxP(alts: Vector[Sym]): P =
    val ns = alts.map(normalize)
    if ns.contains(Inf) then pInf
    else
      val flat = ns.flatMap { case Max(xs) => xs; case x => Vector(x) }.distinct
      // Drop alternatives another alternative already dominates.  Two deliberate restrictions:
      //   * the PURE POLY matcher, not the public `dominates`, so normalisation can never recurse
      //     back into itself through the Max/Pow rules;
      //   * the NATURAL-NUMBER matcher, not the `var ≥ 2` one.  Pruning a Max *rewrites* the
      //     expression, so it must hold for every non-negative valuation — `max(N, N·M)` may NOT
      //     collapse to `N·M`, which is 0 at M = 0.
      var kept = Vector.empty[Sym]
      for x <- flat do
        if !kept.exists(y => dominatesNat(toP(y), toP(x))) then
          kept = kept.filterNot(y => dominatesNat(toP(x), toP(y))) :+ x
      if kept.isEmpty then pZero
      else if kept.size == 1 then toP(kept.head)
      else pAtom(Max(kept.sortBy(render)))

  private def toP(e: Sym): P = e match
    case Inf => pInf
    case Const(n) => pConst(n)
    case Var(x) => pAtom(Var(x))
    case Add(ts) => ts.foldLeft(pZero)((acc, t) => addP(acc, toP(t)))
    case Mul(fs) => fs.foldLeft(pConst(1))((acc, t) => mulP(acc, toP(t)))
    case Pow(b, x) => powP(b, x)
    case Max(as) => maxP(as)
    case Log(a) => logP(a)

  private def monoDeg(m: Mono): Int = m.valuesIterator.map(_._2).sum
  private def monoKey(m: Mono): String = m.toVector.map((k, ae) => s"$k^${ae._2}").mkString("*")

  private def monoSym(m: Mono, cf: Long): Sym =
    val fs = m.toVector.map { case (_, (a, e)) => if e == 1 then a else Pow(a, Const(e.toLong)) }
    val all = if cf == 1 && fs.nonEmpty then fs else Const(cf) +: fs
    if all.size == 1 then all.head else Mul(all)

  private def fromP(p: P): Sym =
    if p.inf then Inf
    else
      val live = p.ts.filter(_._2 != 0L)
      if live.isEmpty then Const(0)
      else
        val terms = live.toVector.sortBy((m, _) => (-monoDeg(m), monoKey(m))).map((m, cf) => monoSym(m, cf))
        if terms.size == 1 then terms.head else Add(terms)

  /** Collect like terms, fold constants, sort canonically.  Idempotent (checked in the suite). */
  def normalize(e: Sym): Sym = fromP(toP(e))

  // ---- the order -------------------------------------------------------------------------------
  /** Does `ma` dominate `mb` monomial-wise, on the `atom ≥ 1` domain?
   *
   *  Exact atom keys are matched first, consuming exponent budget; a leftover `Log(x)` in `mb` may
   *  then be paid for by remaining `x` budget in `ma` (`log₂ x ≤ x` for `x ≥ 2`).  That is what
   *  makes `N²` dominate `N log N`. */
  private def monoGE(ma: Mono, mb: Mono): Boolean =
    val budget = collection.mutable.Map.from(ma.view.map((k, ae) => k -> ae._2))
    var ok = true
    val (exact, rest) = mb.toVector.partition((k, _) => budget.contains(k))
    for (k, (_, e)) <- exact do
      if budget(k) >= e then budget(k) = budget(k) - e else ok = false
    if ok then
      for (_, (atom, e)) <- rest do
        if ok then
          atom match
            case Log(x) =>
              val xk = render(x)
              if budget.getOrElse(xk, 0) >= e then budget(xk) = budget(xk) - e else ok = false
            case _ => ok = false
    ok

  /** Monomial domination valid for EVERY non-negative valuation: the same atoms, with exponents at
   *  least as large.  No extra factors (`N·M ≥ N` fails at `M = 0`) and no log/var trade. */
  private def monoGEnat(ma: Mono, mb: Mono): Boolean =
    ma.keySet == mb.keySet && mb.forall((k, ae) => ma(k)._2 >= ae._2)

  /** Pure monomial matching: every `b` monomial is paid for by an `a` monomial that dominates it,
   *  drawing on that monomial's coefficient budget (all coefficients are non-negative, so
   *  `Σ` splitting is sound). */
  private def dominatesPoly(pa: P, pb: P): Boolean = matchPoly(pa, pb, monoGE)
  private def dominatesNat(pa: P, pb: P): Boolean = matchPoly(pa, pb, monoGEnat)

  private def matchPoly(pa: P, pb: P, ge: (Mono, Mono) => Boolean): Boolean =
    if pa.inf then true
    else if pb.inf then false
    else
      val rem = collection.mutable.Map.from(pa.ts)
      var ok = true
      for (mb, cb) <- pb.ts.toVector.sortBy((m, _) => -monoDeg(m)) do
        if ok then
          val cands = rem.keysIterator.filter(ma => ge(ma, mb)).toVector.sortBy(monoDeg)
          cands.find(ma => rem(ma) >= cb) match
            case Some(ma) => rem(ma) = rem(ma) - cb
            case None => ok = false
      ok

  private def baseGE2(b: Sym): Boolean = b match
    case Const(n) => n >= 2
    case Var(_) => true          // the domain assumption
    case _ => false

  /** SOUND SUFFICIENT CONDITION for `∀ valuation with every variable ≥ 2: a ≥ b`.
   *
   *  Incomplete on purpose — e.g. it does NOT report `2^N ≥ N` (true) because it never reasons
   *  about an exponential against a polynomial.  A `false` therefore means "not proved here", not
   *  "smaller".  Checked numerically against [[evalAt]] in the suite. */
  def dominates(a: Sym, b: Sym): Boolean =
    val na = normalize(a); val nb = normalize(b)
    if na == nb then true
    else if na == Inf then true
    else if nb == Const(0) then true
    else if nb == Inf then false
    else (na, nb) match
      case (Max(as), _) if as.exists(dominates(_, nb)) => true
      case (_, Max(bs)) if bs.forall(dominates(na, _)) => true
      case (Pow(b1, e1), Pow(b2, e2)) if b1 == b2 && baseGE2(b1) && dominates(e1, e2) => true
      case _ => dominatesPoly(toP(na), toP(nb))

  /** Both arguments must be SOUND UPPER BOUNDS of the same quantity; returns one of them (so the
   *  result is still a sound upper bound) preferring the tighter. */
  def tighter(a: Sym, b: Sym): Sym =
    if dominates(a, b) then normalize(b)
    else if dominates(b, a) then normalize(a)
    else if bigO(a) <= bigO(b) then normalize(a) else normalize(b)

  // ---- the asymptotic projection ---------------------------------------------------------------
  def bigO(e: Sym): BigO =
    val p = toP(normalize(e))
    if p.inf then BigO.inf
    else if p.ts.isEmpty then BigO.zero          // the identically-zero quantity, below `const`
    else p.ts.keysIterator.map(monoOrder).reduce(BigO.max)

  /** every order coordinate is clamped, so an absurd exponent saturates to `inf` rather than
   *  wrapping around into a small (and therefore WRONG) order class */
  private val OrderCap = 1000000L
  private def clampOrder(ex: Long, dg: Long, lg: Long): BigO =
    if ex > OrderCap || dg > OrderCap || lg > OrderCap then BigO.inf else BigO(ex.toInt, dg.toInt, lg.toInt)

  private def monoOrder(m: Mono): BigO =
    var ex = 0L; var dg = 0L; var lg = 0L
    var inf = false
    for (_, (a, e)) <- m do
      val o = atomOrder(a)
      if o == BigO.inf then inf = true
      else { ex += o.expFactors.toLong * e; dg += o.degree.toLong * e; lg += o.logs.toLong * e }
    if inf then BigO.inf else clampOrder(ex, dg, lg)

  private def atomOrder(a: Sym): BigO = a match
    case Const(_) => BigO.const
    case Inf => BigO.inf
    case Var(_) => BigO(0, 1, 0)
    case Log(x) =>
      val i = bigO(x)
      if i == BigO.inf then BigO.inf
      else if i.expFactors > 0 then BigO(0, 1, 0)     // log(2^n) is linear in n
      else BigO(0, 0, 1)
    case Pow(b, x) => normalize(x) match
      case Const(k) if k <= 1000L =>
        val ib = bigO(b)
        if ib == BigO.inf then BigO.inf
        else clampOrder(ib.expFactors.toLong * k, ib.degree.toLong * k, ib.logs.toLong * k)
      case Const(_) => BigO.inf
      case _ => BigO(1, 0, 0)                         // a symbolic exponent IS exponential growth
    case Max(as) => as.map(bigO).reduce(BigO.max)
    case Mul(fs) => fs.map(bigO).foldLeft(BigO.const)((x, y) =>
      if x == BigO.inf || y == BigO.inf then BigO.inf
      else clampOrder(x.expFactors.toLong + y.expFactors, x.degree.toLong + y.degree, x.logs.toLong + y.logs))
    case Add(ts) => ts.map(bigO).reduce(BigO.max)

  // ---- numeric read-off (for TESTING the order; never used by the analysis) ---------------------
  def evalAt(e: Sym, v: Map[String, Double]): Double = e match
    case Const(n) => n.toDouble
    case Inf => Double.PositiveInfinity
    case Var(x) => v.getOrElse(x, 2.0)
    case Add(ts) => ts.foldLeft(0.0)((s, t) => s + evalAt(t, v))
    case Mul(fs) => fs.foldLeft(1.0)((s, t) => s * evalAt(t, v))
    case Pow(b, x) => math.pow(evalAt(b, v), evalAt(x, v))
    case Max(as) => as.map(evalAt(_, v)).max
    case Log(a) => math.log(math.max(2.0, evalAt(a, v))) / math.log(2.0)

  def vars(e: Sym): Set[String] = e match
    case Var(x) => Set(x)
    case Const(_) | Inf => Set.empty
    case Add(ts) => ts.flatMap(vars).toSet
    case Mul(fs) => fs.flatMap(vars).toSet
    case Max(as) => as.flatMap(vars).toSet
    case Pow(b, x) => vars(b) ++ vars(x)
    case Log(a) => vars(a)

  private def occurs(e: Sym, name: String): Boolean = vars(e).contains(name)

  /** Split `e` as `a + b·Var(name)`, or `None` when `name` occurs at degree ≥ 2 or inside an
   *  opaque atom (a `Log`/`Pow`/`Max`) — the shapes the linear recurrence solver cannot handle. */
  def splitLinear(e: Sym, name: String): Option[(Sym, Sym)] =
    val p = toP(normalize(e))
    if p.inf then None
    else
      var a = pZero; var b = pZero; var ok = true
      for (m, cf) <- p.ts do
        if ok then
          if m.exists((k, ae) => k != name && occurs(ae._1, name)) then ok = false
          else m.get(name) match
            case None => a = addP(a, P(false, Map(m -> cf)))
            case Some((_, 1)) => b = addP(b, P(false, Map((m - name) -> cf)))
            case Some(_) => ok = false
      if ok then Some((fromP(a), fromP(b))) else None
end Sym

// ================================================================================================
// 2. AMOUNTS AND COST VECTORS
// ================================================================================================

/** A cost component.  `Unbounded` is EXPLICIT — the analysis never silently saturates a quantity it
 *  could not bound; it says which construct defeated it. */
enum Amount:
  case Bounded(e: Sym)
  case Unbounded(reason: String)

  def +(o: Amount): Amount = (this, o) match
    case (Bounded(x), Bounded(y)) => Bounded(x + y)
    case (Unbounded(r), _) => Unbounded(r)
    case (_, Unbounded(r)) => Unbounded(r)

  /** `⊤ · 0 = 0`: doing an unbounded-cost thing zero times is free. */
  def *(o: Amount): Amount = (this, o) match
    case (Bounded(x), Bounded(y)) => Bounded(x * y)
    case (Bounded(Sym.Const(0)), _) => Bounded(Sym.zero)
    case (_, Bounded(Sym.Const(0))) => Bounded(Sym.zero)
    case (Unbounded(r), _) => Unbounded(r)
    case (_, Unbounded(r)) => Unbounded(r)

  infix def lub(o: Amount): Amount = (this, o) match
    case (Bounded(x), Bounded(y)) => Bounded(x lub y)
    case (Unbounded(r), _) => Unbounded(r)
    case (_, Unbounded(r)) => Unbounded(r)

  def bigO: BigO = this match
    case Bounded(e) => Sym.bigO(e)
    case Unbounded(_) => BigO.inf
  /** numeric read-off at a concrete valuation — the calibration harness's only use of the symbols */
  def at(v: Map[String, Double]): Double = this match
    case Bounded(e) => Sym.evalAt(e, v)
    case Unbounded(_) => Double.PositiveInfinity
  def isUnbounded: Boolean = this match { case Unbounded(_) => true; case _ => false }
  def symOpt: Option[Sym] = this match { case Bounded(e) => Some(e); case _ => None }
  def show: String = this match
    case Bounded(e) => e.show
    case Unbounded(r) => s"UNBOUNDED($r)"

object Amount:
  val zero: Amount = Bounded(Sym.zero)
  def of(e: Sym): Amount = Bounded(Sym.normalize(e))

/** A numeric cost read-off, used ONLY by the calibration harness. */
final case class CostPoint(work: Double, alloc: Double, rounds: Double, touch: Double):
  def apply(c: EffortComponent): Double = c match
    case EffortComponent.Work => work
    case EffortComponent.Alloc => alloc
    case EffortComponent.Rounds => rounds
    case EffortComponent.Touch => touch
    case EffortComponent.Explain => 0.0

/** THE COST COMPONENTS.  Three of the four are now DEFINED BY COUNTED EVENTS
 *  ([[EffortComponent]]), which is what makes tightness measurable at all (review.md finding 2):
 *
 *   - `work`   — [[EffortComponent.Work]]: node dispatches, path-item comparisons, cursor reads,
 *                trie-operation entries.  Oracle: `Events.work`.
 *   - `alloc`  — [[EffortComponent.Alloc]]: fresh paths, fresh trie nodes, executor frames.
 *                Oracle: `Events.alloc`.
 *   - `rounds` — [[EffortComponent.Rounds]]: loop-body entries, fixpoint rounds, routine calls.
 *                Oracle: `Events.rounds`.
 *   - `touch`  — [[EffortComponent.Touch]]: the per-node descent INSIDE the trie algebra —
 *                `ITrie`-level recursive entries and `IntMap` Patricia node visits.  Oracle:
 *                `Events.touch`, on the three trie-shaped backends.  It carries the asymptotic
 *                content the other three lose (a merge of two n-node tries is ONE `TrieOpEntry` but
 *                Θ(n) node visits).  For [[ReferenceCost]] ALONE it has no oracle — `eval` does the
 *                equivalent work inside `Set`, whose internals carry no hooks — and that model says so
 *                via [[CostModel.touchNoOracle]] rather than the harness filtering it out. */
final case class Cost(work: Amount, alloc: Amount, rounds: Amount, touch: Amount = Amount.zero):
  def +(o: Cost): Cost = Cost(work + o.work, alloc + o.alloc, rounds + o.rounds, touch + o.touch)
  def scale(k: Sym): Cost = scale(Amount.of(k))
  def scale(k: Amount): Cost = Cost(work * k, alloc * k, rounds * k, touch * k)
  def bigO: BigO = BigO.max(BigO.max(work.bigO, alloc.bigO), BigO.max(rounds.bigO, touch.bigO))
  /** the component a counted [[EffortComponent]] must be compared against */
  def calibrated(c: EffortComponent): Amount = c match
    case EffortComponent.Work => work
    case EffortComponent.Alloc => alloc
    case EffortComponent.Rounds => rounds
    case EffortComponent.Touch => touch
    case EffortComponent.Explain => Amount.zero
  def at(v: Map[String, Double]): CostPoint = CostPoint(work.at(v), alloc.at(v), rounds.at(v), touch.at(v))
  def show: String = s"work=${work.show}  alloc=${alloc.show}  rounds=${rounds.show}  touch=${touch.show}"
  def showO: String = s"work=${work.bigO.show}  alloc=${alloc.bigO.show}  rounds=${rounds.bigO.show}  touch=${touch.bigO.show}"

object Cost:
  val zero: Cost = Cost(Amount.zero, Amount.zero, Amount.zero, Amount.zero)
  def w(e: Sym): Cost = Cost(Amount.of(e), Amount.zero, Amount.zero, Amount.zero)
  def wa(wk: Sym, al: Sym): Cost = Cost(Amount.of(wk), Amount.of(al), Amount.zero, Amount.zero)
  def r(e: Sym): Cost = Cost(Amount.zero, Amount.zero, Amount.of(e), Amount.zero)
  def t(e: Sym): Cost = Cost(Amount.zero, Amount.zero, Amount.zero, Amount.of(e))
  /** the general constructor, in component order */
  def of(work: Sym = Sym.zero, alloc: Sym = Sym.zero, rounds: Sym = Sym.zero, touch: Sym = Sym.zero): Cost =
    Cost(Amount.of(work), Amount.of(alloc), Amount.of(rounds), Amount.of(touch))
  def unbounded(reason: String): Cost =
    Cost(Amount.Unbounded(reason), Amount.Unbounded(reason), Amount.Unbounded(reason), Amount.Unbounded(reason))

/** A LOWER/UPPER cost interval (review.md finding 2: "return lower/upper cost intervals, not only a
 *  worst-case symbolic upper").
 *
 *  The invariant every constructor here maintains is `lo ≤ actual ≤ hi` for the executable the model
 *  names.  The generic lower endpoint is the one whispers §7 prescribes — one dispatch/operation,
 *  zero allocations — replaced by the EXACT value wherever the syntax or the shape domain proves a
 *  fast path (a warm literal, a full-window `Range`, an `x ∖ x`, a provably empty left operand). */
final case class CostInterval(lo: Cost, hi: Cost):
  def +(o: CostInterval): CostInterval = CostInterval(lo + o.lo, hi + o.hi)
  /** scale by an interval of multiplicities (a loop's lower/upper group count) */
  def scale(kLo: Sym, kHi: Sym): CostInterval = CostInterval(lo.scale(kLo), hi.scale(kHi))
  def scale(kLo: Amount, kHi: Amount): CostInterval = CostInterval(lo.scale(kLo), hi.scale(kHi))
  /** Drop the LOWER endpoint of `touch` — see the "TOUCH LOWER ENDPOINT IS 0 BY CONSTRUCTION" note in
   *  the file header.  Applied once, at the end of [[SpatialCost.analyze]]. */
  def withoutTouchLower: CostInterval = CostInterval(lo.copy(touch = Amount.zero), hi)
  def show: String = s"LOWER ${lo.show}\n  UPPER ${hi.show}"

object CostInterval:
  val zero: CostInterval = CostInterval(Cost.zero, Cost.zero)
  /** the model knows this cost EXACTLY (a fast path) */
  def exact(c: Cost): CostInterval = CostInterval(c, c)
  /** an upper bound with the generic "one step, no allocation" lower endpoint */
  def upper(hi: Cost): CostInterval = CostInterval(Cost.of(work = Sym.one), hi)
  /** an upper bound with no lower knowledge at all */
  def upperOnly(hi: Cost): CostInterval = CostInterval(Cost.zero, hi)
  def unbounded(reason: String): CostInterval = CostInterval(Cost.zero, Cost.unbounded(reason))

/** The size/shape facts a cost transfer consumes.  These are the ANALYSIS INPUTS — bounds on the
 *  path count, on the item-length of a path, and on the distinct-head count (an `Iteration`'s group
 *  count).  Symbolic in the free mentions/refs, refined by whatever `SpatialTyping`/`SpatialTypes`
 *  can prove.
 *
 *  `size`/`len`/`heads` are UPPER bounds; `sizeLo`/`headsLo` are the matching LOWER bounds, which
 *  default to 0 (always sound) and only become non-trivial where a declared type or a literal proves
 *  them.  They exist so a loop's body cost can be scaled by an interval of group counts rather than
 *  by the worst case alone. */
final case class Meas(size: Sym, len: Sym, heads: Sym,
                      sizeLo: Sym = Sym.zero, headsLo: Sym = Sym.zero,
                      nodesHi: Option[Sym] = None,
                      headKeys: Option[Set[PathItem]] = None):
  /** Worst-case LOGICAL trie node count: the always-present root plus one node per distinct
   *  non-empty prefix, with no prefix sharing assumed.
   *
   *  The `+ 1` is load-bearing and was missing: `ITrie.empty` is one root object and
   *  `SpaceZipper.materialize` allocates one `ITrie` per visited node INCLUDING the root, so a single
   *  path of length 4 materialises 5 nodes.  Dropping the root made the zipper's `alloc` upper bound
   *  fall below the counted `FreshNode` total (caught by the corpus calibration: 5 counted against a
   *  predicted 4).
   *
   *  This is still the coarse envelope, and it is the one place this file knowingly throws
   *  information away: the EXACT count is `1 + Σ_{d≥1} K_d` over the distinct-prefix counts
   *  (whispers §1).  Once a `SpatialFacts.trieNodes` is available, `nodes` should consume it; until
   *  then `1 + size · len` is the FALLBACK.
   *
   *  `nodesHi` carries the exact identity when one is available: [[SpatialFacts.trieNodes]] computes
   *  `1 + Σ_{d≥1} K_d` from the shape's distinct-prefix profile, which keeps every bit of prefix
   *  sharing that `size · len` throws away.  `refine` meets the two, so the model uses whichever is
   *  tighter and stays sound either way. */
  def nodes: Sym = nodesHi.getOrElse(Sym.one + size * len)
  /** is the space PROVABLY EMPTY here?  Executors have explicit empty guards (`execT`'s
   *  `if a.isEmpty then ITrie.empty`, `ITrie.union`'s `if a.isEmpty then b`), so this is a real
   *  fast-path predicate and not a modelling convenience. */
  def provablyEmpty: Boolean = size == Sym.Const(0)
  /** is the space PROVABLY NON-EMPTY (a constant positive lower bound)? */
  def provablyNonEmpty: Boolean = sizeLo match { case Sym.Const(n) => n >= 1L; case _ => false }
  /** THE EXACT SET OF POSSIBLY-PRESENT HEADS, when the shape's head set is CLOSED (`others.hi == 0`,
   *  i.e. no untracked head) — otherwise `None`.
   *
   *  Carried on the measure rather than re-queried, because it is a by-product of the `shapeAt` call
   *  `refine` already makes for every node: asking a second time (and a third, for the other operand)
   *  cost an extra `SpatialTyping.infer` per merge node and pushed `SpatialPipelineCheck`'s
   *  analysis-latency gate over its budget.  Its only consumer is [[headDisjoint]]. */
  def headDisjointFrom(o: Meas): Boolean = (headKeys, o.headKeys) match
    case (Some(a), Some(b)) => a.intersect(b).isEmpty
    case _ => false
  def show: String =
    val lo = if sizeLo == Sym.zero then "" else s" |·|≥${sizeLo.show}"
    s"|·|≤${size.show} len≤${len.show} heads≤${heads.show}$lo"

object Meas:
  val empty: Meas = Meas(Sym.zero, Sym.zero, Sym.zero, Sym.zero, Sym.zero)
  val top: Meas = Meas(Sym.Inf, Sym.Inf, Sym.Inf, Sym.zero, Sym.zero)
  /** the exact measure of a concrete value */
  def exact(size: Sym, len: Sym, heads: Sym): Meas = Meas(size, len, heads, size, heads)

// ================================================================================================
// 3. BACKEND COST INSTANCES
// ================================================================================================

/** WHICH EXECUTABLE a cost report describes.  review.md finding 2, fourth bullet: one `TrieCost`
 *  instance was documented as the "trie/zipper evaluator" although `execT` and `execZ` are materially
 *  different programs.  They now have separate instances, and each names its executable. */
enum Backend:
  case Reference, Trie, Graph, Zipper
  def executable: String = this match
    case Reference => "eval (MORKL.scala) over Set[PathValue]"
    case Trie => "evalI (IntTrie.scala) over ITrie"
    case Graph => "execT (GraphExec.scala) over the RecursiveOpGraph"
    case Zipper => "execZ (Zipper.scala) over fused SpaceZippers"
  def slug: String = toString.toLowerCase

/** A per-operator cost transfer.  Each method returns the LOCAL cost INTERVAL of one node,
 *  EXCLUDING the node's own dispatch (which the traversal adds once, uniformly, via [[dispatch]]);
 *  the traversal adds the operands' costs and scales loop bodies by their group-count interval.
 *
 *  Four instances over the SAME facts is the point: a program has a different cost on each
 *  executable, and each instance is tied to counted events so its tightness is measurable. */
trait CostModel:
  def backend: Backend
  def phase: ExecutionPhase
  def name: String = s"${backend.slug}/${if phase == ExecutionPhase.Warm then "warm" else "cold"}"

  /** WHY this instance's `touch` component has no counted oracle, when it has none.
   *
   *  `None` (the default) means `touch` IS calibrated against
   *  [[EffortEvent.TrieNodeVisit]] + [[EffortEvent.PatriciaVisit]].  `Some(reason)` is a declared
   *  exclusion from the tightness gate; `SpatialEventsCheck` asserts that exactly one instance per
   *  phase declares one, so this list cannot grow without a test failing.  This is review.md item 1's
   *  fifth point: `touch` either has a counted oracle or says, in the model itself, that it does not. */
  def touchNoOracle: Option[String] = None

  /** the node's own dispatch: `AstDispatch` / `TrieDispatch` / `GraphNodeDispatch` / `ZipperBuild` */
  def dispatch: CostInterval = CostInterval.exact(Cost.of(work = Sym.one))
  /** A `Path` subterm attached to this node.  The two counts are DIFFERENT and both syntactic:
   *  `nodes` is every `Path` subterm (what `eval.recp` dispatches on), `slots` is the number of
   *  operation-graph slots `transpile` allocates for it (a `Deref` reuses the prologue slot, so it
   *  costs none).  A model that ignored this would predict fewer dispatches than `execT` performs. */
  def pathTerm(nodes: Sym, slots: Sym): CostInterval = CostInterval.zero
  /** the per-iteration-subgraph prologue slots (`ExtractPathRef` + `ExtractSpaceMention`) */
  def loopPrologue: CostInterval = CostInterval.zero
  /** the per-fixpoint-subgraph prologue slot (`ExtractSpaceMention(rec)`) */
  def fixPrologue: CostInterval = CostInterval.zero
  /** A `Mention`'s own dispatch.  It differs from [[dispatch]] on the graph backend only: `transpile`
   *  resolves a mention to the EXISTING `ExtractSpaceMention` prologue slot (`g.find`) instead of
   *  storing a new node, so a repeated mention costs no extra `GraphNodeDispatch`. */
  def mentionDispatch: CostInterval = dispatch
  /** the root materialisation, charged ONCE by [[SpatialCost.analyze]] (only the zipper has one).
   *  `concrete` says the root cursor is already a `Lit`, in which case `SpaceZipper.materialize`
   *  returns the existing trie and allocates nothing. */
  def finish(root: Meas, concrete: Boolean): CostInterval = CostInterval.zero
  /** does this executable leave itself for another one on control flow?  `execZ` does: `transpileZ`
   *  materialises `Iteration`/`Fold`/`Fixpoint`/`Call`/grounded subterms through `evalI`. */
  def controlFlowFallback: Option[Backend] = None
  /** the cost of crossing that boundary */
  def fallbackEntry: CostInterval = CostInterval.zero
  /** does the executable RE-READ the left operand of a `Raffination`?  `eval` does — it rewrites to
   *  `Subtraction(x, Restriction(x, y))` and evaluates `recs(x)` twice. */
  def raffinationRereadsX: Boolean = false

  def empty: CostInterval = CostInterval.zero
  def literal(m: Meas): CostInterval
  def singleton(plen: Sym): CostInterval
  def mention(m: Meas): CostInterval
  /** `same` = the two operands are the SAME already-materialised object, so a pointer-identity
   *  short circuit fires (`ITrie.union`'s `a eq b`, `SpaceZipper.sameSpace`) */
  def union(a: Meas, b: Meas, same: Boolean): CostInterval
  def inter(a: Meas, b: Meas, disjoint: Boolean, same: Boolean): CostInterval
  def subtract(a: Meas, b: Meas, disjoint: Boolean, same: Boolean): CostInterval
  def restrict(x: Meas, y: Meas): CostInterval
  def raffine(x: Meas, y: Meas): CostInterval
  def compose(a: Meas, b: Meas): CostInterval
  def wrap(src: Meas, plen: Sym): CostInterval
  def unwrap(src: Meas, plen: Sym): CostInterval
  def tailsUnion(src: Meas): CostInterval
  def tailsInter(src: Meas): CostInterval
  /** `identity` = the window provably covers the whole space, so the implementation may return its
   *  input unchanged (review.md finding 2, second and third bullets) */
  def range(x: Meas, window: Sym, identity: Boolean): CostInterval
  /** splitting the source into head-groups, EXCLUDING the body */
  def group(src: Meas): CostInterval
  /** unioning the per-group body results into the loop's output */
  def collect(groups: Sym, body: Meas): CostInterval
  def foldStep(groups: Sym, updNodes: Sym, updLen: Sym): CostInterval
  /** one fixpoint round's union + equality check, EXCLUDING the body */
  def fixStep(acc: Meas, body: Meas): CostInterval
  /** entering one routine call: a `CallEntry`, plus a frame where the executable allocates one */
  def callFrame: CostInterval = CostInterval.exact(Cost.of(rounds = Sym.one))

// ------------------------------------------------------------------------------------------------
// 3a. THE REFERENCE EVALUATOR — `eval`, Set[PathValue]
// ------------------------------------------------------------------------------------------------

/** `eval` (MORKL.scala).  Counted events: `AstDispatch`, `PathDispatch`, `PathItemComparison`,
 *  `FreshPath`, `LoopBodyEntry`, `FixpointRound`, `CallEntry`.
 *
 *  THREE ATTRIBUTIONS FIXED HERE (review.md finding 2):
 *
 *   1. `eval(Literal(v))` RETURNS THE STORED SET (MORKL.scala, `case Space.Literal`).  A warm
 *      literal is one dispatch and zero allocations; the `|v|` construction cost belongs to the
 *      COLD phase, where whoever built the literal paid it.  The old model charged `|v|` work and
 *      `|v|` alloc unconditionally.
 *   2. `sliceRange` returns its input unchanged when the window covers the whole space
 *      (`if lo == 0 && hi == s.size then s`), so a full `Range` performs NO comparison sort.  The
 *      old model always charged `n log n`.  The non-identity case's `n log n · len` term is now the
 *      one thing here with a real oracle: `pathValueOrdering.compare` counts every item comparison.
 *   3. `Restriction`'s nested `startsWith` scan and `Unwrap`'s prefix test are counted item by item
 *      through `Effort.startsWith`, so `work` for those operators is measured, not asserted.
 *
 *  `touch` carries the un-oracled `Set`-internal element cost (see [[Cost]]). */
final class ReferenceCost(val phase: ExecutionPhase) extends CostModel:
  import Sym.tighter
  val backend = Backend.Reference
  override def raffinationRereadsX = true                     // recs(x) runs twice; see below
  /** THE ONE DECLARED ORACLE GAP in this file.  `eval` never touches an `ITrie`, so no `TrieNodeVisit`
   *  or `PatriciaVisit` is ever counted for it, and the equivalent work happens inside
   *  `scala.collection.immutable.Set` — standard-library code this repository does not own and cannot
   *  hook.  Synthesising an "actual" element count from operand sizes would measure the model against
   *  itself, so it is not done: these `touch` claims are a MODEL, evidenced only by the secondary
   *  rank-correlation trend in `SpatialCostCheck`. */
  override def touchNoOracle: Option[String] =
    Some("eval works over scala.collection.immutable.Set[PathValue] and performs no ITrie work; the " +
         "Set internals (hash probes, bucket copies) are standard-library code with no hooks")

  def literal(m: Meas): CostInterval = phase match
    case ExecutionPhase.Warm => CostInterval.exact(Cost.zero)             // the stored Set is returned
    case ExecutionPhase.Cold => CostInterval.exact(Cost.of(alloc = m.size, touch = m.size))
  /** `eval.recp` dispatches on EVERY Path subterm, `Deref` included */
  override def pathTerm(nodes: Sym, slots: Sym): CostInterval = CostInterval.exact(Cost.of(work = nodes))
  def singleton(plen: Sym): CostInterval =
    CostInterval.exact(Cost.of(alloc = Sym.one, touch = plen))
  def mention(m: Meas): CostInterval = CostInterval.exact(Cost.zero)      // already a materialised set
  def union(a: Meas, b: Meas, same: Boolean): CostInterval =
    CostInterval.exact(Cost.of(touch = a.size + b.size))                  // no PathValue allocated
  def inter(a: Meas, b: Meas, disjoint: Boolean, same: Boolean): CostInterval =
    CostInterval.exact(Cost.of(touch = a.size + b.size))                  // a set evaluator CANNOT skip
  def subtract(a: Meas, b: Meas, disjoint: Boolean, same: Boolean): CostInterval =
    CostInterval.exact(Cost.of(touch = a.size + b.size))
  def restrict(x: Meas, y: Meas): CostInterval =
    // recs(x).filter(p => prefixes.exists(q => startsWith(p, q))): a NESTED scan, and every
    // startsWith compares at most min(len(x), len(y)) items.  Each comparison is COUNTED.
    CostInterval(Cost.zero,
                 Cost.of(work = x.size * y.size * tighter(x.len, y.len), touch = x.size * (Sym.one + y.size)))
  def raffine(x: Meas, y: Meas): CostInterval =
    // eval rewrites `x \| y` to `Subtraction(x, Restriction(x, y))`: two SYNTHESISED nodes (hence
    // two extra dispatches) and a second full evaluation of x (see `raffinationRereadsX`).
    CostInterval(Cost.of(work = Sym.c(2)),
                 Cost.of(work = Sym.c(2) + x.size * y.size * tighter(x.len, y.len),
                         touch = x.size * (Sym.c(2) + y.size)))
  def compose(a: Meas, b: Meas): CostInterval =
    CostInterval(Cost.of(alloc = a.sizeLo * b.sizeLo),
                 Cost.of(alloc = a.size * b.size, touch = a.size * b.size * (a.len + b.len)))
  def wrap(src: Meas, plen: Sym): CostInterval =
    // recs(Composition(Singleton(p), src)): 2 synthesised dispatches, 1 + |src| fresh paths
    CostInterval(Cost.of(work = Sym.c(2), alloc = Sym.one + src.sizeLo),
                 Cost.of(work = Sym.c(2) + plen, alloc = Sym.one + src.size,
                         touch = src.size * (plen + src.len)))
  def unwrap(src: Meas, plen: Sym): CostInterval =
    CostInterval(Cost.zero,
                 Cost.of(work = src.size * plen, alloc = src.size, touch = src.size * (plen + src.len)))
  def tailsUnion(src: Meas): CostInterval =
    CostInterval(Cost.zero, Cost.of(alloc = src.size, touch = src.size))
  def tailsInter(src: Meas): CostInterval =
    CostInterval(Cost.zero, Cost.of(alloc = src.size, touch = src.size + src.size))
  def range(x: Meas, window: Sym, identity: Boolean): CostInterval =
    if identity then CostInterval.exact(Cost.of(touch = Sym.one))         // `s.size`, then return `s`
    else CostInterval(Cost.zero,
                      Cost.of(work = x.size * Sym.log(x.size) * x.len,    // COUNTED sort comparisons
                              touch = x.size * Sym.log(x.size)))
  def group(src: Meas): CostInterval =
    // the `collect{ PathValue(h::Nil) -> PathValue(tail) }.groupMap` allocates TWO paths per source
    // path THAT HAS A HEAD — the ε path is skipped, so the count has no lower bound from |src| alone
    CostInterval(Cost.zero, Cost.of(alloc = Sym.c(2) * src.size, touch = src.size))
  def collect(groups: Sym, body: Meas): CostInterval =
    CostInterval.exact(Cost.of(touch = groups * body.size))              // the yield reuses body paths
  def foldStep(groups: Sym, updNodes: Sym, updLen: Sym): CostInterval =
    // per group: eval(Singleton(update)) is one AstDispatch plus one PathDispatch per update subterm,
    // and it builds the fresh accumulator path
    CostInterval.upperOnly(Cost.of(work = groups * (Sym.one + updNodes), alloc = Sym.c(2) * groups,
                                   touch = groups * updLen))
  def fixStep(acc: Meas, body: Meas): CostInterval =
    CostInterval.exact(Cost.of(touch = acc.size + body.size))            // the `nxt == cur` check

// ------------------------------------------------------------------------------------------------
// 3b. THE TRIE ALGEBRA — shared by `evalI` and `execT`
// ------------------------------------------------------------------------------------------------

/** The `ITrie` algebra costs, shared by the two executables that run it directly.
 *
 *  Three structural wins over the reference evaluator, and they are why this file exists:
 *
 *   1. a merge only visits SHARED structure, so an intersection/subtraction whose operands the
 *      shape domain proves disjoint costs one top-level head comparison and allocates NOTHING;
 *   2. `Unwrap`/`Wrap` are prefix moves: descend `|p|` levels and hand back the focused subtrie
 *      (alloc 0), or allocate a `|p|`-node spine over a SHARED child — neither is proportional to
 *      `|src|`;
 *   3. pointer identity prunes whole branches (`a eq b` in `union`/`intersection`/`subtraction`).
 *
 *  It is NOT uniformly cheaper: `collect` pays per trie node rather than per path, so a loop whose
 *  body produces long paths costs more here.
 *
 *  **RANGE IS NOT FREE (review.md finding 2, third bullet).**  The old comment claimed "ordered
 *  walk, NO SORT".  `ITrie.range` (IntTrie.scala) (a) computes the recursive `t.size` BEFORE the
 *  identity check, so even a full-window `Range` walks every node, and (b) sorts each visited node's
 *  child keys by their un-interned value (`keysIterator.toArray.sortBy(Interner.unintern)`).  Both
 *  are priced below. */
sealed abstract class TrieAlgebraCost(val phase: ExecutionPhase) extends CostModel:
  import Sym.tighter
  protected def nd(m: Meas): Sym = m.nodes
  /** One entry into the ITrie algebra as counted by the EXECUTOR'S OWN slot loop
   *  ([[EffortEvent.TrieOpEntry]]).  `execT` emits one per space slot, so [[GraphCost]] charges 1;
   *  `evalI` emits none — its per-node [[EffortEvent.TrieDispatch]] (charged by [[dispatch]]) already
   *  covers the node — so [[TrieCostModel]] charges 0.  Charging 1 there doubled the predicted work of
   *  every trie program. */
  protected def opEntry: Sym

  /** COUNTED `touch` PER LOGICAL TRIE NODE — the constant that makes every `touch` bound below sound.
   *
   *  One merge of two tries `A`, `B` counts:
   *   - at most `min(N(A), N(B))` [[EffortEvent.TrieNodeVisit]]s (one per recursive `ITrie`-level
   *     entry, which happens only where a key is present in both), and
   *   - at most `2 (N(A) + N(B))` [[EffortEvent.PatriciaVisit]]s: a Patricia tree over `k` keys has at
   *     most `2k-1` nodes, a simultaneous descent visits at most the nodes of both trees, and every
   *     `IntMap` node sits on the child map of exactly one `ITrie` node, so summing over the levels
   *     gives `2 (child edges of A + of B) < 2 (N(A) + N(B))`.
   *
   *  Hence `3 (N(A) + N(B))`.  This is a WORST CASE: pointer identity, empty operands and Patricia
   *  prefix mismatches all cut it, which is why the measured slack on `touch` is much larger than on
   *  the dispatch-level components.  That is a fact about the executor, published in
   *  `SpatialEventsCheck`, not a licence to claim less. */
  protected val tPer: Sym = Sym.c(3)
  /** counted `touch` of ONE two-operand merge over operands of `a` and `b` logical nodes */
  protected def merge2(a: Sym, b: Sym): Sym = tPer * (a + b)
  /** counted `touch`/`alloc` of a BALANCED k-way `joinAll` over operands totalling `tot` nodes */
  protected def joinAllNodes(tot: Sym, k: Sym): Sym = tot * (Sym.one + Sym.log(k))

  protected def mk(work: Sym = Sym.zero, nodes: Sym = Sym.zero, touch: Sym = Sym.zero): Cost =
    Cost.of(work = work, alloc = nodes, touch = touch)
  /** THE GENERIC LOWER ENDPOINT OF ONE OPERATOR OF THIS ALGEBRA: its own op entry, no allocation.
   *
   *  `CostInterval.upper` cannot be used here: it hard-codes a lower endpoint of ONE work unit, which
   *  is right for `execT` (every space slot emits a `TrieOpEntry`) and WRONG for `evalI`, whose
   *  [[opEntry]] is 0 because its single per-node `TrieDispatch` is already charged by [[dispatch]].
   *  With the hard-coded 1 the trie model's lower endpoint EXCEEDED its own upper endpoint on every
   *  program with a set operation — the corpus calibration caught it as 213 inverted intervals. */
  protected def up(hi: Cost): CostInterval = CostInterval(Cost.of(work = opEntry), hi)
  /** an `ITrie` op whose FIRST operand is provably empty returns `ITrie.empty` immediately */
  protected def emptyFast: CostInterval = CostInterval.exact(Cost.of(work = opEntry, touch = Sym.one))
  /** a pointer-identity short circuit */
  protected def sharedFast: CostInterval = CostInterval.exact(Cost.of(work = opEntry, touch = Sym.one))
  override def empty: CostInterval = CostInterval.exact(Cost.of(work = opEntry))
  /** `pathItemsI` dispatches on EVERY Path subterm, `Deref` included, and counts
   *  [[EffortEvent.TriePathDispatch]] for each */
  override def pathTerm(nodes: Sym, slots: Sym): CostInterval = CostInterval.exact(Cost.of(work = nodes))

  def literal(m: Meas): CostInterval = phase match
    // iLiteral / iLiteralStr are memo caches: a warm Literal is a map lookup, NOT |v| insertions
    case ExecutionPhase.Warm => CostInterval.exact(mk(work = opEntry, touch = Sym.one))
    // cold: `fromSpaceValue` folds `union(t, singletonP(p))` over the paths — |p| fresh nodes for the
    // singleton and at most |p|+1 more for the merge spine, i.e. at most 3 nd(m) in total
    case ExecutionPhase.Cold =>
      CostInterval.exact(mk(work = opEntry, nodes = Sym.c(3) * nd(m), touch = Sym.c(3) * nd(m)))
  /** `ITrie.singleton` allocates exactly one node per path item (`epsilon` is a shared val).  NOT
   *  `exact`, because `plen` is itself only an UPPER bound whenever the path is a `Deref` whose
   *  declared length is a bound rather than a value — claiming it as a lower endpoint would predict
   *  more allocation than the run performs. */
  def singleton(plen: Sym): CostInterval = up(mk(work = opEntry, nodes = plen, touch = Sym.one))
  def mention(m: Meas): CostInterval = CostInterval.exact(Cost.of(work = opEntry))
  def union(a: Meas, b: Meas, same: Boolean): CostInterval =
    if same then sharedFast
    else if a.provablyEmpty || b.provablyEmpty then emptyFast          // `if a.isEmpty then b`
    else up(mk(work = opEntry, nodes = tighter(nd(a), nd(b)),
               touch = merge2(nd(a), nd(b))))
  def inter(a: Meas, b: Meas, disjoint: Boolean, same: Boolean): CostInterval =
    if same then sharedFast
    else if a.provablyEmpty || b.provablyEmpty then emptyFast
    // HEAD-DISJOINT (SpatialCost.headDisjoint): `intersectTries` finds no matching key and returns
    // `Nil` at once, so the only allocation is the root node `ITrie(false, Nil)` and the only descent is
    // the top-level Patricia comparison of the two head sets.  An empty RESULT buys nothing — the
    // calibration proved that (12 counted fresh nodes against a predicted 1).
    else if disjoint then CostInterval(Cost.of(work = opEntry),
                                       Cost.of(work = opEntry, alloc = Sym.one,
                                               touch = Sym.one + merge2(a.heads, b.heads)))
    else up(mk(work = opEntry, nodes = tighter(nd(a), nd(b)),
               touch = merge2(nd(a), nd(b))))
  def subtract(a: Meas, b: Meas, disjoint: Boolean, same: Boolean): CostInterval =
    if same then sharedFast                                            // `a eq b` ⇒ empty
    else if a.provablyEmpty || b.provablyEmpty then emptyFast
    else if disjoint then CostInterval(Cost.of(work = opEntry),
                                       Cost.of(work = opEntry, alloc = Sym.one,
                                               touch = Sym.one + merge2(a.heads, b.heads)))
    else up(mk(work = opEntry, nodes = tighter(nd(a), nd(b)),
               touch = merge2(nd(a), nd(b))))
  def restrict(x: Meas, y: Meas): CostInterval =
    if x.provablyEmpty || y.provablyEmpty then emptyFast
    else up(mk(work = opEntry, nodes = tighter(nd(x), nd(y)),
               touch = merge2(nd(x), nd(y))))
  def raffine(x: Meas, y: Meas): CostInterval =
    // subtraction(x, restriction(x, y)): the restriction visits x and y, the subtraction visits x and
    // the restriction's result (at most x's nodes again)
    if x.provablyEmpty then emptyFast
    else up(mk(work = Sym.c(2) * opEntry,
               nodes = nd(x) + tighter(nd(x), nd(y)),
               touch = Sym.c(2) + tPer * (Sym.c(3) * nd(x) + nd(y))))
  def compose(a: Meas, b: Meas): CostInterval =
    // one recursive entry (and one fresh node) per node of `a`, then — at every TERMINAL of `a` — a
    // `union(mapped, b)`.  Summing the merged sizes over a's nodes costs a factor len(a):
    // Σ_v N(subtree_v) ≤ N(a)·len(a) and Σ_v |subtree_v| ≤ |a|·len(a).
    if a.provablyEmpty || b.provablyEmpty then emptyFast
    else up(mk(work = opEntry, nodes = nd(a) + a.size * nd(b),
               touch = nd(a) + tPer * (nd(a) * a.len + a.size * (a.len + Sym.one) * nd(b))))
  def wrap(src: Meas, plen: Sym): CostInterval =
    // NOT exact: `ITrie.wrap` returns `empty` and allocates NOTHING when the source turns out empty at
    // run time, which the shape domain need not have proved
    if src.provablyEmpty then emptyFast
    else up(mk(work = opEntry, nodes = plen, touch = Sym.one))
  def unwrap(src: Meas, plen: Sym): CostInterval =
    if src.provablyEmpty then emptyFast                                // focus, no rebuild
    else CostInterval.exact(Cost.of(work = opEntry, touch = Sym.one + plen))
  def tailsUnion(src: Meas): CostInterval =
    // joinAll over the head children: a BALANCED pairwise merge, log(heads) levels deep
    up(mk(work = opEntry, nodes = joinAllNodes(nd(src), src.heads),
          touch = Sym.one + tPer * joinAllNodes(nd(src), src.heads)))
  def tailsInter(src: Meas): CostInterval =
    // meetAll is a LEFT FOLD of intersections over the present-head children: `heads` merges, each
    // against an accumulator of at most nd(src) nodes
    up(mk(work = opEntry, nodes = src.heads * nd(src),
          touch = Sym.one + tPer * nd(src) * (src.heads + Sym.one)))
  def range(x: Meas, window: Sym, identity: Boolean): CostInterval =
    // `val size = t.size` is a FULL recursive walk and runs before the identity check.
    val sizeWalk = nd(x)
    val w = tighter(window, x.size)
    if identity then CostInterval(Cost.of(work = opEntry),
                                  Cost.of(work = opEntry, touch = Sym.one + sizeWalk))
    else up(mk(work = opEntry,
                               // per emitted path: |p| singleton nodes plus at most |p|+1 merge nodes
                               nodes = Sym.c(3) * w * (x.len + Sym.one),
                               // the size walk, the ordered `go` walk, the per-node child-key sort
                               // (standard-library `sortBy`, so REAL but not counted — see
                               // SpatialEvents.scala gap 3), and the per-path union into the result
                               touch = Sym.c(2) * sizeWalk + sizeWalk * Sym.log(x.heads) +
                                       tPer * w * (w * x.len + x.len + Sym.c(2))))
  def group(src: Meas): CostInterval =
    CostInterval.exact(Cost.of(work = opEntry, touch = src.heads))      // the head children ARE the groups
  def collect(groups: Sym, body: Meas): CostInterval =
    // The accumulation of the per-group results.  This must cover the WORSE of the two shapes `evalI`
    // uses — `Iteration`'s balanced `joinAll` and `Fold`'s LEFT FOLD of unions — so it is the left
    // fold: `groups` merges, the k-th against an accumulator of at most `groups · nd(body)` nodes.
    // That quadratic-in-`groups` factor is real for a left fold and is the single largest source of
    // `touch` slack in the published table.
    // the `+ 1` is load-bearing: `ITrie.joinAll` is ENTERED once per loop node even when the source has
    // no head at all, so a zero-group loop still counts one TrieNodeVisit (caught by the corpus
    // calibration: 4 counted touches against a predicted 3)
    CostInterval.upperOnly(mk(work = groups * opEntry, nodes = groups * nd(body),
                              touch = Sym.one + tPer * groups * (groups + Sym.one) * nd(body)))
  def foldStep(groups: Sym, updNodes: Sym, updLen: Sym): CostInterval =
    // per group: `pathItemsI(update)` dispatches on every update subterm; the accumulator is a
    // PathValue, so nothing is allocated in the trie
    CostInterval.upperOnly(mk(work = groups * (opEntry + updNodes), touch = groups * updLen))
  def fixStep(acc: Meas, body: Meas): CostInterval =
    up(mk(work = opEntry, nodes = tighter(nd(acc), nd(body)),
          touch = merge2(nd(acc), nd(body))))

/** `evalI` (IntTrie.scala): one AST dispatch per node, then the trie algebra.
 *
 *  CALIBRATED (review.md item 1).  `evalI`, `ITrie` and `IntTrieOps` now carry hooks, so this backend
 *  has counted runs for all four components: [[EffortEvent.TrieDispatch]] +
 *  [[EffortEvent.TriePathDispatch]] for `work`, [[EffortEvent.FreshTrieNode]] for `alloc`, `evalI`'s
 *  own [[EffortEvent.LoopBodyEntry]]/[[EffortEvent.FixpointRound]]/[[EffortEvent.CallEntry]] for
 *  `rounds`, and [[EffortEvent.TrieNodeVisit]] + [[EffortEvent.PatriciaVisit]] for `touch`. */
final class TrieCostModel(p: ExecutionPhase) extends TrieAlgebraCost(p):
  val backend = Backend.Trie
  /** `evalI` emits no [[EffortEvent.TrieOpEntry]]: one [[EffortEvent.TrieDispatch]] per node covers
   *  both the AST dispatch and the algebra entry, and [[dispatch]] already charges it. */
  protected def opEntry: Sym = Sym.zero

/** `execT` (GraphExec.scala): the same trie algebra, executed as a flat dataflow graph.
 *
 *  Where it differs from `evalI`, and why one formula could not describe both:
 *
 *   - one `GraphNodeDispatch` per SLOT, including the `ExtractPathRef`/`ExtractSpaceMention`
 *     prologue slots that `evalI` has no analogue for;
 *   - every subgraph allocates a FRAME: one per `Iteration` node (reused across all its children —
 *     that reuse is the reason an n-queens nest is affordable), one per `Fixpoint`, one per `Call`;
 *   - `Literal`/`Constant` payloads are decoded from STRINGS through the `iLiteralStr` /
 *     `internConstStr` caches, so a cold graph pays a decode the interpreters do not. */
final class GraphCost(p: ExecutionPhase) extends TrieAlgebraCost(p):
  val backend = Backend.Graph
  /** `execT` emits one [[EffortEvent.TrieOpEntry]] per `case "space"` slot, on top of the
   *  [[EffortEvent.GraphNodeDispatch]] that [[dispatch]] charges. */
  protected def opEntry: Sym = Sym.one
  /** A mention resolves to the EXISTING prologue slot (`g.find`): no new graph node, so neither a
   *  `GraphNodeDispatch` nor a `TrieOpEntry`.  Charging either made the lower endpoint exceed the
   *  counted total on every program with a repeated mention (caught by the corpus calibration). */
  override def mentionDispatch: CostInterval = CostInterval.zero
  override def mention(m: Meas): CostInterval = CostInterval.zero
  /** the graph allocates one frame per call, and `CallEntry` is counted.  `alloc` now also counts
   *  `FreshTrieNode`, so this is a LOWER endpoint of 1 frame and an upper of 1 frame — the trie nodes
   *  the callee allocates are charged by the callee's own operators. */
  override def callFrame: CostInterval =
    CostInterval.exact(Cost.of(alloc = Sym.one, rounds = Sym.one))
  /** every non-`Deref` path subterm is its own dispatched graph slot */
  override def pathTerm(nodes: Sym, slots: Sym): CostInterval = CostInterval.exact(Cost.of(work = slots))
  /** An `Iteration`/`Fixpoint` node is a `Right(subgraph)` entry, NOT a `case "space"` slot, so it
   *  dispatches but emits no `TrieOpEntry`.  Grouping itself is free: the source trie's children ARE
   *  the groups. */
  override def group(src: Meas): CostInterval = CostInterval.exact(Cost.of(touch = src.heads))
  /** ONE frame per loop node, reused across every child — the reason a deep n-queens nest is
   *  affordable at all.  The per-child prologue dispatches are charged by [[collect]], which the
   *  traversal already scales by the group count. */
  override def loopPrologue: CostInterval = CostInterval.exact(Cost.of(alloc = Sym.one))
  override def fixPrologue: CostInterval = CostInterval.exact(Cost.of(alloc = Sym.one))
  /** per child: the subgraph's `ExtractPathRef` + `ExtractSpaceMention` prologue slots and a possible
   *  trailing pass-through `Union`, all re-dispatched by `execT(sg, ...)` on every iteration */
  override def collect(groups: Sym, body: Meas): CostInterval =
    // per child: `ExtractPathRef` (a "path" slot: 1 dispatch) + `ExtractSpaceMention` (a "space"
    // slot: 1 dispatch + 1 TrieOpEntry) + a possible trailing pass-through `Union` (another 2)
    CostInterval.upperOnly(super.collect(groups, body).hi + Cost.of(work = Sym.c(5) * groups))
  override def fixStep(acc: Meas, body: Meas): CostInterval =
    // per round: the `ExtractSpaceMention(rec)` slot, plus a possible pass-through
    CostInterval.upperOnly(super.fixStep(acc, body).hi + Cost.of(work = Sym.c(4)))

// ------------------------------------------------------------------------------------------------
// 3c. THE FUSED ZIPPER — `execZ`
// ------------------------------------------------------------------------------------------------

/** `execZ` (Zipper.scala).  Counted events: `ZipperBuild`, `ZipperCursorRead`,
 *  `ZipperMaterializeNode`, `FreshNode`, `ReusedSpace`, `ZipperFallbackToEvalI`.
 *
 *  This is the instance review.md finding 2 says cannot share a formula with `execT`:
 *
 *   - the local set algebra ALLOCATES NOTHING while it is built.  Each operator is a virtual cursor;
 *     the cost is one `ZipperCursorRead` PER LAYER per visited node.  A three-deep fused expression
 *     therefore reads each result node three times where `execT` would have built two intermediate
 *     tries.
 *   - allocation happens ONCE, in `SpaceZipper.materialize` at the root: one `ZipperMaterializeNode`
 *     and one `FreshNode` per logical result node.  That is charged by [[finish]], not per operator.
 *   - `Unwrap` is pure navigation and its result is a `Lit` cursor, so `materialize` returns the
 *     ALREADY EXISTING subtrie: zero allocation, whatever `|src|` is.
 *   - control flow is NOT fused.  `transpileZ` falls through to `evalI` for
 *     `Iteration`/`Fold`/`Fixpoint`/`Call`/grounded terms, so such a subterm is priced with the TRIE
 *     model and the crossing is counted.  Reporting one number for both halves is exactly the
 *     conflation the review objects to. */
final class ZipperCost(val phase: ExecutionPhase) extends CostModel:
  import Sym.tighter
  val backend = Backend.Zipper
  /** Per visited node and per layer: two cursor reads (`terminal` + `children`) plus, at whichever
   *  layer forces the materialisation, one `ZipperMaterializeNode`. */
  private def reads(m: Meas): Sym = Sym.c(4) * m.nodes
  /** THE COST OF ONE FUSED BINARY LAYER over a result of `res` logical nodes.
   *
   *  A cursor query CASCADES: `Union.terminal` calls `a.terminal` AND `b.terminal`, each of which is
   *  itself a counted read at its own layer, and `materialize` pays one `ZipperMaterializeNode` per
   *  node on top.  Charging only `reads(a) + reads(b)` treated the operator's OWN layer as free and put
   *  the predicted work below the counted total on 4 of the 200 corpus programs (82 counted work events
   *  against a predicted 75).  Own layer plus both operands' layers is the sound envelope. */
  private def fuse2(a: Meas, b: Meas, res: Sym): Sym = Sym.c(4) * res + reads(a) + reads(b)
  /** NO POSITIVE LOWER BOUND ON CURSOR READS IS CLAIMED.  A fused operator is a lazy cursor: if its
   *  parent never descends into it — a `Composition` whose left operand has no terminal never reads
   *  `b`, an `Intersection` that prunes at the root never reads below it — it performs ZERO reads.  The
   *  meaningful lower endpoint for this backend is [[dispatch]], one `ZipperBuild` per lifted node,
   *  which `transpileZ` really does emit unconditionally. */
  private def up(hi: Cost): CostInterval = CostInterval.upperOnly(hi)
  override def raffinationRereadsX = true            // `Subtraction(x, restriction(x, y))` reads x twice
  override def controlFlowFallback: Option[Backend] = Some(Backend.Trie)
  override def fallbackEntry: CostInterval = CostInterval.exact(Cost.of(work = Sym.one))
  /** MATERIALISATION IS CHARGED PER OPERATOR, NOT AT THE ROOT.
   *
   *  `SpaceZipper.materialize` allocates one `ITrie` per node it VISITS, not per node of the result:
   *  it descends into every child of the fused cursor and only then discards the empty ones.  A term
   *  whose result is empty can therefore still allocate — the corpus calibration caught exactly that
   *  (5 counted `FreshNode`s against a root-result bound of 1).  Each local operator's `alloc` is
   *  bounded by ITS OWN operands' node counts, which is the quantity materialize actually walks, and
   *  the sum over the term is a sound envelope.  A concrete (`Lit`) cursor is never re-materialised,
   *  which is why `mention`/`literal`/`singleton`/`unwrap` contribute nothing. */
  override def finish(root: Meas, concrete: Boolean): CostInterval = CostInterval.zero
  /** `transpileZ` calls `pathItemsI` for `Singleton`/`Wrap`/`Unwrap`, which dispatches on every Path
   *  subterm and counts [[EffortEvent.TriePathDispatch]] — a work event the zipper model owes. */
  override def pathTerm(nodes: Sym, slots: Sym): CostInterval = CostInterval.exact(Cost.of(work = nodes))

  // ALLOC MEANS `FreshNode` (what `SpaceZipper.materialize` allocates) PLUS `FreshTrieNode` (what the
  // `ITrie` calls the zipper still makes — `singleton`, `range`, `tailsIntersection` — allocate).  Both
  // are counted now, so both belong here.
  //
  // TOUCH MEANS THE TRIE-ALGEBRA DESCENT, and the FUSED operators perform none of it: a virtual cursor
  // composes `IntMap`s directly (`unionWith`, `intersectionWith`, `transform`), which allocates no
  // `ITrie` node and enters no `IntTrieOps` descent.  Their real per-node cost is the counted
  // `ZipperCursorRead`/`ZipperMaterializeNode` traffic, which is in `work` — so `touch` is 0 for them
  // and only the operators that genuinely call into `ITrie` claim any.
  def literal(m: Meas): CostInterval = phase match
    case ExecutionPhase.Warm => CostInterval.exact(Cost.zero)                  // iLiteral cache hit, lifted O(1)
    case ExecutionPhase.Cold =>
      CostInterval.exact(Cost.of(alloc = Sym.c(3) * m.nodes, touch = Sym.c(3) * m.nodes))
  // upper-only for the same reason as the trie model's: `plen` may be a bound, not a value
  def singleton(plen: Sym): CostInterval = up(Cost.of(alloc = plen, touch = Sym.one))
  // `traversal` is O(1), but the resulting `Lit` cursor is READ by its parent layer: at most twice
  // per node of the lifted trie, since a union/intersection/subtraction descent visits each node once.
  def mention(m: Meas): CostInterval = CostInterval.upperOnly(Cost.of(work = reads(m)))
  // A pointer-identity short circuit performs NO cursor read: `SpaceZipper.union` tests `sameSpace`
  // and returns an operand, counting only the EXPLANATORY `ReusedSpace`.  Charging one work unit for it
  // put the lower endpoint above the counted total on every `x ∪ x` (caught by the corpus calibration).
  def union(a: Meas, b: Meas, same: Boolean): CostInterval =
    if same then CostInterval.exact(Cost.zero)                                 // ReusedSpace: explanatory
    else up(Cost.of(work = fuse2(a, b, a.nodes + b.nodes), alloc = a.nodes + b.nodes))
  def inter(a: Meas, b: Meas, disjoint: Boolean, same: Boolean): CostInterval =
    if same then CostInterval.exact(Cost.zero)
    // HEAD-disjoint (SpatialCost.headDisjoint): `IntMap.intersectionWith` finds no shared key at the
    // top, so the fused cursor has no children and `materialize` stops there
    else if disjoint then up(Cost.of(work = fuse2(a, b, a.heads + b.heads), alloc = a.heads + b.heads))
    else up(Cost.of(work = fuse2(a, b, tighter(a.nodes, b.nodes)), alloc = tighter(a.nodes, b.nodes)))
  def subtract(a: Meas, b: Meas, disjoint: Boolean, same: Boolean): CostInterval =
    if same then CostInterval.exact(Cost.zero)                                 // instant prune to ∅
    else up(Cost.of(work = fuse2(a, b, a.nodes), alloc = a.nodes))
  def restrict(x: Meas, y: Meas): CostInterval =
    up(Cost.of(work = fuse2(x, y, tighter(x.nodes, y.nodes)), alloc = tighter(x.nodes, y.nodes)))
  def raffine(x: Meas, y: Meas): CostInterval =
    // Subtraction(x, restriction(x, y)) — TWO fused layers over x
    up(Cost.of(work = Sym.c(2) * fuse2(x, y, x.nodes + y.nodes), alloc = x.nodes + y.nodes))
  def compose(a: Meas, b: Meas): CostInterval =
    // `Composition.children` splices ALL of b at every terminal of a, so b's cursor is re-read once
    // per a-terminal.  This is the one local operator whose fused cost is not linear in the operands.
    up(Cost.of(work = Sym.c(4) * (a.nodes + a.size * b.nodes) + reads(a) + a.size * reads(b),
               alloc = a.nodes * b.nodes))
  def wrap(src: Meas, plen: Sym): CostInterval =
    // `Prefix` is a cursor LAYER PER PREFIX ITEM, and `materialize` walks every one of them: each costs
    // one ZipperMaterializeNode plus `terminal` + `children` reads, and the innermost layer delegates
    // both queries to the source cursor as well.  Charging `plen + reads(src)` (as if the prefix were
    // free) made the predicted work fall below the counted total on every wrapped control-flow term —
    // 4 of the 200 corpus programs, visible only once the evalI fallback stopped being excluded.
    up(Cost.of(work = Sym.c(4) * (plen + Sym.one) + reads(src), alloc = plen + Sym.one + src.nodes))
  def unwrap(src: Meas, plen: Sym): CostInterval =
    // p.foldLeft(descend): |p| reads, and the RESULT IS A `Lit`, so materialize allocates nothing
    CostInterval.exact(Cost.of(work = plen))
  def tailsUnion(src: Meas): CostInterval =
    // `TailsUnion.merged` REDUCES the head children with `Union(_, _)`, so one query at the top
    // cascades through a chain of up to `heads` fused layers
    up(Cost.of(work = Sym.c(4) * src.nodes * (Sym.one + src.heads), alloc = src.nodes))
  def tailsInter(src: Meas): CostInterval =
    // TailsIntersection MATERIALISES its source (it needs the present-head set) and then calls
    // `ITrie.tailsIntersection`, a LEFT FOLD of `heads` merges — so this operator does pay real
    // trie-algebra `touch`, and allocates both `FreshNode`s and `FreshTrieNode`s.
    up(Cost.of(work = Sym.c(2) * reads(src), alloc = src.nodes * (Sym.one + src.heads),
               touch = Sym.one + Sym.c(3) * src.nodes * (src.heads + Sym.one)))
  def range(x: Meas, window: Sym, identity: Boolean): CostInterval =
    // materialize(transpileZ(x)) then ITrie.range — inherently count-based, never fused.  transpileZ
    // counts one TrieOpEntry for the crossing; materialize counts one node per visited node.
    val walk = x.nodes
    val w = tighter(window, x.size)
    if identity then up(Cost.of(work = Sym.one + reads(x), alloc = walk, touch = Sym.one + walk))
    else up(Cost.of(work = Sym.one + reads(x),
                    alloc = walk + Sym.c(3) * w * (x.len + Sym.one),
                    touch = Sym.c(2) * walk + walk * Sym.log(x.heads) +
                    Sym.c(3) * w * (w * x.len + x.len + Sym.c(2))))
  // control flow never reaches these: `controlFlowFallback` reprices the whole subterm with the trie
  // model before the traversal gets here.  They stay defined (and no cheaper than the trie model's) so
  // the instance is total rather than throwing.
  def group(src: Meas): CostInterval = CostInterval.exact(Cost.of(work = Sym.one, touch = src.heads))
  def collect(groups: Sym, body: Meas): CostInterval =
    CostInterval.upperOnly(Cost.of(work = groups, alloc = groups * body.nodes,
                                   touch = Sym.c(3) * groups * (groups + Sym.one) * body.nodes))
  def foldStep(groups: Sym, updNodes: Sym, updLen: Sym): CostInterval =
    CostInterval.upperOnly(Cost.of(work = groups * (Sym.one + updNodes), touch = groups * (Sym.one + updLen)))
  def fixStep(acc: Meas, body: Meas): CostInterval =
    CostInterval.upperOnly(Cost.of(work = Sym.one, alloc = tighter(acc.nodes, body.nodes),
                                   touch = Sym.c(3) * (acc.nodes + body.nodes)))

/** The eight instances (four executables x two phases), and the legacy two-instance names the rest
 *  of the tree used before backends were separated. */
object Backends:
  val referenceWarm: CostModel = new ReferenceCost(ExecutionPhase.Warm)
  val referenceCold: CostModel = new ReferenceCost(ExecutionPhase.Cold)
  val trieWarm: CostModel = new TrieCostModel(ExecutionPhase.Warm)
  val trieCold: CostModel = new TrieCostModel(ExecutionPhase.Cold)
  val graphWarm: CostModel = new GraphCost(ExecutionPhase.Warm)
  val graphCold: CostModel = new GraphCost(ExecutionPhase.Cold)
  val zipperWarm: CostModel = new ZipperCost(ExecutionPhase.Warm)
  val zipperCold: CostModel = new ZipperCost(ExecutionPhase.Cold)

  def of(b: Backend, phase: ExecutionPhase = ExecutionPhase.Warm): CostModel = (b, phase) match
    case (Backend.Reference, ExecutionPhase.Warm) => referenceWarm
    case (Backend.Reference, ExecutionPhase.Cold) => referenceCold
    case (Backend.Trie, ExecutionPhase.Warm) => trieWarm
    case (Backend.Trie, ExecutionPhase.Cold) => trieCold
    case (Backend.Graph, ExecutionPhase.Warm) => graphWarm
    case (Backend.Graph, ExecutionPhase.Cold) => graphCold
    case (Backend.Zipper, ExecutionPhase.Warm) => zipperWarm
    case (Backend.Zipper, ExecutionPhase.Cold) => zipperCold

  val all: Vector[CostModel] = Vector(referenceWarm, trieWarm, graphWarm, zipperWarm,
                                      referenceCold, trieCold, graphCold, zipperCold)
  val warm: Vector[CostModel] = Vector(referenceWarm, trieWarm, graphWarm, zipperWarm)

/** the warm reference model — the historical name for "the set backend" */
val SetCost: CostModel = Backends.referenceWarm
/** the warm trie model — the historical name, now explicitly `evalI` and NOT `execZ` */
val TrieCost: CostModel = Backends.trieWarm

// ================================================================================================
// 4. RECURRENCES
// ================================================================================================

/** Closed forms for the one recurrence family this analysis recognises.
 *
 *  `T(n) = a + b·T(n−1)`, `T(0) = 0`, over a measure `n` that provably drops by ≥ 1 per level.
 *  Anything else is [[Amount.Unbounded]] with the reason — never a silent saturation. */
object Recurrence:
  /** `a` = per-level cost outside the recursive call, `b` = branching factor, `n` = level bound */
  final case class Linear(a: Sym, b: Sym, n: Sym)

  /** `T(n) = Σ_{k<n} a·b^k`.  For `b = 1` that is `a·n`; for a constant `b ≥ 2` it is bounded by
   *  `a·b^n`; for a SYMBOLIC `b` (which may be 1) the sound envelope is `a·n·b^n` — each of the `n`
   *  terms is at most `b^n` — and the extra factor `n` is recorded as such, not hidden. */
  def solve(r: Linear): Amount =
    val a = Sym.normalize(r.a); val b = Sym.normalize(r.b); val n = Sym.normalize(r.n)
    if n == Sym.Inf then Amount.Unbounded("recursion depth is unbounded")
    else b match
      case Sym.Const(0) => Amount.of(a)
      case Sym.Const(1) => Amount.of(a * n)
      case Sym.Const(_) => Amount.of(a * (b ** n))
      case Sym.Inf => Amount.Unbounded("recursive branching factor is unbounded")
      case _ => Amount.of(a * n * (b ** n))

  /** Rewrite one cost component `e`, which mentions the recursive marker `tvar`, into a closed
   *  form.  `e = a + b·tvar` is read straight out of the normalised polynomial: `b` is exactly the
   *  coefficient the traversal already multiplied in (enclosing loop group counts included). */
  def close(c: Amount, tvar: String, n: Sym): Amount = c match
    case Amount.Unbounded(r) => Amount.Unbounded(r)
    case Amount.Bounded(e) =>
      if !Sym.vars(e).contains(tvar) then Amount.of(e)
      else Sym.splitLinear(e, tvar) match
        case None => Amount.Unbounded(s"non-linear recurrence in $tvar")
        case Some((a, b)) => solve(Linear(a, b, n))

  def close(c: Cost, tvarWork: String, tvarAlloc: String, tvarRounds: String, tvarTouch: String, n: Sym): Cost =
    Cost(close(c.work, tvarWork, n), close(c.alloc, tvarAlloc, n), close(c.rounds, tvarRounds, n),
         close(c.touch, tvarTouch, n))

  // ---- the decreasing measure -------------------------------------------------------------------
  /** Does `arg` denote a set every path of which is at least one item SHORTER than every path of
   *  `Mention(p)`?  These are the syntactic forms that provably drop an item. */
  private def dropsAnItem(arg: Space, p: SpaceMention): Boolean = arg match
    case Space.TailsUnion(Space.Mention(m)) => m == p
    case Space.TailsIntersection(Space.Mention(m)) => m == p
    case Space.Unwrap(Space.Mention(m), pp) =>
      m == p && SpatialTypes.pathLen(pp, SpatialEnv()).lo >= 1
    case _ => false

  private def calls(s: Space, rp: RoutinePtr): Vector[Space.Call] =
    val out = Vector.newBuilder[Space.Call]
    def go(x: Space): Unit =
      x match
        case c @ Space.Call(r, _, ms) => if r == rp then out += c; ms.foreach(go)
        case _ => SizeZ3.children(x).foreach(go)
    go(s)
    out.result()

  /** Which mention parameter index provably loses an item at EVERY recursive call site (`None` if
   *  none does, or if there is no recursive call). */
  def decreasingArg(body: Space, rp: RoutinePtr, params: Vector[SpaceMention]): Option[Int] =
    val cs = calls(body, rp)
    if cs.isEmpty then None
    else params.indices.find(i => cs.forall(c => c.mentions.lift(i).exists(a => dropsAnItem(a, params(i)))))

  /** Is `arg` syntactically `p ∪ _` or `_ ∪ p` — an argument that can only GROW the parameter? */
  private def growsMonotonically(arg: Space, p: SpaceMention): Boolean = arg match
    case Space.Union(Space.Mention(m), _) => m == p
    case Space.Union(_, Space.Mention(m)) => m == p
    case _ => false

  /** THE SECOND TERMINATION CRITERION (review.md item 1, fourth point).
   *
   *  Which mention parameter is a MONOTONE ACCUMULATOR at every recursive call site: the argument
   *  passed for it is syntactically `p ∪ g`, so `p` can only grow.  Combined with
   *  [[selfTerminating]] — `eval`/`evalI` stop a `Union(_, Call(rp, args))` once the arguments stop
   *  changing — this means every non-final recursive call adds AT LEAST ONE PATH to the accumulator,
   *  so the call depth is at most `|accumulator at the fixpoint| + 2`.
   *
   *  It is the same argument `fixRounds` uses for a monotone `Fixpoint`, and it is why the semi-naive
   *  Datalog cornerstone terminates.  What it does NOT give is the BOUND: `|accumulator at the
   *  fixpoint|` is a property of the least fixpoint of the body's size transformer, and this analysis
   *  has no fixpoint over the size lattice (and no finite path universe to widen into).  So this
   *  predicate makes the REASON precise instead of making the depth finite — see the note the `Call`
   *  transfer records. */
  def accumulatorArg(body: Space, rp: RoutinePtr, params: Vector[SpaceMention]): Option[Int] =
    val cs = calls(body, rp)
    if cs.isEmpty then None
    else params.indices.find(i => cs.forall(c => c.mentions.lift(i).exists(a => growsMonotonically(a, params(i)))))

  /** Is the body the shape `eval`'s self-call detection terminates on (MORKL.scala `Space.Call`
   *  case: a `Union(l, Call(rp, sameArgs))` returns `l` once the arguments stop changing)? */
  def selfTerminating(body: Space, rp: RoutinePtr): Boolean = body match
    case Space.Union(_, Space.Call(r, _, _)) => r == rp
    case Space.Union(Space.Call(r, _, _), _) => r == rp
    case _ => false

  /** The call-depth bound the review asks for (finding 2): a routine that consumes one item per
   *  call, applied to an argument of maximum path length `L`, recurses at most `L + 2` times (`L`
   *  shortening steps, one ε-only step, one empty-argument step at which the recursion stops). */
  def depthBound(maxLen: Long): Sym = if maxLen >= Lower.LenBounds.INF then Sym.Inf else Sym.c(maxLen + 2)
end Recurrence

// ================================================================================================
// 5. THE COST ANALYSIS
// ================================================================================================

object SpatialCost:
  import Lower.{LenBounds, SizeBounds}
  import Sym.tighter

  /** How many times the analysis may query the (linear, per-call) spatial analyses.  Querying at
   *  every node is quadratic in the term size — review.md 4 objects to that — so the refinement is
   *  budgeted, and exhausting the budget only loses precision (the symbolic propagation stands on
   *  its own). */
  val FactBudget = 2000
  val MaxInline = 6
  val MaxDepth = 64

  /** `shapeFacts` selects whether the SHAPE half of the spatial product may be consulted.
   *
   *  The split exists for soundness ATTRIBUTION, so a cost claim can be traced to the tier that
   *  justifies it.  Path counts and lengths come from `SpatialTypes` (the length histogram).
   *  Distinct-head counts — an `Iteration`'s group count — and the disjointness that lets a trie
   *  SKIP a subtrie can only come from `SpatialTyping`'s `Shape`.  A shape that wrongly proves a
   *  subterm empty or a head set small makes the cost too LOW, so with `shapeFacts = false` the
   *  analysis uses only the histogram (head count falls back to `≤ size`, no skips); with it on,
   *  every report names the dependency in `assumptions`. */
  final case class Env(spaces: Map[SpaceMention, Meas] = Map.empty,
                       paths: Map[PathRef, Sym] = Map.empty,
                       routines: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                       active: Set[RoutinePtr] = Set.empty,
                       facts: SpatialTyping.Env = SpatialTyping.Env(),
                       shapeFacts: Boolean = true):
    def withRoutines(rc: PartialFunction[RoutinePtr, Routine]): Env =
      copy(routines = rc, facts = facts.copy(lenv = facts.lenv.copy(routines = rc)))

  /** One backend's answer: WHICH executable, in WHICH phase, and a lower/upper INTERVAL rather than
   *  a bare worst case (review.md finding 2).  `cost` is the upper endpoint, kept under that name so
   *  a caller that only wants the worst case reads the same field it always did. */
  final case class Report(model: String, backend: Backend, phase: ExecutionPhase,
                          interval: CostInterval, meas: Meas, assumptions: Vector[String]):
    def cost: Cost = interval.hi
    def lower: Cost = interval.lo
    def show: String =
      val a = if assumptions.isEmpty then "" else assumptions.distinct.map("    ! " + _).mkString("\n", "\n", "")
      s"[$model] ${backend.executable}\n  LOWER ${lower.show}\n  UPPER ${cost.show}\n  O: ${cost.showO}\n  in: ${meas.show}$a"
    /** the interval for one CALIBRATED component, evaluated at a concrete valuation */
    def bracket(c: EffortComponent, v: Map[String, Double]): (Double, Double) =
      (lower.calibrated(c).at(v), cost.calibrated(c).at(v))

  private final class State:
    var budget: Int = FactBudget
    var fresh: Int = 0
    val notes = collection.mutable.LinkedHashSet.empty[String]
    def note(s: String): Unit = notes += s
    def nextVar(prefix: String): String = { fresh += 1; s"$prefix$fresh" }

  // ---- entry points ----------------------------------------------------------------------------
  def analyze(s: Space, model: CostModel): Report = analyze(s, Env(), model)
  def analyze(s: Space, env: Env, model: CostModel): Report =
    val st = new State
    val (c, m) = go(s, env, model, st, 0)
    if st.budget <= 0 then st.note(s"spatial-fact budget ($FactBudget queries) exhausted; the rest is symbolic only")
    for why <- model.touchNoOracle do
      st.note(s"${model.name}: the `touch` component has NO COUNTED ORACLE and is a model, not a " +
              s"measurement — $why")
    // the root materialisation, if the executable has one (only `execZ` does), and the one structural
    // widening: no positive LOWER bound on library-internal node visits is claimed (file header)
    Report(model.name, model.backend, model.phase,
           (c + model.finish(m, liftsToLit(s))).withoutTouchLower, m, st.notes.toVector)

  /** Every executable's warm interval over the SAME facts — the per-backend cost map review.md
   *  finding 7 asks candidate selection to compare. */
  def analyzeAll(s: Space, env: Env = Env(),
                 phase: ExecutionPhase = ExecutionPhase.Warm): Map[Backend, CostInterval] =
    Backend.values.iterator.map(b => b -> analyze(s, env, Backends.of(b, phase)).interval).toMap

  def reports(s: Space, env: Env = Env(),
              phase: ExecutionPhase = ExecutionPhase.Warm): Vector[Report] =
    Backend.values.toVector.map(b => analyze(s, env, Backends.of(b, phase)))

  /** The historical two-backend comparison: warm reference vs warm trie. */
  def compare(s: Space, env: Env = Env()): (Report, Report) =
    (analyze(s, env, Backends.referenceWarm), analyze(s, env, Backends.trieWarm))

  // ---- fact queries (READ-ONLY; no evaluation anywhere) ----------------------------------------
  private val ShapeNote =
    "distinct-head counts and disjointness skips consume the Shape half of the spatial product, so " +
    "they are only as sound as SpatialShapeCheck's corpus gate — set Env(shapeFacts = false) to " +
    "drop them and fall back to the length histogram alone"

  /** the length-histogram tier (corpus-gated) */
  private def histAt(s: Space, env: Env, st: State): Option[SpaceType] =
    if st.budget <= 0 then None else { st.budget -= 1; Some(SpatialTypes.infer(s, env.facts.lengths)) }

  /** the full reduced product, SHAPE INCLUDED (see [[ShapeNote]]) */
  private def shapeAt(s: Space, env: Env, st: State): Option[SpatialType] =
    if !env.shapeFacts || st.budget <= 0 then None
    else { st.budget -= 1; st.note(ShapeNote); Some(SpatialTyping.infer(s, env.facts)) }

  private def symSize(hi: Long): Sym = if hi >= SizeBounds.INF then Sym.Inf else Sym.c(hi)
  private def symLen(b: LenBounds): Sym =
    if b.isEmpty then Sym.zero else if b.hi >= LenBounds.INF then Sym.Inf else Sym.c(b.hi)

  /** a sound LOWER bound read off the spatial analyses (0 when nothing is proved) */
  private def symLo(lo: Long): Sym = if lo <= 0L || lo >= SizeBounds.INF then Sym.zero else Sym.c(lo)

  /** Meet the symbolically propagated bounds with whatever the spatial analyses prove.
   *
   *  UPPER endpoints: all candidates are sound upper bounds of the SAME quantity, so [[Sym.tighter]]
   *  preserves soundness; `heads ≤ size` is also a true fact and is applied unconditionally.
   *  LOWER endpoints: the MAXIMUM of two sound lower bounds is a sound lower bound, so they are
   *  joined with `lub` rather than met. */
  private def refine(m: Meas, s: Space, env: Env, st: State): Meas =
    var out = histAt(s, env, st) match
      case None => m
      case Some(t) => m.copy(size = tighter(m.size, symSize(t.size.hi)), len = tighter(m.len, symLen(t.len)),
                             sizeLo = m.sizeLo lub symLo(t.size.lo))
    shapeAt(s, env, st) match
      case Some(t) =>
        out = out.copy(heads = tighter(out.heads, symSize(t.headCount.hi)),
                       headsLo = out.headsLo lub symLo(t.headCount.lo),
                       sizeLo = out.sizeLo lub symLo(t.size.lo),
                       headKeys = closedHeadKeys(t.shape).orElse(out.headKeys))
        // THE EXACT TRIE-NODE IDENTITY, when the shape's prefix profile supplies one (whispers §1).
        // Both candidates are sound uppers of the same quantity, so `tighter` preserves soundness.
        SpatialFacts.trieNodes(t) match
          case Right(iv) => out = out.copy(nodesHi = Some(tighter(out.nodes, symSize(iv.hi))))
          case Left(_) => ()                   // an inconsistent hand-built type: keep the fallback
      case None => ()
    out.copy(heads = tighter(out.heads, out.size))

  /** DO THE TWO OPERANDS HAVE PROVABLY DISJOINT HEAD SETS?
   *
   *  THIS REPLACES A WRONG FAST-PATH JUSTIFICATION, and the event calibration is what caught it.  The
   *  model used to take "the intersection is PROVABLY EMPTY" as licence to charge one head comparison
   *  and ZERO allocations.  That is false: `ITrie.intersection`'s empty guard fires on an empty
   *  OPERAND, not an empty RESULT, so two operands that share HEADS but no full path still descend
   *  every shared prefix and allocate one node per level.  Counted: 12 fresh trie nodes against a
   *  predicted 1, on the corpus, three times over.
   *
   *  What DOES stop the merge at the top is disjoint HEAD SETS: `intersectTries`/`diffTries` then find
   *  no matching key, return `IntMap.Nil` immediately, and exactly one root node is built.  Proving it
   *  needs both head sets CLOSED (`Shape.headsClosed`, i.e. no untracked head) and their
   *  possibly-present keys disjoint — strictly stronger than an empty result, and the only form the
   *  executors actually reward. */
  private def headDisjoint(ma: Meas, mb: Meas): Boolean = ma.headDisjointFrom(mb)

  /** the possibly-present head keys of a CLOSED head set, for [[Meas.headKeys]] */
  private def closedHeadKeys(sh: Shape): Option[Set[PathItem]] =
    if !sh.headsClosed then None
    else Some(sh.heads.iterator.filter((_, t) => t.possiblyNonEmpty).map(_._1).toSet)

  /** Provably empty?  With the shape tier on this sees head-set disjointness and absent prefixes;
   *  without it, only what the length histogram derives. */
  private def provablyEmpty(s: Space, env: Env, st: State): Boolean =
    if env.shapeFacts then shapeAt(s, env, st).exists(_.isProvablyEmpty)
    else histAt(s, env, st).exists(_.isProvablyEmpty)

  /** A `SpatialType` to pass on as a declared input type for a binder: the full product when the
   *  shape tier is enabled, otherwise the histogram over a ⊤ shape. */
  private def typeAt(s: Space, env: Env, st: State): SpatialType =
    if env.shapeFacts then shapeAt(s, env, st).getOrElse(SpatialType.top)
    else histAt(s, env, st).map(h => SpatialType(Shape.top, h)).getOrElse(SpatialType.top)

  // ---- symbolic path lengths -------------------------------------------------------------------
  private def plen(p: Path, env: Env): Sym = p match
    case Path.Constant(pv) => Sym.c(pv.items.length)
    case Path.Deref(pr) =>
      env.paths.getOrElse(pr, if pr.lengthHint >= 0 then Sym.c(pr.lengthHint) else Sym.v(s"|${pr.s}|"))
    case Path.Concat(l, r) => plen(l, env) + plen(r, env)
    case Path.GroundedPP(_, _) | Path.GroundedSP(_, _) => Sym.v("|grounded-path|")

  /** Every `Path` subterm — what `eval.recp` dispatches on. */
  private[morkl] def pathNodeCount(p: Path): Long = p match
    case Path.Concat(l, r) => 1L + pathNodeCount(l) + pathNodeCount(r)
    case _ => 1L
  /** The operation-graph slots `transpile` allocates for a path: a `Deref` reuses the prologue slot
   *  found by `g.find`, so it costs none; everything else stores a node. */
  private[morkl] def pathSlotCount(p: Path): Long = p match
    case Path.Deref(_) => 0L
    case Path.Concat(l, r) => 1L + pathSlotCount(l) + pathSlotCount(r)
    case _ => 1L
  private def pathCost(p: Path, model: CostModel): CostInterval =
    model.pathTerm(Sym.c(pathNodeCount(p)), Sym.c(pathSlotCount(p)))

  /** `runGraphT`'s calling convention: one dispatched prologue slot per declared ref and mention,
   *  plus at most one trailing pass-through `Union` when the body's result is not already last.
   *  A caller comparing a Graph report against counted `execT` events must add this. */
  def graphPrologue(nRefs: Int, nMentions: Int): CostInterval =
    // an `ExtractPathRef` is a "path" slot (1 dispatch); an `ExtractSpaceMention` is a "space" slot
    // (1 dispatch + 1 TrieOpEntry); the trailing pass-through, when transpile needs one, is another
    val base = Sym.c(nRefs.toLong + 2L * nMentions.toLong)
    CostInterval(Cost.of(work = base, alloc = Sym.one), Cost.of(work = base + Sym.c(2), alloc = Sym.one))

  private def rangeWindow(lo: Int, hi: Int): Sym =
    if lo == 0 && hi == 0 then Sym.Inf
    else if lo == 0 && hi > 0 then Sym.c(hi.toLong)
    else if hi == 0 && lo < 0 then Sym.c(-lo.toLong)
    else if (lo > 0 && hi >= lo) || (lo < 0 && hi <= 0 && hi >= lo) then Sym.c((hi - lo).toLong)
    else Sym.Inf

  private def mentionMeas(m: SpaceMention, env: Env): Meas =
    env.spaces.getOrElse(m,
      Meas(Sym.v(s"|${m.s}|"), Sym.v(s"len(${m.s})"), Sym.v(s"|${m.s}|")))   // heads ≤ size

  private def recWorkVar(rp: RoutinePtr) = s"T_work(${rp.s})"
  private def recAllocVar(rp: RoutinePtr) = s"T_alloc(${rp.s})"
  private def recRoundVar(rp: RoutinePtr) = s"T_rounds(${rp.s})"
  private def recTouchVar(rp: RoutinePtr) = s"T_touch(${rp.s})"

  /** Does a `Range(x, lo, hi)` window provably cover the WHOLE space, whatever its size?
   *
   *  `RangeBounds.normalize` gives `lower(start) = 0` for `start ∈ {0, 1}` and `upper(0) = size`, and
   *  `sliceRange`/`ITrie.range` then return their input unchanged.  This is the predicate review.md
   *  finding 2 needs: a full `Range` is an identity, so the model may not charge a sort for it, and
   *  the reference backend's warm work for it must not grow with `|x|`. */
  private[morkl] def rangeIsIdentity(lo: Int, hi: Int): Boolean = (lo == 0 || lo == 1) && hi == 0

  /** Do two operands denote the SAME already-materialised object at run time, so a pointer-identity
   *  short circuit fires?  `ITrie.union`/`intersection`/`subtraction` test `a eq b`, and
   *  `SpaceZipper.sameSpace` tests `Lit(s) eq Lit(t)`.  That holds for a repeated `Mention` (the same
   *  trie out of the context), a repeated `Literal` (the `iLiteral` memo cache returns the same
   *  object) and `Empty`.  It does NOT hold for a repeated `Singleton` or a repeated compound: those
   *  build a fresh object each time. */
  private[morkl] def sharedOperands(a: Space, b: Space): Boolean =
    a == b && (a match
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => true
      case _ => false)

  /** Does `transpileZ` produce a CONCRETE `SpaceZipper.Lit` cursor for this term?  If so
   *  `materialize` hands the existing trie straight back and allocates nothing.  Read off
   *  `transpileZ`'s arms: `Empty`/`Singleton`/`Literal`/`Mention`/`Range` lift with `traversal`, the
   *  control-flow fallback re-lifts an `evalI` result with `traversal`, `unwrap` folds `descend`
   *  (which keeps a `Lit` a `Lit`), and the `x∪x`/`x∩x`/`x∖x` smart constructors return an operand. */
  private[morkl] def liftsToLit(s: Space): Boolean = s match
    case Space.Empty | Space.Singleton(_) | Space.Literal(_) | Space.Mention(_) | Space.Range(_, _, _) => true
    case Space.Unwrap(src, _) => liftsToLit(src)
    case Space.Union(a, b) => sharedOperands(a, b) && liftsToLit(a)
    case Space.Intersection(a, b) => sharedOperands(a, b) && liftsToLit(a)
    case Space.Subtraction(a, b) => sharedOperands(a, b)
    case _ => isControlFlow(s)

  /** Terms `transpileZ` refuses to fuse: it materialises them through `evalI` instead. */
  private def isControlFlow(s: Space): Boolean = s match
    case Space.Iteration(_, _, _, _) | Space.Fold(_, _, _, _, _, _, _) | Space.Fixpoint(_, _, _) |
         Space.Call(_, _, _) | Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => true
    case _ => false

  private def nodeName(s: Space): String = s.getClass.getSimpleName.stripSuffix("$")

  // ---- the transfer ----------------------------------------------------------------------------
  private def go(s: Space, env: Env, model: CostModel, st: State, depth: Int): (CostInterval, Meas) =
    if depth > MaxDepth then (CostInterval.unbounded(s"analysis depth cap ($MaxDepth) reached"), Meas.top)
    else model.controlFlowFallback match
      // execZ does not fuse control flow; it hands the whole subterm to evalI.  Pricing it with the
      // zipper's own local-algebra formulas would describe a program that never runs.
      case Some(fb) if isControlFlow(s) =>
        st.note(s"${model.name}: ${nodeName(s)} is NOT fused — transpileZ materialises it through evalI, " +
                s"so this subterm is priced with the ${fb.slug} model (ZipperFallbackToEvalI is counted)")
        val (c, m) = goNode(s, env, Backends.of(fb, model.phase), st, depth)
        (c + model.fallbackEntry, m)
      case _ => goNode(s, env, model, st, depth)

  private def goNode(s: Space, env: Env, model: CostModel, st: State, depth: Int): (CostInterval, Meas) =
    def rec(x: Space) = go(x, env, model, st, depth + 1)
    val d = model.dispatch
    s match
      case Space.Empty => (d + model.empty, Meas.empty)

      case Space.Literal(SpaceValue(ps)) =>
        val hs = ps.iterator.collect { case PathValue(h :: _) => h }.toSet
        val m = Meas.exact(Sym.c(ps.size.toLong),
                           Sym.c(if ps.isEmpty then 0L else ps.iterator.map(_.items.length.toLong).max),
                           Sym.c(hs.size.toLong)).copy(headKeys = Some(hs))
        (d + model.literal(m), m)

      case Space.Singleton(p) =>
        val lp = plen(p, env)
        (d + pathCost(p, model) + model.singleton(lp), Meas(Sym.one, lp, Sym.one, Sym.one, Sym.one))

      case Space.Mention(m) =>
        val mm = refine(mentionMeas(m, env), s, env, st)
        (model.mentionDispatch + model.mention(mm), mm)

      case Space.Union(a, b) =>
        val (ca, ma) = rec(a); val (cb, mb) = rec(b)
        // |a ∪ b| ≥ max(|a|, |b|): the MAX of two sound lower bounds is a sound lower bound
        val m = refine(Meas(ma.size + mb.size, ma.len lub mb.len, ma.heads + mb.heads,
                            ma.sizeLo lub mb.sizeLo, ma.headsLo lub mb.headsLo), s, env, st)
        (d + ca + cb + model.union(ma, mb, sharedOperands(a, b)), m)

      case Space.Intersection(a, b) =>
        val (ca, ma) = rec(a); val (cb, mb) = rec(b)
        // HEAD-set disjointness, not an empty result — see `headDisjoint`
        val disj = headDisjoint(ma, mb)
        val same = sharedOperands(a, b)
        // x ∩ x = x, so a shared operand carries its lower bound through; otherwise nothing is known
        val loSz = if same then ma.sizeLo else Sym.zero
        val loHd = if same then ma.headsLo else Sym.zero
        val m = refine(Meas(tighter(ma.size, mb.size), tighter(ma.len, mb.len), tighter(ma.heads, mb.heads),
                            loSz, loHd), s, env, st)
        (d + ca + cb + model.inter(ma, mb, disj, same), m)

      case Space.Subtraction(a, b) =>
        val (ca, ma) = rec(a); val (cb, mb) = rec(b)
        val disj = headDisjoint(ma, mb)
        val same = sharedOperands(a, b)
        // x ∖ x = ∅; a disjoint subtrahend removes nothing, so a's lower bound survives
        val loSz = if same then Sym.zero else if disj then ma.sizeLo else Sym.zero
        val m = refine(Meas(ma.size, ma.len, ma.heads, loSz, Sym.zero), s, env, st)
        (d + ca + cb + model.subtract(ma, mb, disj, same), m)

      case Space.Restriction(x, y) =>
        val (cx, mx) = rec(x); val (cy, my) = rec(y)
        val m = refine(Meas(mx.size, mx.len, mx.heads), s, env, st)
        (d + cx + cy + model.restrict(mx, my), m)

      case Space.Raffination(x, y) =>
        val (cx, mx) = rec(x); val (cy, my) = rec(y)
        val m = refine(Meas(mx.size, mx.len, mx.heads), s, env, st)
        // `eval` rewrites x \| y to Subtraction(x, Restriction(x, y)) and evaluates recs(x) TWICE;
        // the trie/graph executors evaluate x once and reuse the value.
        val xTwice = if model.raffinationRereadsX then cx else CostInterval.zero
        (d + cx + xTwice + cy + model.raffine(mx, my), m)

      case Space.Composition(a, b) =>
        val (ca, ma) = rec(a); val (cb, mb) = rec(b)
        // concatenations of different pairs CAN collide ({a, a.b} x {b, ε}), so the only generic
        // lower bound is positivity
        val loSz = if ma.provablyNonEmpty && mb.provablyNonEmpty then Sym.one else Sym.zero
        val m = refine(Meas(ma.size * mb.size, ma.len + mb.len, ma.heads + mb.heads, loSz, Sym.zero), s, env, st)
        (d + ca + cb + model.compose(ma, mb), m)

      case Space.Wrap(src, p) =>
        val (cs, ms) = rec(src)
        val lp = plen(p, env)
        val hd = if SpatialTypes.pathLen(p, env.facts.lengths).lo >= 1 then Sym.one else ms.heads
        // prefixing is INJECTIVE, so the source's lower bound carries through exactly
        val m = refine(Meas(ms.size, lp + ms.len, hd, ms.sizeLo, Sym.zero), s, env, st)
        (d + cs + pathCost(p, model) + model.wrap(ms, lp), m)

      case Space.Unwrap(src, p) =>
        val (cs, ms) = rec(src)
        val lp = plen(p, env)
        val m = refine(Meas(ms.size, ms.len, ms.size), s, env, st)
        (d + cs + pathCost(p, model) + model.unwrap(ms, lp), m)

      case Space.TailsUnion(src) =>
        val (cs, ms) = rec(src)
        val m = refine(Meas(ms.size, ms.len, ms.size), s, env, st)
        (d + cs + model.tailsUnion(ms), m)

      case Space.TailsIntersection(src) =>
        val (cs, ms) = rec(src)
        val m = refine(Meas(ms.size, ms.len, ms.size), s, env, st)
        (d + cs + model.tailsInter(ms), m)

      case Space.Range(x, lo, hi) =>
        val (cx, mx) = rec(x)
        val w = rangeWindow(lo, hi)
        val ident = rangeIsIdentity(lo, hi)
        // a full window is the IDENTITY: the size bound (both endpoints) passes straight through
        val m =
          if ident then refine(mx, s, env, st)
          else refine(Meas(tighter(mx.size, w), mx.len, tighter(mx.heads, w)), s, env, st)
        (d + cx + model.range(mx, w, ident), m)

      // ---- THE LOOPS: work = (head-groups) × (body work) ----------------------------------------
      case Space.Iteration(src, sym, rest, body) =>
        val (cs, ms) = rec(src)
        val groups = ms.heads                                  // the GROUP COUNT is the head count
        val groupsLo = ms.headsLo
        val benv = loopEnv(env, src, ms, sym, rest, st)
        val (cb, mb) = go(body, benv, model, st, depth + 1)
        val m = refine(Meas(groups * mb.size, mb.len, groups * mb.size), s, env, st)
        val cost = d + cs + model.loopPrologue + model.group(ms) + cb.scale(groupsLo, groups) +
                   model.collect(groups, mb) + CostInterval(Cost.r(groupsLo), Cost.r(groups))
        (cost, m)

      case Space.Fold(src, initial, acc, sym, rest, body, update) =>
        val (cs, ms) = rec(src)
        val groups = ms.heads
        val groupsLo = ms.headsLo
        val benv0 = loopEnv(env, src, ms, sym, rest, st)
        val benv = benv0.copy(paths = benv0.paths + (acc -> Sym.v(s"|acc:${acc.s}|")))
        val (cb, mb) = go(body, benv, model, st, depth + 1)
        val m = refine(Meas(groups * mb.size, mb.len, groups * mb.size), s, env, st)
        val seed = CostInterval(Cost.zero, Cost.of(alloc = Sym.one)) + pathCost(initial, model)
        val cost = d + cs + model.loopPrologue + model.group(ms) + cb.scale(groupsLo, groups) +
                   model.collect(groups, mb) + seed +
                   model.foldStep(groups, Sym.c(pathNodeCount(update)), plen(update, benv)) +
                   CostInterval(Cost.r(groupsLo), Cost.r(groups))
        (cost, m)

      case f @ Space.Fixpoint(init, recm, body) =>
        val (ci, mi) = rec(init)
        val self = refine(Meas(Sym.v(s"|fix:${recm.s}|"), Sym.v(s"len(fix:${recm.s})"), Sym.v(s"|fix:${recm.s}|")),
                          s, env, st)
        val rounds = fixRounds(f, env, st, self)
        // every iterate is a subset of the accumulated result, so `self` bounds each of them
        val benv = env.copy(spaces = env.spaces + (recm -> self),
                            facts = env.facts.copy(spaces = env.facts.spaces + (recm -> typeAt(f, env, st))))
        val (cb, mb) = go(body, benv, model, st, depth + 1)
        val m = refine(Meas(rounds * mb.size + mi.size, mi.len lub mb.len, rounds * mb.size + mi.size,
                            mi.sizeLo, Sym.zero), s, env, st)
        // AT LEAST ONE round always runs: the loop must evaluate the body once to discover the
        // iterate is unchanged (the terminating round is counted by FixpointRound).
        val cost = d + model.fixPrologue + ci + cb.scale(Sym.one, rounds) +
                   model.fixStep(self, mb).scale(Sym.one, rounds) +
                   CostInterval(Cost.r(Sym.one), Cost.r(rounds))
        (cost, m)

      // ---- CALLS: inline, or solve the recurrence ------------------------------------------------
      case Space.Call(rp, refs, mentions) if env.active(rp) =>
        // a recursive occurrence: emit MARKER variables, which the enclosing inlining step reads
        // back out of the normalised polynomial as the recurrence's branching factor
        (CostInterval(Cost.zero,
                      Cost(Amount.of(Sym.v(recWorkVar(rp))), Amount.of(Sym.v(recAllocVar(rp))),
                           Amount.of(Sym.v(recRoundVar(rp))), Amount.of(Sym.v(recTouchVar(rp))))),
         Meas(Sym.v(s"|${rp.s}()|"), Sym.v(s"len(${rp.s}())"), Sym.v(s"|${rp.s}()|")))

      // `active.size` — not the AST depth — is the CALL depth, so a call deep inside a term is still
      // analysed interprocedurally; only genuinely nested routine bodies hit the cap
      case Space.Call(rp, refs, mentions) if env.routines.isDefinedAt(rp) && env.active.size < MaxInline =>
        val Routine(_, refns, mentionns, rbody) = env.routines(rp)
        val argCosts = mentions.map(a => go(a, env, model, st, depth + 1))
        val callee = Env(
          spaces = mentionns.zip(argCosts.map(_._2)).toMap,
          paths = refns.zip(refs.map(p => plen(p, env))).toMap,
          routines = env.routines, active = env.active + rp,
          facts = SpatialTyping.Env(
            spaces = mentionns.zip(mentions.map(a => typeAt(a, env, st))).toMap,
            paths = Map.empty,
            lenv = SpatialEnv(paths = refns.zip(refs.map(p => SpatialTypes.pathLen(p, env.facts.lengths))).toMap,
                              routines = env.routines)),
          shapeFacts = env.shapeFacts)
        val (cbody, mbody) = go(rbody, callee, model, st, depth + 1)
        val total = argCosts.foldLeft(CostInterval.zero)((c, x) => c + x._1) + d +
                    refs.foldLeft(CostInterval.zero)((c, p) => c + pathCost(p, model))
        def mentionsMarker(a: Amount, v: String) = a.symOpt.exists(e => Sym.vars(e).contains(v))
        val hi = cbody.hi
        if !mentionsMarker(hi.work, recWorkVar(rp)) && !mentionsMarker(hi.alloc, recAllocVar(rp)) &&
           !mentionsMarker(hi.rounds, recRoundVar(rp)) && !mentionsMarker(hi.touch, recTouchVar(rp)) then
          (total + model.callFrame + cbody, mbody)                 // exactly one CallEntry
        else
          // a genuine recursion: find the decreasing measure, then close the linear recurrence
          Recurrence.decreasingArg(rbody, rp, mentionns) match
            case None =>
              // No length-decreasing argument.  Say EXACTLY what is missing rather than "no measure":
              // a monotone accumulator does prove termination, but bounding its fixpoint size needs a
              // fixpoint over the size lattice that this analysis does not have.
              val why = Recurrence.accumulatorArg(rbody, rp, mentionns) match
                case Some(i) if Recurrence.selfTerminating(rbody, rp) =>
                  st.note(s"recursive routine ${rp.s}: parameter $i (${mentionns.lift(i).map(_.s).getOrElse("?")}) is a " +
                          "MONOTONE ACCUMULATOR and the body is the Union(_, Call) shape, so the recursion does " +
                          "terminate — every continuing call adds at least one path and the depth is " +
                          "|accumulator at the fixpoint| + 2.  What is missing is a BOUND on that size: it is the " +
                          "least fixpoint of the body's size transformer, and this analysis has neither a fixpoint " +
                          "over the size lattice nor a finite path universe to widen into.  MODELLING GAP, named.")
                  s"recursion in ${rp.s}: monotone accumulator with no bound on its fixpoint size"
                case _ =>
                  st.note(s"recursive routine ${rp.s}: no argument provably loses an item per call and none is a " +
                          "monotone accumulator, so no recursion depth bound and no closed form")
                  s"recursion in ${rp.s} without a decreasing measure"
              (total + CostInterval.unbounded(why), Meas.top)
            case Some(i) =>
              val argLen = mentions.lift(i).map(a => SpatialTypes.lenOf(a, env.facts.lengths).hi).getOrElse(LenBounds.INF)
              val n = Recurrence.depthBound(argLen)
              if n == Sym.Inf then
                st.note(s"recursive routine ${rp.s}: argument $i decreases but its maximum path length " +
                        "is not bounded, so the depth is not bounded")
                (total + CostInterval.unbounded(s"recursion in ${rp.s}: unbounded argument length"), Meas.top)
              else
                if !Recurrence.selfTerminating(rbody, rp) then
                  st.note(s"recursive routine ${rp.s}: depth bound ${n.show} assumes the recursion stops once " +
                          "the decreasing argument is empty; the body is NOT the Union(_, Call) shape eval's " +
                          "self-call detection handles, so termination is ASSUMED, not derived")
                else
                  st.note(s"recursive routine ${rp.s}: depth bound ${n.show} from maxlen(arg $i) = $argLen, " +
                          "with eval's self-call detection terminating the empty-argument step")
                st.note(s"recursive routine ${rp.s}: the recursive call's RESULT SIZE stays the free variable " +
                        s"|${rp.s}()| — only its COST is closed; there is no interprocedural size summary here")
                val closed = Recurrence.close(hi, recWorkVar(rp), recAllocVar(rp), recRoundVar(rp), recTouchVar(rp), n)
                // ONE CallEntry per level: `n` levels, at least the outermost one
                (total + CostInterval(cbody.lo, closed) + model.callFrame.scale(Sym.one, n),
                 Meas(n * mbody.size, mbody.len, n * mbody.size))

      case Space.Call(rp, _, mentions) =>
        val why = if env.routines.isDefinedAt(rp) then s"call to ${rp.s} beyond the call-depth cap ($MaxInline nested routines)"
                  else s"call to ${rp.s} with no routine body available"
        st.note(why)
        (mentions.foldLeft(CostInterval.zero)((c, a) => c + go(a, env, model, st, depth + 1)._1) +
           CostInterval.unbounded(why), Meas.top)

      case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) =>
        st.note("a grounded closure's cost and output size are opaque to the analysis")
        (CostInterval.unbounded("grounded closure"), Meas.top)

  /** The loop body's environment: the head symbol is ONE item, and `rest` is the tail-set of one
   *  head-group — over-approximated by the union of ALL tails, which is sound (one group's tails
   *  are a subset).
   *
   *  `ms` must be the source's ALREADY-COMPUTED measure.  Re-deriving it from ⊤ here looked
   *  harmless but was not: for a `rest`-chained nest (`x.iter(h, t, t.iter(…))`) the inner source is
   *  a mention with no env entry, so the spatial query returns ⊤ and the whole nest's cost
   *  saturated to `inf`.  That hit 31% of the corpus. */
  private def loopEnv(env: Env, src: Space, ms: Meas, sym: PathRef, rest: SpaceMention, st: State): Env =
    val tailT = if rest.s == "_" then SpatialType.top else groupTailType(typeAt(Space.TailsUnion(src), env, st))
    env.copy(spaces = if rest.s == "_" then env.spaces else env.spaces + (rest -> Meas(ms.size, ms.len, ms.size)),
             paths = env.paths + (sym -> Sym.one),
             facts = env.facts.copy(
               spaces = if rest.s == "_" then env.facts.spaces else env.facts.spaces + (rest -> tailT),
               lenv = env.facts.lenv.withPath(sym -> LenBounds(1, 1))))

  /** THE TYPE OF ONE HEAD-GROUP'S `rest` MENTION.
   *
   *  The union of ALL tails is a sound MAY bound for one group's tails (a subset), and that is the
   *  only thing that survives the weakening.  Its MUST claims and its lower counts do NOT: a path
   *  that is in some group's tails need not be in THIS group's.
   *
   *  Passing the un-weakened tails-union type let the shape's `Subtraction` transfer delete paths
   *  from `x ∖ rest(p)` that were not provably present, which made an iteration source look
   *  PROVABLY EMPTY and collapsed the loop's predicted round count.  The event calibration caught it
   *  on 4-queens: 122 counted loop/call frames against a predicted upper bound of 28.  Widening the
   *  shape to ⊤ and zeroing the histogram's lower bounds costs precision in the loop body and buys
   *  back soundness, which is the required direction. */
  private def groupTailType(t: SpatialType): SpatialType =
    val mayOnly = SpaceType(SortedMap.from(t.lens.byLen.map((l, c) => l -> Ivl(0, c.hi))),
                            Ivl(0, t.lens.rest.hi), t.lens.restLens)
    SpatialType(Shape.top, mayOnly)

  /** THE FIXPOINT ROUND COUNT.
   *
   *  `eval`'s fixpoint replaces the candidate each round (`cur := body(cur)`) and stops when it
   *  stops changing, so in general the round count is NOT bounded by the result size.  When the body
   *  is syntactically `Union(rec, g)` the candidate is MONOTONE (`cur_{k+1} ⊇ cur_k`), so a round
   *  that does not terminate must add at least one path; with a finite bound `K` on the accumulated
   *  result — which contains every iterate — the loop runs at most `K + 1` rounds.  Otherwise the
   *  round count becomes a fresh SYMBOLIC variable and the reason is recorded: the cost stays
   *  parametric in an unknown instead of saturating. */
  private def fixRounds(f: Space.Fixpoint, env: Env, st: State, self: Meas): Sym =
    val Space.Fixpoint(_, recm, body) = f
    val monotone = body match
      case Space.Union(Space.Mention(m), _) => m == recm
      case Space.Union(_, Space.Mention(m)) => m == recm
      case _ => false
    val k = self.size
    if monotone then
      k match
        case Sym.Const(n) => Sym.c(n + 1)
        case Sym.Inf =>
          val v = st.nextVar("R")
          st.note(s"fixpoint over ${recm.s}: monotone accumulator but no finite bound on the result, so the " +
                  s"round count is the free variable $v")
          Sym.v(v)
        case other =>
          st.note(s"fixpoint over ${recm.s}: monotone accumulator, so rounds ≤ |result| + 1 = ${(other + Sym.one).show}")
          other + Sym.one
    else
      val v = st.nextVar("R")
      st.note(s"fixpoint over ${recm.s}: the body is not a monotone accumulator (not Union(${recm.s}, _)), so no " +
              s"round bound is derivable; the round count is the free variable $v")
      Sym.v(v)
end SpatialCost
