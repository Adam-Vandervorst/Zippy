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
 *  The same facts drive TWO backend cost instances ([[SetCost]], [[TrieCost]]).  They disagree — a
 *  trie intersection can skip a provably disjoint subtrie, a zipper `Unwrap` shares the focused
 *  subtrie instead of rebuilding a set, a trie `Range` needs no sort — and that disagreement is
 *  what makes this a cost model rather than a second size bound.
 *
 *  STANDING INVARIANT (docs/design_spatial_lattice.md §0): NO EVALUATION.  Nothing here calls
 *  `eval`/`evalI`/`evalT`/`exec*`.  Every input fact comes from the term's syntax, the declared
 *  annotations, or a read-only query to `SpatialTypes` / `SpatialTyping` / `Lower`.
 *
 *  WHAT IS AND IS NOT ESTABLISHED.  The per-operator constants are a *model* of the two
 *  interpreters, read off `eval` (MORKL.scala:235) and the trie/zipper operations; they are not
 *  measured constants and not proved.  What IS checked (`SpatialCostCheck`): the algebra's
 *  normalisation/idempotence, the soundness of `dominates` against numeric evaluation, the order
 *  chain, the per-operator transfers on small programs, backend disagreement, monotonicity, and a
 *  weak rank-correlation sanity check of the set-backend `work` against measured `eval` runtimes.
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
  def isUnbounded: Boolean = this match { case Unbounded(_) => true; case _ => false }
  def symOpt: Option[Sym] = this match { case Bounded(e) => Some(e); case _ => None }
  def show: String = this match
    case Bounded(e) => e.show
    case Unbounded(r) => s"UNBOUNDED($r)"

object Amount:
  val zero: Amount = Bounded(Sym.zero)
  def of(e: Sym): Amount = Bounded(Sym.normalize(e))

/** The three cost components, kept SEPARATE (review.md 3 asks for exactly this split).
 *
 *   - `work`   — elementary operand/node visits: set-element touches, trie node visits, path
 *                comparisons.  Unit: one touch.
 *   - `alloc`  — materialisation: paths inserted into a fresh intermediate set, or trie nodes
 *                allocated.  A structurally shared subtrie costs 0.  Unit: one path / one node.
 *   - `rounds` — dynamic frames: iteration/fold head-groups entered, fixpoint rounds, and recursive
 *                call levels.
 */
final case class Cost(work: Amount, alloc: Amount, rounds: Amount):
  def +(o: Cost): Cost = Cost(work + o.work, alloc + o.alloc, rounds + o.rounds)
  def scale(k: Sym): Cost =
    val a = Amount.of(k)
    Cost(work * a, alloc * a, rounds * a)
  def scale(k: Amount): Cost = Cost(work * k, alloc * k, rounds * k)
  def bigO: BigO = BigO.max(work.bigO, BigO.max(alloc.bigO, rounds.bigO))
  def show: String = s"work=${work.show}  alloc=${alloc.show}  rounds=${rounds.show}"
  def showO: String = s"work=${work.bigO.show}  alloc=${alloc.bigO.show}  rounds=${rounds.bigO.show}"

object Cost:
  val zero: Cost = Cost(Amount.zero, Amount.zero, Amount.zero)
  def w(e: Sym): Cost = Cost(Amount.of(e), Amount.zero, Amount.zero)
  def wa(wk: Sym, al: Sym): Cost = Cost(Amount.of(wk), Amount.of(al), Amount.zero)
  def r(e: Sym): Cost = Cost(Amount.zero, Amount.zero, Amount.of(e))
  def unbounded(reason: String): Cost =
    Cost(Amount.Unbounded(reason), Amount.Unbounded(reason), Amount.Unbounded(reason))

/** The size/shape facts a cost transfer consumes.  These are the ANALYSIS INPUTS — an upper bound
 *  on the path count, on the item-length of a path, and on the distinct-head count (an
 *  `Iteration`'s group count).  Symbolic in the free mentions/refs, refined by whatever
 *  `SpatialTyping`/`SpatialTypes` can prove. */
final case class Meas(size: Sym, len: Sym, heads: Sym):
  /** worst-case trie node count: no prefix sharing assumed */
  def nodes: Sym = size * len
  def show: String = s"|·|≤${size.show} len≤${len.show} heads≤${heads.show}"

object Meas:
  val empty: Meas = Meas(Sym.zero, Sym.zero, Sym.zero)
  val top: Meas = Meas(Sym.Inf, Sym.Inf, Sym.Inf)

// ================================================================================================
// 3. BACKEND COST INSTANCES
// ================================================================================================

/** A per-operator cost transfer.  Each method returns the LOCAL cost of one node; the traversal in
 *  [[SpatialCost]] adds the operands' costs and scales loop bodies by their group counts.  Two
 *  instances over the SAME facts is the whole point: a program has different costs per backend. */
trait CostModel:
  def name: String
  def literal(m: Meas): Cost
  def singleton(plen: Sym): Cost
  def mention(m: Meas): Cost
  def union(a: Meas, b: Meas): Cost
  def inter(a: Meas, b: Meas, disjoint: Boolean): Cost
  def subtract(a: Meas, b: Meas, disjoint: Boolean): Cost
  def restrict(x: Meas, y: Meas): Cost
  def raffine(x: Meas, y: Meas): Cost
  def compose(a: Meas, b: Meas): Cost
  def wrap(src: Meas, plen: Sym): Cost
  def unwrap(src: Meas, plen: Sym): Cost
  def tailsUnion(src: Meas): Cost
  def tailsInter(src: Meas): Cost
  def range(x: Meas, window: Sym): Cost
  /** splitting the source into head-groups, EXCLUDING the body */
  def group(src: Meas): Cost
  /** unioning the per-group body results into the loop's output */
  def collect(groups: Sym, body: Meas): Cost
  def foldStep(groups: Sym, updLen: Sym): Cost
  /** one fixpoint round's union + equality check, EXCLUDING the body */
  def fixStep(acc: Meas, body: Meas): Cost

/** The reference `Set[PathValue]` evaluator (`eval`, MORKL.scala:235).
 *
 *  Every operator materialises a fresh `Set`, so `alloc` tracks the result size everywhere.  Two
 *  costs are read straight off the code and are where this backend loses: `Restriction` is
 *  `recs(x).filter(x => prefixes.exists(...))` — a NESTED SCAN, `|x|·|y|` prefix comparisons — and
 *  `Range` is `.toVector.sorted.slice`, i.e. a comparison sort, `|x| log |x|` comparisons each
 *  costing up to `len` item compares. */
object SetCost extends CostModel:
  import Sym.tighter
  val name = "set"
  def literal(m: Meas): Cost = Cost.wa(m.size, m.size)
  def singleton(plen: Sym): Cost = Cost.wa(plen, Sym.one)
  def mention(m: Meas): Cost = Cost.zero                      // already a materialised set
  def union(a: Meas, b: Meas): Cost = Cost.wa(a.size + b.size, a.size + b.size)
  def inter(a: Meas, b: Meas, disjoint: Boolean): Cost =
    Cost.wa(a.size + b.size, tighter(a.size, b.size))         // a set evaluator CANNOT skip
  def subtract(a: Meas, b: Meas, disjoint: Boolean): Cost = Cost.wa(a.size + b.size, a.size)
  def restrict(x: Meas, y: Meas): Cost = Cost.wa(x.size * y.size * y.len, x.size)
  def raffine(x: Meas, y: Meas): Cost =                       // x ∖ (x <| y)
    restrict(x, y) + subtract(x, x, false)
  def compose(a: Meas, b: Meas): Cost =
    Cost.wa(a.size * b.size * (a.len + b.len), a.size * b.size)
  def wrap(src: Meas, plen: Sym): Cost = Cost.wa(src.size * (plen + src.len), src.size)
  def unwrap(src: Meas, plen: Sym): Cost = Cost.wa(src.size * plen, src.size)
  def tailsUnion(src: Meas): Cost = Cost.wa(src.size, src.size)
  def tailsInter(src: Meas): Cost = Cost.wa(src.size + src.size, src.size)
  def range(x: Meas, window: Sym): Cost =
    Cost.wa(x.size * Sym.log(x.size) * x.len, x.size)         // COMPARISON SORT
  def group(src: Meas): Cost = Cost.wa(src.size, src.size)    // groupMap over every path
  def collect(groups: Sym, body: Meas): Cost = Cost.wa(groups * body.size, groups * body.size)
  def foldStep(groups: Sym, updLen: Sym): Cost = Cost.wa(groups * updLen, groups)
  def fixStep(acc: Meas, body: Meas): Cost =
    Cost.wa(acc.size + body.size, acc.size + body.size)

/** The trie/zipper evaluator (`Trie.scala` / `IntTrie.scala` / `Zipper.scala`).
 *
 *  Three structural differences from the set backend, and they are the reason this file exists:
 *
 *   1. a merge only visits SHARED structure, so an intersection/subtraction whose operands the
 *      shape domain proves disjoint costs one top-level head comparison and allocates NOTHING;
 *   2. `Unwrap`/`Wrap` are zipper moves: descend `|p|` levels and hand back the focused subtrie
 *      (alloc 0), or allocate a `|p|`-node spine over a SHARED child — neither is proportional to
 *      `|src|`;
 *   3. the trie is stored in canonical path order, so `Range` is an ordered walk, not a sort — the
 *      `n log n` term disappears.
 *
 *  It is NOT uniformly cheaper: `collect` pays per trie node rather than per path, so a loop whose
 *  body produces long paths costs more here.  That asymmetry is the model working. */
object TrieCost extends CostModel:
  import Sym.tighter
  val name = "trie"
  private def nd(m: Meas): Sym = m.nodes
  def literal(m: Meas): Cost = Cost.wa(nd(m), nd(m))
  def singleton(plen: Sym): Cost = Cost.wa(plen, plen)
  def mention(m: Meas): Cost = Cost.zero
  def union(a: Meas, b: Meas): Cost = Cost.wa(nd(a) + nd(b), tighter(nd(a), nd(b)))
  def inter(a: Meas, b: Meas, disjoint: Boolean): Cost =
    if disjoint then Cost.wa(a.heads + b.heads, Sym.zero)     // SKIP: no shared subtrie to descend
    else Cost.wa(tighter(nd(a), nd(b)), tighter(nd(a), nd(b)))
  def subtract(a: Meas, b: Meas, disjoint: Boolean): Cost =
    if disjoint then Cost.wa(a.heads + b.heads, Sym.zero)     // the result IS `a`, shared
    else Cost.wa(tighter(nd(a), nd(b)), nd(a))
  def restrict(x: Meas, y: Meas): Cost =
    Cost.wa(nd(y) + nd(x), nd(y))                             // descend the prefix trie ONCE
  def raffine(x: Meas, y: Meas): Cost = restrict(x, y) + Cost.wa(nd(x), nd(x))
  def compose(a: Meas, b: Meas): Cost =
    Cost.wa(nd(a) + a.size, nd(a))                            // graft the SHARED b under a's leaves
  def wrap(src: Meas, plen: Sym): Cost = Cost.wa(plen, plen)  // a new spine over a shared child
  def unwrap(src: Meas, plen: Sym): Cost = Cost.wa(plen, Sym.zero)   // zipper focus, no rebuild
  def tailsUnion(src: Meas): Cost = Cost.wa(nd(src), nd(src))
  def tailsInter(src: Meas): Cost = Cost.wa(nd(src), nd(src))
  def range(x: Meas, window: Sym): Cost =
    Cost.wa(x.size + x.len, tighter(window, x.size))          // ordered walk, NO SORT
  def group(src: Meas): Cost = Cost.wa(src.heads, Sym.zero)   // the head children ARE the groups
  def collect(groups: Sym, body: Meas): Cost = Cost.wa(groups * nd(body), groups * nd(body))
  def foldStep(groups: Sym, updLen: Sym): Cost = Cost.wa(groups * updLen, groups)
  def fixStep(acc: Meas, body: Meas): Cost = Cost.wa(nd(acc) + nd(body), nd(acc) + nd(body))

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

  def close(c: Cost, tvarWork: String, tvarAlloc: String, tvarRounds: String, n: Sym): Cost =
    Cost(close(c.work, tvarWork, n), close(c.alloc, tvarAlloc, n), close(c.rounds, tvarRounds, n))

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

  final case class Report(model: String, cost: Cost, meas: Meas, assumptions: Vector[String]):
    def show: String =
      val a = if assumptions.isEmpty then "" else assumptions.distinct.map("    ! " + _).mkString("\n", "\n", "")
      s"[$model] ${cost.show}\n  O: ${cost.showO}\n  in: ${meas.show}$a"

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
    Report(model.name, c, m, st.notes.toVector)

  /** Both backends over the same facts — the comparison this file exists to make. */
  def compare(s: Space, env: Env = Env()): (Report, Report) = (analyze(s, env, SetCost), analyze(s, env, TrieCost))

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

  /** Meet the symbolically propagated bound with whatever the spatial analyses prove.  All the
   *  candidates are sound upper bounds of the SAME quantity, so [[Sym.tighter]] preserves
   *  soundness; `heads ≤ size` is also a true fact and is applied unconditionally. */
  private def refine(m: Meas, s: Space, env: Env, st: State): Meas =
    var out = histAt(s, env, st) match
      case None => m
      case Some(t) => Meas(tighter(m.size, symSize(t.size.hi)), tighter(m.len, symLen(t.len)), m.heads)
    shapeAt(s, env, st) match
      case Some(t) => out = out.copy(heads = tighter(out.heads, symSize(t.headCount.hi)))
      case None => ()
    out.copy(heads = tighter(out.heads, out.size))

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

  // ---- the transfer ----------------------------------------------------------------------------
  private def go(s: Space, env: Env, model: CostModel, st: State, depth: Int): (Cost, Meas) =
    if depth > MaxDepth then (Cost.unbounded(s"analysis depth cap ($MaxDepth) reached"), Meas.top)
    else goNode(s, env, model, st, depth)

  private def goNode(s: Space, env: Env, model: CostModel, st: State, depth: Int): (Cost, Meas) =
    def rec(x: Space) = go(x, env, model, st, depth + 1)
    s match
      case Space.Empty => (Cost.zero, Meas.empty)

      case Space.Literal(SpaceValue(ps)) =>
        val m = Meas(Sym.c(ps.size.toLong),
                     Sym.c(if ps.isEmpty then 0L else ps.iterator.map(_.items.length.toLong).max),
                     Sym.c(ps.iterator.collect { case PathValue(h :: _) => h }.toSet.size.toLong))
        (model.literal(m), m)

      case Space.Singleton(p) =>
        val lp = plen(p, env)
        (model.singleton(lp), Meas(Sym.one, lp, Sym.one))

      case Space.Mention(m) =>
        val mm = refine(mentionMeas(m, env), s, env, st)
        (model.mention(mm), mm)

      case Space.Union(a, b) =>
        val (ca, ma) = rec(a); val (cb, mb) = rec(b)
        val m = refine(Meas(ma.size + mb.size, ma.len lub mb.len, ma.heads + mb.heads), s, env, st)
        (ca + cb + model.union(ma, mb), m)

      case Space.Intersection(a, b) =>
        val (ca, ma) = rec(a); val (cb, mb) = rec(b)
        val disj = provablyEmpty(s, env, st)
        val m = refine(Meas(tighter(ma.size, mb.size), tighter(ma.len, mb.len), tighter(ma.heads, mb.heads)), s, env, st)
        (ca + cb + model.inter(ma, mb, disj), m)

      case Space.Subtraction(a, b) =>
        val (ca, ma) = rec(a); val (cb, mb) = rec(b)
        val disj = provablyEmpty(Space.Intersection(a, b), env, st)
        val m = refine(Meas(ma.size, ma.len, ma.heads), s, env, st)
        (ca + cb + model.subtract(ma, mb, disj), m)

      case Space.Restriction(x, y) =>
        val (cx, mx) = rec(x); val (cy, my) = rec(y)
        val m = refine(Meas(mx.size, mx.len, mx.heads), s, env, st)
        (cx + cy + model.restrict(mx, my), m)

      case Space.Raffination(x, y) =>
        val (cx, mx) = rec(x); val (cy, my) = rec(y)
        val m = refine(Meas(mx.size, mx.len, mx.heads), s, env, st)
        (cx + cy + model.raffine(mx, my), m)

      case Space.Composition(a, b) =>
        val (ca, ma) = rec(a); val (cb, mb) = rec(b)
        val m = refine(Meas(ma.size * mb.size, ma.len + mb.len, ma.heads + mb.heads), s, env, st)
        (ca + cb + model.compose(ma, mb), m)

      case Space.Wrap(src, p) =>
        val (cs, ms) = rec(src)
        val lp = plen(p, env)
        val hd = if SpatialTypes.pathLen(p, env.facts.lengths).lo >= 1 then Sym.one else ms.heads
        val m = refine(Meas(ms.size, lp + ms.len, hd), s, env, st)
        (cs + model.wrap(ms, lp), m)

      case Space.Unwrap(src, p) =>
        val (cs, ms) = rec(src)
        val lp = plen(p, env)
        val m = refine(Meas(ms.size, ms.len, ms.size), s, env, st)
        (cs + model.unwrap(ms, lp), m)

      case Space.TailsUnion(src) =>
        val (cs, ms) = rec(src)
        val m = refine(Meas(ms.size, ms.len, ms.size), s, env, st)
        (cs + model.tailsUnion(ms), m)

      case Space.TailsIntersection(src) =>
        val (cs, ms) = rec(src)
        val m = refine(Meas(ms.size, ms.len, ms.size), s, env, st)
        (cs + model.tailsInter(ms), m)

      case Space.Range(x, lo, hi) =>
        val (cx, mx) = rec(x)
        val w = rangeWindow(lo, hi)
        val m = refine(Meas(tighter(mx.size, w), mx.len, tighter(mx.heads, w)), s, env, st)
        (cx + model.range(mx, w), m)

      // ---- THE LOOPS: work = (head-groups) × (body work) ----------------------------------------
      case Space.Iteration(src, sym, rest, body) =>
        val (cs, ms) = rec(src)
        val groups = ms.heads                                  // the GROUP COUNT is the head count
        val benv = loopEnv(env, src, ms, sym, rest, st)
        val (cb, mb) = go(body, benv, model, st, depth + 1)
        val m = refine(Meas(groups * mb.size, mb.len, groups * mb.size), s, env, st)
        val cost = cs + model.group(ms) + cb.scale(groups) + model.collect(groups, mb) + Cost.r(groups)
        (cost, m)

      case Space.Fold(src, initial, acc, sym, rest, body, update) =>
        val (cs, ms) = rec(src)
        val groups = ms.heads
        val benv0 = loopEnv(env, src, ms, sym, rest, st)
        val benv = benv0.copy(paths = benv0.paths + (acc -> Sym.v(s"|acc:${acc.s}|")))
        val (cb, mb) = go(body, benv, model, st, depth + 1)
        val m = refine(Meas(groups * mb.size, mb.len, groups * mb.size), s, env, st)
        val cost = cs + model.group(ms) + cb.scale(groups) + model.collect(groups, mb) +
                   Cost.wa(plen(initial, env), Sym.one) +            // the accumulator's seed, once
                   model.foldStep(groups, plen(update, benv)) + Cost.r(groups)
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
        val m = refine(Meas(rounds * mb.size + mi.size, mi.len lub mb.len, rounds * mb.size + mi.size), s, env, st)
        val cost = ci + cb.scale(rounds) + model.fixStep(self, mb).scale(rounds) + Cost.r(rounds)
        (cost, m)

      // ---- CALLS: inline, or solve the recurrence ------------------------------------------------
      case Space.Call(rp, refs, mentions) if env.active(rp) =>
        // a recursive occurrence: emit MARKER variables, which the enclosing inlining step reads
        // back out of the normalised polynomial as the recurrence's branching factor
        (Cost(Amount.of(Sym.v(recWorkVar(rp))), Amount.of(Sym.v(recAllocVar(rp))), Amount.of(Sym.v(recRoundVar(rp)))),
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
        val total = argCosts.foldLeft(Cost.zero)((c, x) => c + x._1)
        def mentionsMarker(a: Amount, v: String) = a.symOpt.exists(e => Sym.vars(e).contains(v))
        if !mentionsMarker(cbody.work, recWorkVar(rp)) && !mentionsMarker(cbody.alloc, recAllocVar(rp)) &&
           !mentionsMarker(cbody.rounds, recRoundVar(rp)) then
          (total + cbody, mbody)
        else
          // a genuine recursion: find the decreasing measure, then close the linear recurrence
          Recurrence.decreasingArg(rbody, rp, mentionns) match
            case None =>
              st.note(s"recursive routine ${rp.s}: no argument provably loses an item per call, so no " +
                      "recursion depth bound and no closed form")
              (total + Cost.unbounded(s"recursion in ${rp.s} without a decreasing measure"), Meas.top)
            case Some(i) =>
              val argLen = mentions.lift(i).map(a => SpatialTypes.lenOf(a, env.facts.lengths).hi).getOrElse(LenBounds.INF)
              val n = Recurrence.depthBound(argLen)
              if n == Sym.Inf then
                st.note(s"recursive routine ${rp.s}: argument $i decreases but its maximum path length " +
                        "is not bounded, so the depth is not bounded")
                (total + Cost.unbounded(s"recursion in ${rp.s}: unbounded argument length"), Meas.top)
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
                val closed = Recurrence.close(cbody, recWorkVar(rp), recAllocVar(rp), recRoundVar(rp), n)
                (total + closed + Cost.r(n), Meas(n * mbody.size, mbody.len, n * mbody.size))

      case Space.Call(rp, _, mentions) =>
        val why = if env.routines.isDefinedAt(rp) then s"call to ${rp.s} beyond the call-depth cap ($MaxInline nested routines)"
                  else s"call to ${rp.s} with no routine body available"
        st.note(why)
        (mentions.foldLeft(Cost.zero)((c, a) => c + go(a, env, model, st, depth + 1)._1) + Cost.unbounded(why),
         Meas.top)

      case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) =>
        st.note("a grounded closure's cost and output size are opaque to the analysis")
        (Cost.unbounded("grounded closure"), Meas.top)

  /** The loop body's environment: the head symbol is ONE item, and `rest` is the tail-set of one
   *  head-group — over-approximated by the union of ALL tails, which is sound (one group's tails
   *  are a subset).
   *
   *  `ms` must be the source's ALREADY-COMPUTED measure.  Re-deriving it from ⊤ here looked
   *  harmless but was not: for a `rest`-chained nest (`x.iter(h, t, t.iter(…))`) the inner source is
   *  a mention with no env entry, so the spatial query returns ⊤ and the whole nest's cost
   *  saturated to `inf`.  That hit 31% of the corpus. */
  private def loopEnv(env: Env, src: Space, ms: Meas, sym: PathRef, rest: SpaceMention, st: State): Env =
    val tailT = if rest.s == "_" then SpatialType.top else typeAt(Space.TailsUnion(src), env, st)
    env.copy(spaces = if rest.s == "_" then env.spaces else env.spaces + (rest -> Meas(ms.size, ms.len, ms.size)),
             paths = env.paths + (sym -> Sym.one),
             facts = env.facts.copy(
               spaces = if rest.s == "_" then env.facts.spaces else env.facts.spaces + (rest -> tailT),
               lenv = env.facts.lenv.withPath(sym -> LenBounds(1, 1))))

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
