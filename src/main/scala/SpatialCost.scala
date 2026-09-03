package morkl

import scala.collection.immutable.SortedMap

/** ==============================================================================================
 *  SYMBOLIC COST — a cost algebra over the spatial facts.
 *
 *  The point of this file is the distinction the review says the repository keeps losing:
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
 *  WHAT IS AND IS NOT ESTABLISHED.  ALL FOUR cost components —
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
  /** AN ARBITRARY-PRECISION CONSTANT.  A large FINITE polynomial coefficient must
   *  stay a large finite number; the previous normal form multiplied coefficients in saturating `Long`
   *  arithmetic and turned `10^20` into [[Inf]], which is an implementation bug and not semantic
   *  uncertainty.  Never construct this directly: [[Sym.big]] narrows to [[Const]] whenever the value
   *  fits a `Long`, so every existing `Const(0)` / `Const(1)` pattern in the tree still fires. */
  case Big(n: BigInt)
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
  /** THE ARBITRARY-PRECISION CONSTRUCTOR.  Unlike [[c]] it has no `INF` sentinel: `Long.MaxValue` is a
   *  saturation marker in `Ivl`/`LenBounds`, but a coefficient computed HERE is a real number and stays
   *  one however large.  Narrowed to [[Const]] whenever it fits, so nothing downstream has to know. */
  def big(n: BigInt): Sym =
    if n <= 0 then Const(0) else if n < INFB then Const(n.toLong) else Big(n)
  def log(a: Sym): Sym = normalize(Log(a))
  def sum(xs: Iterable[Sym]): Sym = normalize(Add(xs.toVector))
  def prod(xs: Iterable[Sym]): Sym = normalize(Mul(xs.toVector))
  def maxOf(xs: Sym*): Sym = normalize(Max(xs.toVector))

  private[morkl] val INFB: BigInt = BigInt(INF)
  /** THE COEFFICIENT RING IS `BigInt`.  Nothing saturates here.  The ONE budget is
   *  the bit length past which a coefficient stops being expanded and is kept as a FACTORED symbolic
   *  product instead — the other alternative the review names — so an absurd exponent costs precision
   *  in the rendering and never turns a finite quantity into `inf`. */
  private val MaxCoefBits = 4096
  private def tooBig(n: BigInt): Boolean = n.bitLength > MaxCoefBits
  private val bigZero: BigInt = BigInt(0)
  private val bigOne: BigInt = BigInt(1)

  /** `b^e` in exact arithmetic, or `None` when the result would exceed [[MaxCoefBits]] and must stay
   *  factored.  The bit-length pre-check is what keeps this from allocating a gigabyte of digits. */
  private def exactPow(b: BigInt, e: Long): Option[BigInt] =
    if e <= 0 then Some(bigOne)
    else if b == bigZero then Some(bigZero)
    else if b == bigOne then Some(bigOne)
    else if e > Int.MaxValue.toLong then None
    else if b.bitLength.toLong * e > MaxCoefBits.toLong then None
    else Some(b.pow(e.toInt))
  /** ⌈log₂ n⌉, floored at 1 so a folded `Log` still respects the `atom ≥ 1` domain (only loosens) */
  private def ceilLog2(n: BigInt): Long =
    if n <= 2 then 1L else (n - 1).bitLength.toLong

  // ---- rendering (also the canonical key for atoms) ---------------------------------------------
  private[morkl] def render(e: Sym): String = e match
    case Const(n) => n.toString
    case Big(n) => n.toString
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
  private final case class P(inf: Boolean, ts: Map[Mono, BigInt])
  private val pZero = P(false, Map.empty)
  private val pInf = P(true, Map.empty)
  /** the `Long` entry point KEEPS the `INF` sentinel: `Sym.c(Long.MaxValue)` means "unbounded" */
  private def pConst(n: Long): P = if n >= INF then pInf else pConstB(BigInt(n))
  private def pConstB(n: BigInt): P = if n <= 0 then pZero else P(false, Map(unit -> n))
  private def pAtom(a: Sym): P = P(false, Map(SortedMap(render(a) -> (a, 1)) -> bigOne))

  private def addP(x: P, y: P): P =
    if x.inf || y.inf then pInf
    else
      var out = x.ts
      for (m, c) <- y.ts do out = out.updated(m, out.getOrElse(m, bigZero) + c)
      P(false, out.filter(_._2 != bigZero))

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
      var factor = false
      for (ma, ca) <- x.ts; (mb, cb) <- y.ts do
        val cc = ca * cb
        // PAST THE PRECISION BUDGET THE PRODUCT STAYS FACTORED, not infinite
        if tooBig(cc) then factor = true
        else out = addP(out, P(false, Map(mulMono(ma, mb) -> cc)))
      if factor then pAtom(Mul(Vector(fromP(x), fromP(y)).sortBy(render))) else out

  private def powP(b: Sym, e: Sym): P =
    val nb = normalize(b); val ne = normalize(e)
    (nb, ne) match
      case (_, Const(0)) => pConst(1)
      case (_, Const(1)) => toP(nb)
      case (Const(0), _) => pZero
      case (Const(1), _) => pConst(1)
      case (Inf, _) => pInf
      case (_, Inf) => pInf
      case (Const(m), Const(k)) => exactPow(BigInt(m), k).map(pConstB).getOrElse(pAtom(Pow(nb, ne)))
      case (Big(m), Const(k)) => exactPow(m, k).map(pConstB).getOrElse(pAtom(Pow(nb, ne)))
      case (_, Const(k)) if k >= 2 =>
        val pb = toP(nb)
        if pb.inf then pInf
        else if pb.ts.size == 1 then
          // a single monomial raised to a constant: multiply the exponents (keeps `fromP ∘ toP`
          // idempotent for large exponents, which repeated multiplication would not)
          val (m, cf) = pb.ts.head
          exactPow(cf, k) match
            case None => pAtom(Pow(nb, Const(k)))
            case Some(cc) =>
              var mm: Mono = unit
              var bad = false
              for (key, (a, ex)) <- m do
                val ne2 = ex.toLong * k
                if ne2 > Int.MaxValue.toLong then bad = true else mm = mm.updated(key, (a, ne2.toInt))
              if bad then pAtom(Pow(nb, Const(k))) else P(false, Map(mm -> cc))
        else if k <= 12 then
          var acc = pb; var i = 1L
          while i < k do { acc = mulP(acc, pb); i += 1 }
          acc
        else pAtom(Pow(nb, Const(k)))
      case _ => pAtom(Pow(nb, ne))

  private def logP(a: Sym): P = normalize(a) match
    case Inf => pInf
    case Const(n) => pConst(ceilLog2(BigInt(n)))
    case Big(n) => pConst(ceilLog2(n))
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
    case Big(n) => pConstB(n)
    case Var(x) => pAtom(Var(x))
    case Add(ts) => ts.foldLeft(pZero)((acc, t) => addP(acc, toP(t)))
    case Mul(fs) => fs.foldLeft(pConst(1))((acc, t) => mulP(acc, toP(t)))
    case Pow(b, x) => powP(b, x)
    case Max(as) => maxP(as)
    case Log(a) => logP(a)

  private def monoDeg(m: Mono): Int = m.valuesIterator.map(_._2).sum
  private def monoKey(m: Mono): String = m.toVector.map((k, ae) => s"$k^${ae._2}").mkString("*")

  private def monoSym(m: Mono, cf: BigInt): Sym =
    val fs = m.toVector.map { case (_, (a, e)) => if e == 1 then a else Pow(a, Const(e.toLong)) }
    val all = if cf == bigOne && fs.nonEmpty then fs else big(cf) +: fs
    if all.size == 1 then all.head else Mul(all)

  private def fromP(p: P): Sym =
    if p.inf then Inf
    else
      val live = p.ts.filter(_._2 != bigZero)
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
    case Big(n) => n >= 2
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

  /** SATURATING SUBTRACTION, as a FUNCTION and deliberately not as a [[Sym]] case.
   *
   *  `monus(a, b)` is a sound UPPER bound of `a − b` whenever `a` is an upper bound of the minuend
   *  and `b` a LOWER bound of the subtrahend.  It folds only what it can fold exactly and otherwise
   *  returns `a` unchanged — which is always sound, because `a − b ≤ a` over non-negative
   *  quantities.
   *
   *  ==WHY NOT A `Sym` CASE==
   *  The whole algebra is over non-negative quantities and [[Sym.dominates]] is a SYNTACTIC
   *  monotonicity test: adding a factor or raising an exponent may only increase a monomial.  A
   *  subtraction node breaks exactly that invariant, so `dominates` would need a new (and much
   *  harder) rule and every existing normalisation would have to be re-justified.  Keeping monus a
   *  fold means the normal form never contains one. */
  def monus(a: Sym, b: Sym): Sym = (a, b) match
    case (_, Const(0)) => a
    case (Inf, _) => Inf
    case (Const(x), Const(y)) => c(math.max(0L, x - y))
    case (Big(x), Const(y)) => big((x - BigInt(y)).max(0))
    case (Big(x), Big(y)) => big((x - y).max(0))
    case (Const(x), Big(y)) => big((BigInt(x) - y).max(0))
    case _ if a == b => zero
    case _ => a

  /** Both arguments must be SOUND UPPER BOUNDS of the same quantity; returns one of them (so the
   *  result is still a sound upper bound) preferring the tighter. */
  /** the better of two SOUND upper bounds.
   *
   *  `dominates` decides it when it can.  When neither dominates, the choice used to be made by
   *  [[bigO]] alone — an ASYMPTOTIC comparison — and that made the choice arbitrary at any concrete
   *  valuation: two bounds in the same order class, or in incomparable ones, can be ordered one way
   *  asymptotically and the other way at the sizes actually declared.
   *
   *  WHY THAT MATTERED, MEASURED.  `SpatialPipelineCheck`'s ITEM 8 gate compares the prediction with
   *  and without the decorated analysis at a concrete valuation, and consuming a MORE PRECISE input
   *  type made `gol`'s predicted `work` rise from 6051 to 6111 and `alloc` from 25376 to 25439 while
   *  `touch` improved.  Nothing in the transfers was unsound: a tighter input changed which of two
   *  incomparable candidates `tighter` selected, and the newly-selected one was asymptotically no
   *  worse but numerically larger where it is evaluated.  An arbitrary tie-break cannot be monotone
   *  in input precision, and monotonicity in input precision is the one thing a caller consuming a
   *  better analysis is entitled to.
   *
   *  So the fallback breaks the tie by VALUE when — and ONLY when — both bounds are GROUND, and
   *  otherwise by order class as before.  Both branches remain sound (this picks between two upper
   *  bounds, it does not compute a new one), and for two ground bounds the numerically smaller one is
   *  unambiguously the better answer where the old code chose arbitrarily.
   *
   *  THE GROUNDNESS CONDITION IS LOAD-BEARING, and leaving it out was a bug.  A first version
   *  compared at [[Sym.evalAt]]'s valuation unconditionally, and that valuation defaults an unknown
   *  variable to 2.0 — a PLACEHOLDER, not a size.  So `tighter(4, N)` saw `N = 2 < 4` and returned
   *  `N`, preferring a symbolic bound over a known smaller constant, which is backwards for a cost
   *  model: a declared constant is strictly more informative than a variable.  `SpatialCostCheck`'s
   *  "tighter picks a sound upper bound, and prefers the declared constant" caught it immediately,
   *  along with two transfer tests downstream of the same wrong choice.  With the condition, that
   *  case falls through to the order comparison, where `const <= linear` restores the preference.
   *
   *  WHAT THIS IS NOT.  It is not the pointwise minimum, which would be the principled answer and
   *  needs a `Min` node the polynomial normal form has no representation for (`Max` exists because
   *  the normal form treats it as an atom; `Min` would need the same treatment throughout
   *  `normalize`/`toP`/`bigO`/`dominates`). The residual arbitrariness is confined to bounds that
   *  are incomparable BOTH asymptotically and at the canonical valuation. */
  def tighter(a: Sym, b: Sym): Sym =
    if dominates(a, b) then normalize(b)
    else if dominates(b, a) then normalize(a)
    else
      val ground = vars(a).isEmpty && vars(b).isEmpty
      val (va, vb) = if ground then (evalAt(a, Map.empty), evalAt(b, Map.empty)) else (0.0, 0.0)
      if ground && va < vb then normalize(a)
      else if ground && vb < va then normalize(b)
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
    case Const(_) | Big(_) => BigO.const
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
    case Big(n) => n.toDouble
    case Inf => Double.PositiveInfinity
    case Var(x) => v.getOrElse(x, 2.0)
    case Add(ts) => ts.foldLeft(0.0)((s, t) => s + evalAt(t, v))
    case Mul(fs) => fs.foldLeft(1.0)((s, t) => s * evalAt(t, v))
    case Pow(b, x) => math.pow(evalAt(b, v), evalAt(x, v))
    case Max(as) => as.map(evalAt(_, v)).max
    case Log(a) => math.log(math.max(2.0, evalAt(a, v))) / math.log(2.0)

  def vars(e: Sym): Set[String] = e match
    case Var(x) => Set(x)
    case Const(_) | Big(_) | Inf => Set.empty
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
 *  ([[EffortComponent]]), which is what makes tightness measurable at all:
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
  /** COMPONENTWISE MEET OF TWO SOUND UPPER BOUNDS of the same cost.  Used where two independent
   *  derivations of the same quantity exist — the per-operator sum and the whole-region demand price
   *  for `execZ`, the frontier bound and the size ceiling for the trie algebra — so the report carries
   *  the tighter of the two and stays sound either way. */
  def meetHi(a: Cost, b: Cost): Cost =
    def m(x: Amount, y: Amount): Amount = (x, y) match
      case (Amount.Bounded(p), Amount.Bounded(q)) => Amount.of(Sym.tighter(p, q))
      case (Amount.Bounded(p), _) => Amount.of(p)
      case (_, Amount.Bounded(q)) => Amount.of(q)
      case (u, _) => u
    Cost(m(a.work, b.work), m(a.alloc, b.alloc), m(a.rounds, b.rounds), m(a.touch, b.touch))
  /** the JOIN of two sound LOWER bounds is a sound lower bound */
  def joinLo(a: Cost, b: Cost): Cost =
    def j(x: Amount, y: Amount): Amount = (x, y) match
      case (Amount.Bounded(p), Amount.Bounded(q)) => Amount.of(if Sym.dominates(p, q) then p else q)
      case (Amount.Bounded(p), _) => Amount.of(p)
      case (_, Amount.Bounded(q)) => Amount.of(q)
      case _ => Amount.zero
    Cost(j(a.work, b.work), j(a.alloc, b.alloc), j(a.rounds, b.rounds), j(a.touch, b.touch))
  def w(e: Sym): Cost = Cost(Amount.of(e), Amount.zero, Amount.zero, Amount.zero)
  def wa(wk: Sym, al: Sym): Cost = Cost(Amount.of(wk), Amount.of(al), Amount.zero, Amount.zero)
  def r(e: Sym): Cost = Cost(Amount.zero, Amount.zero, Amount.of(e), Amount.zero)
  def t(e: Sym): Cost = Cost(Amount.zero, Amount.zero, Amount.zero, Amount.of(e))
  /** the general constructor, in component order */
  def of(work: Sym = Sym.zero, alloc: Sym = Sym.zero, rounds: Sym = Sym.zero, touch: Sym = Sym.zero): Cost =
    Cost(Amount.of(work), Amount.of(alloc), Amount.of(rounds), Amount.of(touch))
  def unbounded(reason: String): Cost =
    Cost(Amount.Unbounded(reason), Amount.Unbounded(reason), Amount.Unbounded(reason), Amount.Unbounded(reason))

/** A LOWER/UPPER cost interval (the requirement: "return lower/upper cost intervals, not only a
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
  /** TWO INDEPENDENT DERIVATIONS OF THE SAME INTERVAL, met: the tighter upper and the stronger lower.
   *  Both inputs must bracket the same quantity, which is the caller's obligation. */
  def meet(a: CostInterval, b: CostInterval): CostInterval =
    CostInterval(Cost.joinLo(a.lo, b.lo), Cost.meetHi(a.hi, b.hi))

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
                      headKeys: Option[Set[PathItem]] = None,
                      epsAbsent: Boolean = false,
                      /** THE PER-VALUE COUNT-CACHE STATE — `CountKnown` when true, `CountUnknown`
                       *  otherwise (the "count-cache readiness is not part of the cost state").
                       *
                       *  `ITrie.count` memoises the terminal count PER NODE OBJECT (`IntTrie.scala`'s
                       *  `szc`), and it recurses, so one forced count on a node leaves EVERY node of that
                       *  subtree answered.  A transfer that prices a count therefore has two different
                       *  prices, and the difference is a property of the VALUE, not of the operator:
                       *
                       *    `CountKnown`   — every node of this value already carries its count, so
                       *                     `ITrie.count` is `O(1)` and emits no `TrieNodeVisit`;
                       *    `CountUnknown` — it may not, so the count costs the pre-order walk `N(x)`.
                       *
                       *  WHAT MAKES IT DERIVABLE FROM THE ANNOTATED TYPES rather than from a measured
                       *  run: the flag is set for exactly one syntactic class of value — a mention that is
                       *  FREE in the term being priced, i.e. an INPUT (nothing inside the term bound it,
                       *  so the object comes from the caller) — and only in [[ExecutionPhase.Warm]].  `Warm` means this executable has already
                       *  run on these very objects; the run is a function of the program and its inputs,
                       *  so every count the warm run forces the cold run forced too, and `count`'s memo
                       *  is on the shared immutable nodes.  A freshly built subexpression is never
                       *  `CountKnown`: its nodes were allocated by this run.  Loop-`rest` mentions and
                       *  callee parameters INHERIT the state of the value they are bound to (an `ITrie`
                       *  child is a shared subtrie of its parent, and `count`'s recursion answered it),
                       *  which is why the binder environments set the field explicitly. */
                      countKnown: Boolean = false,
                      /** DOES THIS OPERAND ALREADY EXIST AS A CONCRETE TRIE at run time?
                       *
                       *  `transpileZ` lifts `Empty`/`Singleton`/`Literal`/`Mention`/`Range` (and an
                       *  `Unwrap` chain over one of them) to a `SpaceZipper.Lit`, whose `materialize`
                       *  hands the existing `ITrie` straight back — zero `FreshNode`, zero
                       *  `ZipperMaterializeNode`, not one cursor read.  [[SpatialCost.liftsToLit]] is
                       *  the syntactic decision procedure; this field carries its answer into the
                       *  transfers that would otherwise charge a materialisation walk.
                       *
                       *  Defaults to `false`, which is always the SOUND direction (charging a walk
                       *  that does not happen over-approximates), so an unconverted construction site
                       *  cannot become unsound. */
                      concrete: Boolean = false,
                      /** THE TRIE-NODE COUNT'S LOWER ENDPOINT, when the shape's prefix profile gives
                       *  one.  `nodes`/`nodesHi` is an UPPER bound and may never be used as a must
                       *  count; the operators whose recursion visits EVERY node of an operand
                       *  (`compositionR`) need the other endpoint, and this is it. */
                      nodesLo: Option[Sym] = None,
                      /** IS THE ZIPPER'S `Lit` HANDED BACK BY POINTER, with no trie built at all?
                       *
                       *  Strictly stronger than [[concrete]] ([[SpatialCost.liftsToLit]]), and the
                       *  distinction is the one the counted oracle drew: `liftsToLit` is also true of
                       *  `Singleton` / `Range` / `Unwrap`-chains, whose OWN lift allocates trie nodes,
                       *  which is why zeroing the materialisation term on `concrete` took zipper
                       *  `Alloc` containment to 98%.  A bare `Mention` (and `Empty`) has no such lift:
                       *  `transpileZ` wraps an ITrie THAT ALREADY EXISTS. */
                      pointerLit: Boolean = false,
                      /** THE N-ARY FRONTIER OF THIS VALUE'S HEAD CHILDREN — see [[TailsFacts]].
                       *  `None` means the head set is not closed, or there are fewer than two
                       *  children, in which case the transfers' own identities already cover it. */
                      tails: Option[TailsFacts] = None,
                      /** A LOWER BOUND ON THE NODES OF THIS VALUE THAT HAVE AT LEAST ONE CHILD
                       *  ([[SpatialFacts.interiorNodes]]), `None` when the prefix profile gives none.
                       *
                       *  `nodesLo` is the wrong count for an allocation floor and the counted oracle
                       *  says so out loud: `compositionR` allocates at the nodes it does NOT take a
                       *  `{ε}` fast path at, and a LEAF terminal takes `rIdent(RIGHT)` and grafts `b`
                       *  by pointer.  On the operator fixture that is 9 of `a`'s 73 nodes — claiming
                       *  `nodesLo` as the `alloc` floor would put the lower endpoint at 73 against a
                       *  counted 9, i.e. an interval that does not contain the run. */
                      interiorLo: Option[Sym] = None):
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
  /** the OTHER endpoint of the same quantity: `0` when the profile gives none */
  def nodesFloor: Sym = nodesLo.getOrElse(Sym.zero)
  /** a MUST count of the nodes with a child — see [[interiorLo]]; `0` when nothing is proved */
  def interiorFloor: Sym = interiorLo.getOrElse(Sym.zero)
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
    s"|·|≤${size.show} len≤${len.show} heads≤${heads.show}$lo${if countKnown then " countKnown" else ""}"

/** ==================================================================================================
 *  THE N-ARY FRONTIER OF ONE VALUE'S HEAD CHILDREN.
 *
 *  `SpatialFrontier` gives every BINARY node a relational fact (paired prefixes, reuse, the algebraic
 *  case).  `TailsUnion`/`TailsIntersection` are not binary: they are `ITrie.joinAll` / `ITrie.meetAll`
 *  over the head children of ONE value, and until this record existed the model was told only how MANY
 *  children there are.  That is the gap `CostModel.naryScratchLo`'s note calls "the n-ary analogue of
 *  `SpatialFrontier`'s binary paired/reuse split, and the named next step".  This is that step.
 *
 *  ==THE TWO FACTS, AND WHY EACH IS SOUND==
 *
 *  `distinctLo` — A LOWER BOUND ON `live.length`.  `ITrie.joinAll`/`meetAll` open with
 *  `IntTrieOps.collectLive`, which dedups the operand array BY OBJECT IDENTITY.  Two tries with
 *  DIFFERENT CONTENT cannot be the same object, so a set of head children that are pairwise
 *  provably-different in γ is a set of pairwise-distinct objects and bounds `live.length` BELOW.  This
 *  is exactly what the refuted `kLo` must-count got wrong — `kLo` counts HEADS, and `{a·x, b·x}` builds
 *  ONE `{x}` object and hangs it under both keys — and it is why this channel is a different quantity
 *  and not a re-run of the same guess.
 *
 *  `keyDisjoint` — NO KEY IS PRESENT IN EVERY CHILD, and at most one child holds ε.  For the MEET that
 *  is decisive: `meetAllTries` only ever recurses into `ITrie.meetAll` on a key all `k` operands carry,
 *  so with `k ≥ 2` pairwise key-disjoint operands it never enters the ITrie level at all.  It stays in
 *  the Patricia layer, allocates no result node, and the whole call is bounded by the operands' own key
 *  count rather than by their node count.
 *
 *  ==WHAT IT IS NOT==
 *  It says nothing about `Iteration`'s accumulator: the operands there are the per-group BODY results,
 *  which are not the source's head children.  `collectJoin` therefore does NOT read this record. */
final case class TailsFacts(distinctLo: Long, keyDisjoint: Boolean, arity: Long,
                           childKeys: Option[Long],
                           /** EVERY child provably has a head of its own (`ε ∉ γ` on a node that is
                            *  not empty forces one).  `IntTrieOps.collectLive` runs with
                            *  `stopOnNil = true` under `meetAll` and ABANDONS the whole call at the
                            *  first operand whose child map is `IntMap.Nil` — which is exactly an
                            *  ε-only child — so without this the dedup scan has no must-count. */
                           allHeaded: Boolean):
  def show: String =
    s"tails(k=$arity distinct>=$distinctLo${if keyDisjoint then " KEY-DISJOINT" else ""}" +
      (if allHeaded then " all-headed" else "") + childKeys.map(n => s" keys<=$n").getOrElse("") + ")"

object TailsFacts:
  /** the per-pair work is `O(MaxHeads²)` set intersections; refuse to do it over spilled key sets that
   *  can be `MaxSpillKeys` wide, where the answer is almost never `disjoint` anyway */
  private val MaxKeysScanned = 256

  /** ================================================================================================
   *  THE JOIN'S FORCED DESCENT, when the operand set is PAIRWISE KEY-DISJOINT.
   *
   *  `T(m)` is a floor on the [[EffortEvent.NaryOperandProbe]]s that `IntTrieOps.joinAllTries` emits
   *  from ONE call with `m` live, pairwise key-disjoint, non-`Nil`, pairwise-distinct operands
   *  DOWNWARD — its own branching/split/identity scans and, recursively, everything its two child
   *  calls cannot avoid.  It is what turns the tails-union must side from "the root call" into "the
   *  root call and the descent it is committed to", and it is the only place in this file where a
   *  LOWER endpoint follows the recursion rather than stopping at the entry.
   *
   *  ==THE INVARIANT, AND WHY IT PROPAGATES==
   *  Call an operand array PKD when its entries are non-`Nil`, have pairwise disjoint key sets, and
   *  are therefore pairwise distinct OBJECTS (two `IntMap`s over different key sets cannot be the
   *  same object).  [[TailsFacts.keyDisjoint]] gives PKD at the root: it is computed over EVERY
   *  possibly-present child (`kids`, not `sure`), so it constrains the actual children too, and
   *  `allHeaded` (`ε ∉ γ` on every child) forces every child's children map to be non-`Nil`.
   *  `joinAllTries`'s split puts each live operand's LEFT child, or the operand itself, into `ls` and
   *  the mirror into `rs`; sub-maps of disjoint key sets are disjoint and `IntMap.Bin`'s children are
   *  never `Nil`, so BOTH child arrays are PKD again.
   *
   *  ==WHAT EACH TERM IS, QUOTED FROM `IntTrieOps.joinAllTries`==
   *   - `br ≠ 0`: `acc |= (repKey(live(i)) ^ rep) | maskOf(live(i))` is non-zero on a PKD array of
   *     `m ≥ 2` — either some operand is a `Bin` (mask ≠ 0) or all are `Tip`s on pairwise distinct
   *     keys (reps differ).  So a PKD call NEVER takes the `br == 0` `Tip` arm; it always splits.
   *   - `probes(k)` × 2: the branching-bit scan and the split, both exactly `m`.
   *   - `probes(i)` = `m`: the result-identity search runs to the END.  `nl + nr ≥ m` with both ≥ 1
   *     (an operand with `mm == br` lands on both sides, otherwise two reps differ at `br` and go
   *     opposite ways), so with `m ≥ 3` one side holds ≥ 2 instances; the join of ≥ 2 disjoint
   *     non-empty maps has a strictly larger key set than any one of them, so that side's merged map
   *     is `ne` every `l0`/`r0` and the `(l eq l0) && (r eq r0)` guard fails for every `i`.
   *   - the two child calls are UNCONDITIONAL in the split arm (`val l = joinAllTries(ls, nl)`,
   *     `val r = joinAllTries(rs, nr)`), and each opens with `collectLive`, whose `pr` over `a`
   *     pairwise-distinct entries is `Σ_{j<a} j` while the distinct count is under `dedupScanMax`.
   *     `dedupFloor` caps that at 24 exactly as [[SpatialCost]]'s `tailsProbesLo` does, because past
   *     the threshold the scan becomes one `IdentityHashMap` probe.
   *   - `a + b ≥ m` with `a, b ≥ 1`, and `dedupFloor(x) + T(x)` is non-decreasing, so the ADVERSARIAL
   *     split is on the boundary `a + b = m` and the `min` below is a floor for every real split.
   *   - `m ≤ 2` contributes nothing below it: `joinAllTries` returns a pointer at `k == 1` and
   *     delegates to the pairwise `unionTries` at `k == 2`, and neither emits a probe.
   *
   *  The table's own fixture: `T(8) = 64` against a counted 929 probes below the `ITrie` level, so
   *  this is a floor with two orders of slack on that point and not a fitted constant. */
  private final val MaxDescent = 256
  private def dedupFloor(x: Int): Long = { val d = math.min(x, 24); d.toLong * (d - 1) / 2 }
  private lazy val joinFloor: Array[Long] =
    val t = new Array[Long](MaxDescent + 1)
    var m = 3
    while m <= MaxDescent do
      var best = Long.MaxValue
      var a = 1
      while a < m do
        val v = dedupFloor(a) + dedupFloor(m - a) + t(a) + t(m - a)
        if v < best then best = v
        a += 1
      t(m) = 3L * m + best
      m += 1
    t
  /** `T(kd)`, clamped.  `T` is NON-DECREASING — `3m` grows and so does the `min`, since
   *  `dedupFloor(x) + T(x)` is monotone and every split of `m` extends to a split of `m + 1` — so
   *  reading it at `min(kd, MaxDescent)` is a floor for every larger live count too, and the clamp
   *  keeps the `O(MaxDescent²)` table from growing with a spilled head set.  (Verified numerically
   *  over `3 .. MaxDescent`: `T(3) = 10`, `T(8) = 64`, `T(64) = 2344`, `T(256) = 12568`.) */
  def joinDescentLo(kd: Long): Long =
    if kd < 3L then 0L else joinFloor(math.min(kd, MaxDescent.toLong).toInt)

  /** DERIVE the record from a shape whose head set is CLOSED — an open head set means an unknown
   *  number of unknown children and neither fact can be stated about them. */
  def of(sh: Shape): Option[TailsFacts] =
    if !sh.headsClosed then None
    else
      // TWO DIFFERENT SUB-SETS OF THE HEADS, AND CONFUSING THEM IS UNSOUND.  `sh.heads` is a MAY map:
      // a value in γ(sh) need only have the heads whose sub-shape is DEFINITELY non-empty, and the
      // rest it may simply lack.  So `keyDisjoint` — an upper-bound property, "no key can be in all
      // of them" — quantifies over every POSSIBLE child, while `distinctLo` — a must-count that ends
      // up as a LOWER endpoint — may only count children that are certainly there.  Counting the
      // possible ones instead put the predicted `alloc` floor for datalog-sn's `tails` at 84 against
      // a counted 67, i.e. an interval that does not contain the run.
      val kids = sh.heads.iterator.filter((_, t) => t.possiblyNonEmpty).map(_._2).toVector
      val sure = kids.filter(_.definitelyNonEmpty)
      if kids.length < 2 then None            // 0 or 1 head is an identity every transfer already has
      else
        val hs = kids.map(_.possibleHeads)
        val scannable = hs.forall(o => o.exists(_.size <= MaxKeysScanned))
        // PROVABLY DIFFERENT: both children are certainly present, both must have a head (`ε ∉ γ` on a
        // non-empty node forces one), and their possible head sets are known and share nothing — so no
        // one value can satisfy both, and two different values are two different objects.
        val sureHs = sure.map(_.possibleHeads)
        def differs(i: Int, j: Int): Boolean =
          sure(i).eps == Presence.No && sure(j).eps == Presence.No &&
            sureHs(i).exists(a => sureHs(j).exists(b => a.intersect(b).isEmpty))
        var reps = List.empty[Int]
        if scannable && sureHs.forall(o => o.exists(_.size <= MaxKeysScanned)) then
          for i <- sure.indices do if reps.forall(j => differs(i, j)) then reps = i :: reps
        val disjoint =
          scannable && kids.count(_.eps.mayBe) <= 1 &&
            (for i <- kids.indices; j <- i + 1 until kids.length yield hs(i).get.intersect(hs(j).get).isEmpty)
              .forall(identity)
        val keys = if scannable then Some(hs.map(_.get.size.toLong).sum) else None
        Some(TailsFacts(reps.length.toLong, disjoint, kids.length.toLong, keys,
                        kids.forall(_.eps == Presence.No)))

object Meas:
  val empty: Meas = Meas(Sym.zero, Sym.zero, Sym.zero, Sym.zero, Sym.zero)
  val top: Meas = Meas(Sym.Inf, Sym.Inf, Sym.Inf, Sym.zero, Sym.zero)
  /** the exact measure of a concrete value */
  def exact(size: Sym, len: Sym, heads: Sym): Meas = Meas(size, len, heads, size, heads)

// ------------------------------------------------------------------------------------------------
// 2b. THE RELATIONAL FACT OF ONE BINARY NODE
// ------------------------------------------------------------------------------------------------

/** WHAT A BINARY TRANSFER IS TOLD ABOUT THE *PAIR*, not about the two operands separately.
 *
 *  the complaint is that `Meas(size, len, heads, nodes)` plus the two booleans `same`
 *  and `headDisjoint` "cannot express these" — the paired-prefix frontier, the terminal-prefix accept
 *  count, the Patricia visits, the rebuilt-node bound, and the algebraic RESULT CASE
 *  (`Empty | Left | Right | Bespoke`).  [[SpatialFrontier.FrontierSummary]] expresses exactly those, and
 *  this record is how a [[CostModel]] receives one.
 *
 *  `frontier = None` means NO relational fact was obtainable at all (an inlined routine body whose
 *  positions belong to another tree, a `Meas` synthesised from a free variable, `shapeFacts = false`);
 *  the transfer then falls back to the size-only ceiling and says so.  `frontier.exists(_.isFallback)`
 *  is the MARKED coarse ceiling *inside* the summary — the summary was computed but the depth profile
 *  was truncated — which the review permits as a last resort provided it is labelled.  Both are counted
 *  by [[FrontierCensus]] so the report can state how much of a program was frontier-driven. */
/** ==================================================================================================
 *  WHICH ALREADY-MATERIALISED OBJECTS A TERM'S VALUE MAY SHARE `ITrie` NODES WITH.
 *
 *  `Rel.same` answers "are the two operands the SAME object" and that is all the ROOT `a eq b` test
 *  needs.  It is not what the RECURSIVE pointer-identity short circuits need.  Every ring operation in
 *  IntTrie.scala re-enters itself through its children-map merge, and both levels short-circuit on
 *  pointer identity:
 *
 *  {{{
 *    def unionR(a: ITrie, b: ITrie): AlgebraicResult =
 *      effort(EffortEvent.TrieNodeVisit)
 *      if a eq b then { effort(EffortEvent.ReusedSubtrie); ... rIdent(BOTH) }   // IntTrie.scala
 *    def unionTries(a: IntMap[ITrie], b: IntMap[ITrie]): IntMap[ITrie] =
 *      enter(); if a eq b then a                                               // IntTrieOps.scala
 *  }}}
 *
 *  so ONE pointer-shared subtree at a paired prefix of depth `d` skips EVERY paired prefix below it,
 *  while a must-paired floor is charged for all of them.  That is a LOWER-endpoint claim about a MAY
 *  fact (lessons 9), and it is reachable on two bare mentions: `S"a" ∪ (S"a" <| {h0})` counted a `touch`
 *  of 6 against a claimed floor of 11.
 *
 *  This record is the MAY over-approximation that discharges it.  `bases` names the already-existing
 *  objects the value can be built out of — a declared input mention, or a `Literal`'s `SpaceValue`,
 *  which the `iLiteral` / `internConstStr` memo caches turn into ONE trie per value — and `opaque`
 *  means "may share with anything", the answer whenever a rule cannot enumerate them.  Two values
 *  whose base sets are disjoint and neither opaque share no `ITrie` node, hence no interior `a eq b`
 *  and no child-map `a eq b` can fire between them.
 *
 *  THE ONE OBJECT DELIBERATELY NOT TRACKED is `ITrie.epsilon`, the process-wide terminal leaf every
 *  `ITrie.singleton` fold bottoms out in, and `IntMap.Nil`, its children.  A shared LEAF is harmless
 *  to a must-paired count for a reason that has nothing to do with the operands: the `a eq b` test is
 *  preceded by `effort(EffortEvent.TrieNodeVisit)`, so the visit at that prefix IS counted, and a leaf
 *  has no paired prefix strictly below it for the short circuit to skip.  `ITrie.empty` is the same
 *  object story and cannot be an interior child of a well-formed trie at all; at the root every caller
 *  of [[TrieAlgebraCost.priced]] has already discharged it (`provablyEmpty`, and `mustDescend`'s own
 *  `provablyNonEmpty`).  Nothing else in IntTrie.scala is shared or hash-consed: `ITrie.node` is a
 *  plain allocation (it counts one `EffortEvent.FreshTrieNode` and interns nothing), so two tries
 *  built from disjoint bases are node-disjoint however structurally equal they are.
 *
 *  ==THE ONE PREMISE THIS ANALYSIS DOES NOT ESTABLISH, STATED BECAUSE IT IS REFUTABLE==
 *  Two DISTINCT declared mentions are two different base tokens, so `disjointFrom` calls them
 *  node-disjoint.  `ic: Map[SpaceMention, ITrie]` does not promise that: a caller is free to bind `y`
 *  to a trie built out of `a`'s nodes, and then the floor is claimed on operands that do share.
 *  MEASURED, with `ic(y) = ITrie.wrap(h0, ITrie.unwrap(ic(a), h0))` and both mentions declared exactly
 *  (`a` = 64 paths over 8 heads, `y` = its `h0` slice re-wrapped, so `unwrap(ic(a), h0) eq
 *  ic(y).children(h0)`):
 *
 *  {{{
 *    trie/graph   a ∪ y   a ∩ y   a ∖ y      Touch [10, 60]  counted 3   OUT OF INTERVAL
 *  }}}
 *
 *  THAT IS NOT A COST OF THIS RECORD.  The same eight rows read the same intervals with the analysis
 *  removed — `mustDescend` alone assumed no sharing AT ALL, syntactic sharing included, so `Shares`
 *  strictly shrinks the set of programs that rest on the premise, and every row above is byte-identical
 *  before and after.  Closing it needs an ALIASING CHANNEL on the declared inputs (something in
 *  `SpatialAnnotations` that says which mentions may reach each other's nodes); until there is one, the
 *  premise is published on every report that depends on it, through the `st.note` in `relAt`.  Every
 *  calibration, corpus and cornerstone context materialises each declared space independently
 *  (`ITrie.fromSpaceValue` per mention), which is what makes the token disjointness a real disjointness
 *  there. */
private[morkl] final case class Shares(bases: Set[Any], opaque: Boolean):
  def lub(o: Shares): Shares = Shares(bases ++ o.bases, opaque || o.opaque)
  /** can NO `ITrie` node be reachable in both?  Conservative: `false` whenever either side is opaque. */
  def disjointFrom(o: Shares): Boolean =
    !opaque && !o.opaque && !bases.exists(o.bases.contains)

private[morkl] object Shares:
  /** a value built entirely out of fresh nodes (plus the shared `epsilon` leaf) */
  val fresh: Shares = Shares(Set.empty, opaque = false)
  /** may share with anything — the answer for every rule that cannot enumerate the bases */
  val any: Shares = Shares(Set.empty, opaque = true)
  def of(base: Any): Shares = Shares(Set(base), opaque = false)

final case class Rel(frontier: Option[FrontierSummary], same: Boolean, disjoint: Boolean,
                     /** CAN THE TWO OPERANDS SHARE AN `ITrie` NODE OBJECT?  See [[Shares]].  The
                      *  default is `true` — refuse the must-paired count — so a `Rel` built by a
                      *  construction site that has no syntax to look at claims nothing. */
                     mayShare: Boolean = true):
  /** does the frontier PROVE the result is an operand (or empty)?  Then nothing is rebuilt anywhere
   *  above it either — identity propagation, the case a size-only bound cannot see. */
  def identity: Boolean = frontier.exists(_.identity)
  /** is the price a real frontier bound rather than a ceiling on one? */
  def derived: Boolean = frontier.exists(!_.isFallback)
  def fallbackReason: Option[String] = frontier.flatMap(_.fallback)
  def source: Option[FrontierSource] = frontier.map(_.source)
  def show: String = frontier match
    case None => s"no relational fact (same=$same disjoint=$disjoint mayShare=$mayShare)"
    case Some(f) => f.show + (if mayShare then "  (operands MAY share structure)" else "")

object Rel:
  val none: Rel = Rel(None, false, false)

/** HOW MUCH OF A COST REPORT IS FRONTIER/DEMAND DRIVEN, and how much is the marked ceiling.
 *
 *  Published rather than argued: the review's instruction is "retain the coarse size ceiling only as a
 *  last-resort fallback", and the only way to know whether that held is to count. */
final case class FrontierCensus(binaryNodes: Int = 0, derived: Int = 0, fallback: Int = 0,
                                noFact: Int = 0, bySource: Map[String, Int] = Map.empty,
                                demandRegions: Int = 0, demandExact: Int = 0,
                                demandTruncated: Int = 0, chainNests: Int = 0):
  def derivedFraction: Double = if binaryNodes == 0 then 1.0 else derived.toDouble / binaryNodes
  def show: String =
    if binaryNodes == 0 && demandRegions == 0 && chainNests == 0 then "(no binary ring node)"
    else
      f"frontier ${derived}/${binaryNodes} derived (${100 * derivedFraction}%.0f%%), " +
      s"$fallback marked-ceiling, $noFact no-fact" +
      (if bySource.isEmpty then "" else bySource.toVector.sorted.map((k, v) => s"$k=$v").mkString(" [", " ", "]")) +
      (if demandRegions == 0 then "" else s"; demand $demandRegions regions ($demandExact exact, $demandTruncated truncated)") +
      (if chainNests == 0 then "" else s"; $chainNests rest-chain nests priced by the frame law")

// ================================================================================================
// 3. BACKEND COST INSTANCES
// ================================================================================================

/** WHICH EXECUTABLE a cost report describes.  The review: one `TrieCost`
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

/** WHICH FORM OF THE PROGRAM A COST REPORT DESCRIBES — the user's third steer, and the review 8's
 *  second half.
 *
 *  "Asymptotics belong on the OPTIMIZED/SUPERCOMPILED program, not the definitional one.  Just as one
 *  runs the optimized backend rather than the reference, a cost estimate should describe
 *  `Routine.optimized`'s body (spatial hook + `Lower` rules) or an `SC.reduce`/Supercompiler residual."
 *  A definitional-form estimate is not forbidden — sometimes there is nothing else — but it must be
 *  LABELLED as such rather than reported as if it described what runs. */
enum CostForm:
  /** `Routine.optimized`: the spatial hook (`SpatialHook.rewrite`) plus the ordinary `Lower` rule list */
  case Optimized
  /** an `SC.reduce` / `Supercompiler` residual */
  case Residual
  /** the DEFINITIONAL term, unoptimised.  Labelled, because it is the wrong question. */
  case Definitional
  /** whatever the caller handed in, provenance unknown */
  case AsGiven
  def show: String = this match
    case Optimized => "the OPTIMIZED body (spatial hook + Lower rules)"
    case Residual => "an SC/Supercompiler RESIDUAL"
    case Definitional => "the DEFINITIONAL term (NOT what runs — see CostForm)"
    case AsGiven => "the term as given"
  def describesWhatRuns: Boolean = this == Optimized || this == Residual

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
   *  phase declares one, so this list cannot grow without a test failing.  This is the review 1's
   *  fifth point: `touch` either has a counted oracle or says, in the model itself, that it does not. */
  def touchNoOracle: Option[String] = None

  // ---- THE N-ARY OPERAND LOOPS (the first P0) -------------------------------------------

  /** THE `work` OF THE OPERAND LOOPS OF ONE n-ARY JOIN/MEET — counted
   *  [[EffortEvent.NaryOperandProbe]]s of `ITrie.joinAll`/`meetAll` plus the `IntTrieOps` descent under
   *  it, over `k` operands whose subtries hold `nodes` nodes in total.
   *
   *  WHY THIS TERM EXISTS AT ALL.  These operations run several single-pass loops over their live
   *  operands PER RECURSIVE CALL — the identity dedup, the branching-bit scan, the split, the
   *  result-identity search — and none of it emits a `touch` event, so until `NaryOperandProbe` existed
   *  no bound charged for it.  That is exactly how a `Θ(k²)` dedup survived behind a passing "linear in
   *  arity" gate (the first P0).  With the dedup now expected-`O(k)` per call, this is what the
   *  loops cost.
   *
   *  BELOW THREE OPERANDS THERE IS NO DESCENT AND THE COUNT IS EXACT.  `joinAll`/`meetAll` return a
   *  pointer at `k <= 1` and delegate to the pairwise merge at `k == 2`, so the only loop that runs is
   *  `liveDistinct`'s dedup: `k(k-1)/2` identity comparisons, i.e. 0 and 1.  That is the common case on
   *  the corpus and it is priced exactly.
   *
   *  AT `k >= 3`, per live operand of a call: at most `min(k, 24)` identity comparisons in
   *  `collectLive`'s scan (one `IdentityHashMap` probe past that threshold, plus a one-off rehash of at
   *  most 24 buffered operands — the `+1` inside the `min`), then four more single passes (branching
   *  bit, split or `Tip` read, result identity, and `ITrie`'s own terminal/children/result scans).
   *
   *  ACROSS CALLS the live counts sum two ways and the SMALLER is used:
   *   - `k · (2·nodes + 1)`: no call has more than `k` live operands, and the descent makes at most
   *     `2·(child edges) + 1` calls because it follows the Patricia union of the operands' children maps
   *     and a Patricia tree over `m` keys has at most `2m-1` nodes;
   *   - `2·nodes + W·k` with `W = 32` the width of an interned `Int` key: an operand is live only at a
   *     call whose key region meets its own, which is the at most `W` levels above its range plus the at
   *     most `2·fan - 1` calls inside it.
   *  The first is tighter for few operands (the corpus), the second for many (the arity ladder). */
  /** THE SECOND FACTOR IS `Σ_calls |live|`, AND IT IS DERIVED FROM THE DESCENT, NOT GUESSED.
   *
   *  `IntTrieOps.joinAllTries` / `meetAllTries` recurse on a branching bit: at each call the live
   *  operands are partitioned into `ls`/`rs`, and an operand that is a `Bin` AT THAT BIT contributes
   *  its TWO CHILDREN, one to each side.  Every live entry in the whole descent is therefore a
   *  DISTINCT PATRICIA NODE of some operand's child map, and each such node appears in exactly one
   *  call's `live` array.  So
   *
   *      Σ_calls |live|  ≤  Σ_i (patricia nodes of operand i)  ≤  2·Σ_i m_i  ≤  2·nodes
   *
   *  (an `IntMap` with `m` entries has at most `2m − 1` nodes, and the operands here are the
   *  source's head-subtries, whose child edges are counted by `nodes`), plus `k` for the opening
   *  `collectLive` pass over the `k` top-level operands.
   *
   *  IT USED TO BE `tighter(k·(2·nodes+1), 2·nodes + 32k)`.  The `32k` was slack — `perProbe`'s own
   *  comment already said "the remaining slack is in `Σ|live|` (the `2·nodes + 32k` ceiling), not
   *  here" — and at the operator table's arity it DOMINATED: with `k` head groups, `32k` is 2048
   *  where the derived bound is `2·nodes + k`.  That single factor is most of the OP-6 / OP-6g /
   *  OP-6z interval width (99.8% of the counted `Work` on `iteration`, `tails-union` and
   *  `tails-inter` is `NaryOperandProbe`).
   *
   *  SOUNDNESS IS THE POINT, SO IT IS CHECKED AND NOT ARGUED.  A tighter interval that stops
   *  CONTAINING the counted value is worse than a wide one, so this bound is validated against the
   *  counted oracle by `SpatialEventsCheck`'s CALIBRATION gate (predicted intervals vs counted
   *  events on the optimised cornerstones) and by `SpatialCostCheck`'s corpus soundness sweep — the
   *  same gates that fail on any under-prediction anywhere. */
  protected def naryProbes(k: Sym, nodes: Sym): Sym = k match
    case Sym.Const(n) if n <= 2L => Sym.c(n * (n - 1) / 2)
    case _ =>
      perProbe(k) * Sym.tighter(k * (Sym.c(2) * nodes + Sym.one), Sym.c(2) * nodes + k)

  /** PROBES PER (CALL, LIVE OPERAND), derived from the three loops rather than bounded by the widest
   *  of them.  Per `joinAllTries`/`meetAllTries` call over `k` live operands (`IntTrieOps.scala`):
   *
   *    collectLive's dedup   Σ_{j<k} j = k(k−1)/2 while the distinct count is ≤ `dedupScanMax` = 24,
   *                          and `n + k + 24` past it (one `IdentityHashMap` probe each, plus the
   *                          one-off promotion pass) — so `(k−1)/2` per operand below the threshold
   *                          and at most `2 + 24/k` above it;
   *    the branching-bit scan  k          (one per operand)
   *    the split, or the Tip arm's value read + result-identity search   k, or 2k
   *
   *  so at most `dedup/k + 3` per operand.  The predecessor charged `min(k, 24) + 4`, which prices the
   *  dedup as a FULL linear scan for EVERY operand — i.e. `k` per operand where the amortised truth is
   *  `(k−1)/2` — and it did so even past the threshold where the scan is a hash probe.  At `k = 8`
   *  that is 12 against a derived 7; counted, the amortised figure over a whole `tails-union` on the
   *  operator table's source is 981/402 ≈ 2.4, so 7 is still an upper bound with room, and the
   *  remaining slack is in `Σ|live|` (the `2·nodes + 32k` ceiling), not here.
   *
   *  A SYMBOLIC `k` keeps the coarse form: the fold below needs an integer to halve. */
  private def perProbe(k: Sym): Sym = k match
    case Sym.Const(n) =>
      val dedupPer = if n <= 25L then (n + 1L) / 2L else 2L + (24L + n - 1L) / n
      Sym.c(dedupPer + 3L)
    case _ => Sym.tighter(k, Sym.c(24)) + Sym.c(4)

  /** THE MEET'S PRE-SCAN, which [[naryProbes]] does not price because it is a JOIN-shaped formula.
   *
   *  `IntTrie.meetAll` opens with `anyEmptyOperand(ts)`, whose `effortN(NaryOperandProbe, n)` counts how
   *  far the short-circuit got — at most one probe per operand, and exactly that when no operand is
   *  empty.  Nothing in [[naryProbes]] covers it: its `perProbe` accounts for `collectLive`'s dedup and
   *  the branching / split / identity scans of `{join,meet}AllTries`, and this loop is above all of
   *  them.  At three or more operands the `Σ|live|` ceiling swallows the difference, but at TWO it does
   *  not: `naryProbes(2, ·)` is `1` (`liveDistinct`'s single comparison) while a two-operand
   *  `tailsIntersection` counts 3 — 2 for this scan and 1 for the dedup — so the upper endpoint was
   *  BELOW the run on every two-headed meet.  Charged here rather than inside `naryProbes` so the
   *  n-ary JOIN, which has no such pre-scan, is not made to pay for it. */
  protected def naryPreScan(k: Sym): Sym = k

  /** THE `alloc` OF THE SAME LOOPS — counted [[EffortEvent.NaryScratchSlot]]s.  Per call the descent
   *  allocates the `live` operand array and the two split arrays, so three reference slots per live
   *  operand; `ITrie.joinAll`/`meetAll` add their `ArrayBuffer` (4 slots at construction, under `4k` once
   *  it has doubled to hold `k`) and the `children` array (`k`).
   *
   *  THE CONSTANT IS PER OPERATION AND IT IS GENEROUS ON PURPOSE.  One executed n-ary operation costs at
   *  least the buffer, and a transfer prices ONE operation where the executor may run its recursive
   *  `Tip`-arm joins as well; the flat `24` covers several such buffers rather than counting calls the
   *  shape domain cannot see.  It is a constant, so it changes no slope — and `alloc` is the Budget tier,
   *  where a per-operation constant of two dozen slots is inside the noise of a bound already met against
   *  `nd`. */
  protected def naryScratch(k: Sym, nodes: Sym): Sym = k match
    case Sym.Const(n) if n <= 2L => Sym.c(24) + Sym.c(4) * k
    case _ =>
      Sym.c(24) + Sym.c(5) * k +
        Sym.c(3) * Sym.tighter(k * (Sym.c(2) * nodes + Sym.one), Sym.c(2) * nodes + Sym.c(32) * k)

  /** ==============================================================================================
   *  THE MUST SIDE OF THE SAME TWO LOOPS — the endpoint that was 0 by construction.
   *
   *  Every n-ary transfer used `CostInterval.upperOnly`, so `alloc` started at 0 and `work`'s lower
   *  endpoint was the AST dispatch alone (2 or 10) against a counted 983.  99.8% of the counted
   *  `work` on `tails-union` / `tails-inter` / `iteration` is `NaryOperandProbe`, i.e. a component
   *  the model claimed NOTHING about on the must side — and interval WIDTH is
   *  `(upper + 1)/(lower + 1)`, so that alone put those channels three orders of magnitude over
   *  their budget.
   *
   *  THERE IS NO MUST SIDE HERE, AND IT IS NOT FOR WANT OF TRYING.  This is the single largest reason
   *  `tails-union` / `tails-inter` / `iteration` miss their `Alloc` and `Work` width budgets — both
   *  endpoints start at 0 — so two must-counts were derived from `Meas.headsLo` and both were REFUTED
   *  by the counted oracle on the first corpus run.  Recording why, because the intuition is very
   *  persuasive and wrong:
   *
   *   1. `4 + 3·kLo` SCRATCH SLOTS AND `kLo` PROBES from `kLo` heads: trie `Alloc` containment
   *      100% -> 98.5%, graph 100% -> 94%, zipper 100% -> 97.5%.  `kLo` bounds the HEADS, not the
   *      LIVE OPERANDS, and `liveDistinct` DEDUPS BY OBJECT IDENTITY — two distinct heads routinely
   *      share one child object (`{a.x, b.x}` builds ONE `{x}` trie and hangs it under both keys; an
   *      unchanged branch of a fixpoint iterate is literally the previous round's object).  `k` heads
   *      can collapse to ONE live operand, and then `joinAll` returns it by pointer: no split arrays,
   *      no terminal scan, and `collectLive`'s `pr += j` adds ZERO because every duplicate is found
   *      at index 0.
   *   2. THE BARE `ArrayBuffer(4)` that `liveDistinct` allocates on entry, which looks unconditional:
   *      zipper `Alloc` containment 100% -> 98% (4 of 200 corpus points).  Zeroing it took the whole
   *      suite back to exactly its baseline 97.33% (80 of 3000), which is what identifies it.
   *
   *  So: `alloc` and the operand-loop half of `work` keep a lower endpoint of 0 on every n-ary
   *  transfer, and the corresponding width rows stay RED.  Closing them needs a bound the current
   *  `Meas` channels cannot express — a LIVE-OPERAND count, i.e. how many of the head children are
   *  DISTINCT OBJECTS, which is per-head sub-shape information the measure does not carry.  That is
   *  the n-ary analogue of `SpatialFrontier`'s binary paired/reuse split, and it is the named next
   *  step rather than a constant to guess at. */
  protected def naryScratchLo(kLo: Sym): Sym = Sym.zero

  /** ==============================================================================================
   *  THE MUST SIDE OF THE TWO N-ARY LOOPS, FROM THE LIVE-OPERAND COUNT.
   *
   *  [[CostModel.naryScratchLo]]'s note records two must-counts derived from `Meas.headsLo` and
   *  REFUTED by the counted oracle within one run, and names what would close them: "a LIVE-OPERAND
   *  count, i.e. how many of the head children are DISTINCT OBJECTS".  [[TailsFacts.distinctLo]] is
   *  that count, and it is a different quantity from `headsLo` in exactly the way the refutation
   *  needed — `{a·x, b·x}` has two heads and ONE child object, and `distinctLo` counts 1 there
   *  because the two sub-shapes are not provably different.
   *
   *  WHAT THE RUN MUST DO, read off `IntTrie.liveDistinct` and `IntTrieOps.{join,meet}AllTries`
   *  (both `joinAll` and `meetAll` open with `liveDistinct`, so the first two lines hold for both):
   *
   *    `liveDistinct`  scratch  `max(4, 4·live.length)`               ≥ 4·kd   — UNCONDITIONAL
   *                    probes   `Σ_{i<kd} i` = kd(kd−1)/2 while kd ≤ 24        — every DISTINCT
   *                             operand scans all previously kept ones, and a duplicate found at
   *                             index 0 adds 0, so this is the floor and not the typical case
   *    `joinAll`/`meetAll` with 3+ live operands:
   *                    scratch  `live.length` for the `maps` array   ≥ kd
   *                    probes   `live.length` for the maps copy      ≥ kd
   *    the root `{join,meet}AllTries` call:
   *                    scratch  `n` for its own `live` array         ≥ kd
   *                             plus `k` (Tip arm) or `2k` (split)   ≥ kd
   *                    probes   `collectLive` again                  ≥ kd(kd−1)/2
   *                             the branching-bit scan               ≥ kd
   *                             the split, or the Tip value read     ≥ kd
   *
   *  `allHeaded` gates everything below `liveDistinct` because `meetAll`'s `collectLive` runs with
   *  `stopOnNil = true` and abandons the call at the first ε-only child; `kd ≥ 3` gates it because at
   *  two live operands `joinAll`/`meetAll` delegate to the binary `union`/`intersection`, which run
   *  none of these loops.  Nothing here is an estimate of the typical cost — every term is a floor a
   *  counted run cannot go below, and `SpatialEventsCheck`'s CALIBRATION is what says so. */
  protected def naryLiveLo(src: Meas): Option[Long] =
    src.tails.map(_.distinctLo).filter(_ >= 3L)
  protected def naryDeepLo(src: Meas): Option[Long] =
    src.tails.filter(t => t.allHeaded && t.distinctLo >= 3L).map(_.distinctLo)
  /** `NaryScratchSlot` this call cannot avoid */
  protected def tailsScratchLo(src: Meas): Sym =
    val shallow = naryLiveLo(src).map(4L * _).getOrElse(0L)
    val deep = naryDeepLo(src).map(3L * _).getOrElse(0L)
    Sym.c(shallow + deep)
  /** THE OPERAND SET IS PAIRWISE KEY-DISJOINT and every child is headed, so the whole
   *  `joinAllTries`/`meetAllTries` descent runs on PKD arrays — see
   *  [[TailsFacts.joinDescentLo]] for the invariant and what it licenses.  Gated on
   *  `Tuning.patriciaOps` for the same reason [[tailsForced]] is: with the flag off, `ITrie.joinAll`
   *  takes the `LongMap` group-by path and `IntTrieOps.joinAllTries` never runs at all, so a floor
   *  read off its source would be a claim about code that is not executing. */
  protected def naryDisjointLo(src: Meas): Option[Long] =
    if !Tuning.patriciaOps then None
    else src.tails.filter(t => t.allHeaded && t.keyDisjoint && t.distinctLo >= 3L).map(_.distinctLo)
  /** `NaryOperandProbe` this call cannot avoid */
  protected def tailsProbesLo(src: Meas): Sym =
    def dedup(kd: Long): Long = { val d = math.min(kd, 24L); d * (d - 1) / 2 }
    val shallow = naryLiveLo(src).map(dedup).getOrElse(0L)
    // ONE MORE FULL SCAN OF THE OPERANDS, ON BOTH OPERATORS, AND FROM DIFFERENT LINES.
    //   join: `ITrie.joinAll`'s terminal-flag loop is `while i < live.length` followed by
    //         `effortN(NaryOperandProbe, live.length)` — unconditional in the `>= 3` arm, and
    //         `live.length >= kd` because `liveDistinct(ts, dropEmpty = true)` keeps every one of the
    //         `kd` distinct non-empty children.
    //   meet: `ITrie.meetAll` opens with `anyEmptyOperand(ts)`, which counts HOW FAR IT GOT and stops
    //         at the first empty operand — so this term rests on exactly the premise the `3 * kd`
    //         below ALREADY needs: if any child were empty, `meetAll` would return `empty` right there
    //         and the maps copy / branching / split it charges would never run.  Under that premise
    //         the scan runs to the end of `ts = s.children.valuesIterator.toSeq`, i.e. `>= kd`.
    // Plus ONE probe neither operator can skip afterwards: the join's `ITrie`-level result-identity
    // search (`probes(i)`, and `i >= 1` because the loop body runs before the first test), the meet's
    // leading-terminal scan (`effortN(NaryOperandProbe, math.min(ti + 1, live.length))`, `>= 1`).
    val deep = naryDeepLo(src).map(kd => dedup(kd) + 3L * kd + kd + 1L).getOrElse(0L)
    Sym.c(shallow + deep)
  /** THE SAME FLOOR FOR THE JOIN, WHICH IS COMMITTED TO ITS DESCENT WHERE THE MEET IS NOT.
   *
   *  This is the asymmetry between the two operators, and it is one line of `IntTrieOps`:
   *  `meetAllTries` tests `if forcedL && forcedR then Nil` BEFORE it recurses, so on a key-disjoint
   *  operand set — the case where that test is most likely to fire — NOTHING below the root split is
   *  forced, and `tailsInter`'s floor stops there.  `joinAllTries` has no such exit: in the split arm
   *  both `joinAllTries(ls, nl)` and `joinAllTries(rs, nr)` are evaluated unconditionally.  That is
   *  also why the counted `tails-inter` (371) sits so far below the counted `tails-union` (983) on the
   *  very same operands.
   *
   *  Two terms are added on top of [[tailsProbesLo]], both from `IntTrie.joinAll`/`IntTrieOps`:
   *   - `kd - 1`: the `ITrie`-level result-identity search runs to the END, not one step.  `ch` is
   *     `joinAllTries(maps)`, the union of `>= 2` pairwise disjoint non-empty children maps, so its
   *     key set strictly contains each `maps(i)` and `ch eq live(i).children` is false for every `i`.
   *     One of those `kd` probes is already in `tailsProbesLo`'s `+ 1`.
   *   - `joinDescentLo(kd) - 2 * kd`: the descent, minus the root's branching-bit scan and split,
   *     which `tailsProbesLo`'s `3 * kd` already charges. */
  protected def tailsJoinProbesLo(src: Meas): Sym =
    val extra = naryDisjointLo(src)
      .map(kd => (kd - 1L) + (TailsFacts.joinDescentLo(kd) - 2L * kd)).getOrElse(0L)
    tailsProbesLo(src) + Sym.c(extra)

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
  /** THE CHARGE FOR A `Raffination`'s SECOND REFERENCE TO ITS LEFT OPERAND, given that operand's own
   *  priced interval `cx`.  RE-EVALUATING `x` AND RE-READING ONE SHARED CURSOR ARE NOT THE SAME
   *  QUANTITY, and the single boolean [[raffinationRereadsX]] could not tell them apart.
   *
   *   - `eval` RE-EVALUATES.  `MORKL.scala`: `case Space.Raffination(x_e, y_e) =>
   *     recs(Space.Subtraction(x_e, Space.Restriction(x_e, y_e)))` — the SAME `Space` term is handed to
   *     `recs` twice, so a loop inside `x` really runs its head-groups again and emits its
   *     `LoopBodyEntry`s again.  Both endpoints of `cx` are charged again, and the counted oracle
   *     agrees: `Raffination(Iteration(a, h, t, Mention(t) ∩ b), b)` over an 8-head `a` counts 16
   *     `Rounds` against a reference prediction of `[16, 16]`.  So [[ReferenceCost]] keeps the full `cx`.
   *   - `evalI`/`execT` EVALUATE ONCE.  `IntTrie.scala`: `case Space.Raffination(a, b) =>
   *     ITrie.raffination(evalI(a), evalI(b))`; `GraphExec.scala`: `case "Raffination" => … inputs(0).sget`
   *     — one value, reused inside `ITrie.raffination`.  Nothing extra: the default `zero`.
   *   - `execZ` LIFTS ONCE AND READS TWICE.  `Zipper.scala`: `case Space.Raffination(x, y) =>
   *     raffination(transpileZ(x), transpileZ(y))` with
   *     `def raffination(x, y) = Subtraction(x, restriction(x, y))` — ONE cursor object appears in both
   *     positions.  Everything the LIFT does therefore happens exactly once: every `ZipperBuild`, every
   *     `ITrie` call a lift makes, and — the part that made the old charge UNSOUND — the entire
   *     `case other => effort(ZipperFallbackToEvalI); traversal(evalI(other))` materialisation of a
   *     control-flow subterm inside `x`, whose `LoopBodyEntry`/`FixpointRound`/`CallEntry` events are
   *     what `Rounds` counts for this backend (`SpatialEvents.scala`, `OracleGap("ZIPPER-ROUNDS")`:
   *     execZ's rounds are "EXACTLY evalI's own … emitted INSIDE the same counted region").  What DOES
   *     happen twice is cursor TRAFFIC — the shared cursor is queried from the `Subtraction`'s left
   *     slot and again through `restriction(x, y)` — and that is an upper bound and nothing else, so
   *     the second charge is `upperOnly` and the LOWER endpoint of `cx` is charged ONCE.
   *
   *  MEASURED (the `raffL-*` fixtures over the shipped |a| = 64 / 8-head, |b| = 16 / 4-head inputs).
   *  Before: `Raffination(Iteration(a, h, t, Mention(t) ∩ b), b)` predicted zipper `Rounds` `[16, 8]`
   *  — an INVERTED interval — against a counted 8, and `Work` `[56, 992]` against a counted 38;
   *  `Raffination(Fixpoint(a, r, r ∪ Iteration(a, h, t, Mention(t) ∩ b)), b)` predicted `Rounds`
   *  `[18, 18]` against a counted 9.  This is the corpus signature `SpatialEventsCheck`'s CALIBRATION
   *  reported as `zipper Rounds actual= 8 in [16, 16]` and `zipper Work actual=29 in [38, 30]`.
   *  After: `[8, 8]` and `[9, 18]`, both containing the run.  The UPPER endpoints are untouched. */
  def raffinationSecondRead(cx: CostInterval): CostInterval =
    if raffinationRereadsX then cx else CostInterval.zero

  def empty: CostInterval = CostInterval.zero
  def literal(m: Meas): CostInterval
  def singleton(plen: Sym): CostInterval
  def mention(m: Meas): CostInterval
  /** THE BINARY TRANSFERS TAKE A [[Rel]], not two booleans.  `Rel.same` is still the
   *  pointer-identity fact (`ITrie.union`'s `a eq b`, `SpaceZipper.sameSpace`) and `Rel.disjoint` still
   *  the head-set disjointness one, but the frontier summary carried alongside them is what lets a
   *  transfer price the PAIRED FRONTIER instead of `N(a) + N(b)`. */
  def union(a: Meas, b: Meas, rel: Rel): CostInterval
  def inter(a: Meas, b: Meas, rel: Rel): CostInterval
  def subtract(a: Meas, b: Meas, rel: Rel): CostInterval
  def restrict(x: Meas, y: Meas, rel: Rel): CostInterval
  def raffine(x: Meas, y: Meas, rel: Rel): CostInterval
  def compose(a: Meas, b: Meas, rel: Rel): CostInterval
  /** THE SAME OPERATOR WHEN IT IS THE PRICED TERM'S OWN ROOT.
   *
   *  For the three EAGER executables that is no different from [[compose]] and the default says so.
   *  It exists for `execZ`, which is `SpaceZipper.materialize(transpileZ(s))`: a fused operator has no
   *  must side ANYWHERE INSIDE a term, because its parent layer decides whether it is ever forced —
   *  but the ROOT cursor is the one `materialize` is handed, so at the root, and only there, a
   *  materialisation floor is a fact about the executable rather than a hope about its consumer.
   *  Called with `depth == 0`; every other occurrence keeps [[compose]]. */
  def composeRoot(a: Meas, b: Meas, rel: Rel): CostInterval = compose(a, b, rel)
  def wrap(src: Meas, plen: Sym): CostInterval
  def unwrap(src: Meas, plen: Sym): CostInterval
  /** `forced` SAYS THE CONSUMER CANNOT DECLINE TO QUERY THIS CURSOR.
   *
   *  It is `true` exactly at the ROOT of the term being priced, because `execZ` is
   *  `SpaceZipper.materialize(transpileZ(s))` and `materialize`'s non-`Lit` arm runs
   *  `z.children` and `z.terminal` unconditionally — and `transpileZ` lifts `TailsUnion`/
   *  `TailsIntersection` to a virtual cursor that is never a `Lit`.  Only [[ZipperCost]] reads it:
   *  the eager executables call `ITrie.tailsUnion`/`tailsIntersection` whatever their consumer does,
   *  so their must side is unconditional and the flag is redundant for them.
   *
   *  THIS IS THE SIDE CONDITION `ZipperCost.tailsInter`'s note was missing.  That note refuses a must
   *  side because `merged` is a LAZY VAL and "a consumer that meets it with ∅ never [queries it]" —
   *  true of an INNER node and false of the root, which the model could not tell apart until this
   *  parameter existed. */
  def tailsUnion(src: Meas, forced: Boolean): CostInterval
  def tailsInter(src: Meas, forced: Boolean): CostInterval
  /** `identity` = the window provably covers the whole space, so the implementation may return its
   *  input unchanged */
  def range(x: Meas, window: Sym, identity: Boolean): CostInterval
  /** splitting the source into head-groups, EXCLUDING the body */
  def group(src: Meas): CostInterval
  /** unioning the per-group body results into the loop's output */
  def collect(groups: Sym, body: Meas): CostInterval
  def foldStep(groups: Sym, updNodes: Sym, updLen: Sym): CostInterval
  /** ITERATION's accumulation, which is `joinAll` — an N-ARY SIMULTANEOUS join, not the left fold
   *  [[collect]] had to cover for both (the requirement: "Split them").  Defaults to [[collect]] so an
   *  instance that has no separate story keeps the old, worse price. */
  /** `groupsLo` is a LOWER bound on the live GROUP count.  It is threaded in for the must side even
   *  though [[CostModel.naryScratchLo]] currently derives nothing from it — see the note there for the
   *  two must-counts the counted oracle refuted and for the live-operand channel that would close it. */
  /** `single` SAYS THIS TRANSFER PRICES EXACTLY ONE `ITrie.joinAll` CALL.  It is `true` at the plain
   *  `Iteration` arm — `evalI`'s `case Space.Iteration` ends in one `ITrie.joinAll(...)` — and `false`
   *  at the REST-CHAINED NEST arm, where one transfer stands in for the whole nest and the executable
   *  makes one `joinAll` call PER LOOP FRAME.  The degenerate arms below may only collapse the upper
   *  endpoint under `single`: the frame count is `Σ K_d`, a MAX over each level's distinct prefixes,
   *  so multiplying a per-call cost by it is the may/must confusion traps.md lesson 9 is about. */
  def collectJoin(groups: Sym, groupsLo: Sym, body: Meas, single: Boolean = true): CostInterval =
    collect(groups, body)
  /** one fixpoint round's union + equality check, EXCLUDING the body.
   *
   *  CHARGED `R` TIMES.  Every executable's loop is now
   *  `{ round; step := body; nxt := cur ∪ step; if nxt = cur then stop else cur := nxt }` —
   *  `MORKL.scala`'s `val nxt = cur union eval(body)…; if nxt == cur then stop = true else cur = nxt`,
   *  and the same shape in `IntTrie.scala` (`ITrie.union` + `equalT`), `Trie.scala` (`Trie.union`) and
   *  `GraphExec.scala` (`ITrie.union` + `equalT`).  The union is what makes the iterated operator
   *  `X ↦ X ∪ F(X)` INFLATIONARY, which is the premise
   *  `terminating/fixpoint_is_lfp.smt2` (O1) needs on top of monotonicity — so it is UNCONDITIONAL
   *  and happens in the convergence-detecting round too.
   *
   *  IT USED TO BE `R - 1`.  The old loop kept a side accumulator and merged only in the `else`
   *  branch (`if nxt == cur then stop = true else { acc = acc union nxt; cur = nxt }`), so the merge
   *  really was skipped in the last round.  Moving the union into the iteration moved it into every
   *  round; a model that still charged `R - 1` would under-price every fixpoint by one merge.
   *  Whatever else a round does UNCONDITIONALLY belongs in [[fixRound]], also charged `R` times —
   *  the two stay separate because they scale off different `Meas`. */
  def fixStep(acc: Meas, body: Meas, rel: Rel): CostInterval
  /** THE PER-ROUND OVERHEAD OF THE LOOP ITSELF — everything a round performs whether or not it
   *  merges, and excluding both the body and the accumulating merge [[fixStep]] prices.  Charged
   *  `R` times, as `fixStep` now is; the two still may not be folded together because they scale off
   *  different `Meas` (the accumulator+iterate vs the loop's own bookkeeping).  On the
   *  graph executable the round re-runs the whole fixpoint subgraph (its `ExtractSpaceMention(rec)`
   *  slot included) on the terminating round too, while `ITrie.union` is not called at all. */
  def fixRound(acc: Meas, body: Meas): CostInterval = CostInterval.zero
  /** THE FRAME LAW FOR A REST-CHAINED ITERATOR NEST.
   *
   *  `frames = Σ_{d=1..D} K_d` loop-frame entries, `leaves = K_D` leaf invocations,
   *  `visits = Σ_{d=1..D} E_d` grouping visits — the exact identities `SpatialFacts.PrefixProfile`
   *  already computes.  This replaces the recursive product of independent per-level group maxima,
   *  which is what turned 122 counted rounds into a predicted 390,580 (and then into `inf`).
   *  `refCounted` selects the reference evaluator's `groupMap`, which regroups the whole surviving PATH
   *  set at every level rather than the distinct prefixes. */
  def chainNest(frames: Sym, leaves: Sym, visits: Sym, depth: Sym, leaf: Meas): CostInterval =
    CostInterval.upperOnly(Cost.of(work = frames, rounds = frames, touch = visits))
  /** entering one routine call: a `CallEntry`, plus a frame where the executable allocates one */
  def callFrame: CostInterval = CostInterval.exact(Cost.of(rounds = Sym.one))

  /** THE WHOLE-REGION PRICE FROM A DEMAND ANALYSIS.  `None` means this instance has
   *  no demand semantics — only `execZ` does, because only `execZ` is lazy: "a lazy fused expression
   *  does not evaluate its children independently; its outer consumer determines which cursor prefixes
   *  are ever forced", so summing local worst cases is the wrong semantics for it and only for it. */
  def demandPrice(d: DemandSummary): Option[CostInterval] = None
  /** does this instance want a demand analysis run for it at all? */
  def demandDriven: Boolean = false

// ------------------------------------------------------------------------------------------------
// 3a. THE REFERENCE EVALUATOR — `eval`, Set[PathValue]
// ------------------------------------------------------------------------------------------------

/** `eval` (MORKL.scala).  Counted events: `AstDispatch`, `PathDispatch`, `PathItemComparison`,
 *  `FreshPath`, `LoopBodyEntry`, `FixpointRound`, `CallEntry`.
 *
 *  THREE ATTRIBUTIONS FIXED HERE:
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
  def union(a: Meas, b: Meas, rel: Rel): CostInterval =
    CostInterval.exact(Cost.of(touch = a.size + b.size))                  // no PathValue allocated
  def inter(a: Meas, b: Meas, rel: Rel): CostInterval =
    CostInterval.exact(Cost.of(touch = a.size + b.size))                  // a set evaluator CANNOT skip
  def subtract(a: Meas, b: Meas, rel: Rel): CostInterval =
    CostInterval.exact(Cost.of(touch = a.size + b.size))
  def restrict(x: Meas, y: Meas, rel: Rel): CostInterval =
    // recs(x).filter(p => prefixes.exists(q => startsWith(p, q))): a NESTED scan, and every
    // startsWith compares at most min(len(x), len(y)) items.  Each comparison is COUNTED.
    CostInterval(Cost.zero,
                 Cost.of(work = x.size * y.size * tighter(x.len, y.len), touch = x.size * (Sym.one + y.size)))
  def raffine(x: Meas, y: Meas, rel: Rel): CostInterval =
    // eval rewrites `x \| y` to `Subtraction(x, Restriction(x, y))`: two SYNTHESISED nodes (hence
    // two extra dispatches) and a second full evaluation of x (see `raffinationRereadsX`).
    CostInterval(Cost.of(work = Sym.c(2)),
                 Cost.of(work = Sym.c(2) + x.size * y.size * tighter(x.len, y.len),
                         touch = x.size * (Sym.c(2) + y.size)))
  def compose(a: Meas, b: Meas, rel: Rel): CostInterval =
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
  def tailsUnion(src: Meas, forced: Boolean): CostInterval =
    CostInterval(Cost.zero, Cost.of(alloc = src.size, touch = src.size))
  def tailsInter(src: Meas, forced: Boolean): CostInterval =
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
    // and it builds the fresh accumulator path.  THE LOWER ENDPOINT IS REAL (the last
    // paragraph): the must-group count is a mandatory number of iterations, so it is charged, not erased
    // by `upperOnly`.
    CostInterval(Cost.of(work = Sym.zero, alloc = Sym.zero),
                 Cost.of(work = groups * (Sym.one + updNodes), alloc = Sym.c(2) * groups,
                         touch = groups * updLen))
  /** THE ACCUMULATE, NOT THE CONVERGENCE TEST.  `eval`'s loop is
   *  `val nxt = cur union eval(body)…; if nxt == cur then stop = true else cur = nxt` (MORKL.scala):
   *  the `Set` union is now UNCONDITIONAL and runs `R` times, exactly as the `==` does — the union is
   *  what makes the iterated operator inflationary, so it cannot be skipped in the last round.  The
   *  two terms stay separate because they measure different sets ([[fixRound]] prices the `==`). */
  def fixStep(acc: Meas, body: Meas, rel: Rel): CostInterval =
    CostInterval.exact(Cost.of(touch = acc.size + body.size))            // `acc union nxt`
  /** THE CONVERGENCE TEST, every round.  `scala.collection.immutable.Set.equals` is a size check plus
   *  `subsetOf`, i.e. at most `|nxt|` membership probes into `cur` — the same un-oracled `Set`-internal
   *  element cost [[touchNoOracle]] declares.  `upperOnly`, not `exact`: the size check answers `false`
   *  in `O(1)` whenever the cardinalities differ, so no probe is forced. */
  override def fixRound(acc: Meas, body: Meas): CostInterval =
    CostInterval.upperOnly(Cost.of(touch = body.size))
  /** the reference evaluator regroups the whole surviving PATH set at every level (`groupMap`), which
   *  is `Σ E_d` and not `Σ K_d` — the identity `PrefixProfile.groupingVisits` computes */
  override def chainNest(frames: Sym, leaves: Sym, visits: Sym, depth: Sym, leaf: Meas): CostInterval =
    val entries = Sym.c(2) * (frames + depth) + Sym.c(2)
    CostInterval(Cost.of(rounds = Sym.zero),
                 Cost.of(work = entries, alloc = Sym.c(2) * visits + entries, rounds = frames,
                         touch = visits + entries))

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
 *  **RANGE IS AN ORDER-STATISTIC SLICE, AND ITS COST IS A SUM.**  Two earlier revisions of this
 *  paragraph were wrong about the implementation and are worth recording so the model is not
 *  "corrected" back: the first claimed "ordered walk, NO SORT"; the second claimed `ITrie.range`
 *  "computes the recursive `t.size` BEFORE the identity check, so even a full-window `Range` walks
 *  every node" and "sorts each visited node's child keys" as if both were unavoidable.  Against
 *  `IntTrie.scala`'s `range`/`slice`/`ordered` as they stand:
 *
 *   - the terminal count is MEMOISED PER NODE OBJECT (`ITrie.szc`) and recursive, so on a warm
 *     operand `count` is `O(1)` and a full window returns its operand BY POINTER after one visit
 *     ([[Meas.countKnown]] is the channel that decides which price applies);
 *   - the canonical child order is memoised per node object too (`IntTrie.ordered`), and — the point
 *     the old model missed — it emits NO counted event at all, so its `k log k` has no oracle and
 *     must not sit inside `touch`, which is DEFINED as `TrieNodeVisit + PatriciaVisit`.  It is
 *     declared as an assumption on the report instead of charged;
 *   - and the slice is `O(depth + window)`, NOT `O(depth · window)`.  At any node the window is one
 *     contiguous index block and the children occupy contiguous DISJOINT blocks, so at most TWO
 *     children (the one containing `lo` and the one containing `hi-1`) can be partial.  Every other
 *     overlapping child satisfies `lo-base <= 0 && hi-base >= c.count` and is returned by pointer
 *     after exactly one visit, and `firstAfter`'s binary search means the children entirely before
 *     the window are never looked at.  The recursion is therefore at most TWO root-to-leaf chains.
 *
 *  `slice` also uses plain `IntMap.apply`/`updated` rather than the instrumented `IntTrieOps`, so it
 *  emits ZERO `PatriciaVisit` and the [[tPer]] multiplier — which exists because MERGES do run the
 *  instrumented ops — does not apply to this operator. */
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
  /** counted `touch` of ONE two-operand merge over operands of `a` and `b` logical nodes — THE COARSE
   *  CEILING, now used only where no frontier summary exists */
  protected def merge2(a: Sym, b: Sym): Sym = tPer * (a + b)

  // ---- THE FRONTIER BRIDGE --------------------------------------------------
  /** does this instance price the algebra WITH the `AlgebraicResult` identity cases?
   *
   *  `ITrie`'s ring operations now return `ITrie.AlgebraicResult`, so `evalI` and `execT` both accept
   *  and reject whole subtries by pointer and propagate `Identity` to the root.  A DIAGNOSTIC instance
   *  can set this to `false` to price the same executable as if it had no identity case — which is what
   *  makes the slope difference visible as a number instead of a claim. */
  protected def caseReturning: Boolean = true

  private def numHi(i: Ivl): Sym = if i.hi >= Ivl.INF then Sym.Inf else Sym.c(i.hi)

  /** THE PRICE OF ONE RING OPERATION FROM ITS FRONTIER SUMMARY.
   *
   *  `alloc` is the summary's `rebuilt` — `|A|` for the pruned ops, `|Q|` for the merges, and ZERO
   *  whenever the case set proves an identity, which is the whole-subtree case `min(N(a), N(b))` cannot
   *  express.  `touch` is the summary's `descents` AND NOTHING ELSE: `FrontierSummary.descents` IS
   *  `|Q| + J` — the counted `TrieNodeVisit`s are the per-node algebra entries (`Θ(|Q|)`) and the counted
   *  `PatriciaVisit`s are `J` — so the `descents + patricia` this used to charge added `J` A SECOND TIME
   *  and doubled every frontier-driven `touch` upper endpoint.  `patricia` stays on the summary as the
   *  named component of that sum (it is what the report and the census show), not as an addend.  Both
   *  are met (`Sym.tighter`) against the coarse ceiling, so the answer is never WORSE than the size-only
   *  bound was and is asymptotically better exactly where the frontier is smaller — restriction by a
   *  length-`d` prefix, a disjoint intersection, an absorbed union.
   *
   *  With no summary at all the coarse ceiling is used and the census records it. */
  /** CAN THE TWO OPERANDS FAIL TO BE THE SAME OBJECT?
   *
   *  Every ring operation tests `a eq b` at the top and returns without descending, so a must-descent
   *  claim is only sound when that test cannot succeed.  Cardinality settles it without any sharing
   *  analysis: if one operand's PROVEN minimum size exceeds the other's maximum, they are different
   *  sets, hence different objects.  Conservative by construction — `false` simply means no must-paired
   *  count is claimed. */
  protected def provablyDifferent(a: Meas, b: Meas): Boolean =
    def gt(x: Sym, y: Sym): Boolean = (x, y) match
      case (Sym.Const(m), Sym.Const(n)) => m > n
      case _ => false
    gt(a.sizeLo, b.size) || gt(b.sizeLo, a.size)

  /** THE PRECONDITION FOR CLAIMING THE MUST-PAIRED COUNT on a symmetric merge: neither operand can be
   *  empty (the `isEmpty` fast paths return without descending) and the two cannot be the same object
   *  (the `a eq b` fast path does the same).  Only the three symmetric merges use it — `restriction`
   *  and `raffination` also short-circuit on `ε ∈ right`, and `composition` on `{ε}` on either side, so
   *  their must side needs those cases discharged too and is left unclaimed.
   *
   *  IT IS ONLY HALF THE PRECONDITION.  This settles the ROOT `a eq b`; the RECURSIVE ones — one per
   *  level in `unionR`/`intersectionR`/`…`, and one per level on the whole child map in
   *  `unionTries`/`intersectTries`/`diffTries`/`raffTries` — are settled by `Rel.mayShare`, which
   *  [[priced]] conjoins.  Neither implies the other: two operands of provably different CARDINALITY
   *  can still be built out of the same object (`a ∪ (a <| {h0})`). */
  protected def mustDescend(a: Meas, b: Meas): Boolean =
    a.provablyNonEmpty && b.provablyNonEmpty && provablyDifferent(a, b)

  /** RESTRICTION AND RAFFINATION have one whole-skip path the symmetric merges do not: `ε ∈ right`.
   *  `restrictionR` returns `Identity(LEFT)` and `raffinationR` returns `Empty` on `prefixes.terminal`,
   *  both without descending, because ε prefixes everything.  `Meas.epsAbsent` is the shape's MUST fact
   *  that discharges it. */
  protected def mustDescendPrefixed(x: Meas, p: Meas): Boolean = mustDescend(x, p) && p.epsAbsent

  /** COMPOSITION's whole-skip paths are `{ε}` on either side (`a·{ε} == a`, `{ε}·b == b`) and an empty
   *  operand.  It has no `a eq b` test, so no distinctness is needed — only that neither side can BE
   *  `{ε}`, which either `epsAbsent` or a proven size of at least two settles. */
  protected def mustDescendComposed(a: Meas, b: Meas): Boolean =
    def notEpsOnly(m: Meas): Boolean = m.epsAbsent || (m.sizeLo match
      case Sym.Const(n) => n >= 2L
      case _ => false)
    a.provablyNonEmpty && b.provablyNonEmpty && notEpsOnly(a) && notEpsOnly(b)

  /** the stronger of two sound LOWER bounds */
  private def stronger(x: Sym, y: Sym): Sym = if Sym.dominates(x, y) then x else y

  /** THE FORCED ALGEBRA ENTRY of a binary operation.  `evalI` is eager and always calls the operation,
   *  so for it this is one visit unconditionally.  `execT` is not: `GraphExec.scala` guards
   *  `Intersection`/`Subtraction`/`Restriction`/`Raffination`/`Composition`/`Wrap`/`Unwrap` with
   *  `if a.isEmpty then ITrie.empty` — on the LEFT operand only — and guards `Union` not at all.  So on
   *  the graph backend the entry is forced exactly when the left operand cannot be empty, which is a
   *  fact the shape domain supplies, and always for a union. */
  protected def forcedEntry(a: Meas, leftGuarded: Boolean): Sym = entryVisit

  /** THE FORCED ENTRY OF A UNARY OPERATION.  `execT`'s guards are per-operator and reading
   *  `GraphExec.scala` is the only way to know which: `Wrap` and `Unwrap` are guarded on their SOURCE
   *  (`if a.isEmpty then ITrie.empty`), while `TailsUnion`, `TailsIntersection` and `Range` call the
   *  `ITrie` operation with NO guard at all — so for those three the entry is forced on `execT` exactly
   *  as it is on `evalI`.  `guarded = false` says so. */
  protected def forcedUnary(src: Meas, guarded: Boolean): Sym = entryVisit

  protected def priced(rel: Rel, a: Meas, b: Meas,
                       coarseTouch: => Sym, coarseAlloc: => Sym,
                       mustDescend: Boolean = false,
                       leftGuarded: Boolean = true,
                       /** an operator-specific `touch` FLOOR the generic paired-frontier one cannot
                        *  express — see [[compose]], whose recursion enters every node of its LEFT
                        *  operand and not only the paired keys.  Joined with, never substituted for,
                        *  the generic floor, and only where the caller's `mustDescend` holds. */
                       extraTouchLo: Sym = Sym.zero,
                       /** an operator-specific `alloc` FLOOR.  THE FRONTIER HAS NO SUCH ENDPOINT AND
                        *  MAY NEVER BE READ FOR ONE — see the `rebuilt.lo` note below, refuted on
                        *  eight programs — so an `alloc` must-count has to come from the OPERATOR'S
                        *  OWN source, from a count no fast path of that operator can skip, and it is
                        *  claimed only under the caller's `mustDescend` certificate.  [[compose]] is
                        *  the one caller: `compositionR` reaches `ITrie.node` at every node of its
                        *  left operand that has a child. */
                       extraAllocLo: Sym = Sym.zero): CostInterval =
    rel.frontier match
      case None =>
        val e = forcedEntry(a, leftGuarded)
        CostInterval(Cost.of(work = opEntry, alloc = extraAllocLo,
                             touch = if e == Sym.zero then e else stronger(e, extraTouchLo)),
                     mk(work = opEntry, nodes = coarseAlloc, touch = coarseTouch))
      case Some(f) =>
        val fs = f.syms(nd(a), nd(b), coarseTouch)
        // an interned node is still built at the root even when the CASE is an identity, unless the
        // algebra can hand the argument object back — which is exactly what `caseReturning` says
        val rebuiltHi =
          if fs.fallback then coarseAlloc
          // NO `Identity` TO RETURN: the counterfactual instance rebuilds its WHOLE frontier — `|A|` for a
          // pruned op, `|Q|` for a merge — where the case-returning algebra hands the argument object back
          // and allocates nothing.  That difference is `|A|` against `0`, a slope and not a constant.
          else if f.identity && !caseReturning then
            Sym.tighter(coarseAlloc,
                        numHi(if f.op.prunes then f.depth.activeTotal else f.depth.pairedTotal) + Sym.one)
          else Sym.tighter(fs.rebuilt + Sym.one, coarseAlloc)
        val touchHi = if fs.fallback then coarseTouch else Sym.tighter(fs.descents, coarseTouch)
        // ONE NODE OF SLACK ON THE FRONTIER'S ALLOCATION BOUND — a CONSTANT, deliberately, and measured
        // into existence.  `rebuilt = 0` from a decided case (`Empty`, or an identity) says the operation
        // reuses an argument or the shared `ITrie.empty`, and that is what the executor does at the node
        // the decision was made at; the corpus calibration nevertheless found three programs where the
        // summed prediction sat just below the counted `FreshTrieNode` total (`trie alloc actual=3 in
        // [0,0]`), so one root node per decided operation is charged rather than assumed away.  It changes
        // no slope: the slope tests in `SpatialPipelineCheck` still see a flat predicted allocation.
        // NO POSITIVE LOWER ENDPOINT ON `alloc` IS CLAIMED FROM THE FRONTIER.  `rebuilt.lo` reads like a
        // must-rebuild count, and it was tried as one: the corpus calibration refuted it on eight programs
        // (`trie alloc actual=8 in [14, 16]`), because a merge can return a whole subtrie by pointer at a
        // level the frontier counts as rebuilt.  A lower endpoint has to be sound before it can be useful.
        //
        // THE `touch` LOWER ENDPOINT, HOWEVER, IS REAL, and its absence was the single cause of every
        // WIDTH failure in `SpatialCostCheck`'s per-operator table (62 of 62, all of them `width`).  Two
        // parts, both derived and neither measured:
        //
        //  1. ONE VISIT IS UNCONDITIONAL.  `unionR`/`intersectionR`/`subtractionR`/`restrictionR`/
        //     `raffinationR`/`compositionR` each emit their `TrieNodeVisit` as the FIRST statement, before
        //     `a eq b`, before the empty tests, before everything (IntTrie.scala).  No data distribution
        //     and no fast path can avoid it.
        //  2. THE MUST-PAIRED COUNT, when the caller certifies that the whole-skip fast paths cannot
        //     fire (`mustDescend`).  `FrontierSummary.descents.lo` is the number of prefixes present in
        //     BOTH operands; the merge enters the algebra once per such key, and the entry hook again
        //     precedes every test inside.  It is claimed ONLY under `mustDescend` because the frontier
        //     reasons about SETS: it cannot see that two operands are the same OBJECT, and `a eq b`
        //     returns at the top having descended nothing.
        //
        //     AND `mustDescend` ALONE IS NOT THAT SIDE CONDITION.  It is
        //     `provablyNonEmpty ∧ provablyNonEmpty ∧ provablyDifferent`, and `provablyDifferent` is a
        //     pure CARDINALITY test: it discharges the ROOT `a eq b` and says nothing whatever about
        //     the RECURSIVE ones, of which IntTrie.scala has one per level (`unionR`'s own `a eq b`,
        //     reached through `mergeUnion`) and IntTrieOps.scala one more per level on the whole child
        //     MAP (`unionTries`' `if a eq b then a`).  ONE pointer-shared subtree at a paired prefix
        //     therefore skips EVERY paired prefix beneath it while this floor is charged for all of
        //     them, and it is reachable on two bare mentions: `S"a" ∪ (S"a" <| {h0})` on the 64-path
        //     fixture counts a `touch` of 6 against a claimed floor of 11 — OUTSIDE its own interval,
        //     on both trie-shaped executables.  [[Shares]] is the MAY over-approximation that closes
        //     it and `rel.mayShare` is its answer: the count is claimed only when the two operands
        //     provably share no `ITrie` node object.  It costs nothing on the ordinary case — two
        //     distinct declared inputs have disjoint bases — which is what keeps `union`,
        //     `intersection`, `subtraction`, `restriction` and `raffination` at their widths.
        val mustPaired = mustDescend && !rel.mayShare
        val entry = forcedEntry(a, leftGuarded)
        val touchLo0 =
          if fs.fallback then entry
          else if mustPaired && entry != Sym.zero then stronger(Sym.one, fs.descentsLo)
          else entry
        val touchLo = if entry == Sym.zero then touchLo0 else stronger(touchLo0, extraTouchLo)
        CostInterval(Cost.of(work = opEntry, alloc = extraAllocLo, touch = touchLo),
                     Cost.of(work = opEntry, alloc = rebuiltHi, touch = touchHi))

  protected def mk(work: Sym = Sym.zero, nodes: Sym = Sym.zero, touch: Sym = Sym.zero): Cost =
    Cost.of(work = work, alloc = nodes, touch = touch)
  /** THE GENERIC LOWER ENDPOINT OF ONE OPERATOR OF THIS ALGEBRA: its own op entry, no allocation.
   *
   *  `CostInterval.upper` cannot be used here: it hard-codes a lower endpoint of ONE work unit, which
   *  is right for `execT` (every space slot emits a `TrieOpEntry`) and WRONG for `evalI`, whose
   *  [[opEntry]] is 0 because its single per-node `TrieDispatch` is already charged by [[dispatch]].
   *  With the hard-coded 1 the trie model's lower endpoint EXCEEDED its own upper endpoint on every
   *  program with a set operation — the corpus calibration caught it as 213 inverted intervals. */
  /** IS THE ALGEBRA ENTRY FORCED?  `evalI` is eager: `ITrie.union(evalI(a), evalI(b))` calls the
   *  operation unconditionally, and every operation emits its `TrieNodeVisit` as its first statement,
   *  before `a eq b` and before the empty tests.  So for `evalI` one visit per algebra node cannot be
   *  avoided by any data distribution, and that is the lower endpoint the WIDTH requirement needs.
   *
   *  `execT` is NOT eager in this respect: it guards every space slot with `if a.isEmpty then empty` and
   *  never calls the operation, so nothing is forced there — [[GraphCost]] overrides this to zero.  The
   *  corpus calibration is what settled the difference: with the entry claimed for both, `execT` came in
   *  BELOW the lower endpoint on six programs (`graph Touch actual=4 in [7, 23]`). */
  protected def entryVisit: Sym = Sym.one

  protected def up(hi: Cost): CostInterval =
    CostInterval(Cost.of(work = opEntry, touch = entryVisit), hi)
  /** the same with NO forced visit — for the operators whose `ITrie` entry can be skipped entirely */
  protected def upNoVisit(hi: Cost): CostInterval = CostInterval(Cost.of(work = opEntry), hi)
  /** an `ITrie` op whose FIRST operand is provably empty returns `ITrie.empty` immediately */
  protected def emptyFast: CostInterval =
    CostInterval(Cost.of(work = opEntry, touch = entryVisit), Cost.of(work = opEntry, touch = Sym.one))
  /** a pointer-identity short circuit */
  protected def sharedFast: CostInterval =
    CostInterval(Cost.of(work = opEntry, touch = entryVisit), Cost.of(work = opEntry, touch = Sym.one))
  override def empty: CostInterval = CostInterval.exact(Cost.of(work = opEntry))
  /** `pathItemsI` dispatches on EVERY Path subterm, `Deref` included, and counts
   *  [[EffortEvent.TriePathDispatch]] for each */
  override def pathTerm(nodes: Sym, slots: Sym): CostInterval = CostInterval.exact(Cost.of(work = nodes))

  def literal(m: Meas): CostInterval = phase match
    // iLiteral / iLiteralStr are memo caches: a warm Literal is a map lookup, NOT |v| insertions — and
    // a lookup emits NO `TrieNodeVisit` at all (`iLiteral` never enters the algebra), so the lower
    // endpoint here is ZERO.  It read `exact(touch = 1)`, which was an unsound lower endpoint hidden by
    // the blanket `withoutTouchLower`; removing that blanket is what exposed it.
    case ExecutionPhase.Warm => CostInterval(mk(work = opEntry), mk(work = opEntry, touch = Sym.one))
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
  def union(a: Meas, b: Meas, rel: Rel): CostInterval =
    if rel.same then sharedFast
    else if a.provablyEmpty || b.provablyEmpty then emptyFast          // `if a.isEmpty then b`
    else priced(rel, a, b, merge2(nd(a), nd(b)), tighter(nd(a), nd(b)), mustDescend(a, b),
                leftGuarded = false)
  def inter(a: Meas, b: Meas, rel: Rel): CostInterval =
    if rel.same then sharedFast
    else if a.provablyEmpty || b.provablyEmpty then emptyFast
    // HEAD-DISJOINT (SpatialCost.headDisjoint): `intersectTries` finds no matching key and returns
    // `Nil` at once, so the only allocation is the root node `ITrie(false, Nil)` and the only descent is
    // the top-level Patricia comparison of the two head sets.  An empty RESULT buys nothing — the
    // calibration proved that (12 counted fresh nodes against a predicted 1).
    else if rel.disjoint && !rel.derived then
      CostInterval(Cost.of(work = opEntry),
                   Cost.of(work = opEntry, alloc = Sym.one, touch = Sym.one + merge2(a.heads, b.heads)))
    else priced(rel, a, b, merge2(nd(a), nd(b)), tighter(nd(a), nd(b)), mustDescend(a, b))
  def subtract(a: Meas, b: Meas, rel: Rel): CostInterval =
    if rel.same then sharedFast                                        // `a eq b` ⇒ empty
    else if a.provablyEmpty || b.provablyEmpty then emptyFast
    else if rel.disjoint && !rel.derived then
      CostInterval(Cost.of(work = opEntry),
                   Cost.of(work = opEntry, alloc = Sym.one, touch = Sym.one + merge2(a.heads, b.heads)))
    else priced(rel, a, b, merge2(nd(a), nd(b)), tighter(nd(a), nd(b)), mustDescend(a, b))
  /** RESTRICTION IS THE CENTRAL CASE the review opens with.  The frontier is `Q(X,P)` pruned at
   *  terminal right prefixes, so restriction by `{ε}` is constant with zero allocation and restriction
   *  by one present prefix of length `d` is `Θ(d)` with a `d`-node spine, INDEPENDENT of the millions of
   *  nodes below the matched prefix.  The old `min(N(X),N(P))` allocation and `N(X)+N(P)` touch is the
   *  fallback only. */
  def restrict(x: Meas, y: Meas, rel: Rel): CostInterval =
    if x.provablyEmpty || y.provablyEmpty then emptyFast
    else priced(rel, x, y, merge2(nd(x), nd(y)), tighter(nd(x), nd(y)), mustDescendPrefixed(x, y))
  def raffine(x: Meas, y: Meas, rel: Rel): CostInterval =
    // `ITrie.raffination` is now the FUSED one-pass algorithm: one
    // traversal of the pruned frontier, not a restriction followed by a subtraction.  With a frontier
    // summary that IS the price; without one the two-pass ceiling stands.
    if x.provablyEmpty then emptyFast
    else priced(rel, x, y,
                Sym.c(2) + tPer * (Sym.c(3) * nd(x) + nd(y)),
                nd(x) + tighter(nd(x), nd(y)),
                mustDescendPrefixed(x, y))
  def compose(a: Meas, b: Meas, rel: Rel): CostInterval =
    // one recursive entry (and one fresh node) per node of `a`, then — at every NON-LEAF TERMINAL of `a`
    // — a `union(mapped, b)`; a LEAF terminal grafts `b` by pointer and costs nothing, which is why
    // `{ε}·B` is constant-time and a single depth-`d` path composes in `Θ(d)`.  The summary computes the
    // non-leaf graft count; the coarse ceiling below assumes every terminal is a graft.
    if a.provablyEmpty || b.provablyEmpty then emptyFast
    else
      // THE MUST SIDE IS `N(a)`, NOT THE PAIRED FRONTIER.  `compositionR` recurses through
      // `a.children.transform`, i.e. into EVERY child of `a` and not only into keys `b` also has, and
      // every entry emits its `TrieNodeVisit` as its first statement.  So once the two whole-skip
      // identities are excluded (`b = {ε}` returns `a`, `a = {ε}` returns `b`, both in one visit —
      // exactly `mustDescendComposed`), the run visits each of `a`'s nodes exactly once.  `priced`'s
      // generic must is `descentsLo`, the PAIRED count, which is the right quantity for a merge and
      // strictly too weak here.  Read off the counted oracle: `a` with 73 nodes composes with a
      // 21-node `b` for a measured `touch` of exactly 73.
      priced(rel, a, b,
             nd(a) + tPer * (nd(a) * a.len + a.size * (a.len + Sym.one) * nd(b)),
             nd(a) + a.size * nd(b),
             mustDescendComposed(a, b),
             extraTouchLo = if mustDescendComposed(a, b) then a.nodesFloor else Sym.zero,
             // AND THE `alloc` FLOOR IS `I(a)`, THE NODES OF `a` THAT HAVE A CHILD — not `N(a)`.
             // Under `mustDescendComposed` neither `{ε}` identity and neither empty test can fire at
             // ANY node of the recursion (`b` is the same object throughout, and a child of a
             // well-formed trie is non-empty), so the only branch a node of `a` can take is decided by
             // its OWN shape: `a.terminal && a.children.isEmpty` — a LEAF — returns `rIdent(RIGHT)`
             // and grafts `b` by pointer with no allocation, and every other node falls into
             // `node(false, a.children.transform(...))`, whose `ITrie.node` emits its
             // `EffortEvent.FreshTrieNode` before it builds anything.  `a.children.transform` enters
             // EVERY child, so the recursion reaches every node of `a` and the count is exact up to
             // the extra `union(mapped, b)` at a terminal WITH children, which only adds.
             //   Read off the counted oracle: `a` = 64 paths over 8 heads at depth 2 has 73 nodes, 64
             // of them leaves, and composing it with a 21-node `b` allocates exactly 9 — which is
             // `73 - 64`, and which `a.nodesFloor` (73) would have OVERSHOT.  That is the whole reason
             // this is a separate `SpatialFacts` fact and not another read of `trieNodes`.
             extraAllocLo = if mustDescendComposed(a, b) then a.interiorFloor else Sym.zero)
  def wrap(src: Meas, plen: Sym): CostInterval =
    // NOT exact: `ITrie.wrap` returns `empty` and allocates NOTHING when the source turns out empty at
    // run time, which the shape domain need not have proved.  But when it HAS proved the source
    // non-empty, the fold runs and allocates exactly one node per prefix item — the FIRST must-allocate
    // count in this model, and an exact one, because `wrap` has no other allocation and no fast path
    // between the emptiness test and the fold.  `plen` must be a VALUE and not a bound for that: a
    // `Deref` whose declared length is an upper bound would over-claim.
    if src.provablyEmpty then emptyFast
    else
      val mustAlloc = if src.provablyNonEmpty && exactLen(plen) then plen else Sym.zero
      CostInterval(Cost.of(work = opEntry, alloc = mustAlloc, touch = forcedUnary(src, guarded = true)),
                   mk(work = opEntry, nodes = plen, touch = Sym.one))
  def unwrap(src: Meas, plen: Sym): CostInterval =
    if src.provablyEmpty then emptyFast                                // focus, no rebuild
    // NOT `exact`: `ITrie.unwrap` stops at the first ABSENT item (`children.get(h)` is `None` ⇒
    // `empty`), so a missing prefix costs ONE visit and not `1 + |p|`.  The old `exact` claimed the
    // full spine as a lower endpoint too — unsound, and hidden by the blanket `withoutTouchLower`.
    else CostInterval(Cost.of(work = opEntry, touch = forcedUnary(src, guarded = true)),
                      Cost.of(work = opEntry, touch = Sym.one + plen))
  /** `ITrie.tailsUnion` is now `joinAll` — ONE simultaneous n-ary pass (the review third
   *  bullet), so the `log k` merge depth of the balanced pairwise fold is gone, and ZERO or ONE head is
   *  an identity that returns the child subtrie by pointer without touching it.
   *
   *  THE OPERAND LOOPS ARE PRICED (the first P0).  `joinAll` over the `heads` child subtries runs
   *  `O(k)` loops per recursive call that emit no `touch` event at all, so `work` and `alloc` carry
   *  [[naryProbes]] and [[naryScratch]] now that those loops have an oracle
   *  ([[EffortEvent.NaryOperandProbe]], [[EffortEvent.NaryScratchSlot]]).  Their absence was not
   *  conservatism, it was an unsound `work` upper bound: the corpus calibration put the counted total
   *  ABOVE the prediction on 107 of 3000 points the moment the events were counted. */
  def tailsUnion(src: Meas, forced: Boolean): CostInterval =
    // `forced` IS IGNORED HERE ON PURPOSE: `evalI`/`execT` are eager — `IntTrie.scala`'s
    // `case Space.TailsUnion(src) => ITrie.tailsUnion(evalI(src))` calls the operation whatever the
    // consumer does — so this model's must side never needed the flag.
    if atMostOneHead(src) then CostInterval.exact(Cost.of(work = opEntry, touch = Sym.one))
    else CostInterval(Cost.of(work = opEntry + tailsJoinProbesLo(src), alloc = tailsScratchLo(src),
                              touch = tailsForced(src)),
                      mk(work = opEntry + naryProbes(src.heads, nd(src)),
                         nodes = nd(src) + naryScratch(src.heads, nd(src)),
                         touch = Sym.one + tPer * nd(src)))
  /** `ITrie.tailsIntersection` is now `meetAll`, whose work is controlled by the SMALLEST branch and
   *  which abandons a key on the first input that lacks it.  The
   *  zero/one-head identities are explicit and cost one visit. */
  def tailsInter(src: Meas, forced: Boolean): CostInterval =        // `forced` ignored: eager, as above
    if atMostOneHead(src) then CostInterval.exact(Cost.of(work = opEntry, touch = Sym.one))
    // THE `heads` FACTOR IS GONE, and it was not a measurement that removed it.  `ITrie.meetAll`'s
    // children step is now `IntTrieOps.meetAllTries`, a simultaneous descent whose frontier lies inside
    // the SMALLEST child: a key survives only if every child has it.  Write `h = heads` and let the
    // children hold `n_1 .. n_h` nodes with `nd(src) = 1 + Σ n_i`; then `n_min ≤ (nd(src) - 1)/h`
    // because the minimum is at most the mean, and each entered node costs `O(h)` (one step per live
    // operand).  So the product is `n_min · h ≤ nd(src) - 1` and the `h` cancels — the same bound the
    // n-ary JOIN carries.  The previous `tPer · heads · nd(src)` priced the per-key probe loop that
    // `meetAllTries` replaced, and kept charging for it after the loop was gone.
    //
    // THE CANCELLATION IS VALID FOR `touch` AND IT IS NOT A `work` BOUND (the first P0, last
    // paragraph).  "Each entered node costs `O(h)`" is a statement about the OPERAND LOOPS, not about
    // the counted `touch` events — a `meetAllTries` call emits ONE `PatriciaVisit` however many operands
    // are live in it — so the `n_min · h <= nd(src) - 1` cancellation bounds the DESCENT and always did.
    // The operand loops it describes are the `work` the review says the formula could understate by a
    // factor proportional to arity; they are now counted as `NaryOperandProbe` and charged below by
    // `naryProbes`, whose `min(k, 24)` factor is sound only because `collectLive`'s dedup is
    // expected-`O(k)` per call.  With the previous `Θ(k²)` scan the per-operand factor would have been
    // `k`, i.e. exactly the missing arity factor.
    else CostInterval(Cost.of(work = opEntry + tailsProbesLo(src), alloc = tailsScratchLo(src),
                              touch = tailsForced(src)),
                      mk(work = opEntry + naryPreScan(src.heads) + naryProbes(src.heads, nd(src)),
                         nodes = nd(src) + naryScratch(src.heads, nd(src)),
                         touch = Sym.one + tPer * nd(src)))
  /** RANGE.  The ORDER-STATISTIC SLICE changed two of the three terms:
   *  the child-key order is memoised per node and the window test reads a CACHED terminal count, so a
   *  partial window rebuilds only the two cut frontiers plus genuinely partial nodes — `(w + 2)·(len+1)`
   *  instead of `w²·len` — and a full window returns the operand by pointer.
   *
   *  THE COUNT WALK IS NOW A FUNCTION OF THE OPERAND'S CACHE STATE, not a constant of the operator.
   *  `ITrie.count` caches the terminal count PER NODE OBJECT and the pass that computes it walks,
   *  emitting one `TrieNodeVisit` per node — which is exactly what happens on the fresh trie a
   *  subexpression just produced.  So the walk `N(x)` is charged when `x` is `CountUnknown`, and NOT
   *  charged when [[Meas.countKnown]] proves every node of `x` already answers in `O(1)`.  What this
   *  model used to say — "this model does not know which query it is pricing" — was a missing channel,
   *  not an unknowable fact: see `Meas.countKnown` for what makes the state derivable from the annotated
   *  types.  A `Warm` full-window query on a DECLARED INPUT is `O(1)`; the same query on a freshly built
   *  subexpression, and every `Cold` query, still pays the walk — which is what `SpatialEventsCheck`'s
   *  "FIX 3" and "IDENTITY REGRESSION" tests protect (both use a `Literal`, never a declared input).
   *
   *  THE ORDERING MEMO IS THE SAME KIND OF STATE AND IS NO LONGER CHARGED TO `touch` AT ALL — not
   *  because it is free, but because it has NO ORACLE.  `IntTrie.ordered`'s `sortBy` emits no
   *  [[EffortEvent]], and `touch` is contractually defined by `TrieNodeVisit + PatriciaVisit`, so a
   *  `heads·log(heads)` term inside it charges work that no counted run can ever confirm or refute —
   *  it was pure, unmeasurable slack (and the dominant term in `range-part`'s interval width).  The
   *  term moves to a DECLARED ASSUMPTION on the report, exactly as [[CostModel.touchNoOracle]]
   *  declares the reference backend's `Set` internals, rather than being silently deleted.
   *
   *  ==THE SHAPE OF THE BOUND==
   *  `slice` is an order-statistic descent.  Per node the window is ONE contiguous index block and
   *  the children occupy contiguous disjoint blocks, so at most the child containing `lo` and the
   *  child containing `hi-1` are PARTIAL; every other overlapping child is whole and is returned by
   *  pointer after one visit, and `firstAfter` binary-searches past the children before the window.
   *  Hence, with `L = x.len` and `w = min(window, |x|)`:
   *
   *    visits   <= 1                          (`range`'s own entry)
   *              + 2·(L+1)                    (the two cut chains, one visit at each spine node)
   *              + w                          (whole children: disjoint, each holds >=1 in-window
   *                                            terminal, one visit each)
   *    rebuilt  <= 2·(L+1) + 1                (only the spine nodes call `node(term, ch)`)
   *
   *  A SUM, not the product `(w+2)·(L+1)` the predecessor charged for BOTH `nodes` and (times `tPer`)
   *  `touch`.  Both are additionally met against `nd(x)`, which no walk can exceed. */
  def range(x: Meas, window: Sym, identity: Boolean): CostInterval =
    val w = tighter(window, x.size)
    val countWalk = if x.countKnown then Sym.zero else nd(x)
    // `ITrie.range` is entered UNCONDITIONALLY on every executable that runs this algebra: `evalI` is
    // eager and `GraphExec` has no empty guard for `Range` at all — which `forcedUnary` already knows
    // and `entryVisit` (0 on the graph backend) threw away.
    val forced = forcedUnary(x, guarded = false)
    if identity then CostInterval(Cost.of(work = opEntry, touch = forced),
                                  Cost.of(work = opEntry, touch = Sym.one + countWalk))
    else
      val spine = Sym.c(2) * (x.len + Sym.one)
      val rebuilt = tighter(spine + Sym.one, nd(x))
      val visits = tighter(Sym.one + spine + w, nd(x))
      CostInterval(Cost.of(work = opEntry, touch = forced),
                   mk(work = opEntry, nodes = rebuilt, touch = countWalk + visits))
  /** THE HEAD CHILDREN ARE THE GROUPS: `evalI`'s `Iteration` iterates `t.children` and emits NO
   *  `TrieNodeVisit` for the split at all.  `heads` is a model of the iterator's per-child work and is
   *  sound as an UPPER endpoint; as a lower endpoint it claimed visits that never happen (the corpus
   *  calibration refuted it the moment the blanket `withoutTouchLower` stopped hiding it:
   *  `Touch actual=25 in [27, 209]` on a two-group loop, overshooting by exactly `heads`). */
  def group(src: Meas): CostInterval =
    CostInterval(Cost.of(work = opEntry), Cost.of(work = opEntry, touch = src.heads))
  /** FOLD's accumulation: an ORDERED LEFT FOLD of unions (the review says split
   *  this from `Iteration`'s n-ary join, and it is now split).  The `groups²` factor is real for a left
   *  fold, but only when the outputs genuinely overlap: an ABSORBED or DISJOINT step keeps the
   *  accumulator by pointer, which is why the lower endpoint is `groups` and not `groups²`. */
  def collect(groups: Sym, body: Meas): CostInterval =
    CostInterval(Cost.of(work = Sym.zero, touch = Sym.zero),
                 mk(work = groups * opEntry, nodes = groups * nd(body),
                    touch = Sym.one + tPer * groups * (groups + Sym.one) * nd(body)))
  /** ITERATION's accumulation: `ITrie.joinAll`, ONE simultaneous pass over all group results.  A key
   *  present in exactly one group is placed BY POINTER, so `k` disjoint groups allocate one node in
   *  total — the case the pairwise fold cannot express and the quadratic bound above cannot see.
   *
   *  The `groups` operands' own loops are priced by [[naryProbes]]/[[naryScratch]], with the total
   *  operand size `groups · nd(body)` — the same quantity the `touch` term uses. */
  /** ==============================================================================================
   *  `liveDistinct`'s BUFFER IS THE ONE `alloc` THIS LOOP CANNOT AVOID — a MUST count, and NOT the
   *  one `CostModel.naryScratchLo`'s note records as refuted.
   *
   *  `evalI`'s `case Space.Iteration` (IntTrie.scala) ends in `ITrie.joinAll(t.children.iterator.map
   *  {...}.toSeq)` — unconditionally, for every source, empty included.  `ITrie.joinAll`'s first two
   *  statements are `effort(EffortEvent.TrieNodeVisit)` and `val live = liveDistinct(ts, dropEmpty =
   *  true)`, and `liveDistinct`'s last statement before it returns is
   *  `effortN(EffortEvent.NaryScratchSlot, math.max(4L, 4L * buf.length))` — after every `return`-less
   *  arm of its loop, so no data distribution reaches the end of `joinAll` without it.  Hence
   *  `alloc >= 4` and `touch >= 1` per executed loop.
   *
   *  WHY THIS IS NOT REFUTATION #2 IN [[CostModel.naryScratchLo]]'s NOTE.  That one put the same
   *  constant in `naryScratchLo`, which the TAILS transfers also read, and
   *  [[ZipperCost.tailsUnion]] is a FUSED CURSOR REDUCE that never enters `ITrie.joinAll` at all —
   *  its counted `Alloc` on the operator table is 1 (one `FreshNode`), so a floor of 4 there is an
   *  inverted interval on its own row, which is what 4 of 200 corpus points were. The claim here is
   *  about ONE call site, `evalI`'s loop accumulation, and it is charged only by the model that
   *  prices that executable. `GraphCost` overrides this method (`GraphExec.scala`'s `case
   *  "Iteration"` accumulates with a PAIRWISE `ITrie.union` left fold and calls no n-ary op), and
   *  `naryScratchLo` itself is left at 0 so its own refutation record still stands.  So does
   *  [[ZipperCost.collectJoin]]: its own note says "the comment above about `controlFlowFallback` is
   *  not true of every route into a loop", i.e. there is a route on which the zipper model prices a
   *  loop ITSELF rather than handing it to the trie model, and this floor makes no claim about that
   *  route — that override keeps its 0.
   *
   *  THE ZIPPER INHERITS IT, AND THAT IS THE POINT OF OP-2's "conditional on WHICH BACKEND".  It is
   *  conditional in the only way that matters: `execZ` does not fuse a loop —
   *  `Zipper.scala`'s `case other => effort(ZipperFallbackToEvalI); traversal(evalI(other))` — so the
   *  events `execZ` counts for an `Iteration` subterm ARE `evalI`'s events, this buffer included.
   *  The harness confirms it on every loop fixture (`it-inter` counted `execZ` `Alloc` = 4 = exactly
   *  this buffer; `iteration` 123; `it-empty` 12).  What OP-2's note refuses is a floor derived from
   *  the GROUP COUNT (`4 · groupsLo`), which claims `live.length >= groupsLo` and is false whenever
   *  group results coincide by pointer or come back empty; `max(4, ·)`'s constant half claims nothing
   *  about `live` at all.
   *
   *  ==AND THE TWO ARMS THAT RETURN BEFORE THE SPLIT ARRAYS==
   *  `joinAll` is `if live.isEmpty then empty else if live.length == 1 then live(0) else if
   *  live.length == 2 then union(...) else <the n-ary descent>`.  Two of those are decidable here:
   *
   *   - A PROVABLY EMPTY BODY makes every operand empty, and `liveDistinct(ts, dropEmpty = true)`
   *     skips its whole probe block on an empty operand (`if !dropEmpty || t.nonEmpty`), so `pr` is 0
   *     and `live` is empty: `NaryOperandProbe` 0, `NaryScratchSlot` `max(4, 0) = 4`, one
   *     `TrieNodeVisit`, and `empty` is a shared object.
   *   - AT MOST ONE GROUP (`groups <= 1`) leaves at most one operand, so `live.length <= 1`: the
   *     first kept operand scans an EMPTY buffer (`pr += i` with `i = 0`), `NaryScratchSlot` is
   *     `max(4, 4) = 4`, and the `length == 1` arm hands `live(0)` back by pointer.
   *
   *  Both arms therefore cost EXACTLY `work 0, alloc 4, touch 1` — no split array, no maps copy, no
   *  terminal-flag scan, no result-identity search, and no `ITrie.node`.  `groups * opEntry` is kept
   *  in the upper endpoint so a subclass with a nonzero op entry cannot be under-charged. */
  override def collectJoin(groups: Sym, groupsLo: Sym, body: Meas, single: Boolean): CostInterval =
    val buffer = Cost.of(alloc = Sym.c(4), touch = entryVisit)
    if single && joinReturnsEarly(groups, body) then
      // THE `nodes` (alloc) UPPER ENDPOINT IS NOT COLLAPSED, and the reason is a MEASURED refutation
      // of the SUM rather than of this transfer.  The degenerate `joinAll` really does allocate exactly
      // the 4-slot buffer and nothing else — that part of the argument above holds — but `ZipperCost`
      // under-charges `alloc` by one at a RAFFINATION layer under a binary op (`n1 ∩ (n1 \| Lit{s})`
      // with `n1 = {"s"}` declared exactly reads zipper `Alloc` `[0, 1]` against a counted 2, out of
      // interval BEFORE this change), and the `naryScratch(1, ·) = 28` this arm would remove is the
      // slack that covered it whenever the same term also held a one-head loop.  Collapsing it turns
      // contained rows into out-of-interval ones: `c.iter(h, t, Singleton(h)) ∩ (c \| Lit{s})` over an
      // 8-path single-head `c` reads zipper `Alloc` `[4, 6]` against a counted 7.  So the exact arm
      // tightens `work` and `touch`, where the term has no deficit, and leaves `alloc` at the general
      // form until the raffination layer's own price is fixed.  The FLOOR — `liveDistinct`'s
      // unavoidable 4-slot buffer — is unaffected and stays.
      CostInterval(buffer, mk(work = groups * opEntry, touch = Sym.one,
                              nodes = Sym.one + groups * nd(body) +
                                      naryScratch(groups, groups * nd(body))))
    else
      CostInterval(buffer + Cost.of(alloc = naryScratchLo(groupsLo)),
                   mk(work = groups * opEntry + naryProbes(groups, groups * nd(body)),
                      nodes = Sym.one + groups * nd(body) + naryScratch(groups, groups * nd(body)),
                      touch = Sym.one + tPer * groups * nd(body)))

  /** does `ITrie.joinAll` provably take its `live.isEmpty` or `live.length == 1` arm? */
  private def joinReturnsEarly(groups: Sym, body: Meas): Boolean =
    body.provablyEmpty || (groups match { case Sym.Const(n) => n <= 1L; case _ => false })
  def foldStep(groups: Sym, updNodes: Sym, updLen: Sym): CostInterval =
    // per group: `pathItemsI(update)` dispatches on every update subterm; the accumulator is a
    // PathValue, so nothing is allocated in the trie
    CostInterval(Cost.zero, mk(work = groups * (opEntry + updNodes), touch = groups * updLen))
  /** ONE FIXPOINT ROUND: the union of the iterate into the accumulator, priced by the CHANGED frontier
   *  (the last table row), plus the convergence test — which is `ITrie.equalT`, whose
   *  visits are counted as `EqualityFrontierVisit` (an `Explain` event) and therefore do NOT belong in
   *  the calibrated `touch` component. */
  def fixStep(acc: Meas, body: Meas, rel: Rel): CostInterval =
    // NO FORCED VISIT PER ROUND: the round that DETECTS convergence runs `equalT` and then stops
    // without the accumulating `union`, so `R` rounds perform at most `R - 1` merges and a per-round
    // lower endpoint of one visit over-claims on every fixpoint.
    val coarseAlloc = tighter(nd(acc), nd(body))
    val alloc = childlessPairedPruned(rel) match
      case Some(r) => tighter(coarseAlloc, r + Sym.one)
      case None => coarseAlloc
    val p = priced(rel, acc, body, merge2(nd(acc), nd(body)), alloc)
    CostInterval(p.lo.copy(touch = Amount.zero), p.hi)

  /** ==============================================================================================
   *  A PAIRED PREFIX WITH NO CHILDREN ON EITHER SIDE IS NEVER REBUILT BY THE ACCUMULATING UNION.
   *
   *  `FrontierSummary.rebuilt` for a merge is the WHOLE paired frontier `|Q|` — every depth, leaves
   *  included.  Read `IntTrie.unionR` at a paired prefix `p` whose node is CHILDLESS on both sides:
   *
   *  {{{
   *    val term = a.terminal || b.terminal
   *    val ch = mergeUnion(a.children, b.children)
   *    val l = (ch eq a.children) && term == a.terminal
   *    val r = (ch eq b.children) && term == b.terminal
   *    if l then rIdent(...) else if r then rIdent(RIGHT) else rBespoke(node(term, ch))
   *  }}}
   *
   *  Both child maps are `IntMap.Nil`, which is a single object, so `a.children eq b.children` and
   *  `mergeUnion` returns it under BOTH tunings — `IntTrieOps.unionTries` by its leading `if a eq b
   *  then a`, and the `-Dmorkl.patriciaOps=false` fold because it starts from `x` and iterates an
   *  empty `y`.  And `term` is the OR of two booleans, so it equals at least one of them: `l` or `r`
   *  holds, `rBespoke(node(term, ch))` is unreachable, and `node` — the ONLY site that counts
   *  [[EffortEvent.FreshTrieNode]] (`IntTrie.scala`: `effort(FreshTrieNode); ITrie(terminal,
   *  children)`) — is never called at that prefix.  Nothing here depends on the data distribution or
   *  on which side is larger, which is why it is an upper-endpoint fact and not a measurement.
   *
   *  WHICH DEPTHS QUALIFY, WITHOUT PER-NODE INFORMATION.  `DepthFrontier.fanLeft(d)`/`fanRight(d)`
   *  bound the child-map fan-out SUMMED OVER THE ACTIVE DEPTH-`d` NODES, so `fanLeft(d).hi == 0 &&
   *  fanRight(d).hi == 0` says every depth-`d` node the merge can enter is childless on both sides —
   *  exactly the side condition above, stated for a whole level (LESSON 9: the level-wide fact is
   *  usable here because it is a MAY bound being read as "no such child exists", not a must-count
   *  being read as a floor).  The surviving depths' `|Q_d|` are summed; a depth whose fan is unknown
   *  (`Ivl.INF`) counts as fanned and keeps its whole `|Q_d|`.
   *
   *  REFUSED, NOT GUESSED, where the profile cannot support it: no frontier, a `fallback` summary, a
   *  `truncated` profile (nothing is known below its last depth) or an unbounded `|Q_d|` all return
   *  `None`, and the caller keeps the coarse `min(N(acc), N(iterate))` ceiling.
   *
   *  Applied HERE ONLY — to the fixpoint's accumulating merge, whose operand node counts are both the
   *  whole accumulated result and for which the leaf level is therefore the dominant term.  The same
   *  reading holds for `unionR` wherever it is called, and for the other symmetric merges by the same
   *  three lines; generalising it belongs with a full re-calibration of every merge row rather than
   *  with this one. */
  protected def childlessPairedPruned(rel: Rel): Option[Sym] = rel.frontier match
    // `!op.prunes` is load-bearing: the fan vectors are summed over the ACTIVE nodes, and for a
    // pruning op `active ⊆ paired`, so a zero fan would say nothing about the paired-but-accepted
    // nodes this sum still counts.  The two merges that prune are refused rather than reasoned about.
    case Some(f) if !f.op.prunes && !f.isFallback && !f.depth.truncated && f.depth.paired.nonEmpty =>
      // a fan vector shorter than `paired` says NOTHING about the missing depths, so the default is
      // "fanned" (`Ivl.INF`), which keeps that depth's `|Q_d|` — the sound direction
      def fanHi(v: Vector[Ivl], d: Int): Long = if d < v.length then v(d).hi else Ivl.INF
      var total = 0L
      var ok = true
      for d <- f.depth.paired.indices do
        val childless = fanHi(f.depth.fanLeft, d) == 0L && fanHi(f.depth.fanRight, d) == 0L
        if !childless then
          if f.depth.paired(d).hi >= Ivl.INF then ok = false else total += f.depth.paired(d).hi
      if ok then Some(Sym.c(total)) else None
    case _ => None
  /** THE FRAME LAW, on the trie executables: `Σ K_d` loop-body entries and one `joinAll` per frame.
   *  The per-frame constant of 4 covers what one ENTRY into a level really dispatches — the `Iteration`
   *  node itself, its `Mention(rest)` source and its group split — because the nest is
   *  priced in ONE transfer and its inner nodes are no longer visited individually.  A constant, not a
   *  slope: the whole point of the frame law is that `Σ K_d` replaces `Π K_d`. */
  override def chainNest(frames: Sym, leaves: Sym, visits: Sym, depth: Sym, leaf: Meas): CostInterval =
    val entries = Sym.c(2) * (frames + depth) + Sym.c(2)
    CostInterval(Cost.of(rounds = Sym.zero),
                 Cost.of(work = entries * (Sym.one + opEntry),
                         alloc = frames + depth + leaves * nd(leaf),
                         rounds = frames,
                         touch = entries + tPer * (frames + depth + leaves * nd(leaf))))

  /** TWO VISITS ARE FORCED on a multi-head source: the `tailsUnion`/`tailsIntersection` entry, and then
   *  the `joinAll`/`meetAll` entry — both hooks precede every test in their operation, including the
   *  `liveDistinct` dedup that can collapse the operand list back to one.  Only two, for that reason. */

  protected def tailsForced(src: Meas): Sym =
    val entry = forcedUnary(src, guarded = false)
    if entry == Sym.zero then Sym.zero
    else
      // …and with THREE OR MORE live operands the n-ary path is taken and its first Patricia call
      // is entered unconditionally: `IntTrie.joinAll`/`meetAll` hand the child maps to
      // `IntTrieOps.{join,meet}AllTries`, whose `enter()` — a counted `PatriciaVisit` — is its first
      // statement, before `collectLive` and before every test.  `Tuning.patriciaOps` selects that
      // implementation and this model prices THAT executable; under the `LongMap` alternative the
      // per-group `ITrie.joinAll` recursion emits its own `TrieNodeVisit` instead, so the floor holds
      // either way, but the claim is gated on the flag rather than argued across two code paths.
      val nary = if Tuning.patriciaOps && naryDeepLo(src).isDefined then Sym.one else Sym.zero
      src.headsLo match
        case Sym.Const(n) if n >= 2L => Sym.c(2) + nary
        case _ => entry

  /** is `plen` a VALUE rather than an upper bound?  A constant path length is; a `Deref`'s declared
   *  `lengthHint` is not, and claiming it as a must-allocate count would predict more allocation than
   *  the run performs. */
  protected def exactLen(plen: Sym): Boolean = plen match
    case Sym.Const(_) => true
    case _ => false

  /** a source with at most one head: the `tails*` identities fire and nothing below is touched */
  protected def atMostOneHead(m: Meas): Boolean = m.heads match
    case Sym.Const(n) => n <= 1L
    case _ => false

/** `evalI` (IntTrie.scala): one AST dispatch per node, then the trie algebra.
 *
 *  CALIBRATED.  `evalI`, `ITrie` and `IntTrieOps` now carry hooks, so this backend
 *  has counted runs for all four components: [[EffortEvent.TrieDispatch]] +
 *  [[EffortEvent.TriePathDispatch]] for `work`, [[EffortEvent.FreshTrieNode]] for `alloc`, `evalI`'s
 *  own [[EffortEvent.LoopBodyEntry]]/[[EffortEvent.FixpointRound]]/[[EffortEvent.CallEntry]] for
 *  `rounds`, and [[EffortEvent.TrieNodeVisit]] + [[EffortEvent.PatriciaVisit]] for `touch`. */
final class TrieCostModel(p: ExecutionPhase) extends TrieAlgebraCost(p):
  val backend = Backend.Trie
  /** `evalI` emits no [[EffortEvent.TrieOpEntry]]: one [[EffortEvent.TrieDispatch]] per node covers
   *  both the AST dispatch and the algebra entry, and [[dispatch]] already charges it. */
  protected def opEntry: Sym = Sym.zero

/** THE DIAGNOSTIC COUNTERFACTUAL: the SAME executable, priced as if its ring operations returned a
 *  fresh node instead of an `AlgebraicResult`.
 *
 *  This is not a backend — it names no executable of its own, and `Backends.of` never returns it — it
 *  is how the central claim becomes a NUMBER: the difference between this instance and
 *  [[TrieCostModel]] on the same term is exactly what accept-by-pointer, disjoint-reject and identity
 *  propagation buy, and on the geometric-scale generators it is a SLOPE difference (`0` rebuilt nodes
 *  against `|A|`) and not a constant factor.  Reported by `SpatialPipelineCheck`, never used to choose a
 *  backend. */
final class NaiveTrieCostModel(p: ExecutionPhase) extends TrieAlgebraCost(p):
  val backend = Backend.Trie
  protected def opEntry: Sym = Sym.zero
  override protected def caseReturning: Boolean = false
  override def name: String = s"trie-no-identity/${if phase == ExecutionPhase.Warm then "warm" else "cold"}"

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
  /** `execT` guards its space slots with `if a.isEmpty then empty`, so no visit is forced UNCONDITIONALLY
   *  on this executable — see [[TrieAlgebraCost.entryVisit]]. */
  override protected def entryVisit: Sym = Sym.zero
  /** but the guard reads the LEFT operand only, and `Union` carries none at all, so the entry IS forced
   *  whenever the shape domain proves the left operand non-empty (`GraphExec.scala`) */
  override protected def forcedEntry(a: Meas, leftGuarded: Boolean): Sym =
    if !leftGuarded || a.provablyNonEmpty then Sym.one else Sym.zero
  /** `Wrap`/`Unwrap` are guarded on the source; `TailsUnion`/`TailsIntersection`/`Range` are not guarded
   *  at all (`GraphExec.scala`), so their entry is forced on `execT` unconditionally. */
  override protected def forcedUnary(src: Meas, guarded: Boolean): Sym =
    if !guarded || src.provablyNonEmpty then Sym.one else Sym.zero
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
  override def group(src: Meas): CostInterval =
    CostInterval(Cost.zero, Cost.of(touch = src.heads))
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
  /** `execT` DOES NOT USE `joinAll` FOR A LOOP'S ACCUMULATION, and the model inherited from
   *  [[TrieAlgebraCost]] said it did.  Read `GraphExec.scala`'s `case "Iteration"`:
   *
   *  {{{
   *    var acc = ITrie.empty
   *    src.children.foreach { case (k, sub) => … ; acc = ITrie.union(acc, frame(last)) }
   *  }}}
   *
   *  — a PAIRWISE LEFT FOLD.  So this executable emits no `NaryOperandProbe` and no
   *  `NaryScratchSlot` for a loop at all, and pricing it with the n-ary transfer charged both.  The
   *  counted oracle is unambiguous: with the n-ary must-scratch inherited here, graph `Alloc`
   *  containment fell from 100% to 89% (`actual=7 in [18, 208]` on the worst point) — the model
   *  claimed forced allocations for an operation this backend never performs.
   *
   *  ==AND THE LEFT FOLD IS STILL LINEAR IN `groups`, NOT QUADRATIC==
   *  [[collect]] — the generic left-fold price — charges `groups · (groups + 1) · nd(body)` for
   *  `touch`, on the reading that step `i` merges an accumulator of `i · nd(body)` nodes.  That over-
   *  reads `ITrie.union`: its descent follows only the keys present in BOTH operands, so one merge
   *  visits at most `min(nd(acc), nd(b_i)) ≤ nd(body)` nodes however large the accumulator has grown.
   *  Summed over the fold that is `tPer · groups · nd(body)` — the same linear form the n-ary transfer
   *  had, derived from the pairwise operation this backend actually performs.  (Using `collect` here
   *  unchanged measured `iteration graph Touch` width 1954 against the n-ary model's 226, with no
   *  containment gained: the quadratic was slack, not safety.)
   *
   *  No must side: an empty source runs the fold zero times. */
  override def collectJoin(groups: Sym, groupsLo: Sym, body: Meas, single: Boolean): CostInterval =
    CostInterval.upperOnly(
      mk(work = groups * opEntry + Sym.c(5) * groups,
         nodes = groups * nd(body),
         touch = Sym.one + tPer * groups * nd(body)))
  /** THE `work` THAT WAS HERE IS PER-ROUND, NOT PER-MERGE, so it moved to [[CostModel.fixRound]].
   *  `GraphExec.scala`'s `case "Fixpoint"` calls `execT(sg, stack, index)` on EVERY round, including
   *  the one that detects convergence, and that re-execution dispatches the subgraph's
   *  `ExtractSpaceMention(rec)` slot again (one `GraphNodeDispatch` + one `TrieOpEntry`); the
   *  `ITrie.union(acc, nxt)` this transfer prices is in the `else` branch and is skipped on that
   *  round.  Charging both `R` times over-read the merge; charging both `R - 1` times would
   *  UNDER-read the slot, which is the unsound direction — hence two hooks. */
  override def fixRound(acc: Meas, body: Meas): CostInterval =
    CostInterval.upperOnly(Cost.of(work = Sym.c(4)))
  override def chainNest(frames: Sym, leaves: Sym, visits: Sym, depth: Sym, leaf: Meas): CostInterval =
    // one FRAME per loop node (reused across its children) plus the per-child prologue slots
    CostInterval.upperOnly(super.chainNest(frames, leaves, visits, depth, leaf).hi +
                           Cost.of(work = Sym.c(2) * frames, alloc = depth))

// ------------------------------------------------------------------------------------------------
// 3c. THE FUSED ZIPPER — `execZ`
// ------------------------------------------------------------------------------------------------

/** `execZ` (Zipper.scala).  Counted events: `ZipperBuild`, `ZipperCursorRead`,
 *  `ZipperMaterializeNode`, `FreshNode`, `ReusedSpace`, `ZipperFallbackToEvalI`.
 *
 *  This is the instance the review says cannot share a formula with `execT`:
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
  /** …READS, and the lift happens ONCE — see [[CostModel.raffinationSecondRead]].  `transpileZ` builds
   *  `x`'s cursor a single time and puts that one object in both slots of
   *  `Subtraction(x, restriction(x, y))`, so the second reference emits no `ZipperBuild`, no `ITrie`
   *  allocation and — the soundness bug this closes — no `ZipperFallbackToEvalI` round.  The extra
   *  cursor reads are already the `2 · fuse2(x, y, r)` in [[raffine]]; `cx.hi` is kept on top as the
   *  generous envelope, and only the LOWER endpoint changes. */
  override def raffinationSecondRead(cx: CostInterval): CostInterval = CostInterval.upperOnly(cx.hi)
  override def demandDriven: Boolean = true
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
  /** THE FUSED NODE COUNT — AND IT IS THE OPERAND ENVELOPE, NOT THE FRONTIER'S `rebuilt`.
   *
   *  This used to read `tighter(coarse, rebuilt.hi + 1)`, on the argument that "`materialize`
   *  allocates one node per FORCED cursor node, and a forced node is a rebuilt node of the underlying
   *  merge".  THE SECOND HALF IS FALSE, and `FrontierSummary.rebuilt` says so itself: it bounds the
   *  nodes of the RESULT, while `SpaceZipper.materialize` allocates one `FreshNode` per node it
   *  VISITS — the recursive descent into each child happens BEFORE the `if c.nonEmpty` filter that
   *  drops an empty subtree, so a subtree that materialises to nothing is walked, and charged, in
   *  full.  The block comment above this one already recorded exactly that failure mode ("A term whose
   *  result is empty can therefore still allocate — the corpus calibration caught exactly that (5
   *  counted `FreshNode`s against a root-result bound of 1)") and then `res` reintroduced it per
   *  operator.
   *
   *  MEASURED, five UPPER endpoints that were under the counted run and are now over it.  The sharpest
   *  is `Raffination(a, a')` with `a'` STRUCTURALLY EQUAL to the 64-path/8-head `a` but a
   *  POINTER-DISTINCT object: `SpatialFrontier.sameObject` does not fire, so the algebra descends and
   *  rebuilds, while the result is exactly empty (every path of `a` is its own prefix in `a'`, so
   *  `restriction(a, a') = a` and `a \ a = {}`) — `rebuilt.hi = 0`, the old `alloc` upper was 1, and
   *  the run counts NINE `FreshNode`s.  The others: `Raffination(a, Raffination(a, b))` `[0, 16]`
   *  against 17, `Intersection(Raffination(a, b), b)` and `Subtraction(Raffination(a, b), b)` `[0, 7]`
   *  against 13, `Raffination(Singleton("h0.t0"), b)` `[0, 1]` against 2.  None is reachable from the
   *  15000-point corpus — `zipper Alloc` reads 100% containment there — which is why the fixtures had
   *  to be built to find it.
   *
   *  THE PRICE, and it is width bought with soundness in the direction the requirement prescribes:
   *  `restriction zipper Alloc` 7.00 -> 14.00 (inside the budget tier either way) and
   *  `raffination zipper Alloc` 7.00 -> 95.00, which fails it (see the ledger entry that records it).
   *  WHAT WOULD RECOVER THE PRECISION SOUNDLY is a bound on the VISITED count rather than the result
   *  count: where the frontier proves an operand is handed back BY POINTER the cursor is a `Lit` and
   *  `materialize` allocates nothing for it, so the walk is bounded by the nodes of the OTHER operand.
   *  That is a different fact from `rebuilt` and it is not derived yet. */
  private def res(rel: Rel, coarse: Sym): Sym = coarse
  def union(a: Meas, b: Meas, rel: Rel): CostInterval =
    if rel.same then CostInterval.exact(Cost.zero)                             // ReusedSpace: explanatory
    else
      val r = res(rel, a.nodes + b.nodes)
      up(Cost.of(work = fuse2(a, b, r), alloc = r))
  def inter(a: Meas, b: Meas, rel: Rel): CostInterval =
    if rel.same then CostInterval.exact(Cost.zero)
    // HEAD-disjoint (SpatialCost.headDisjoint): `IntMap.intersectionWith` finds no shared key at the
    // top, so the fused cursor has no children and `materialize` stops there
    else if rel.disjoint && !rel.derived then
      up(Cost.of(work = fuse2(a, b, a.heads + b.heads), alloc = a.heads + b.heads))
    else
      val r = res(rel, tighter(a.nodes, b.nodes))
      up(Cost.of(work = fuse2(a, b, r), alloc = r))
  def subtract(a: Meas, b: Meas, rel: Rel): CostInterval =
    if rel.same then CostInterval.exact(Cost.zero)                             // instant prune to ∅
    else
      val r = res(rel, a.nodes)
      up(Cost.of(work = fuse2(a, b, r), alloc = r))
  def restrict(x: Meas, y: Meas, rel: Rel): CostInterval =
    val r = res(rel, tighter(x.nodes, y.nodes))
    up(Cost.of(work = fuse2(x, y, r), alloc = r))
  def raffine(x: Meas, y: Meas, rel: Rel): CostInterval =
    // Subtraction(x, restriction(x, y)) — TWO fused layers over x
    val r = res(rel, x.nodes + y.nodes)
    up(Cost.of(work = Sym.c(2) * fuse2(x, y, r), alloc = r))
  def compose(a: Meas, b: Meas, rel: Rel): CostInterval =
    // `Composition.children` splices ALL of b at every terminal of a, so b's cursor is re-read once
    // per a-terminal.  This is the one local operator whose fused cost is not linear in the operands.
    up(Cost.of(work = Sym.c(4) * (a.nodes + a.size * b.nodes) + reads(a) + a.size * reads(b),
               alloc = a.nodes * b.nodes))
  /** THE ROOT COMPOSITION'S MATERIALISATION FLOOR — `N(a)` forced cursor nodes, and the only must
   *  side this backend has for a local operator.
   *
   *  `execZ(s) = SpaceZipper.materialize(transpileZ(s))`, and `transpileZ(Space.Composition(x, y))` is
   *  `Composition(X, Y)` with NO smart constructor — unlike `union`/`intersection`/`subtraction`/
   *  `restriction`, every one of which can hand back an operand (and therefore possibly a `Lit`), a
   *  `Composition` cursor is always a `Composition` cursor.  `materialize` takes the `case _` arm on
   *  it and emits one `ZipperMaterializeNode` (work) and one `FreshNode` (alloc) before it looks at
   *  anything, so the root alone is never free — not even when `y` is `∅` or `{ε}`, because
   *  `Composition` has no fast path for either.
   *
   *  THE FLOOR IS `N(a)` AND THE INJECTION IS INTO `a`'s NODES, NOT THE RESULT'S.  Take any prefix `p`
   *  of a path of `a`'s value and induct on `|p|`: the cursor `materialize` reaches at `p` is either
   *  `Composition(X_p, Y)` or `union(Composition(X_p, Y), ·)`.  `Composition.children` is
   *  `X_p.children.transform((_, c) => Composition(c, Y))`, optionally `unionWith`-ed with `Y.children`
   *  at a terminal `X_p`; both keep every key of `X_p.children`, `unionWith` only ADDS keys, and
   *  `SpaceZipper.union` cannot short-circuit here (`sameSpace` needs two `Lit`s or one object, and a
   *  `Composition` is neither).  `materialize` recurses on EVERY entry of the child map — the
   *  `if c.nonEmpty` filter runs AFTER the recursive call — so every such `p` is forced, every forced
   *  cursor is non-`Lit`, and each pays its `FreshNode`.  Hence `alloc ≥ N(a)`, where `N` is the node
   *  count of `a`'s VALUE and `a.nodesFloor` is the sound reading of it.
   *
   *  AND `work ≥ 3·N(a)`: each of those forced nodes emits one `ZipperMaterializeNode`, then
   *  `z.children` and `z.terminal`, and `Composition`/`Union` open BOTH of those with
   *  `effort(EffortEvent.ZipperCursorRead)` before any operand is consulted.  (`Composition.terminal`
   *  is `a.terminal && b.terminal`, which short-circuits — the layer's own read does not.)
   *
   *  Measured against the counted oracle on the operator fixture: `a` has 73 nodes, and the run counts
   *  exactly 73 `FreshNode`s and 569 work events against the 219 + dispatch claimed here.  The
   *  UPPER endpoint is untouched — it is the demand analysis's, and it is met, not replaced. */
  override def composeRoot(a: Meas, b: Meas, rel: Rel): CostInterval =
    val forced = a.nodesFloor
    CostInterval(Cost.of(work = Sym.c(3) * forced, alloc = forced), compose(a, b, rel).hi)
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
  /** A MUST LOWER BOUND ON `src.children.size` AT THE CURSOR, from the n-ary frontier.
   *
   *  `TailsUnion.merged` reduces `src.children` — the CURSOR's child map, not the value's head set —
   *  so the floor has to be a must-count of THAT map's size.  It is, and by the same argument
   *  [[TailsFacts.distinctLo]] already carries: every cursor `children` implementation in
   *  `Zipper.scala` returns a map whose key set CONTAINS the result value's heads (a `Union` unions
   *  both maps, an `Intersection`/`RestrictionNode` intersects them and the result's keys must be in
   *  both, a `Subtraction` transforms the left map and the result's keys are left keys, a
   *  `Composition` transforms `a`'s map and grafts, a `Lit` transforms the trie's own map) — that is
   *  exactly why `materialize` has to drop the empty children afterwards.  `distinctLo` counts head
   *  children that are DEFINITELY present in γ and pairwise provably different, so the value has at
   *  least that many distinct heads and the map has at least that many keys.
   *
   *  `Meas.headsLo` would do as well for the map size, but `distinctLo` is the endpoint that has
   *  already been calibrated against the counted oracle (traps.md lesson 9's fourth refutation), and
   *  it is never larger, so it is the one used. */
  private def childFloor(src: Meas): Long = src.tails.map(_.distinctLo).getOrElse(0L)

  /** THE FUSED REDUCE'S UNION CHAIN SURVIVES BELOW THE TOP ONLY ON A SHARED KEY.
   *
   *  `merged.children` is `ac.unionWith(bc, …)` per chain layer, and `IntMap.unionWith` calls its
   *  combiner ONLY on a key both maps carry: "a key present in only one side is handed through
   *  UNCHANGED".  So a `Union` cursor — the thing that makes the next level down cost another
   *  `heads`-deep cascade and another forced node — is created exactly where two head children share
   *  a key.  [[TailsFacts.keyDisjoint]] is the fact that no two of them do (it is PAIRWISE
   *  disjointness of the children's possible head sets, over every POSSIBLY-present child, so it is
   *  the right MAY-side reading for an upper bound), and under it the reduce's chain exists at the
   *  RESULT ROOT and nowhere else.
   *
   *  `src.concrete` IS A SIDE CONDITION AND NOT A CONVENIENCE.  `keyDisjoint` quantifies over the
   *  SHAPE's `possibleHeads`, which bounds the keys a VALUE can carry — and a VIRTUAL cursor's child
   *  map can carry more than that.  `Intersection.children` is `ac.intersectionWith(bc, …)`: a key both
   *  operands hold survives into the map even when the shape has proved the meet BELOW it empty and
   *  dropped the key from `possibleHeads`; `Subtraction.children` is `ac.transform{…}`, which keeps
   *  every LEFT key whatever the shape proved removed.  Two head children could then share a key the
   *  shape says neither can have, `unionWith` would build a `Union` cursor there, and both the
   *  collapsed `alloc` and the one-level chain would be wrong.  A `Lit` source has no such gap: its
   *  cursor's keys ARE the value's keys, which is exactly what `possibleHeads` over-approximates. */
  private def chainSurvives(src: Meas): Boolean =
    !(src.concrete && src.tails.exists(_.keyDisjoint))

  def tailsUnion(src: Meas, forced: Boolean): CostInterval =
    // `TailsUnion.merged` REDUCES the head children with `Union(_, _)`, so one query at the top
    // cascades through a chain of up to `heads` fused layers.
    //
    // THE `nodes · heads` PRODUCT IS THE KEY-SHARING CASE AND ONLY THAT.  The chain is `heads` layers
    // deep at every result node only if the cursor keeps re-creating it below the top, and
    // `IntMap.unionWith` re-creates it exactly on a SHARED key — see [[chainSurvives]].  When the
    // frontier proves the head children pairwise key-disjoint the whole product collapses: the layer
    // stack is `nodes` reads for the source's own cursor (the `4 · N` per-layer envelope this model
    // uses everywhere) plus ONE `heads`-deep cascade at the result root, read at most four times.
    //
    // `alloc` COLLAPSES WITH IT.  `materialize` allocates one `FreshNode` per FORCED non-`Lit` cursor
    // node; with no shared key the reduce forces exactly its own top node and hands every child
    // through unchanged — by pointer when the source is concrete, and otherwise as one of the SOURCE's
    // own cursor nodes, which that operand's transfer already charges (this is the per-operator
    // envelope [[finish]]'s note describes, not a claim that nothing below is allocated).
    //
    // AND THE COLLAPSE NEEDS THE SAME `forced` SIDE CONDITION THE FLOOR BELOW DOES.  "Every handed-
    // through child is a `Lit`, taken by pointer" is a statement about the cursor `materialize` is
    // CALLED ON.  At depth > 0 the consumer re-wraps them: `Intersection.children` is
    // `ac.intersectionWith(bc, (_, x, y) => intersection(x, y))`, and `intersection(Lit, Lit)` is NOT
    // a `Lit`, so `materialize` recurses and emits one `FreshNode` per forced node all the way down
    // BOTH operands — `Subtraction.children`'s `case None => x` and `Composition.children`'s
    // `ac.transform(x => Composition(x, b))` re-wrap the same way.  Measured on
    // `Intersection(TailsUnion(a), b)` with both declared exactly and `a` key-disjoint: the collapsed
    // `alloc` upper is a CONSTANT 2 against a counted `2n + 1` — 5, 7, 9, … 17 for n = 2..8 — i.e. a
    // missing Θ(nodes) term and not a constant slip.  Gated on `forced`, the row is contained at every
    // n by the envelope this `else` replaced.
    //
    // AND THE PER-LAYER ENVELOPE DOES NOT COVER THE FORCED ROOT'S OWN SIX EVENTS.  This was a
    // MEASURED node-price deficit, not a reading of the formula: `TailsUnion(<a loop>)` against the
    // bare loop, both priced on `Routine.optimized`'s body with `|a| = 64` / `|b| = 16` declared
    // exactly (harness fixtures `tu-it-inter` / `it-inter`), counted `execZ` `Work` 34 against 27 —
    // SEVEN events for the one extra `SpaceZipper.TailsUnion` node — while the model's marginal was
    // FIVE: one `ZipperBuild` from [[dispatch]] plus `4 · N · (1 + heads)` = 4 at `N = 1, heads = 0`.
    // It was contained only because the loop is priced by the trie model through
    // `controlFlowFallback` and `naryProbes` leaves ~950 units of slack in the same total, so any
    // tightening of the loop's price would have turned it into an out-of-interval row.
    //
    // THE SIX ARE READ STRAIGHT OFF `Zipper.scala` AND NONE OF THEM SCALES WITH `heads`:
    //   `materialize`'s non-`Lit` arm  1 `ZipperMaterializeNode` (a `TailsUnion` cursor is never a
    //                                  `Lit`, so the `Lit` arm cannot be taken)
    //   `TailsUnion.children`          1 `ZipperCursorRead`, which forces `merged`
    //   `merged`'s `val cs = src.children`  1 read on the SOURCE's top layer
    //   `merged.children`              1 read — AT `cs.size <= 1` `merged` IS `SpaceZipper.empty` or
    //                                  the single child cursor, so the reduce builds NO `Union` layer
    //                                  and the `m - 1` chain terms of the floor below are all zero
    //   `TailsUnion.terminal`          1 read
    //   `merged.terminal`              1 read
    // The envelope's `(1 + heads)` layer factor collapses to `4 · N` exactly where `heads` is proved
    // 0 — an ε-only or empty source, which is what an `Intersection` body under a loop gives — and
    // `4 · 1` is below six.  `lub`, not `+`: the six ARE cursor traffic of the layers the envelope
    // counts, so the two are alternative readings of one quantity and the max of them is the sound
    // one.  The `+` form would charge every wide source six units it has already paid for, and
    // `tails-union`'s own row (envelope 328) is where that would show.
    //
    // THE SOURCE'S OWN `children` READ IS INSIDE THE SIX FOR THE SAME REASON IT HAS TO BE COUNTED
    // HERE AT ALL: when the source is a control-flow subterm, `transpileZ` lifts it with
    // `traversal(evalI(other))` and `SpatialCost.go`'s fallback prices it with the TRIE model, which
    // has no `ZipperCursorRead` vocabulary — so nothing else in the term charges that read.
    val rootTraffic = Sym.c(6)
    val hi =
      if chainSurvives(src) || !forced then
        Cost.of(work = (Sym.c(4) * src.nodes * (Sym.one + src.heads)) lub rootTraffic,
                alloc = src.nodes)
      else Cost.of(work = (reads(src) + Sym.c(4) * (Sym.one + src.heads)) lub rootTraffic,
                   alloc = Sym.one)
    // THE MUST SIDE — AND IT IS THE FUSED CURSOR'S OWN TRAFFIC, NOT `ITrie.joinAll`'s.  The reduce
    // never enters the n-ary trie op, so none of [[tailsScratchLo]]/[[tailsProbesLo]] applies here;
    // what a FORCED `TailsUnion` cannot avoid is read straight off `Zipper.scala`, with `m` the
    // cursor's child-map size and `m >= kd = childFloor(src)`:
    //
    //   `materialize`'s non-`Lit` arm   1 `ZipperMaterializeNode` + 1 `FreshNode`   (a `TailsUnion`
    //                                   cursor is never a `Lit`, so the `Lit` arm cannot be taken)
    //   `TailsUnion.children`           1 `ZipperCursorRead`, then forces `merged`
    //   `merged`'s `src.children`       1 read — EVERY `children` implementation in Zipper.scala
    //                                   opens with `effort(EffortEvent.ZipperCursorRead)`
    //   `merged.children`               the chain is `m - 1` `Union` layers, each of whose `children`
    //                                   reads once and then queries BOTH operands: `(m-1) + m`
    //   `TailsUnion.terminal`           1 read (`ITrie(z.terminal, ch)` is evaluated unconditionally)
    //   `merged.terminal`               `a.terminal || b.terminal` short-circuits, but the chain is
    //                                   LEFT-nested, so all `m - 1` `Union.terminal` reads are
    //                                   entered before the first leaf answers: `m - 1`
    //
    // = `3m + 2` work and 1 alloc, and it is monotone in `m`, so `kd` may replace it.  The leaf
    // `terminal` reads are NOT claimed: `RestrictionNode.terminal` is a literal `false` that emits
    // nothing, so a leaf can answer for free.
    val lo =
      if !forced || childFloor(src) < 2L then Cost.zero
      else Cost.of(work = Sym.c(3L * childFloor(src) + 2L), alloc = Sym.one)
    CostInterval(lo, hi)
  def tailsInter(src: Meas, forced: Boolean): CostInterval =
    // TailsIntersection MATERIALISES its source (it needs the present-head set) and then calls
    // `ITrie.tailsIntersection`, a LEFT FOLD of `heads` merges — so this operator does pay real
    // trie-algebra `touch`, and allocates both `FreshNode`s and `FreshTrieNode`s.
    // and `meetAll`'s OPERAND LOOPS are real `work` here for the same reason the trie model charges them:
    // they emit `NaryOperandProbe`, not `touch`.
    //
    // NO MUST SIDE, AND THE REASON IS ONE WORD IN `Zipper.scala`: `merged` is a LAZY VAL.  The
    // materialisation and the `ITrie.tailsIntersection` call happen only when a consumer QUERIES the
    // cursor, and a consumer that meets it with ∅ never does.  Claiming the n-ary op's forced scratch
    // and its entry visit here cost zipper `Touch` containment 100% -> 93% and `Alloc` 100% -> 98% on
    // the corpus, with `actual=10 in [18, 16]` on the worst point — an INVERTED interval, which is the
    // unmistakable signature of a must claim for work that did not happen.
    //
    // THE `heads` FACTOR WAS A STALE LEFT-FOLD TERM.  `ITrie.tailsIntersection` has been `meetAll` — ONE
    // simultaneous n-ary descent — since the trie model dropped the same factor, and the cancellation
    // that licenses it is the one written out in `TrieAlgebraCost.tailsInter`: the meet's frontier lies
    // inside the SMALLEST child, `n_min ≤ (nd − 1)/h` because the minimum is at most the mean, so
    // `n_min · h ≤ nd − 1` and the arity cancels.  It applies here for the same reason: this backend
    // calls the same `ITrie` entry point.  Measured on the operator table: `alloc` 1927 -> 1336 and
    // `touch` 1972 -> 219 against a counted 209 and 9.
    // `naryPreScan` is NOT added here, and the omission is deliberate: this backend already pays
    // `2 * reads(src) = 8 * nd(src)` for the materialisation the trie executables do not, and
    // `nd(src) >= 1 + heads` on every shape whose `nodesHi` comes from `SpatialFacts.trieNodes`
    // (`1 + Σ K_d` with `K_1 = heads`), so `anyEmptyOperand`'s at most `heads` probes are inside that
    // envelope.  1200 randomised tails shapes refute the trie endpoint at two heads and never this one.
    val hi = Cost.of(work = Sym.c(2) * reads(src) + naryProbes(src.heads, src.nodes),
                     alloc = src.nodes + naryScratch(src.heads, src.nodes),
                     touch = Sym.one + Sym.c(3) * src.nodes)
    CostInterval(if forced then tailsInterLo(src) else Cost.zero, hi)

  /** THE MUST SIDE OF A *FORCED* `TailsIntersection`, WHICH IS THE TRIE MODEL'S OWN N-ARY FLOOR.
   *
   *  The refutation recorded above is about the LAZY VAL and nothing else: "the materialisation and
   *  the `ITrie.tailsIntersection` call happen only when a consumer QUERIES the cursor, and a consumer
   *  that meets it with ∅ never does".  `forced` is the side condition that removes the escape — at
   *  the root, `execZ` is `materialize(transpileZ(s))`, a `TailsIntersection` cursor is never a `Lit`
   *  so `materialize` takes its non-`Lit` arm, and that arm runs `z.children` (hence `merged`, hence
   *  `ITrie.tailsIntersection(materialize(src))`) unconditionally.  Once the call happens it is the
   *  SAME `ITrie` entry point `evalI` calls, so [[tailsScratchLo]]/[[tailsProbesLo]] — derived in the
   *  block comment above them from `IntTrie.liveDistinct` and `IntTrieOps.meetAllTries` — hold here
   *  verbatim, and so does their `distinctLo >= 3` / `allHeaded` gating.
   *
   *  The zipper's own three events on top of them, from `SpaceZipper.materialize` and
   *  `SpaceZipper.TailsIntersection`: 1 `ZipperMaterializeNode` + 1 `FreshNode`, 1 read for
   *  `children` and 1 read for `terminal`.  Nothing is claimed for `merged`'s own reads or for
   *  `materialize(src)`.
   *
   *  `touch` IS THE ONE FLOOR THAT NEEDS NO ARITY FACT: `ITrie.tailsIntersection`'s first statement is
   *  `effort(EffortEvent.TrieNodeVisit)`, before the `children.isEmpty` and `children.size == 1`
   *  tests.  A second visit needs the two-head case (`meetAll` opens with its own `TrieNodeVisit`) and
   *  a third needs the n-ary path (`IntTrieOps.meetAllTries`'s `enter()` is a counted `PatriciaVisit`
   *  and its first statement) — the same three [[TrieAlgebraCost.tailsForced]] claims, restated here
   *  because `ZipperCost` is not a `TrieAlgebraCost` and has no `entryVisit`. */
  private def tailsInterLo(src: Meas): Cost =
    if atMostOneHeadZ(src) then Cost.of(work = Sym.c(3), alloc = Sym.one, touch = Sym.one)
    else
      val twoHeads = (src.headsLo match { case Sym.Const(n) => n >= 2L; case _ => false }) ||
                     src.tails.exists(_.distinctLo >= 2L)
      val touch =
        if !twoHeads then Sym.one
        else if Tuning.patriciaOps && naryDeepLo(src).isDefined then Sym.c(3)
        else Sym.c(2)
      Cost.of(work = Sym.c(3) + tailsProbesLo(src),
              alloc = Sym.one + tailsScratchLo(src),
              touch = touch)
  /** `TrieAlgebraCost.atMostOneHead`, which this instance does not inherit */
  private def atMostOneHeadZ(m: Meas): Boolean = m.heads match
    case Sym.Const(n) => n <= 1L
    case _ => false
  /** `materialize(transpileZ(x))` then `ITrie.range` — inherently count-based, never fused.
   *
   *  THREE TERMS OF THE PREDECESSOR WERE LEFT BEHIND BY THE ORDER-STATISTIC SLICE and are gone:
   *   - `3·w·(w·len + len + 2)` was QUADRATIC IN THE WINDOW, a leftover from the implementation that
   *     "enumerated the window path-by-path and re-`union`ed each one" (`IntTrie.slice`'s header says
   *     so in as many words).  The slice is linear in `w + depth`; see [[TrieAlgebraCost.range]] for
   *     the two-partial-children argument that establishes it.
   *   - `walk·log(heads)` charged `IntTrie.ordered`'s per-node sort, which emits no counted event and
   *     therefore cannot live in `touch` (declared as an assumption instead).
   *   - `walk = x.nodes` was charged for `materialize` UNCONDITIONALLY, but `SpaceZipper.materialize`
   *     returns a `Lit` cursor BY POINTER with zero `FreshNode`, and [[liftsToLit]] decides that
   *     statically.  [[Meas.concrete]] is the channel that carries it. */
  def range(x: Meas, window: Sym, identity: Boolean): CostInterval =
    // a CONCRETE operand is already a `Lit`: `materialize` hands the trie back, allocating nothing and
    // performing no cursor read.  Anything else really is walked and rebuilt into a fresh trie.
    // `mat` IS THE UPPER ENDPOINT'S MATERIALISATION TERM AND IT STAYS UNCONDITIONAL.  Zeroing it on a
    // `liftsToLit` operand is right for the CURSOR READS (`materialize` hands a `Lit` back without
    // querying it, which is what `rd` uses) but NOT for `alloc`: `liftsToLit` is true for
    // `Singleton`/`Range`/`Unwrap`-chains whose own lift allocates trie nodes, and the counted oracle
    // said so — zipper `Alloc` containment 100% -> 98% on the corpus with `mat` zeroed here.
    // …and the operand that needs NO materialisation at all is the stricter `pointerLit` one: a bare
    // `Mention` is an ITrie the caller already owns, so `materialize` returns it and the only
    // allocation left is `ITrie.range`'s own rebuilt spine.  Measured on the operator table: predicted
    // zipper `Alloc` for `Range(a, 0, 4)` over a 73-node `a` was `[0, 80]` against a counted 2.
    val mat = if x.pointerLit then Sym.zero else x.nodes
    val rd = if x.concrete then Sym.zero else reads(x)
    // the trie handed to `ITrie.range` is FRESHLY BUILT unless the operand was already concrete, so
    // its per-node counts are `CountUnknown` in that case whatever the operand's own state said
    val cnt = if x.concrete && x.countKnown then Sym.zero else x.nodes
    val w = tighter(window, x.size)
    if identity then up(Cost.of(work = Sym.one + rd, alloc = mat, touch = Sym.one + cnt))
    else
      val spine = Sym.c(2) * (x.len + Sym.one)
      val rebuilt = tighter(spine + Sym.one, x.nodes)
      val visits = tighter(Sym.one + spine + w, x.nodes)
      up(Cost.of(work = Sym.one + rd, alloc = mat + rebuilt, touch = mat + cnt + visits))
  // control flow never reaches these: `controlFlowFallback` reprices the whole subterm with the trie
  // model before the traversal gets here.  They stay defined (and no cheaper than the trie model's) so
  // the instance is total rather than throwing.
  def group(src: Meas): CostInterval = CostInterval.exact(Cost.of(work = Sym.one, touch = src.heads))
  def collect(groups: Sym, body: Meas): CostInterval =
    CostInterval.upperOnly(Cost.of(work = groups, alloc = groups * body.nodes,
                                   touch = Sym.c(3) * groups * (groups + Sym.one) * body.nodes))
  /** ITERATION's accumulation is `ITrie.joinAll` even on this backend — `transpileZ` has no fused n-ary
   *  union, so the loop is materialised through `evalI` — and its OPERAND LOOPS are `work`.  Inheriting
   *  `collect` here (a left fold, which runs no operand loop at all) put the prediction BELOW the counted
   *  total on two corpus programs the moment `NaryOperandProbe` existed; the comment above about
   *  `controlFlowFallback` is not true of every route into a loop. */
  override def collectJoin(groups: Sym, groupsLo: Sym, body: Meas, single: Boolean): CostInterval =
    CostInterval(Cost.of(alloc = naryScratchLo(groupsLo)),
                 Cost.of(work = groups + naryProbes(groups, groups * body.nodes),
                         alloc = groups * body.nodes + naryScratch(groups, groups * body.nodes),
                         touch = Sym.c(3) * groups * (groups + Sym.one) * body.nodes))
  def foldStep(groups: Sym, updNodes: Sym, updLen: Sym): CostInterval =
    CostInterval.upperOnly(Cost.of(work = groups * (Sym.one + updNodes), touch = groups * (Sym.one + updLen)))
  def fixStep(acc: Meas, body: Meas, rel: Rel): CostInterval =
    val r = res(rel, tighter(acc.nodes, body.nodes))
    CostInterval.upperOnly(Cost.of(work = Sym.one, alloc = r, touch = Sym.c(3) * (acc.nodes + body.nodes)))
  /** THE DEMAND-ANALYSIS PRICE of one fused region.
   *
   *  ==THE PRICE IS QUOTED IN THE COUNTED UNIT, AND IN NOTHING ELSE==
   *  `Work` for `execZ` is exactly `ZipperBuild + ZipperCursorRead + ZipperMaterializeNode` and `Alloc`
   *  is exactly `FreshNode + FreshTrieNode` (SpatialEvents.scala).  The demand summary supplies three of
   *  those five directly and EXACTLY: `cursorReads` is the `ZipperCursorRead` traffic and `forcedVirtual`
   *  is BOTH the `ZipperMaterializeNode` count and the `FreshNode` count, because `materialize` emits one
   *  of each per forced non-`Lit` cursor node and an accepted `Lit` subtrie arrives by pointer however
   *  large it is.  `ZipperBuild` is structural (one per lifted `Space` node) and `FreshTrieNode` comes
   *  from the operators that really call `ITrie`; both are outside the fused cursor algebra and are
   *  accumulated in `State.demandExtra` instead.
   *
   *  ==WHY `cursorMapEntries` / `materializeEntries` / `virtualAlloc` ARE NOT ADDED HERE==
   *  They are real work and real allocation — the per-ENTRY `IntMap.transform`/`unionWith` traffic and
   *  the virtual cursor objects the review is about — but they are counted in the SEPARATE
   *  [[ZipperDemandComponent]] vocabulary, which `EffortComponent.Work`/`Alloc` do not include.  Adding
   *  an uncounted quantity to a CALIBRATED component does not make the model more honest, it makes the
   *  calibrated number wrong by that quantity, and the quantity has a different GROWTH CLASS: on a
   *  key-disjoint union the counted `Work` is 17 flat over a 64 -> 1024 ladder while the map entries are
   *  `2n`, and on `(A ∪ B) ∩ C` with a fixed `C` the counted `Alloc` is 10 flat while `virtualAlloc`
   *  grows with `A`.  Folding them in is what made this price lose the meet against the eager
   *  per-operator sum (LIM-1/LIM-2).  They are reported in the analysis note and gated EXACTLY — not as
   *  a bound — against their own oracle in `SpatialDemandCheck`; that is where they are answerable.
   *
   *  `touch` is 0: a fused cursor composes `IntMap`s directly and enters no `IntTrieOps` descent. */
  override def demandPrice(d: DemandSummary): Option[CostInterval] =
    if d.truncated then None
    else
      val work = Sym.c(d.cursorReads) + Sym.c(d.forcedVirtual)
      val alloc = Sym.c(d.forcedVirtual)
      // EXACT means the supplied facts settled every case distinction the executor makes, so the
      // interval collapses; otherwise these are upper bounds and the lower endpoint stays at the
      // mandatory root materialisation.
      if d.exact then Some(CostInterval.exact(Cost.of(work = work, alloc = alloc)))
      else Some(CostInterval(Cost.zero, Cost.of(work = work, alloc = alloc)))

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

  /** THE DIAGNOSTIC COUNTERFACTUAL — not a backend, never returned by [[of]].  See
   *  [[NaiveTrieCostModel]]: the same `evalI` executable priced without its `AlgebraicResult` identity
   *  cases, so the whole-subtree wins are a measured difference rather than a claim. */
  val trieNoIdentityWarm: CostModel = new NaiveTrieCostModel(ExecutionPhase.Warm)

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
      case Sym.Const(_) | Sym.Big(_) => Amount.of(a * (b ** n))
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

  /** THE SECOND TERMINATION CRITERION.
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
   *  every node is quadratic in the term size — the review objects to that — so the refinement is
   *  budgeted, and exhausting the budget only loses precision (the symbolic propagation stands on
   *  its own). */
  val FactBudget = 2000
  /** extra body walks the seed-priced first round may cost one analysis — see `State.seedRounds` */
  val SeedRoundBudget = 16
  val MaxInline = 6
  /** THE AST-DEPTH CAP.  It used to be 64, which `puzzle15` exceeds — 16 `Iteration`s around a
   *  `superpose` call whose body nests 15 more inside a 16-way `Union` — and the transfer then returned
   *  an explicit `Unbounded("analysis depth cap")` on a program known to terminate.  The review
   *  is right that this is an implementation bug: raising the cap alone did NOT fix it (the per-level
   *  group-count product then saturated instead), but raising it TOGETHER with the rest-chain frame law
   *  below does — a recognised nest is priced in ONE transfer, so the depth a nest contributes is 1 and
   *  not its arity.  The cap now exists only to keep a pathological term off the JVM stack. */
  val MaxDepth = 1024
  /** How many rounds the interprocedural size/universe fixpoint may take before it gives up
   *  ([[universeOf]]).  The alphabet lattice is finite, so this only bounds the LENGTH iteration. */
  val UniverseRounds = 8

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
                       shapeFacts: Boolean = true,
                       /** THE DECORATED, `NodeId`-INDEXED ANALYSIS OF THE TERM BEING PRICED
                        *.  Present ⇒ every per-node type query is an `O(1)` index
                        *  lookup into the analysis that ALREADY ran, law refinements and spatial
                        *  refinements included, instead of a fresh `SpatialTyping.infer` that throws
                        *  them away.  That disconnect is why Life's cardinality tightened 5785 → 45
                        *  without moving its predicted work.  Cleared when the traversal crosses into an
                        *  inlined routine body, whose positions belong to a different tree. */
                       decorated: Option[SpatialAnalysis] = None,
                       /** the frontier budgets — `interned = false` because `ITrie`'s ring operations now
                        *  DO return an `AlgebraicResult` (the case-returning algebra was moved onto the
                        *  interned representation), so identity propagation is real for `evalI`/`execT` */
                       frontierConfig: FrontierConfig = FrontierConfig.default,
                       /** THE MENTIONS BOUND BY A BINDER INSIDE THE TERM BEING PRICED — a loop's `rest`,
                        *  a `Fixpoint`'s recursive mention, a callee's parameter.  Everything else in
                        *  `spaces` is a DECLARED INPUT: an object the caller already holds, which is what
                        *  [[Meas.countKnown]] needs to distinguish (a bound mention carries whatever state
                        *  the binder gave it, and the binder sets it explicitly). */
                       bound: Set[SpaceMention] = Set.empty,
                       /** WHAT EACH BOUND MENTION MAY POINT INTO — see [[Shares]].  A loop's `rest` IS
                        *  an `ITrie` child of the source object (`ic.updated(rest, sub)` in `evalI`), a
                        *  `Fixpoint`'s recursion mention IS the seed object on round 1
                        *  (`var cur = evalI(init)`), and a callee's parameter IS the argument's value,
                        *  so each of them can carry another operand's nodes and a share analysis that
                        *  looked only at MENTION NAMES would miss it.  A bound mention with no entry
                        *  here reads as [[Shares.any]] — opaque — which refuses the must-paired count
                        *  rather than claiming it. */
                       share: Map[SpaceMention, Shares] = Map.empty):
    def withRoutines(rc: PartialFunction[RoutinePtr, Routine]): Env =
      copy(routines = rc, facts = facts.copy(lenv = facts.lenv.copy(routines = rc)))
    /** install a bound mention's alias set (see [[share]]); the mention is marked bound at the same
     *  time, because an entry for a mention the analysis still thinks is a declared input would be
     *  read as [[Shares.of]] that mention's own name and the alias lost */
    def bindShare(m: SpaceMention, sh: Shares): Env =
      copy(bound = bound + m, share = share + (m -> sh))
    /** consume an existing decorated analysis instead of re-inferring per node */
    def withDecorated(d: SpatialAnalysis): Env = copy(decorated = Some(d))
    def withoutDecorated: Env = if decorated.isEmpty then this else copy(decorated = None)

  /** One backend's answer: WHICH executable, in WHICH phase, and a lower/upper INTERVAL rather than
   *  a bare worst case.  `cost` is the upper endpoint, kept under that name so
   *  a caller that only wants the worst case reads the same field it always did. */
  final case class Report(model: String, backend: Backend, phase: ExecutionPhase,
                          interval: CostInterval, meas: Meas, assumptions: Vector[String],
                          /** HOW MUCH OF THIS ANSWER IS FRONTIER/DEMAND DRIVEN vs the marked ceiling */
                          census: FrontierCensus = FrontierCensus(),
                          /** was the term priced as `Routine.optimized`'s body / an `SC` residual, or as
                           *  the DEFINITIONAL term?  The user's third steer: a definitional-form estimate
                           *  is the wrong question, so where one is unavoidable it says so. */
                          form: CostForm = CostForm.AsGiven):
    def cost: Cost = interval.hi
    def lower: Cost = interval.lo
    /** are ALL FOUR components finite?  The review: on a closed, terminating, non-grounded
     *  program an infinite estimate is a FAILED RESULT, and this is the predicate the invariant uses. */
    def finite: Boolean =
      Vector(cost.work, cost.alloc, cost.rounds, cost.touch)
        .forall(a => !a.isUnbounded && !a.at(Map.empty).isInfinite)
    def infiniteComponents: Vector[String] =
      Vector("work" -> cost.work, "alloc" -> cost.alloc, "rounds" -> cost.rounds, "touch" -> cost.touch)
        .filter((_, a) => a.isUnbounded || a.at(Map.empty).isInfinite).map((n, a) => s"$n=${a.show}")
    def show: String =
      val a = if assumptions.isEmpty then "" else assumptions.distinct.map("    ! " + _).mkString("\n", "\n", "")
      s"[$model] ${backend.executable} on ${form.show}\n  LOWER ${lower.show}\n  UPPER ${cost.show}\n" +
      s"  O: ${cost.showO}\n  in: ${meas.show}\n  ${census.show}$a"
    /** the interval for one CALIBRATED component, evaluated at a concrete valuation */
    def bracket(c: EffortComponent, v: Map[String, Double]): (Double, Double) =
      (lower.calibrated(c).at(v), cost.calibrated(c).at(v))

  private final class State:
    var budget: Int = FactBudget
    var fresh: Int = 0
    val notes = collection.mutable.LinkedHashSet.empty[String]
    def note(s: String): Unit = notes += s
    def nextVar(prefix: String): String = { fresh += 1; s"$prefix$fresh" }
    // ---- the frontier / demand census (the "last-resort fallback" requirement) ----
    var binaryNodes = 0
    var derived = 0
    var fallback = 0
    var noFact = 0
    var chainNests = 0
    val bySource = collection.mutable.Map.empty[String, Int]
    /** the cost of every subterm this executable handed to ANOTHER one (`execZ` → `evalI`), so the
     *  whole-region demand price can be compared against the per-operator sum on equal terms */
    var handedOff: CostInterval = CostInterval.zero
    /** WHAT THE DEMAND ANALYSIS DOES **NOT** MODEL, accumulated so the whole-region price can be
     *  compared against the per-operator sum on equal terms.
     *
     *  This field is a soundness device and it exists because the naive version was UNSOUND and the
     *  corpus calibration said so: meeting the raw demand price against the per-operator sum zeroed
     *  `touch` (the demand summary makes no `touch` claim — a fused cursor enters no `IntTrieOps`
     *  descent, but `ITrie.singleton`/`range`/`tailsIntersection` DO) and zeroed a cold `Literal`'s
     *  construction, producing 109 out-of-interval corpus points including `touch actual=3 in [0,0]`.
     *  So everything OUTSIDE the fused cursor algebra — every `ZipperBuild` dispatch, every
     *  `TriePathDispatch`, and every operator that really calls into `ITrie` — is accumulated here and
     *  ADDED to the demand price before the two are met.
     *
     *  THE COMPLEMENT MUST ALSO HOLD, and that was the other half of LIM-1: a contribution the demand
     *  analysis DOES model must NOT be accumulated here, or the sum re-imports the eager quantity the
     *  demand price exists to replace.  Two did — `ZipperCost.mention`'s `4 · N(operand)` cursor reads
     *  and the raffination re-read of `x` — and each is linear in an operand, so `whole` was linear on
     *  every term with a `Mention` in it and the meet could never bind.  The dividing line is the counted
     *  EVENT, not the operator: cursor reads and materialised nodes are the demand summary's, dispatches
     *  and `ITrie` traffic are this field's. */
    var demandExtra: CostInterval = CostInterval.zero
    /** how many `SpatialFrontier.binary` calls are left.  The relational walk is bounded but not free,
     *  and a hot `Routine.optimized` hook cannot afford one per node of a 300-node body. */
    var frontierBudget: Int = 512
    /** how many `Fixpoint` nodes may price their FIRST round separately against the seed (see the
     *  `Fixpoint` arm of `goNode`).  That pricing walks the body a second time, so a nest of
     *  fixpoints would double per level; this bounds the extra walks for the WHOLE analysis at
     *  [[SeedRoundBudget]], after which every round is priced against `self` as before. */
    var seedRounds: Int = SeedRoundBudget
    /** the frontier summaries already computed, keyed by the operand PAIR — reused as the zipper demand
     *  analysis's `Pairing`, so the relational fact is derived once and consumed twice */
    val relCache = collection.mutable.Map.empty[(Space, Space), FrontierSummary]
    /** recognised rest-chain nests, so the guard and the body of the same match arm do not each pay for
     *  the recognition and the profile query */
    val chainCache = collection.mutable.Map.empty[(Space, NodeId), Option[ChainCost]]
    /** THE RECURSIVE CALL'S OWN RESULT MEASURE, when [[paramFixpoint]] derived one.
     *
     *  Without it the `env.active(rp)` arm has nothing to say about the recursive occurrence's SIZE and
     *  emits the free variables `|rp()|` / `len(rp())`, which is why `datalog-sn`'s reference and zipper
     *  reports had no number to gate at all.  The spatial least fixpoint bounds every reachable value of
     *  the accumulator, hence the routine's result, so the occurrence gets a NUMERIC measure.  Set by the
     *  inlining arm immediately before it analyses the body, and restored afterwards. */
    val selfResult = collection.mutable.Map.empty[RoutinePtr, Meas]
    def recordRel(r: Rel): Unit =
      binaryNodes += 1
      r.frontier match
        case None => noFact += 1
        case Some(f) =>
          if f.isFallback then fallback += 1 else derived += 1
          bySource(f.source.show) = bySource.getOrElse(f.source.show, 0) + 1
    def census(demandRegions: Int, demandExact: Int, demandTrunc: Int): FrontierCensus =
      FrontierCensus(binaryNodes, derived, fallback, noFact, bySource.toMap,
                     demandRegions, demandExact, demandTrunc, chainNests)

  // ---- entry points ----------------------------------------------------------------------------
  def analyze(s: Space, model: CostModel): Report = analyze(s, Env(), model)
  def analyze(s: Space, env: Env, model: CostModel): Report =
    analyze(s, env, model, CostForm.AsGiven)
  def analyze(s: Space, env: Env, model: CostModel, form: CostForm): Report =
    val st = new State
    val (c0, m) = go(s, env, model, st, 0, NodeId(Vector.empty))
    val c1 = c0 + model.finish(m, liftsToLit(s))
    // ---- THE DEMAND ANALYSIS -----------------------------------------------
    // `execZ` is the ONE lazy executable, so it is the one whose cost is not the sum of its
    // subexpressions' local worst cases.  A whole-region demand analysis is an independent derivation of
    // the same quantity; the two are MET, so the answer is the tighter and is sound either way.
    var regions = 0; var exact = 0; var trunc = 0
    val c =
      if !model.demandDriven then c1
      else
        demandOf(s, env, st) match
          case None => c1
          case Some(d) =>
            regions = 1
            if d.exact then exact = 1
            if d.truncated then trunc = 1
            model.demandPrice(d) match
              case None => c1
              case Some(dp) =>
                // dp bounds the FUSED CURSOR ALGEBRA in the counted unit (`ZipperCursorRead` and
                // `ZipperMaterializeNode`/`FreshNode`); `demandExtra` bounds everything else the
                // executable does inside the region (`ZipperBuild`, `TriePathDispatch`, and the operators
                // that really call `ITrie`); `handedOff` bounds the control-flow subterms `evalI` was
                // given.  The three partition the counted events of the region, which is what makes the
                // meet sound — and the partition is why neither side may carry the other's events.
                val whole = dp + st.demandExtra + st.handedOff
                st.note(s"${model.name}: the fused region was priced by the DEMAND ANALYSIS " +
                        s"(${d.show}; ${d.showProfile}); that price plus the non-fused remainder is MET " +
                        "against the per-operator sum, because a lazy fused expression does not evaluate " +
                        "its children independently — summing their local worst cases is the wrong semantics")
                // AND THE PART OF THE ANSWER THAT IS NOT IN ANY CALIBRATED COMPONENT SAYS SO OUT LOUD.
                // `cursorMapEntries`/`materializeEntries`/`virtualAlloc` are real per-ENTRY `IntMap` work
                // and real virtual-cursor allocation that `EffortComponent.Work`/`Alloc` do not count
                // (SpatialEvents.scala's declared oracle gap), so they are NOT folded
                // into `work`/`alloc` — a tight `work` here is a statement about the counted unit and
                // this note is what stops it being read as a statement about the machine.
                if d.cursorMapEntries + d.materializeEntries + d.virtualAlloc > 0L then
                  st.note(s"${model.name}: OUTSIDE THE CALIBRATED UNIT, from the same demand analysis — " +
                          s"${d.cursorMapEntries} cursor child-map entries, ${d.materializeEntries} " +
                          s"materialize entries and ${d.virtualAlloc} virtual cursor allocations.  These " +
                          "are executed work with no counted `EffortEvent`, so they are reported here and " +
                          "gated exactly against their own oracle (`ZipperDemandEvent`) rather than added " +
                          "to `work`/`alloc`, which would put an uncounted quantity — of a different " +
                          "growth class — inside a calibrated number")
                // ONLY THE UPPER ENDPOINT IS MET.  `c1.lo` is the established, corpus-calibrated lower
                // endpoint; the demand derivation contributes an upper bound and nothing else, and joining
                // the two lower endpoints produced INVERTED intervals on the corpus (`work actual=141 in
                // [142, 141]`).  A meet that can raise a lower endpoint is not a meet worth having.
                CostInterval(c1.lo, Cost.meetHi(c1.hi, whole.hi))
    if st.budget <= 0 then st.note(s"spatial-fact budget ($FactBudget queries) exhausted; the rest is symbolic only")
    for why <- model.touchNoOracle do
      st.note(s"${model.name}: the `touch` component has NO COUNTED ORACLE and is a model, not a " +
              s"measurement — $why")
    if form == CostForm.Definitional then
      st.note("THIS ESTIMATE DESCRIBES THE DEFINITIONAL TERM, not `Routine.optimized`'s body and not " +
              "an SC residual — it is not a prediction about what runs")
    // ---- THE `touch` LOWER ENDPOINT POLICY ------------------------------------------------------
    // CLAIM A LOWER ENDPOINT ONLY WHERE THERE IS AN ORACLE TO REFUTE IT.  This used to be an
    // unconditional `withoutTouchLower`, justified by "the fast paths can eliminate essentially every
    // internal visit" — true of the RECURSIVE visits and false of the ENTRY: every `ITrie` operation
    // emits its `TrieNodeVisit` before any test.  Zeroing it cost the WIDTH requirement its entire
    // discriminating power on this component (62 of 62 per-operator failures were `width`) AND hid two
    // unsound lower endpoints (a warm `Literal` and a missing-prefix `Unwrap`), both now fixed.
    // For a model whose `touch` has NO counted oracle — `ReferenceCost` over `Set[PathValue]` — a lower
    // endpoint would be an unfalsifiable claim, so that one keeps the zero.
    val reported = if model.touchNoOracle.isDefined then c.withoutTouchLower else c
    Report(model.name, model.backend, model.phase, reported, m, st.notes.toVector,
           st.census(regions, exact, trunc), form)

  /** Every executable's warm interval over the SAME facts — the per-backend cost map the review
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
  private def refine(m: Meas, s: Space, env: Env, st: State, id: NodeId): Meas =
    // THE SIZE/LENGTH SOURCE IS APPLIED IN BOTH CASES, and it did not used to be.
    //
    // `histAt` is an independent sound source of the same quantities, so meeting it can only help —
    // but the decorated branch was an EARLY EXIT that skipped it, on the reasoning that reading a
    // per-node type out of the finished analysis should be O(1) rather than a fresh inference.  The
    // consequence is that consuming a BETTER analysis could produce a WORSE bound, which is the one
    // thing a caller consuming a better analysis is entitled to rely on not happening.  MEASURED via
    // `SpatialPipelineCheck`'s ITEM 8 gate: `gol`'s predicted `work` was 5913 with the decoration and
    // 5853 without, a flat +60 with nothing gained, because the histogram bound the fresh path meets
    // here was dropped.
    //
    // The speed argument survives, because it was never about this source: the expensive re-derivation
    // the decorated path exists to avoid is `shapeAt`'s full `SpatialTyping.infer` (the reduced
    // product, shape included), and that is still skipped.  `histAt` is the size/length product only,
    // and the fresh path already spends the same budget unit on it.
    var out = histAt(s, env, st) match
      case None => m
      case Some(t) => m.copy(size = tighter(m.size, symSize(t.size.hi)), len = tighter(m.len, symLen(t.len)),
                             sizeLo = m.sizeLo lub symLo(t.size.lo))
    decoratedAt(s, env, id) match
      // THE DECORATED PATH.  This occurrence's type is read out of the analysis that
      // already ran — with its law refinements, its per-node spatial refinements and its binder
      // environment — in O(1), instead of being re-derived by a fresh `SpatialTyping.infer` that has
      // none of them.  Life's 5785 → 45 cardinality tightening reaches the cost model through here.
      // THE DECORATED PATH *ADDS* INFORMATION; IT NO LONGER REPLACES IT.
      //
      // This branch used to return `refineWith(m, t, env)` and stop, on the reasoning that a per-node
      // type read out of the finished analysis is strictly better than re-deriving one.  It is not
      // strictly better, and that is the defect: the decorated analysis is a WHOLE-ROUTINE run under
      // `SpatialConfig`'s budgets, so at an individual node it may have widened or capped where an
      // unbudgeted single-node `SpatialTyping.infer` would not.  Where that happens, consuming the
      // better analysis produced a WORSE bound.
      //
      // DIAGNOSED, not guessed.  `SpatialPipelineCheck`'s ITEM 8 gate had `gol`'s predicted `work` at
      // 5913 with the decoration and 5853 without — a flat +60 on a variable-free quantity, so no
      // coefficient trade could explain it.  Two other hypotheses were tested and ruled out first
      // (`Sym.tighter`'s asymptotic tie-break, and this branch skipping `histAt`); meeting the fresh
      // inference here closes it exactly: work 5853 = 5853, alloc 24172 < 24176, touch 86083 < 86259.
      //
      // WHAT IT COSTS, STATED PRECISELY — because the obvious summary ("the decorated path no longer
      // saves the shape inference") is only half true and the other half matters.
      //
      // `histAt` and `shapeAt` both decrement `State.budget`, ONE GLOBAL COUNTER per analysis
      // (`FactBudget` = 2000).  So calling them here does NOT add inference calls to the run: the
      // total is capped either way.  What it changes is WHICH nodes spend the budget.  Two regimes:
      //
      //   * UNDER the budget — every node on the six cornerstones, measured: the
      //     "spatial-fact budget exhausted" note appears nowhere in a full run — this is a strict
      //     GAIN.  Three sound bounds on the same quantities are met instead of one being chosen, so
      //     the result can only be tighter, and `puzzle15`'s own numbers moved the right way
      //     (alloc 8.272e55 -> 7.610e55, touch 2.680e56 -> 2.581e56).
      //   * OVER the budget, the change becomes a REDISTRIBUTION and could starve a later node,
      //     relocating the defect rather than fixing it.  Nothing in the corpus currently exercises
      //     that, and the check that would catch it is `SpatialEventsCheck`'s containment table —
      //     100.0% on every gated channel over 200 corpus programs after this change.  If a future
      //     term does exhaust the budget, spending it on an already-decorated node is the wrong
      //     trade and this branch should consult `shapeAt` only when the decorated type is not
      //     already at least as strong.
      //
      // So what the decoration is WORTH here is its LAW AND BINDER REFINEMENTS — which a fresh
      // per-node infer genuinely cannot have — rather than a saved traversal.  Making
      // `SpatialAnalysis` strong enough per node to drop the re-inference is the right long-run fix
      // and belongs there, not here; PLAN.md records it.
      case Some(t) =>
        st.note(DecoratedNote)
        if env.shapeFacts then st.note(ShapeNote)
        var o2 = refineWith(out, t, env)
        shapeAt(s, env, st) match
          case Some(t2) => o2 = refineWith(o2, t2, env)
          case None => ()
        o2
      case None =>
        shapeAt(s, env, st) match
          case Some(t) => out = refineWith(out, t, env)
          case None => ()
        out.copy(heads = tighter(out.heads, out.size))

  /** meet a `Meas` with everything ONE already-computed `SpatialType` proves */
  private def refineWith(m: Meas, t: SpatialType, env: Env): Meas =
    var out = m.copy(size = tighter(m.size, symSize(t.size.hi)), len = tighter(m.len, symLen(t.len)),
                     sizeLo = m.sizeLo lub symLo(t.size.lo))
    if env.shapeFacts then
      out = out.copy(heads = tighter(out.heads, symSize(t.headCount.hi)),
                     headsLo = out.headsLo lub symLo(t.headCount.lo),
                     headKeys = closedHeadKeys(t.shape).orElse(out.headKeys),
                     tails = TailsFacts.of(t.shape).orElse(out.tails),
                     // `ε ∉ this space` — a MUST fact, and the one the prefixed operators need to
                     // discharge their whole-skip fast paths (`prefixes.terminal` prefixes everything)
                     epsAbsent = out.epsAbsent || t.shape.eps == Presence.No)
      // THE EXACT TRIE-NODE IDENTITY, when the shape's prefix profile supplies one (whispers §1).
      // Both candidates are sound uppers of the same quantity, so `tighter` preserves soundness.
      SpatialFacts.trieNodes(t) match
        case Right(iv) =>
          out = out.copy(nodesHi = Some(tighter(out.nodes, symSize(iv.hi))),
                         // BOTH ENDPOINTS.  `trieNodes` returns an interval and only its upper half was
                         // being read; the lower half is what a "this recursion visits every node of the
                         // operand" claim needs, and using `nodesHi` there would be unsound the moment
                         // the profile is not exact.
                         nodesLo = Some(out.nodesLo.map(_ lub symLo(iv.lo)).getOrElse(symLo(iv.lo))))
        case Left(_) => ()                     // an inconsistent hand-built type: keep the fallback
      // THE THIRD ENDPOINT OF THE SAME PROFILE — the nodes that HAVE A CHILD.  `compositionR`'s one
      // allocation site is entered at exactly those and at no leaf, so this — and not `nodesLo` — is
      // the quantity a composition `alloc` floor may read.  Lower endpoint only: nothing upstream
      // wants a second upper bound on the node count.
      SpatialFacts.interiorNodes(t) match
        case Right(iv) =>
          out = out.copy(interiorLo =
            Some(out.interiorLo.map(_ lub symLo(iv.lo)).getOrElse(symLo(iv.lo))))
        case Left(_) => ()
    out.copy(heads = tighter(out.heads, out.size))

  private val DecoratedNote =
    "per-node types come from the DECORATED, NodeId-indexed analysis (SpatialAnalysis) — law and " +
    "spatial refinements included — not from a fresh SpatialTyping.infer per node"

  /** THIS OCCURRENCE'S already-computed type, from the decorated analysis.  The `expression` guard is
   *  load-bearing: a `NodeId` is only meaningful against the tree the analysis was run on, so if the
   *  subterm at that position is not the subterm being priced the lookup is REFUSED rather than
   *  answered with somebody else's type. */
  private def decoratedAt(s: Space, env: Env, id: NodeId): Option[SpatialType] =
    env.decorated.flatMap(_.at(id)).filter(_.expression == s).map(_.result)

  // ---- THE RELATIONAL FRONTIER -----------------------------------------------

  /** THE BINARY NODE'S RELATIONAL FACT.  Derived from the two children's already-computed
   *  `SpatialType`s — the decorated ones when available, a budgeted fresh inference otherwise — and
   *  never from an evaluation. */
  private def relAt(op: FrontierOp, a: Space, b: Space, ma: Meas, mb: Meas,
                    env: Env, st: State, id: NodeId): Rel =
    val same = sharedOperands(a, b) || SpatialFrontier.sameObject(a, b)
    val disj = headDisjoint(ma, mb)
    val f =
      if !env.shapeFacts || st.frontierBudget <= 0 then None
      else
        val pair = (decoratedAt(a, env, id.child(0)), decoratedAt(b, env, id.child(1))) match
          case (Some(l), Some(r)) => Some((l, r))
          case _ =>
            if st.budget <= 1 then None
            else for l <- shapeAt(a, env, st); r <- shapeAt(b, env, st) yield (l, r)
        pair.map { (l, r) =>
          st.frontierBudget -= 1
          val summary = SpatialFrontier.binary(op, l, r, same, env.frontierConfig)
          st.relCache((a, b)) = summary
          summary
        }
    // THE SHARE CHANNEL.  `same` is the ROOT `a eq b`; this is the RECURSIVE one, and it is a separate
    // question with a separate answer — see [[Shares]] and `TrieAlgebraCost.priced`.
    // computed only where a frontier exists: with `frontier = None` `priced` takes the coarse arm and
    // makes no must-paired claim at all, so the walk would be pure cost
    val mayShare = f.isEmpty || !sharesOf(a, env).disjointFrom(sharesOf(b, env))
    // AND THE ONE THING THE SYNTAX CANNOT SETTLE IS PUBLISHED RATHER THAN ASSUMED.  Two DISTINCT
    // declared inputs are two different base tokens, and `ic` is an opaque map: a caller free to bind
    // `b` to `ITrie.unwrap(ic(a), p)` would make them node-shared with no syntax to show it.  Every
    // calibration and corpus context materialises each declared space independently
    // (`ITrie.fromSpaceValue` per mention), which is what makes the token disjointness a real
    // disjointness, and the same sentence covers a declared input against a `Literal`'s memo trie.
    // It is a strictly WEAKER assumption than the one this side condition replaces — `mustDescend`
    // alone assumed no sharing at all, syntactic sharing included — so it is stated, not hidden.
    if !mayShare && f.exists(!_.isFallback) then
      st.note("must-paired descent floors assume DISTINCT declared spaces are independently " +
              "materialised objects (no operand of `ic` is built out of another's nodes); syntactic " +
              "sharing is analysed and refused (SpatialCost.Shares).  THE PREMISE IS REFUTABLE AND " +
              "PRE-EXISTING: with `ic(y) = ITrie.wrap(h0, ITrie.unwrap(ic(a), h0))` and both declared " +
              "exactly, `a ∪ y` / `a ∩ y` / `a ∖ y` all read `Touch [10, 60]` against a counted 3 on " +
              "both trie-shaped backends — IDENTICALLY with and without the `Shares` analysis, which " +
              "only ever refuses a claim.  Closing it needs an aliasing channel on the declared " +
              "inputs, which `SpatialAnnotations` does not have.")
    val rel = Rel(f, same, disj, mayShare = mayShare)
    st.recordRel(rel)
    rel

  // ---- THE ZIPPER DEMAND ANALYSIS -------------------------------------------

  /** does `transpileZ` turn this subterm into a CONCRETE cursor, so the demand analysis needs its
   *  per-depth profile rather than a fused-operator rule? */
  private def demandLeaf(s: Space): Boolean = s match
    case Space.Union(_, _) | Space.Intersection(_, _) | Space.Subtraction(_, _) |
         Space.Restriction(_, _) | Space.Raffination(_, _) | Space.Composition(_, _) |
         Space.Wrap(_, _) | Space.Unwrap(_, _) | Space.TailsUnion(_) | Space.Empty => false
    case _ => true

  /** THE COST OF A SUBTERM THE DEMAND WALK NEVER ENTERS, routed to `demandExtra` when — and only when —
   *  the executable really forces a cursor there.
   *
   *  Two operators are demand LEAVES that still transpile their operand as a ZIPPER: `Range`
   *  (`ITrie.range(materialize(transpileZ(x)), …)`) and `TailsIntersection` (whose `merged` materialises
   *  its source).  `fromSpace` lifts both as a `Lit` over the RESULT profile, so the demand price makes no
   *  claim about the operand's layer cascade and `demandExtra` must carry it — otherwise the meet can put
   *  the whole-region price below the counted total, which is exactly what two corpus programs did.
   *
   *  BUT ONLY WHEN THERE IS A CASCADE.  If the operand is itself a demand leaf, `transpileZ` hands back a
   *  concrete `Lit` (a mention, a literal, a singleton) or an `evalI` result already accounted in
   *  `handedOff`, and `materialize` then returns that trie BY POINTER without one cursor read.  Charging
   *  the operand there would double-count `handedOff` and re-import `ZipperCost.mention`'s eager
   *  `4 · N(operand)` — measured: it doubled `range/full`'s predicted `Work` and took `tails-inter`'s
   *  operator width from 197.67 to 1901 for no soundness gain at all. */
  private def belowLeaf(operand: Space, c: CostInterval, model: CostModel, st: State): CostInterval =
    if model.demandDriven && !demandLeaf(operand) then st.demandExtra = st.demandExtra + c
    c

  /** ONE OPERAND'S PER-DEPTH PROFILE, as `SpatialDemand.Layers`, read off the spatial product.  `None`
   *  when no finite profile exists — an unbounded length, a truncated profile, a saturated count — in
   *  which case no demand price is claimed at all rather than a wrong one.
   *
   *  ==THE TERMINAL COUNT IS A DIFFERENCE, NOT A `min`==
   *  `Layers.termsAt(d)` is an upper bound on how many depth-`d` trie nodes are TERMINAL, and a
   *  terminal depth-`d` node is exactly a path of length EXACTLY `d`.  This used to read
   *  `min(K_d.hi, E_d.hi)`, but `SpatialFacts.pathsAtDepth` defines `E_d = |{p ∈ V : |p| ≥ d}|` — the
   *  paths that REACH depth `d`, not the ones that STOP there — so on any value whose paths all have
   *  the same length that bound was `K_d` at EVERY depth: "every node of every level may be terminal".
   *  On the operator table's `b` (16 paths, 4 heads, depth 2, declared exactly) it read `T = [1,4,16]`
   *  against a truth of `[0,0,16]`.
   *
   *  The identity is the one [[SpatialFacts.interiorNodes]] already argues for LEAVES:
   *
   *      terminals(d) = |{p : |p| = d}| = E_d − E_{d+1}
   *
   *  whose sound UPPER endpoint reads the minuend high and the subtrahend LOW — `E_d.hi − E_{d+1}.lo`
   *  — because those are the two readings that can hold simultaneously for one concrete member
   *  (LESSON 9: every input is read in the direction that weakens the claim).  Clamped at 0, and still
   *  capped by `K_d` since a terminal node is a depth-`d` prefix.  `pathsAtDepth`'s LOWER endpoint is a
   *  must count — see its scaladoc for the care the spill bucket needs — so subtracting it is sound.
   *  A profile that is `truncated` is rejected above, so `p.paths(d+1)` past `lastDepth` is `Ivl.zero`
   *  and the deepest level keeps its full `E_d`.
   *
   *  This only ever LOWERS `termsAt`, and `termsAt` is consumed as an upper bound everywhere
   *  (`SpatialDemand.terminalCount`) plus, guarded by `Layers.exact`, as a floor in
   *  `terminalCountLo` — which `layersOf` never sets, so no lower endpoint moves. */
  private def layersOf(t: SpatialType, env: Env): Option[Layers] =
    if t.isProvablyEmpty then Some(Layers.empty)
    else if t.len.isEmpty then Some(Layers.empty)
    else if t.len.hi >= LenBounds.INF then None
    else
      SpatialFacts.profile(t, env.frontierConfig.facts).toOption.flatMap { p =>
        if p.truncated then None
        else
          val d = p.lastDepth
          val ks = Vector.tabulate(d + 1)(i => p.prefixes(i).hi)
          val esHi = Vector.tabulate(d + 2)(i => p.paths(i).hi)
          val esLo = Vector.tabulate(d + 2)(i => p.paths(i).lo)
          // E_d.hi − E_{d+1}.lo, clamped at 0; `∞` minuend stays `∞` and the `K_d` cap then decides
          def termsHi(i: Int): Long =
            if esHi(i) >= Ivl.INF then Ivl.INF
            else math.max(0L, esHi(i) - math.min(esLo(i + 1), esHi(i)))
          if ks.exists(_ >= Ivl.INF) then None
          else Some(Layers(ks,
                           Vector.tabulate(d + 1)(i => math.min(ks(i), termsHi(i))),
                           Vector.tabulate(d + 1)(i => if i + 1 <= d then ks(i + 1) else 0L),
                           exact = false))
      }

  /** THE DEMAND SUMMARY OF THE WHOLE FUSED REGION.  Top-down over a demanded-prefix profile and layer
   *  count, exactly as the review prescribes: no `SpaceZipper` is ever built, `children` /
   *  `terminal` / `descend` are never called, nothing is evaluated.  `None` whenever a leaf's profile is
   *  not finitely known — the per-operator sum then stands alone. */
  private def demandOf(s: Space, env: Env, st: State): Option[DemandSummary] =
    val leaves = collection.mutable.Map.empty[Space, Layers]
    var ok = true
    def collect(x: Space, id: NodeId): Unit =
      if ok then
        if demandLeaf(x) then
          if !leaves.contains(x) then
            decoratedAt(x, env, id).orElse(shapeAt(x, env, st)).flatMap(t => layersOf(t, env)) match
              case Some(l) => leaves(x) = l
              case None => ok = false
        else SpatialAnalysis.childrenOf(x).zipWithIndex.foreach((k, i) => collect(k, id.child(i)))
    collect(s, NodeId(Vector.empty))
    if !ok then None
    else
      // THE RELATIONAL SIBLING FACT, reused from the frontier summaries the traversal already computed.
      def pairing(a: Space, b: Space): Pairing =
        if SpatialFrontier.sameObject(a, b) then Pairing.identical
        else st.relCache.get((a, b)) match
          case Some(f) if !f.isFallback && !f.depth.truncated &&
                          f.depth.paired.forall(_.hi < Ivl.INF) =>
            Pairing(Some(f.depth.paired.map(_.hi)), same = false, exact = false)
          case _ => Pairing.unknown
      try Some(SpatialDemand.analyze(SpatialDemand.fromSpace(s, x => leaves.getOrElse(x, Layers.empty), pairing)))
      catch case scala.util.control.NonFatal(_) => None

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
   *  `sliceRange`/`ITrie.range` then return their input unchanged.  This is the predicate the review
   *  finding 2 needs: a full `Range` is an identity, so the model may not charge a sort for it, and
   *  the reference backend's warm work for it must not grow with `|x|`. */
  private[morkl] def rangeIsIdentity(lo: Int, hi: Int): Boolean = (lo == 0 || lo == 1) && hi == 0

  /** Do two operands denote the SAME already-materialised object at run time, so a pointer-identity
   *  short circuit fires?  `ITrie.union`/`intersection`/`subtraction` test `a eq b`, and
   *  `SpaceZipper.sameSpace` tests `Lit(s) eq Lit(t)`.  That holds for a repeated `Mention` (the same
   *  trie out of the context), a repeated `Literal` (the `iLiteral` memo cache returns the same
   *  object) and `Empty`.  It does NOT hold for a repeated `Singleton` or a repeated compound: those
   *  build a fresh object each time. */
  private[morkl] def sharedOperands(a: Space, b: Space): Boolean = (a, b) match
    case (Space.Empty, Space.Empty) => true
    case (Space.Mention(x), Space.Mention(y)) => x == y
    // OBJECT IDENTITY, NOT STRUCTURAL EQUALITY, ON A LITERAL.  `iLiteral` is keyed by an
    // `IdentityHashMap` over the `SpaceValue`, so two DISTINCT but equal `SpaceValue`s build two
    // DISTINCT tries and `a eq b` is false at run time.  Claiming the pointer-identity fast path for
    // them predicted less work than the executor performs — the same rule
    // `SpatialFrontier.sameObject` uses, and a soundness fix rather than a tightening.
    case (Space.Literal(x), Space.Literal(y)) => x eq y
    case _ => false

  /** ==============================================================================================
   *  THE OBJECTS THIS TERM'S VALUE MAY SHARE `ITrie` NODES WITH — the MAY analysis [[Shares]]
   *  documents, and the side condition [[TrieAlgebraCost.priced]]'s must-paired `touch` floor needs on
   *  top of `mustDescend`.
   *
   *  Every rule below is read off an executable, and every rule is an over-approximation of the node
   *  set, never of the skip.  The ring operations are persistent and hand whole subtries back by
   *  POINTER (`unionR`'s `rIdent(LEFT)`, `diffTries`' `took(); a`, `restrictTries`' `if r eq w2 then p`),
   *  so a binary node's value can hold nodes of EITHER operand and the rule is the `lub` of the two —
   *  including for the one-sided-looking ops, because `restrictTries` really can return the PREFIX
   *  map.  `Wrap`/`Unwrap`/`TailsUnion`/`TailsIntersection`/`Range` graft, focus, join or slice their
   *  source and reuse its subtries, so they inherit its bases and add none.
   *
   *  `Singleton` is fresh (`ITrie.singleton` folds `ITrie.node` over interned ids), `Empty` is the
   *  shared `ITrie.empty` — which no caller of `priced` can reach, every one of them having proved both
   *  operands non-empty first.  A `Literal`'s base is its `SpaceValue` under STRUCTURAL equality, not
   *  identity: `evalI`'s `iLiteral` is an `IdentityHashMap` and would justify identity, but `execT`
   *  decodes through the process-wide STRING-keyed `iConstStrCache`/`iLiteralStr`, where two distinct
   *  but equal values do come back as one object.  Merging them is the conservative reading and the
   *  only one sound on all three executables.
   *
   *  `Iteration` binds `rest` to an `ITrie` child of its source (`ic.updated(rest, sub)`), so the body
   *  is analysed with that alias installed — a name-only test would call `Intersection(rest, a)`
   *  share-free when `rest` IS a subtrie of `a`.  `Fixpoint` is the same shape one level up: the value
   *  is `init ∪ body[init] ∪ …`, so its bases are `init`'s together with the body's non-recursive ones,
   *  which is what binding the recursion mention to [[Shares.fresh]] and taking the `lub` computes (the
   *  rules are all unions, so that assignment deletes exactly the recursive contribution, and the
   *  induction `bases(cur_{k+1}) ⊆ bases(init) ∪ B` closes).
   *
   *  Everything else — `Call`, `Fold`, the grounded host escapes — is [[Shares.any]].  A routine body
   *  is priced through the `Call` arm with the callee's parameters bound to the ARGUMENTS' bases, so an
   *  inlined body keeps its floors; an opaque answer only ever refuses a claim.
   *
   *  BOUNDED, because it is called once per binary node and walks that node's whole subterm: a
   *  pathological term would make the pass quadratic in a hook that has to stay hot.  The budget is
   *  spent per top-level query and returns [[Shares.any]] when it runs out, which refuses a claim and
   *  never grants one — the same direction every other rule here fails in. */
  private val ShareBudget = 4096

  private[morkl] def sharesOf(s: Space, env: Env): Shares =
    var left = ShareBudget
    def go(x: Space, e: Env): Shares =
      left -= 1
      if left <= 0 then Shares.any else sharesNode(x, e, go)
    go(s, env)

  private def sharesNode(s: Space, env: Env, rec: (Space, Env) => Shares): Shares = s match
    case Space.Empty => Shares.fresh
    case Space.Singleton(_) => Shares.fresh
    case Space.Literal(v) => Shares.of(v)
    case Space.Mention(m) =>
      if env.bound.contains(m) then env.share.getOrElse(m, Shares.any) else Shares.of(m)
    case Space.Union(x, y) => rec(x, env) lub rec(y, env)
    case Space.Intersection(x, y) => rec(x, env) lub rec(y, env)
    case Space.Subtraction(x, y) => rec(x, env) lub rec(y, env)
    case Space.Restriction(x, y) => rec(x, env) lub rec(y, env)
    case Space.Raffination(x, y) => rec(x, env) lub rec(y, env)
    case Space.Composition(x, y) => rec(x, env) lub rec(y, env)
    case Space.Wrap(src, _) => rec(src, env)
    case Space.Unwrap(src, _) => rec(src, env)
    case Space.TailsUnion(src) => rec(src, env)
    case Space.TailsIntersection(src) => rec(src, env)
    case Space.Range(x, _, _) => rec(x, env)
    case Space.Iteration(src, _, rest, body) => rec(body, env.bindShare(rest, rec(src, env)))
    case Space.Fixpoint(init, recm, body) =>
      rec(init, env) lub rec(body, env.bindShare(recm, Shares.fresh))
    case Space.Fold(_, _, _, _, _, _, _) => Shares.any
    case Space.Call(_, _, _) => Shares.any
    case Space.GroundedPS(_, _) => Shares.any
    case Space.GroundedSS(_, _) => Shares.any

  /** Does `transpileZ` produce a CONCRETE `SpaceZipper.Lit` cursor for this term?  If so
   *  `materialize` hands the existing trie straight back and allocates nothing.  Read off
   *  `transpileZ`'s arms: `Empty`/`Singleton`/`Literal`/`Mention`/`Range` lift with `traversal`, the
   *  control-flow fallback re-lifts an `evalI` result with `traversal`, `unwrap` folds `descend`
   *  (which keeps a `Lit` a `Lit`), and the `x∪x`/`x∩x`/`x∖x` smart constructors return an operand. */
  /** THE STRICT HALF OF [[liftsToLit]]: `transpileZ` wraps an ITrie THAT ALREADY EXISTS, so
   *  `materialize` hands it back with no `FreshNode` at all.  Only a bare `Mention` (the caller's own
   *  object, or a binder's subtrie of it) and `Empty` (the shared `ITrie.empty`) qualify.  A
   *  `Singleton`, a `Literal` and a nested `Range` all BUILD their trie during the lift, which is what
   *  the counted oracle said when the whole of `liftsToLit` was used here. */
  private[morkl] def pointerLit(s: Space): Boolean = s match
    case Space.Empty | Space.Mention(_) => true
    case _ => false

  /** THE MUST-`Lit` SUBSET OF [[liftsToLit]], and the difference is not pedantry.
   *
   *  `liftsToLit` also admits `Union`/`Intersection`/`Subtraction` over SHARED OPERANDS, where the
   *  cursor is a `Lit` only if `SpaceZipper.sameSpace` actually fires — and it fires on POINTER
   *  identity, so `Singleton(p) ∪ Singleton(p)` lifts to two DIFFERENT `ITrie.singleton` objects and
   *  the cursor is a `Union` after all.  That is fine for the transfers that use `liftsToLit` to skip
   *  a walk they would otherwise over-charge, and NOT fine for a claim that reads "and therefore every
   *  child cursor below is a `Lit` too" — which is what [[ZipperCost.tailsUnion]]'s key-disjoint
   *  collapse needs.  Every arm below is a `traversal(...)` (or a `descend` chain from one, and
   *  `Lit.descend` returns a `Lit` or `SpaceZipper.empty`), so it is a `Lit` unconditionally. */
  private[morkl] def mustLit(s: Space): Boolean = s match
    case Space.Empty | Space.Singleton(_) | Space.Literal(_) | Space.Mention(_) | Space.Range(_, _, _) => true
    case Space.Unwrap(src, _) => mustLit(src)
    case _ => isControlFlow(s)

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
  private def go(s: Space, env: Env, model: CostModel, st: State, depth: Int,
                 id: NodeId): (CostInterval, Meas) =
    if depth > MaxDepth then (CostInterval.unbounded(s"analysis depth cap ($MaxDepth) reached"), Meas.top)
    else model.controlFlowFallback match
      // execZ does not fuse control flow; it hands the whole subterm to evalI.  Pricing it with the
      // zipper's own local-algebra formulas would describe a program that never runs.
      case Some(fb) if isControlFlow(s) =>
        st.note(s"${model.name}: ${nodeName(s)} is NOT fused — transpileZ materialises it through evalI, " +
                s"so this subterm is priced with the ${fb.slug} model (ZipperFallbackToEvalI is counted)")
        val (c, m) = goNode(s, env, Backends.of(fb, model.phase), st, depth, id)
        val handed = c + model.fallbackEntry
        st.handedOff = st.handedOff + handed
        (handed, m)
      case _ => goNode(s, env, model, st, depth, id)

  private def goNode(s: Space, env: Env, model: CostModel, st: State, depth: Int,
                     id: NodeId): (CostInterval, Meas) =
    def rec(x: Space, i: Int) = go(x, env, model, st, depth + 1, id.child(i))
    def refineHere(m: Meas) = refine(m, s, env, st, id)
    val d = model.dispatch
    /** RECORD A CONTRIBUTION THE DEMAND ANALYSIS DOES NOT MODEL (see `State.demandExtra`). */
    def dext(ci: CostInterval): CostInterval =
      if model.demandDriven then st.demandExtra = st.demandExtra + ci
      ci
    // every node of the fused region is one `ZipperBuild`, which is structural and not cursor traffic
    dext(d)
    s match
      case Space.Empty => (d + dext(model.empty), Meas.empty)

      case Space.Literal(SpaceValue(ps)) =>
        val hs = ps.iterator.collect { case PathValue(h :: _) => h }.toSet
        val m = Meas.exact(Sym.c(ps.size.toLong),
                           Sym.c(if ps.isEmpty then 0L else ps.iterator.map(_.items.length.toLong).max),
                           Sym.c(hs.size.toLong)).copy(headKeys = Some(hs))
        (d + dext(model.literal(m)), m)

      case Space.Singleton(p) =>
        val lp = plen(p, env)
        (d + dext(pathCost(p, model) + model.singleton(lp)),
         Meas(Sym.one, lp, Sym.one, Sym.one, Sym.one))

      case Space.Mention(m) =>
        val base = mentionMeas(m, env)
        // THE COUNT-CACHE STATE OF A MENTION (see `Meas.countKnown`).  A DECLARED INPUT of the term being
        // priced is an object the caller already holds; in the `Warm` phase this executable has already
        // run on it, and a run is a function of the program and its inputs, so every `ITrie.count` the
        // warm run forces was already forced — and memoised on the shared nodes — by the cold one.  A
        // BINDER-BOUND mention keeps whatever state its binder recorded, which is the value it aliases.
        val mm = refineHere(base).copy(
          countKnown = base.countKnown ||
            (model.phase == ExecutionPhase.Warm && !env.bound.contains(m)))
        // ONLY THE DISPATCH IS `demandExtra`.  `ZipperCost.mention` is `4 · N(operand)` CURSOR READS —
        // "the parent layer might read every node of me" — and cursor reads are precisely what the demand
        // analysis derives from the consumer's demand.  Accumulating the eager form here put a term linear
        // in every operand into `whole`, so the whole-region price could never come out below the eager
        // per-operator sum and `Cost.meetHi` always kept the eager number: that WAS LIM-1, and it is why
        // eleven flat families were predicted linear.  The dispatch itself (`ZipperBuild`, one per lifted
        // node) is structural, is not cursor traffic, and the demand summary makes no claim about it.
        (dext(model.mentionDispatch) + model.mention(mm), mm)

      case Space.Union(a, b) =>
        val (ca, ma) = rec(a, 0); val (cb, mb) = rec(b, 1)
        // |a ∪ b| ≥ max(|a|, |b|): the MAX of two sound lower bounds is a sound lower bound
        val m = refineHere(Meas(ma.size + mb.size, ma.len lub mb.len, ma.heads + mb.heads,
                                ma.sizeLo lub mb.sizeLo, ma.headsLo lub mb.headsLo))
        (d + ca + cb + model.union(ma, mb, relAt(FrontierOp.Union, a, b, ma, mb, env, st, id)), m)

      case Space.Intersection(a, b) =>
        val (ca, ma) = rec(a, 0); val (cb, mb) = rec(b, 1)
        val rel = relAt(FrontierOp.Intersection, a, b, ma, mb, env, st, id)
        // x ∩ x = x, so a shared operand carries its lower bound through; otherwise nothing is known
        val loSz = if rel.same then ma.sizeLo else Sym.zero
        val loHd = if rel.same then ma.headsLo else Sym.zero
        val m = refineHere(Meas(tighter(ma.size, mb.size), tighter(ma.len, mb.len),
                                tighter(ma.heads, mb.heads), loSz, loHd))
        (d + ca + cb + model.inter(ma, mb, rel), m)

      case Space.Subtraction(a, b) =>
        val (ca, ma) = rec(a, 0); val (cb, mb) = rec(b, 1)
        val rel = relAt(FrontierOp.Subtraction, a, b, ma, mb, env, st, id)
        // x ∖ x = ∅; a disjoint subtrahend removes nothing, so a's lower bound survives
        val loSz = if rel.same then Sym.zero else if rel.disjoint then ma.sizeLo else Sym.zero
        val m = refineHere(Meas(ma.size, ma.len, ma.heads, loSz, Sym.zero))
        (d + ca + cb + model.subtract(ma, mb, rel), m)

      case Space.Restriction(x, y) =>
        val (cx, mx) = rec(x, 0); val (cy, my) = rec(y, 1)
        val m = refineHere(Meas(mx.size, mx.len, mx.heads))
        (d + cx + cy + model.restrict(mx, my, relAt(FrontierOp.Restriction, x, y, mx, my, env, st, id)), m)

      case Space.Raffination(x, y) =>
        val (cx, mx) = rec(x, 0); val (cy, my) = rec(y, 1)
        val m = refineHere(Meas(mx.size, mx.len, mx.heads))
        // `eval` rewrites x \| y to Subtraction(x, Restriction(x, y)) and evaluates recs(x) TWICE;
        // the trie/graph executors evaluate x once and reuse the value.
        //
        // NOT `demandExtra`.  `transpileZ` lifts `x` ONCE (`raffination(transpileZ(x), transpileZ(y))`),
        // so the second charge is entirely the cursor traffic of reading the same cursor from two places,
        // and the demand analysis already carries `x` twice for exactly that reason (`ZIR.Raff` builds
        // `x` and `Res(x, y)`).  Accumulating it here would re-import the operand-linear term the
        // `Mention` case above stopped importing.
        // …AND HOW MUCH OF `cx` THE SECOND REFERENCE COSTS IS THE MODEL'S TO SAY, not a boolean's.
        // `execZ` shares ONE cursor between the two slots, so its lift — `ZipperBuild`s, `ITrie` calls
        // and the whole `evalI` fallback of a control-flow subterm inside `x`, ROUNDS INCLUDED — runs
        // once, while `eval` really re-runs `recs(x)`.  Charging `cx` twice for both put the zipper's
        // must side at twice the counted round total, and above its own `handedOff`-based upper: 13 of
        // the 44 residual corpus rows were INVERTED.  See `CostModel.raffinationSecondRead`.
        val xTwice = model.raffinationSecondRead(cx)
        (d + cx + xTwice + cy +
           model.raffine(mx, my, relAt(FrontierOp.Raffination, x, y, mx, my, env, st, id)), m)

      case Space.Composition(a, b) =>
        val (ca, ma) = rec(a, 0); val (cb, mb) = rec(b, 1)
        // concatenations of different pairs CAN collide ({a, a.b} x {b, ε}), so the only generic
        // lower bound is positivity
        val loSz = if ma.provablyNonEmpty && mb.provablyNonEmpty then Sym.one else Sym.zero
        val m = refineHere(Meas(ma.size * mb.size, ma.len + mb.len, ma.heads + mb.heads, loSz, Sym.zero))
        // AT THE ROOT — and only at the root — the term IS what the executable is handed, so a
        // materialisation floor is available to a demand-driven model; see `CostModel.composeRoot`.
        val cmp = relAt(FrontierOp.Composition, a, b, ma, mb, env, st, id)
        val price = if depth == 0 then model.composeRoot(ma, mb, cmp) else model.compose(ma, mb, cmp)
        (d + ca + cb + price, m)

      case Space.Wrap(src, p) =>
        val (cs, ms) = rec(src, 0)
        val lp = plen(p, env)
        val hd = if SpatialTypes.pathLen(p, env.facts.lengths).lo >= 1 then Sym.one else ms.heads
        // prefixing is INJECTIVE, so the source's lower bound carries through exactly
        val m = refineHere(Meas(ms.size, lp + ms.len, hd, ms.sizeLo, Sym.zero))
        (d + cs + dext(pathCost(p, model)) + model.wrap(ms, lp), m)

      case Space.Unwrap(src, p) =>
        val (cs, ms) = rec(src, 0)
        val lp = plen(p, env)
        val m = refineHere(Meas(ms.size, ms.len, ms.size))
        (d + cs + dext(pathCost(p, model)) + model.unwrap(ms, lp), m)

      case Space.TailsUnion(src) =>
        val (cs, ms0) = rec(src, 0)
        // `Meas.concrete` is the channel `ZipperCost.tailsUnion` reads to know that the reduce's
        // operands — `src.children` — are `Lit` cursors over the SOURCE'S OWN trie, so their key sets
        // are the value's own and the shape's `possibleHeads` bounds them.  [[mustLit]], not
        // `liftsToLit`: see the note there.
        val ms = ms0.copy(concrete = mustLit(src))
        val m = refineHere(Meas(ms.size, ms.len, ms.size))
        (d + cs + model.tailsUnion(ms, forced = depth == 0), m)

      case Space.TailsIntersection(src) =>
        val (cs, ms) = rec(src, 0)
        val m = refineHere(Meas(ms.size, ms.len, ms.size))
        // `belowLeaf(src, cs)` — SEE THE `Range` CASE BELOW.  The demand walk stops at this node, so the
        // demand price says nothing about `src`'s fused algebra, yet `TailsIntersection(transpileZ(src))`
        // materialises `src` through the cursor and every layer of it emits real reads.
        (d + belowLeaf(src, cs, model, st) + dext(model.tailsInter(ms, forced = depth == 0)), m)

      case Space.Range(x, lo, hi) =>
        val (cx, mx0) = rec(x, 0)
        // `liftsToLit` decides statically whether the ZIPPER's `materialize` will hand back an
        // existing trie (zero fresh nodes, zero cursor reads) instead of walking one into being; the
        // trie/graph models ignore the channel, so this is sound for all four.
        val mx = mx0.copy(concrete = liftsToLit(x), pointerLit = pointerLit(x))
        val w = rangeWindow(lo, hi)
        val ident = rangeIsIdentity(lo, hi)
        // THE ONE PIECE OF REAL WORK THIS OPERATOR PERFORMS WITH NO ORACLE, declared rather than
        // charged: `touch` is defined as `TrieNodeVisit + PatriciaVisit`, and `IntTrie.ordered`'s
        // canonical child-key sort emits neither.  It is memoised per node object in a bounded
        // identity map, so it is also not a per-visit cost — but the honest statement is that it is
        // outside the counted unit, not that it is free.
        if !ident then
          st.note("ITrie.range's canonical child-key order (IntTrie.ordered) is memoised per node " +
                  "object and emits NO counted event; its heads·log(heads) is therefore OUTSIDE " +
                  "`touch`, which is defined by TrieNodeVisit + PatriciaVisit.  `slice` also uses " +
                  "plain IntMap ops rather than the instrumented IntTrieOps, so it emits no " +
                  "PatriciaVisit and the tPer=3 per-node multiplier does not apply to this operator.")
        // a full window is the IDENTITY: the size bound (both endpoints) passes straight through
        val m = if ident then refineHere(mx)
                else refineHere(Meas(tighter(mx.size, w), mx.len, tighter(mx.heads, w)))
        // THE OPERAND'S COST IS `demandExtra`, AND THIS IS A DEMAND-LEAF BOUNDARY, NOT AN OPERATOR RULE.
        // `SpatialDemand.demandLeaf(Range)` is true, so `fromSpace` lifts this node as a `Lit` and the
        // demand walk NEVER ENTERS `x` — while `transpileZ` really does build a fused cursor for `x` and
        // `materialize` it (`ITrie.range(materialize(transpileZ(x)), lo, hi)`), so `x`'s layer cascade
        // emits ZipperCursorReads and ZipperMaterializeNodes that the demand price makes no claim about.
        // Leaving `cx` out of `demandExtra` was sound only while the eager slack elsewhere kept the meet
        // from binding; with the price quoted in the counted unit the meet DOES bind, and two corpus
        // programs — both a fused subterm under a `Range` — came out at work 84 against a counted 88 and
        // work 61 against 65.  The rule is structural: whatever is below a demand leaf is `demandExtra`'s.
        (d + belowLeaf(x, cx, model, st) + dext(model.range(mx, w, ident)), m)

      // ---- THE LOOPS ---------------------------------------------------------------------------
      // THE REST-CHAIN FRAME LAW COMES FIRST.  A rest-chained nest is
      // priced as ONE transfer from the source's prefix profile — `frames = Σ K_d`, `leaves = K_D`,
      // `visits = Σ E_d` — BEFORE the generic transfer recursively multiplies independent per-level
      // group maxima.  That product is what turned 122 counted rounds into 390,580 and then, on a
      // 16-level nest, into `inf`; and because the whole nest costs one level of recursion here, the
      // 16-deep `puzzle15` term also stops hitting the AST depth cap.
      case it @ Space.Iteration(src, _, _, _) if chainOf(it, env, st, id).isDefined =>
        val ch = chainOf(it, env, st, id).get
        st.chainNests += 1
        st.note(ch.note)
        val (cs, _) = rec(src, 0)
        val (cl, ml) = go(ch.chain.leaf, ch.leafEnv(env, st), model, st, depth + 1, ch.leafId(id))
        // the result is the union over the leaf invocations, so its cardinality is `K_D · |leaf|` and
        // the only generic lower bound is positivity (different source paths' outputs can collide)
        val m = refineHere(Meas(ch.leaves * ml.size, ml.len, ch.leaves * ml.size))
        // the leaf runs at most `leaves = K_D` times — NOT `Π K_d` times — and one dispatch per FRAME is
        // charged by `chainNest`, which also carries the `rounds` component
        val cost = d + cs + model.loopPrologue.scale(Sym.one, ch.depthSym) +
                   model.chainNest(ch.frames, ch.leaves, ch.visits, ch.depthSym, ml) +
                   cl.scale(ch.leavesLo, ch.leaves) +
                   model.collectJoin(ch.leaves, ch.leavesLo, ml, single = false)
        (cost, m)

      case Space.Iteration(src, sym, rest, body) =>
        val (cs, ms) = rec(src, 0)
        val groups = ms.heads                                  // the GROUP COUNT is the head count
        val groupsLo = ms.headsLo
        val benv = loopEnv(env, src, ms, sym, rest, st)
        val (cb, mb) = go(body, benv, model, st, depth + 1, id.child(1))
        val m = refineHere(Meas(groups * mb.size, mb.len, groups * mb.size))
        // ITERATION ACCUMULATES WITH `joinAll`, an n-ary simultaneous pass, NOT the left fold `Fold`
        // uses — the requirement: "Split them."
        val cost = d + cs + model.loopPrologue + model.group(ms) + cb.scale(groupsLo, groups) +
                   model.collectJoin(groups, groupsLo, mb) + CostInterval(Cost.r(groupsLo), Cost.r(groups))
        (cost, m)

      case Space.Fold(src, initial, acc, sym, rest, body, update) =>
        val (cs, ms) = rec(src, 0)
        val groups = ms.heads
        val groupsLo = ms.headsLo
        val benv0 = loopEnv(env, src, ms, sym, rest, st)
        val benv = benv0.copy(paths = benv0.paths + (acc -> Sym.v(s"|acc:${acc.s}|")))
        val (cb, mb) = go(body, benv, model, st, depth + 1, id.child(1))
        val m = refineHere(Meas(groups * mb.size, mb.len, groups * mb.size))
        val seed = CostInterval(Cost.zero, Cost.of(alloc = Sym.one)) + pathCost(initial, model)
        val cost = d + cs + model.loopPrologue + model.group(ms) + cb.scale(groupsLo, groups) +
                   model.collect(groups, mb) + seed +
                   model.foldStep(groups, Sym.c(pathNodeCount(update)), plen(update, benv)) +
                   CostInterval(Cost.r(groupsLo), Cost.r(groups))
        (cost, m)

      case f @ Space.Fixpoint(init, recm, body) =>
        val (ci, mi) = rec(init, 0)
        val self = refineHere(Meas(Sym.v(s"|fix:${recm.s}|"), Sym.v(s"len(fix:${recm.s})"),
                                   Sym.v(s"|fix:${recm.s}|")))
        val (roundsLo, rounds) = fixRoundsIvl(f, env, st, self, mi.sizeLo)
        // every iterate is a subset of the accumulated result, so `self` bounds each of them
        // the iterate is BUILT by this run, so its per-node counts are `CountUnknown` (the default)
        // THE ITERATE'S BASES, for the share analysis: `cur` starts at the seed object and every later
        // round is `body[cur]`, so the nodes it can hold are the seed's together with the body's
        // NON-recursive ones.  `sharesOf(f, env)` computes exactly that (see its rule for `Fixpoint`),
        // and it is the alias the `self`-priced rounds must reason under — round `k > 1`'s recursion
        // variable really can be pointer-shared with a body operand over the seed.
        val selfShares = sharesOf(f, env)
        val benv = env.copy(spaces = env.spaces + (recm -> self), bound = env.bound + recm,
                            share = env.share + (recm -> selfShares),
                            facts = env.facts.copy(spaces = env.facts.spaces + (recm -> typeAt(f, env, st))))
        val (cb, mb) = go(body, benv, model, st, depth + 1, id.child(1))
        // THE FIRST ROUND'S RECURSION VARIABLE IS THE SEED, EXACTLY — and `self` is only an
        // over-approximation of it.  All three executables open the loop the same way:
        // `var cur = evalI(init)` / `var cur = recs(init)` / `var cur = sg.root.inputs(0).sget`, and
        // the FIRST `evalI(body)(ic.updated(rec, cur))` therefore runs with `rec` bound to the seed
        // OBJECT.  Pricing that round with `mi` — the measure this arm already computed for `init` —
        // is not a tightening heuristic, it is the value the executable binds.
        //
        // WHY IT MOVES THE INTERVAL AND `self` CANNOT: the seed is a DECLARED input with must-present
        // structure, where the bound recursion mention's decorated type is may-only (`SizeBounds(0,0,·)`
        // and a `?` shape at every prefix — a fixpoint's result is not known to contain anything).  A
        // may-only left operand gives `SpatialFrontier`'s paired frontier a lower endpoint of 1 (the
        // root pair and nothing more), so the whole loop's `touch` floor was one visit; with the seed's
        // own type the round-1 body is the same must-paired frontier a top-level binary node gets.
        // THE DECORATION IS DROPPED for this pricing on purpose: `decoratedAt` answers from the
        // NodeId-indexed analysis, which decorated `Mention(rec)` under the analysis's own binder
        // environment, and it would override the seed facts installed here.
        //
        // BOTH ENDPOINTS ARE NOW TAKEN FROM THE SEED-PRICED ROUND, and the history of that line is the
        // argument for it.  `CostInterval.meet` joins the LOWER endpoints too, and that installs, as the
        // fixpoint's floor, whatever `priced` claims for the body when `rec` carries the seed's EXACT
        // measure — which is `fs.descentsLo`, the must-paired count.  On its first draft that was
        // UNSOUND, and the reason was not this arm: `priced`'s side condition was `mustDescend` alone,
        // a pure cardinality test that discharges the ROOT `a eq b` and says NOTHING about the
        // recursive pointer-identity short circuits (`unionR`'s `a eq b` at every level,
        // `IntTrieOps.unionTries`' `if a eq b then a` on whole child maps).  Round 1 is the worst
        // possible place to meet that hole: `var cur = evalI(init)` IS the caller's own trie by pointer
        // when `init` is a mention, and the body's sibling operand is commonly a term over the same
        // input that the algebra hands back by pointer — the semi-naive Datalog shape.  Measured then,
        // on `Fixpoint(a, r, Union(r, Restriction(a, {h0})))` with `a` declared exactly: the joined
        // floor claimed `touch >= 11` against a counted 4, and nine rows over four fixpoint fixtures
        // went from inside the interval to outside.
        //
        // THE HOLE IS NOW CLOSED WHERE IT LIVED.  `priced` conjoins `Rel.mayShare`, so the must-paired
        // count is refused for exactly the operand pairs that can share an `ITrie` node — and the
        // round-1 environment installs the SEED's own bases for `rec` (`share + (recm -> sharesOf(init,
        // env))` below), which is what makes `Union(rec, Restriction(a, {h0}))` read as a sharing pair
        // on round 1 instead of a disjoint one.  The four fixtures that refuted the first draft
        // (`fx-shrA`, `fx-shr2`, `fx-sharesl`, `fx-sharesl-i`) stay inside their intervals with the
        // meet restored, and the standalone `S"a" ∪ (S"a" <| {h0})` — outside its interval on pristine
        // source, with no fixpoint anywhere in it — is inside again.  What the meet buys back is the
        // `touch` WIDTH: the shipped table's `fixpoint` row went `[1, 691]` (width 346, RED on all
        // three trie-shaped executables) to `[13, 691]` (width 49.4, inside the 64 budget).
        val cbFirst =
          if st.seedRounds <= 0 then cb
          else
            st.seedRounds -= 1
            // ROUND 1's RECURSION VARIABLE IS THE SEED OBJECT, so its bases are the SEED's and not the
            // whole iterate's — `var cur = evalI(init)` binds `rec` to that object by pointer, which is
            // both why the measure `mi` is exact here and why the share answer is `sharesOf(init)`.
            val benv1 = env.copy(spaces = env.spaces + (recm -> mi), bound = env.bound + recm,
                                 share = env.share + (recm -> sharesOf(init, env)),
                                 facts = env.facts.copy(
                                   spaces = env.facts.spaces + (recm -> typeAt(init, env, st))))
                           .withoutDecorated
            val raw = go(body, benv1, model, st, depth + 1, id.child(1))._1
            CostInterval.meet(raw, cb)
        val m = refineHere(Meas(rounds * mb.size + mi.size, mi.len lub mb.len,
                                rounds * mb.size + mi.size, mi.sizeLo, Sym.zero))
        // THE FIXPOINT'S UNION IS PRICED BY THE CHANGED FRONTIER:
        // an ABSORBED iterate is `Identity(LEFT)` and rebuilds nothing, which is exactly what makes the
        // terminating round free.  `Rel` here is the accumulator-against-iterate summary.
        val fixRel = fixpointRel(f, env, st, id, body)
        // AT LEAST `roundsLo` ROUNDS RUN, and the loop must evaluate the body once whatever happens
        // (the terminating round is counted by `FixpointRound`).  The body's must cost therefore
        // scales by `roundsLo`, not by 1 — with an IDEMPOTENT step that is the difference between a
        // `[1, 73]` round interval and a `[1, 2]` one, and the interval WIDTH of a fixpoint is the
        // width of its round bound on every one of the four components.
        //
        // `fixStep` NOW SCALES BY THE FULL `[roundsLo, rounds]`.  The loop used to keep a side
        // accumulator and merge only in the `else` branch, so the convergence-detecting round did no
        // merge and `R` rounds performed `R - 1` of them.  The loop now iterates `cur := cur ∪ F(cur)`
        // — the union IS the iteration step, which is what makes the operator inflationary and the
        // limit the least post-fixpoint (terminating/fixpoint_is_lfp.smt2, O1) — so the merge happens
        // in EVERY round, the last one included.  Charging `R - 1` here would under-price every
        // fixpoint by one whole accumulating merge.
        //
        // The BODY still scales by the full `[roundsLo, rounds]` — it is evaluated on the terminating
        // round too — with round 1 taken out and priced against the seed (`cbFirst`), so the remaining
        // `self`-priced rounds are `R - 1` of them.  `model.fixRound` is what a round performs
        // unconditionally and keeps the full `[roundsLo, rounds]` multiplicity, as `fixStep` now does.
        val stepLo = Sym.monus(roundsLo, Sym.one)
        val stepHi = Sym.monus(rounds, Sym.one)
        val cost = d + model.fixPrologue + ci + cbFirst + cb.scale(stepLo, stepHi) +
                   model.fixStep(self, mb, fixRel).scale(roundsLo, rounds) +
                   model.fixRound(self, mb).scale(roundsLo, rounds) +
                   CostInterval(Cost.r(roundsLo), Cost.r(rounds))
        (cost, m)

      // ---- CALLS: inline, or solve the recurrence ------------------------------------------------
      case Space.Call(rp, refs, mentions) if env.active(rp) =>
        // A recursive occurrence: emit MARKER variables, which the enclosing inlining step reads back out
        // of the normalised polynomial as the recurrence's branching factor.
        //
        // THE ARGUMENT EXPRESSIONS ARE CHARGED HERE, and were not.  Every level of the recursion
        // re-evaluates them — for the semi-naive Datalog cornerstone they ARE the whole per-round delta
        // computation — so omitting them made the closed form's per-level constant `a` almost empty.  It
        // was invisible while the depth was unbounded, and became a 172-against-50 containment failure the
        // moment the universe summary bounded it.
        val argCosts = mentions.zipWithIndex.map((a, i) => go(a, env, model, st, depth + 1, id.child(i)))
        val marker = CostInterval(Cost.zero,
                      Cost(Amount.of(Sym.v(recWorkVar(rp))), Amount.of(Sym.v(recAllocVar(rp))),
                           Amount.of(Sym.v(recRoundVar(rp))), Amount.of(Sym.v(recTouchVar(rp)))))
        // THE RECURSIVE OCCURRENCE'S SIZE, from the spatial least fixpoint when one was derived — the
        // free `|rp()|` / `len(rp())` only when it was not.  The markers above stay symbolic either way:
        // they are the recurrence's unknown COST, which the enclosing arm closes.
        val selfM = st.selfResult.getOrElse(rp,
          Meas(Sym.v(s"|${rp.s}()|"), Sym.v(s"len(${rp.s}())"), Sym.v(s"|${rp.s}()|")))
        (argCosts.foldLeft(marker)((c, x) => c + x._1) +
           refs.foldLeft(CostInterval.zero)((c, p) => c + pathCost(p, model)), selfM)

      // `active.size` — not the AST depth — is the CALL depth, so a call deep inside a term is still
      // analysed interprocedurally; only genuinely nested routine bodies hit the cap
      case Space.Call(rp, refs, mentions) if env.routines.isDefinedAt(rp) && env.active.size < MaxInline =>
        val Routine(_, refns, mentionns, rbody) = env.routines(rp)
        val argCosts = mentions.zipWithIndex.map((a, i) => go(a, env, model, st, depth + 1, id.child(i)))
        val callee = Env(
          spaces = mentionns.zip(argCosts.map(_._2)).toMap,
          paths = refns.zip(refs.map(p => plen(p, env))).toMap,
          routines = env.routines, active = env.active + rp,
          // a parameter is BOUND here; the `Meas` it is bound to already carries the argument's own
          // count-cache state, so the mention arm reads it off that rather than re-deriving it
          bound = mentionns.toSet,
          // AND THE PARAMETER CARRIES THE ARGUMENT'S BASES.  `evalI`'s `Call` arm binds each parameter
          // to `evalI(m)` — the argument's own object — so two parameters bound to terms over one input
          // may share, and a parameter bound to a caller mention shares with that mention.  Without
          // this the callee's `share` map would be empty and every parameter opaque, which is sound but
          // would drop the must-paired floor on every inlined body.
          share = mentionns.zip(mentions.map(m => sharesOf(m, env))).toMap,
          facts = SpatialTyping.Env(
            spaces = mentionns.zip(mentions.map(a => typeAt(a, env, st))).toMap,
            paths = Map.empty,
            lenv = SpatialEnv(paths = refns.zip(refs.map(p => SpatialTypes.pathLen(p, env.facts.lengths))).toMap,
                              routines = env.routines)),
          shapeFacts = env.shapeFacts,
          // THE CALLEE'S BODY IS A DIFFERENT TREE: the decorated analysis's `NodeId`s do not address it,
          // so the index is dropped rather than misread (the `expression` guard would refuse anyway).
          decorated = None, frontierConfig = env.frontierConfig)
        // ---- THE SPATIAL LEAST FIXPOINT, SOLVED BEFORE THE BODY IS PRICED -------------------------
        // The body contains the recursive occurrence, and that occurrence's SIZE is what the fixpoint
        // supplies (see `State.selfResult`), so the order matters: solve, publish, then price.  All four
        // guards are syntactic and cheap, so a non-recursive call pays nothing.
        val accArg =
          if selfCalls(rbody, rp).isEmpty || !Recurrence.selfTerminating(rbody, rp) ||
             Recurrence.decreasingArg(rbody, rp, mentionns).isDefined then None
          else Recurrence.accumulatorArg(rbody, rp, mentionns)
        val paramFix: Either[String, ParamFix] =
          accArg.toRight("no monotone accumulator parameter")
                .flatMap(i => paramFixpoint(rp, i, mentions, refs, env, st))
        val savedSelf = st.selfResult.get(rp)
        paramFix.foreach(f => st.selfResult(rp) = refineWith(Meas.top, f.acc, env))
        val (cbody, mbody) = go(rbody, callee, model, st, depth + 1, NodeId(Vector.empty))
        savedSelf match
          case Some(m) => st.selfResult(rp) = m
          case None => st.selfResult.remove(rp)
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
              // NO LENGTH-DECREASING ARGUMENT, but a MONOTONE ACCUMULATOR under a `Union(_, Call)` body
              // proves termination: every continuing call adds at least one path.  What bounds the DEPTH
              // is [[paramFixpoint]] — the SPATIAL least fixpoint `T_{i+1} = T_i ⊔ F#(T_i)` over the
              // parameter tuple, solved above — and not a path-universe cardinality: the number of
              // continuing calls is at most the room the accumulator has to grow, `|acc∞| − |acc₀|`.
              (accArg, paramFix.toOption) match
                case (Some(i), Some(fx)) =>
                  val n = Sym.c(fx.depth)
                  st.note(s"recursive routine ${rp.s}: parameter $i " +
                          s"(${mentionns.lift(i).map(_.s).getOrElse("?")}) is a MONOTONE ACCUMULATOR under a " +
                          s"Union(_, Call) body, so every continuing call adds at least one path.  THE " +
                          s"SPATIAL LEAST FIXPOINT of the parameter tuple bounds that accumulator: " +
                          s"${fx.show}.  Counts, path lengths and the round count are derived from that " +
                          "post-fixpoint TYPE, not from the all-strings path universe (the review, " +
                          "the Datalog half).")
                  val closed = Recurrence.close(hi, recWorkVar(rp), recAllocVar(rp), recRoundVar(rp),
                                                recTouchVar(rp), n)
                  // THE CALL'S RESULT IS THE ACCUMULATOR AT THE FIXPOINT, so `fx.acc` bounds it directly;
                  // the propagated `n · |body|` is the other sound upper and the two are met.
                  (total + CostInterval(cbody.lo, closed) + model.callFrame.scale(Sym.one, n),
                   refineWith(Meas(n * mbody.size, mbody.len, n * mbody.size), fx.acc, env))
                case (Some(i), None) =>
                  val why = paramFix.left.getOrElse("?")
                  st.note(s"recursive routine ${rp.s}: parameter $i is a MONOTONE ACCUMULATOR, so the recursion " +
                          s"terminates, but the SPATIAL LEAST FIXPOINT of the parameter tuple failed: $why.  The " +
                          "depth is therefore not bounded — and the reason is a named limit of this fixpoint, " +
                          "not a shrug")
                  (total + CostInterval.unbounded(
                     s"recursion in ${rp.s}: monotone accumulator, spatial parameter fixpoint failed ($why)"),
                   Meas.top)
                case _ =>
                  st.note(s"recursive routine ${rp.s}: no argument provably loses an item per call and none is a " +
                          "monotone accumulator, so no recursion depth bound and no closed form")
                  (total + CostInterval.unbounded(
                     s"recursion in ${rp.s} without a decreasing measure"), Meas.top)
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
        (mentions.zipWithIndex.foldLeft(CostInterval.zero)((c, ai) =>
           c + go(ai._1, env, model, st, depth + 1, id.child(ai._2))._1) +
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
    // `rest` is one head group's tail set — an `ITrie` CHILD of the source, i.e. a shared subtrie, so it
    // INHERITS the source's count-cache state (`count` recurses and memoises every descendant).
    env.copy(spaces = if rest.s == "_" then env.spaces
                      else env.spaces + (rest -> Meas(ms.size, ms.len, ms.size, countKnown = ms.countKnown)),
             bound = if rest.s == "_" then env.bound else env.bound + rest,
             // `rest` IS an `ITrie` child of the source object, so it carries the source's bases: see
             // `evalI`'s `ic.updated(rest, sub)`.  Without this a body operand over `rest` would look
             // share-free against an operand over the source itself.
             share = if rest.s == "_" then env.share else env.share + (rest -> sharesOf(src, env)),
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

  /** THE FIXPOINT ROUND COUNT, as an INTERVAL.
   *
   *  `eval`'s fixpoint replaces the candidate each round (`cur := body(cur)`) and stops when it stops
   *  changing, so in general the round count is NOT bounded by the result size.  Three things make it
   *  bounded, and the previous revision used only the weakest of them.
   *
   *  1. MONOTONICITY, DECIDED AC-MODULO.  A body is an accumulator when the recursive mention is one
   *     of the operands of its UNION TOWER — `Union(Union(rec, a), b)` and `Union(a, Union(b, rec))`
   *     are as monotone as `Union(rec, a)`, and the old syntactic two-case match called both of them
   *     non-monotone and fell straight to a free variable.  `unionOperands` flattens the tower.
   *  2. THE SEED IS NOT PART OF THE GROWTH.  The chain `cur_{k+1} = F(cur_k) ⊇ cur_k` grows by at
   *     least one path per non-final round, so `R ≤ (|result|_hi − |init|_lo) + 1` — not
   *     `|result|_hi + 1`.  On the operator table's fixpoint that is 72 − 64 + 1 = 9 instead of 73.
   *     `Meas.sizeLo` is a LOWER bound and defaults to 0, so the subtraction can only help; it is
   *     guarded anyway (an `initLo` of 0 gives back exactly the old bound).
   *  3. AN IDEMPOTENT STEP RUNS TWICE, WHATEVER THE CARDINALITIES.  When the body is
   *     `Union(rec, E)` with `rec` NOT FREE IN `E` — checked with the binder-aware free-mention walk,
   *     not a syntactic top-level test, so a `Call`, a `GroundedSS` closure or a nested `Fixpoint`
   *     that hides an occurrence cannot fool it — then `F(F(x)) = F(x)` for every `x`.  The loop
   *     therefore runs ONE round when `E ⊆ init` and TWO otherwise: `rounds ∈ [1, 2]`, whatever
   *     `|result|` is.  That is the shape of every "accumulate a fixed set" fixpoint, and it is the
   *     one the operator table measures: counted `FixpointRound` = 2 against a predicted 73.
   *
   *  Returns `(lo, hi)`.  The lower endpoint matters as much as the upper: the interval WIDTH of a
   *  fixpoint is the width of its round bound, so a `[1, 73]` against a counted 2 is a 37x width on
   *  every one of the four components. */
  private def fixRoundsIvl(f: Space.Fixpoint, env: Env, st: State, self: Meas, initLo: Sym): (Sym, Sym) =
    val Space.Fixpoint(_, recm, body) = f
    val operands = unionOperands(body)
    val monotone = operands.exists { case Space.Mention(m) => m == recm; case _ => false }
    // the step's NON-RECURSIVE part: everything in the union tower other than the bare `rec` operand
    val rest = operands.filterNot { case Space.Mention(m) => m == recm; case _ => false }
    val idempotent = monotone && rest.forall(e => !freeMentions(e).contains(recm))
    if idempotent then
      st.note(s"fixpoint over ${recm.s}: the body is Union(${recm.s}, E) with ${recm.s} NOT free in E, " +
              "so the step is IDEMPOTENT (F(F(x)) = F(x)) and the loop runs at most TWO rounds — one " +
              "to add E, one to observe that nothing changed — whatever the cardinalities are")
      (Sym.one, Sym.c(2))
    else if monotone then
      // the accumulated result contains every iterate, and each non-final round adds >= 1 path
      val grown = if initLo == Sym.zero then self.size else Sym.monus(self.size, initLo)
      grown match
        case Sym.Const(n) => (Sym.one, Sym.c(n + 1))
        case Sym.Inf =>
          val v = st.nextVar("R")
          st.note(s"fixpoint over ${recm.s}: monotone accumulator but no finite bound on the result, so the " +
                  s"round count is the free variable $v")
          (Sym.one, Sym.v(v))
        case other =>
          st.note(s"fixpoint over ${recm.s}: monotone accumulator, so rounds <= |result| - |init| + 1 = " +
                  s"${(other + Sym.one).show}")
          (Sym.one, other + Sym.one)
    else
      val v = st.nextVar("R")
      st.note(s"fixpoint over ${recm.s}: the body's union tower does not contain the bare mention " +
              s"${recm.s}, so the accumulator is not provably monotone and no round bound is " +
              s"derivable; the round count is the free variable $v")
      (Sym.one, Sym.v(v))

  /** the operands of a UNION TOWER, flattened — `Union(Union(a, b), c)` gives `[a, b, c]`.  Union is
   *  associative and commutative, so monotonicity of an accumulator is an AC-modulo property and
   *  testing only the two top-level shapes missed every re-associated body. */
  private def unionOperands(s: Space): Vector[Space] = s match
    case Space.Union(a, b) => unionOperands(a) ++ unionOperands(b)
    case other => Vector(other)

  /** THE FIXPOINT'S CHANGED FRONTIER.  The accumulator against one
   *  iterate: an ABSORBED iterate is `Identity(LEFT)` and rebuilds nothing, an unchanged subtrie is
   *  reused by pointer, and only the CHANGED frontier is merged. */
  private def fixpointRel(f: Space.Fixpoint, env: Env, st: State, id: NodeId, body: Space): Rel =
    val fr =
      if !env.shapeFacts || st.frontierBudget <= 0 then None
      else
        val accT = decoratedAt(f, env, id).orElse(shapeAt(f, env, st))
        val itT = decoratedAt(body, env, id.child(1)).orElse(shapeAt(body, env, st))
        (accT, itT) match
          case (Some(a), Some(i)) =>
            st.frontierBudget -= 1
            Some(SpatialFrontier.fixpointUnion(a, i, shared = false, absorbed = false, env.frontierConfig))
          case _ => None
    val rel = Rel(fr, same = false, disjoint = false)
    st.recordRel(rel)
    rel

  // ================================================================================================
  // 6.  THE REST-CHAIN FRAME LAW  (the review — the Puzzle half)
  // ================================================================================================

  /** A RECOGNISED REST-CHAINED ITERATOR NEST, priced from the source's PREFIX PROFILE.
   *
   *  `frames = Σ_{d=1..D} K_d` is a STRUCTURAL IDENTITY, not an estimate: the level-`i` iteration groups
   *  the tails of one depth-`(i-1)` prefix, so its groups are exactly the depth-`i` prefixes extending
   *  it, and summing over the levels gives the total frame count.  `leaves = K_D` is the leaf invocation
   *  count and `visits = Σ E_d` the reference evaluator's `groupMap` visits.  What this replaces is
   *  `Π_{d} K_d` — `SpatialFacts.PrefixProfile.naiveProductBound`, which the profile itself documents as
   *  neither tight NOR sound — which the generic loop transfer produced by recursively multiplying the
   *  per-level group counts. */
  private final case class ChainCost(chain: RestChain, frames: Sym, leaves: Sym, leavesLo: Sym,
                                     visits: Sym, depthSym: Sym, srcMeas: Meas, note: String):
    def depth: Int = chain.depth
    /** the leaf sits at `child(1)` of every level, so its position is `1` repeated `depth` times */
    def leafId(root: NodeId): NodeId = (0 until depth).foldLeft(root)((n, _) => n.child(1))
    /** the leaf's environment: each head ref is ONE item, and each `rest` mention is over-approximated
     *  by the union of ALL tails (a sound MAY bound — one group's tails are a subset), with a ⊤ shape so
     *  no must claim leaks from a sibling group. */
    def leafEnv(env: Env, st: State): Env =
      var sp = env.spaces
      var fsp = env.facts.spaces
      var lenv = env.facts.lenv
      var ps = env.paths
      var bd = env.bound
      // every `rest` in the chain is a descendant subtrie of the chain's SOURCE object (each link's
      // source is the previous link's `rest`), so they all carry the source's bases — the same alias
      // `loopEnv` installs, transitively
      val srcShares = sharesOf(chain.source, env)
      var sh = env.share
      for l <- chain.links do
        if l.rest.s != "_" then
          sp = sp + (l.rest -> Meas(srcMeas.size, srcMeas.len, srcMeas.size,
                                    countKnown = srcMeas.countKnown))
          fsp = fsp + (l.rest -> SpatialType.top)
          bd = bd + l.rest
          sh = sh + (l.rest -> srcShares)
        lenv = lenv.withPath(l.head -> LenBounds(1, 1))
        ps = ps + (l.head -> Sym.one)
      env.copy(spaces = sp, paths = ps, bound = bd, share = sh,
               facts = env.facts.copy(spaces = fsp, lenv = lenv))

  private def chainOf(it: Space.Iteration, env: Env, st: State, id: NodeId): Option[ChainCost] =
    st.chainCache.getOrElseUpdate((it, id), computeChain(it, env, st, id))

  private def computeChain(it: Space.Iteration, env: Env, st: State, id: NodeId): Option[ChainCost] =
    RestChain.recognize(it).filter(_.depth >= 2).flatMap { ch =>
      // depth 1 is an ordinary `Iteration`: there is no product of independent per-level maxima to lose,
      // and the generic transfer's `heads`-scaled body cost is already the right shape.
      decoratedAt(ch.source, env, id.child(0)).orElse(shapeAt(ch.source, env, st)).flatMap { t =>
        SpatialFacts.profile(t, env.frontierConfig.facts).toOption.flatMap { p =>
          val dd = ch.depth
          val frames = p.frameEntries(dd)
          val leaves = p.prefixes(dd)
          val visits = p.groupingVisits(dd)
          if frames.hi >= Ivl.INF || leaves.hi >= Ivl.INF then None
          else
            val naive = p.naiveProductBound(dd)
            val note =
              s"rest-chain nest of depth $dd priced by the FRAME LAW: frames = Σ K_d = ${frames.show}, " +
              s"leafInvocations = K_$dd = ${leaves.show}, groupingVisits = Σ E_d = ${visits.show} — " +
              s"instead of the per-level product Π K_d = ${naive.show}, which the profile itself " +
              "documents as neither tight nor sound"
            Some(ChainCost(ch, symSize(frames.hi), symSize(leaves.hi), symLo(leaves.lo),
                           symSize(visits.hi), Sym.c(dd.toLong), refineWith(Meas.top, t, env), note))
        }
      }
    }

  // ================================================================================================
  // 7.  THE SPATIAL LEAST FIXPOINT OF A RECURSIVE ROUTINE'S PARAMETERS
  // ================================================================================================

  /** THE POST-FIXPOINT of the recursive parameter tuple, in the SPATIAL domain.
   *
   *  `T₀ = α(the actual arguments)`;  `T_{i+1} = T_i ⊔ F#(T_i)`, where `F#(T)` is the tuple of
   *  ABSTRACT TYPES of the self-call's argument expressions analysed with `parameters ↦ T`.  Iterated
   *  with [[SpatialRecursion.join]] and [[SpatialRecursion.widenType]] — the same join/widen order the
   *  interprocedural summary solver uses — until `F#(T) ⊑ T`, which IS the post-fixed-point property
   *  and is therefore the certification, not a schedule promise.
   *
   *  Every reachable value of parameter `j`, at EVERY recursion depth, lies in `γ(params(j))`: `T₀`
   *  covers depth 0 and the transfer covers the step.  That is what licenses reading the accumulator's
   *  CARDINALITY, PATH LENGTH, PREFIX PROFILE and hence its round count off `params(accIdx)`.
   *
   *  ==NO EVALUATION==
   *  `SpatialTyping.infer` on an argument EXPRESSION under abstract parameter bindings is abstract
   *  interpretation of annotated types; nothing here runs the routine (standing constraint 1). */
  final case class ParamFix(params: Vector[SpatialType], accIdx: Int, rounds: Int, widened: Int,
                            accPaths: Ivl, accLen: Ivl, initialLo: Long, universe: Option[Universe],
                            depth: Long, binding: String):
    def acc: SpatialType = params(accIdx)
    def show: String =
      s"spatial least fixpoint in $rounds rounds ($widened widened): accumulator " +
      s"|acc| ∈ ${accPaths.show}, len(acc) ∈ ${accLen.show}, |acc₀| ≥ $initialLo, call depth ≤ $depth " +
      s"[$binding]"

  /** the ascending chain is joined for this many steps before [[SpatialRecursion.widenType]] takes over */
  private val FixWidenAfter = 4
  private val FixMaxRounds = 24
  private def showSize(hi: Long): String = if hi >= SizeBounds.INF then "inf" else hi.toString

  /** The self-call sites, or `None` when this fixpoint cannot address them: a site under an
   *  `Iteration`/`Fold`/`Fixpoint` BODY reads binders this environment has no entry for, and a site in
   *  a PATH position is not reachable by the space traversal at all.  Reported rather than guessed. */
  private def unboundSelfCalls(body: Space, rp: RoutinePtr): Either[String, Vector[Space.Call]] =
    val (_, inPath) = SpatialRecursion.callSites(body)
    if inPath.exists(_.r == rp) then Left(s"a self-call of ${rp.s} sits in a path position")
    else
      val out = Vector.newBuilder[Space.Call]
      var under = false
      def go(x: Space, bound: Boolean): Unit = x match
        case c @ Space.Call(r, _, ms) =>
          if r == rp then { if bound then under = true else out += c }
          ms.foreach(go(_, bound))
        case Space.Iteration(s, _, _, b) => go(s, bound); go(b, true)
        case Space.Fold(s, _, _, _, _, b, _) => go(s, bound); go(b, true)
        case Space.Fixpoint(i, _, b) => go(i, bound); go(b, true)
        case other => SizeZ3.children(other).foreach(go(_, bound))
      go(body, false)
      val cs = out.result()
      if under then Left(s"a self-call of ${rp.s} sits under a loop binder, whose bindings this " +
                         "fixpoint has no environment for")
      else if cs.isEmpty then Left(s"no self-call of ${rp.s} the parameter fixpoint can address")
      else if cs.exists(c => c.mentions.exists(a => selfCalls(a, rp).nonEmpty)) then
        Left(s"a self-call argument of ${rp.s} contains another self-call, so one abstract step is " +
             "not one recursion step")
      else Right(cs)

  /** THE FIXPOINT ITSELF.  `accIdx` is the monotone-accumulator parameter whose cardinality bounds the
   *  recursion depth; every other parameter is iterated alongside it because the accumulator's own
   *  transfer reads them (`delta` in the semi-naive body). */
  private def paramFixpoint(rp: RoutinePtr, accIdx: Int, args: Vector[Space], refs: Vector[Path],
                            env: Env, st: State): Either[String, ParamFix] =
    if !env.routines.isDefinedAt(rp) then Left(s"no body for ${rp.s}")
    else
      val r = env.routines(rp)
      if args.length != r.mentions.length then Left(s"arity mismatch on ${rp.s}")
      else if !r.mentions.indices.contains(accIdx) then Left(s"parameter $accIdx out of range for ${rp.s}")
      else unboundSelfCalls(r.body, rp).flatMap { sites =>
        val refLens = r.refs.zip(refs.map(p => SpatialTypes.pathLen(p, env.facts.lengths))).toMap
        // α(arguments): the DECLARED input types, weakened to may-only.  Weakening is what makes the
        // join below an upper bound of its operands (SpatialRecursion's class comment) and what makes
        // γ downward closed, which a set that only ever grows to a SUBSET of the bound needs.
        val start = args.map(a => SpatialRecursion.weaken(SpatialRecursion.keyType(typeAt(a, env, st))))
        def transfer(cur: Vector[SpatialType]): Vector[SpatialType] =
          val benv = SpatialTyping.Env(spaces = r.mentions.zip(cur).toMap, paths = Map.empty,
                                       lenv = SpatialEnv(routines = env.routines), opaque = refLens)
          var out = cur
          for c <- sites; j <- r.mentions.indices do
            c.mentions.lift(j).foreach { a =>
              out = out.updated(j, SpatialRecursion.join(out(j), SpatialTyping.infer(a, benv)))
            }
          out
        var cur = start
        var k = 0
        var widened = 0
        var stable = false
        while k < FixMaxRounds && !stable do
          val nx = transfer(cur)
          if nx.indices.forall(j => SpatialRecursion.leq(nx(j), cur(j))) then stable = true
          else
            cur = if k >= FixWidenAfter then { widened += 1; nx.map(SpatialRecursion.widenType) } else nx
            k += 1
        if !stable then
          Left(s"the spatial parameter fixpoint of ${rp.s} did not reach a post-fixed point in " +
               s"$FixMaxRounds rounds")
        else
          val accT = cur(accIdx)
          val fixHi = if accT.isProvablyEmpty then 0L else accT.size.hi
          // THE REDUNDANT SECOND CEILING, kept only as a meet: the all-strings path universe.  It is
          // NOT the fixpoint and the note says which of the two is binding — a bound of the form
          // `Σ_{d≤L} |A|^d` is a statement about the whole path universe, not about this recursion.
          val uni = universeOf(rp, accIdx, args, refs, env, st).toOption
          val uniHi = uni.map(u => if u.paths > BigInt(Long.MaxValue / 4) then Ivl.INF else u.paths.toLong)
          val hi = (uniHi.toVector :+ fixHi).filter(_ < Ivl.INF).minOption.getOrElse(Ivl.INF)
          if hi >= Ivl.INF then
            Left(s"neither the spatial fixpoint (|acc| ≤ ${showSize(accT.size.hi)}) nor the path universe " +
                 "bounds the accumulator's cardinality")
          else
            // EVERY CONTINUING CALL ADDS AT LEAST ONE PATH to the accumulator, so the number of levels
            // is at most (how much room there is to grow) + the terminating call + the outermost call.
            val lo0 = args.lift(accIdx).map(a => typeAt(a, env, st).size.lo max 0L).getOrElse(0L)
            val room = (hi - (lo0 min hi)) max 0L
            val binding =
              if hi == fixHi && uniHi.forall(_ >= fixHi) then "the spatial fixpoint is binding"
              else s"the path universe ($hi) is binding; the spatial fixpoint gave ${showSize(accT.size.hi)}"
            val ln = accT.len
            val lenIvl =
              if ln.isEmpty then Ivl.zero
              else Ivl(ln.lo, if ln.hi >= LenBounds.INF then Ivl.INF else ln.hi)
            Right(ParamFix(cur, accIdx, k, widened, Ivl(0, hi), lenIvl, lo0, uni, room + 2L, binding))
      }

  /** THE FINITE PATH UNIVERSE a monotone accumulator lives in — A REDUNDANT SECOND CEILING, NOT THE
   *  ANSWER.
   *
   *  WHAT THIS IS NOT.  `Σ_{d≤L} |A|^d` counts every string of length ≤ L over the alphabet; it is a
   *  statement about the PATH UNIVERSE and not about the recursion, and the review is right that calling it
   *  a "least-fixpoint universe summary" overstated it (measured: it put `sn_tc`'s call depth at 23 where
   *  the spatial fixpoint puts it at 3, and the analysis multiplied every per-round cost by that).
   *  [[paramFixpoint]] is the answer; this is kept only as the OTHER sound upper bound of the same
   *  quantity, so `paramFixpoint` can MEET the two and never lose the finiteness guarantee when its own
   *  chain widens to an open count.  [[ParamFix.binding]] states which of the two is binding, so a report
   *  can never quietly rest on this one.
   *
   *  TWO COMPONENTS, both finite for the semi-naive transitive closure:
   *
   *   - the ITEM ALPHABET `A`.  Every path the body produces is built out of items of the ARGUMENTS and
   *     of the body's own literals and constant paths; composition, union, restriction and the tails
   *     operators introduce no new item, and a head `Deref` bound by an enclosing `Iteration` ranges over
   *     items of the space it iterates.  So `A₀ = items(args) ∪ items(literals in the body)` is already
   *     closed under the body's transfer, and the alphabet fixpoint is reached in ZERO rounds.
   *   - the LENGTH `L`, which is NOT reached in zero rounds (composition grows length), so it is
   *     iterated: `L_{k+1} = max(L_k, len(recursive argument) under params ↦ L_k)`, up to
   *     [[UniverseRounds]].
   *
   *  Then `|universe| = Σ_{d≤L} |A|^d` in ARBITRARY PRECISION, and the accumulator holds at most that
   *  many paths.  Sound, and almost always astronomically loose. */
  final case class Universe(alphabet: Int, maxLen: Long, paths: BigInt):
    def show: String =
      s"|A| = $alphabet distinct items, length fixpoint L = $maxLen, " +
      s"|universe| = Σ_{d≤$maxLen} $alphabet^d = $paths"

  private val UniverseBits = 4096
  private def universeSize(alphabet: Int, maxLen: Long): Option[BigInt] =
    if maxLen < 0 || maxLen >= LenBounds.INF then None
    else if alphabet <= 0 then Some(BigInt(1))               // only ε is expressible
    else if maxLen > 8192 then None
    else
      val a = BigInt(alphabet)
      var acc = BigInt(0); var p = BigInt(1); var d = 0L; var ok = true
      while d <= maxLen && ok do
        acc += p
        if acc.bitLength > UniverseBits then ok = false else { p *= a; d += 1 }
      if ok then Some(acc) else None

  /** every item a CLOSED shape admits, or `None` once an open head set makes the set unenumerable */
  private def shapeAlphabet(sh: Shape, budget: Int): Option[Set[PathItem]] =
    if sh.definitelyEmpty then Some(Set.empty)
    else if budget <= 0 then None
    else if !sh.headsClosed then None
    else
      var out = Set.empty[PathItem]
      var ok = true
      for (h, c) <- sh.heads do
        if ok then
          out += h
          shapeAlphabet(c, budget - 1) match
            case Some(s) => out ++= s
            case None => ok = false
      if ok then Some(out) else None

  /** the items the TERM ITSELF names.  `None` when a `Deref` of an unbound path ref or a grounded
   *  function could contribute an item this analysis cannot see. */
  private def syntacticItems(s: Space, bound: Set[PathRef]): Option[Set[PathItem]] =
    var out = Set.empty[PathItem]
    var ok = true
    // `bs` — NOT the top-level `bound` — is what decides whether a `Deref` is a bound head ref.  Closing
    // over `bound` here made every loop body's head `Deref` look unbound, which answered "unknown
    // alphabet" on exactly the Datalog-shaped terms this exists for.
    def gp(p: Path, bs: Set[PathRef]): Unit =
      if ok then p match
        case Path.Constant(pv) => out ++= pv.items
        case Path.Deref(pr) => if !bs.contains(pr) then ok = false
        case Path.Concat(l, r) => gp(l, bs); gp(r, bs)
        case Path.GroundedPP(_, _) | Path.GroundedSP(_, _) => ok = false
    def go(x: Space, bs: Set[PathRef]): Unit =
      if ok then
        x match
          case Space.Literal(v) => v.paths.foreach(p => out ++= p.items)
          case Space.Singleton(p) => gp(p, bs)
          case Space.Wrap(_, p) => gp(p, bs)
          case Space.Unwrap(_, p) => gp(p, bs)
          case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => ok = false
          case _ => ()
        if ok then
          x match
            case Space.Iteration(src, sym, _, body) => go(src, bs); go(body, bs + sym)
            case Space.Fold(src, _, acc, sym, _, body, upd) =>
              go(src, bs); go(body, bs + sym + acc)
            case other => SizeZ3.children(other).foreach(go(_, bs))
    go(s, bound)
    if ok then Some(out) else None

  /** EVERY ITEM A TERM'S VALUE CAN CONTAIN: the items the term itself names, plus the items its free
   *  mentions' DECLARED types admit.
   *
   *  Deliberately NOT read off the term's own inferred shape.  A shape that has been through an
   *  `Iteration` or a `Composition` transfer is typically OPEN (`others.hi > 0`) even when the value is a
   *  closed set over a known alphabet, because the transfer summarises untracked heads rather than
   *  enumerating them — so asking the result's shape for an alphabet answers "unknown" on exactly the
   *  Datalog-shaped terms this exists for.  The INPUTS' shapes are the closed ones, and every item of the
   *  output came from an input or from a literal in the term. */
  private def spaceAlphabet(s: Space, env: Env, st: State): Option[Set[PathItem]] =
    val syn = syntacticItems(s, Set.empty)
    val fromMentions = freeMentions(s).toVector.map { m =>
      env.facts.spaces.get(m).orElse(Some(typeAt(Space.Mention(m), env, st)))
        .flatMap(t => if t.uninhabited then Some(Set.empty[PathItem]) else shapeAlphabet(t.shape, 64))
    }
    if syn.isEmpty || fromMentions.exists(_.isEmpty) then None
    else Some(syn.get ++ fromMentions.flatten.flatten)

  /** FREE space mentions — the ones an environment can answer for.  A `rest` mention bound by an
   *  enclosing `Iteration`/`Fold`, or a `Fixpoint`'s recursive mention, is NOT free: asking the
   *  environment for it gets `⊤`, whose head set is open, which would make every alphabet query on a
   *  loop-containing term answer "unknown".  Its items are those of the space it iterates, which the
   *  enclosing source contributes anyway. */
  private def freeMentions(s: Space): Set[SpaceMention] =
    val out = collection.mutable.Set.empty[SpaceMention]
    def go(x: Space, bound: Set[SpaceMention]): Unit = x match
      case Space.Mention(m) => if !bound.contains(m) then out += m
      case Space.Iteration(src, _, rest, body) => go(src, bound); go(body, bound + rest)
      case Space.Fold(src, _, _, _, rest, body, _) => go(src, bound); go(body, bound + rest)
      case Space.Fixpoint(init, recm, body) => go(init, bound); go(body, bound + recm)
      case other => SizeZ3.children(other).foreach(go(_, bound))
    go(s, Set.empty)
    out.toSet

  /** the recursive call sites of `rp` inside `body` */
  private def selfCalls(body: Space, rp: RoutinePtr): Vector[Space.Call] =
    val out = Vector.newBuilder[Space.Call]
    def go(x: Space): Unit = x match
      case c @ Space.Call(r, _, ms) => if r == rp then out += c; ms.foreach(go)
      case _ => SizeZ3.children(x).foreach(go)
    go(body)
    out.result()

  /** THE SYNTACTIC LENGTH TRANSFER, as an upper bound.  `None` = not bounded here.  Every rule is a
   *  sound upper bound on the maximum item length of the term's value; a `Call` is deliberately opaque so
   *  the fixpoint below never claims a bound it did not derive. */
  private def lenAbs(s: Space, bind: Map[SpaceMention, Long], refs: Map[PathRef, Long],
                     depth: Int): Option[Long] =
    def gp(p: Path): Option[Long] = p match
      case Path.Constant(pv) => Some(pv.items.length.toLong)
      case Path.Deref(pr) => refs.get(pr).orElse(if pr.lengthHint >= 0 then Some(pr.lengthHint.toLong) else None)
      case Path.Concat(l, r) => for a <- gp(l); b <- gp(r) yield a + b
      case _ => None
    if depth > 64 then None
    else
      val rec = (x: Space) => lenAbs(x, bind, refs, depth + 1)
      s match
        case Space.Empty => Some(0L)
        case Space.Literal(v) => Some(if v.paths.isEmpty then 0L else v.paths.iterator.map(_.items.length.toLong).max)
        case Space.Singleton(p) => gp(p)
        case Space.Mention(m) => bind.get(m)
        case Space.Union(a, b) => for x <- rec(a); y <- rec(b) yield x max y
        case Space.Intersection(a, b) => for x <- rec(a); y <- rec(b) yield x min y
        case Space.Subtraction(a, _) => rec(a)
        case Space.Restriction(a, _) => rec(a)
        case Space.Raffination(a, _) => rec(a)
        case Space.Composition(a, b) => for x <- rec(a); y <- rec(b) yield x + y
        case Space.Wrap(src, p) => for x <- rec(src); k <- gp(p) yield x + k
        case Space.Unwrap(src, _) => rec(src)
        case Space.TailsUnion(src) => rec(src).map(x => 0L max (x - 1))
        case Space.TailsIntersection(src) => rec(src).map(x => 0L max (x - 1))
        case Space.Range(x, _, _) => rec(x)
        case Space.Iteration(src, sym, rest, body) =>
          rec(src).flatMap(x => lenAbs(body, bind + (rest -> (0L max (x - 1))), refs + (sym -> 1L), depth + 1))
        case Space.Fold(src, _, _, sym, rest, body, _) =>
          rec(src).flatMap(x => lenAbs(body, bind + (rest -> (0L max (x - 1))), refs + (sym -> 1L), depth + 1))
        case Space.Fixpoint(init, recm, body) =>
          rec(init).flatMap { l0 =>
            var cur = l0; var k = 0; var stable = false; var bad = false
            while k < UniverseRounds && !stable && !bad do
              lenAbs(body, bind + (recm -> cur), refs, depth + 1) match
                case None => bad = true
                case Some(nx) => if nx <= cur then stable = true else cur = nx
                k += 1
            if stable then Some(cur) else None
          }
        case _ => None                                  // Call, grounded: deliberately opaque

  /** THE LENGTH FIXPOINT over the recursive routine's mention parameters. */
  private def paramLenFix(rp: RoutinePtr, params: Vector[SpaceMention], start: Vector[Long],
                          body: Space, refs: Map[PathRef, Long]): Option[Vector[Long]] =
    val sites = selfCalls(body, rp)
    if sites.isEmpty then Some(start)
    else
      var cur = start
      var k = 0; var stable = false; var bad = false
      while k < UniverseRounds && !stable && !bad do
        val bind = params.zip(cur).toMap
        var next = cur
        for c <- sites; j <- params.indices do
          if !bad then
            c.mentions.lift(j) match
              case None => ()
              case Some(arg) => lenAbs(arg, bind, refs, 0) match
                case None => bad = true
                case Some(l) => if l > next(j) then next = next.updated(j, l)
        if !bad then { if next == cur then stable = true else cur = next }
        k += 1
      if stable && !bad then Some(cur) else None

  /** THE SUMMARY ITSELF, for the accumulator parameter `argIdx` of a recursive call to `rp`. */
  private def universeOf(rp: RoutinePtr, argIdx: Int, args: Vector[Space], refs: Vector[Path],
                         env: Env, st: State): Either[String, Universe] =
    if !env.routines.isDefinedAt(rp) then Left(s"no body for ${rp.s}")
    else
      val r = env.routines(rp)
      val refLens = r.refs.zip(refs.map(p => SpatialTypes.pathLen(p, env.facts.lengths)))
        .collect { case (pr, b) if !b.isEmpty && b.hi < LenBounds.INF => pr -> b.hi }.toMap
      if refLens.size != r.refs.size then
        Left(s"a path argument of ${rp.s} has no bounded item length")
      else
        // (1) THE ALPHABET, closed in zero rounds
        val argAlphabets = args.map(a => spaceAlphabet(a, env, st))
        val bodyItems = syntacticItems(r.body, r.refs.toSet)
        val alphabet =
          if argAlphabets.exists(_.isEmpty) then
            Left(s"argument ${argAlphabets.indexWhere(_.isEmpty)} has no enumerable item alphabet " +
                 "(an open head set on a free mention's declared type, or an opaque path/grounded term)")
          else if bodyItems.isEmpty then
            Left(s"${rp.s}'s body names an item this analysis cannot see (an unbound path Deref or a " +
                 "grounded function)")
          else Right(argAlphabets.flatten.flatten.toSet ++ bodyItems.get)
        // (2) THE LENGTH FIXPOINT
        val startLens = args.map(a => SpatialTypes.lenOf(a, env.facts.lengths))
        val lens =
          if startLens.exists(b => b.isEmpty || b.hi >= LenBounds.INF) then
            Left(s"argument ${startLens.indexWhere(b => b.isEmpty || b.hi >= LenBounds.INF)} has no " +
                 "bounded maximum path length")
          else paramLenFix(rp, r.mentions, startLens.map(_.hi), r.body, refLens)
            .toRight(s"the length transfer did not reach a fixpoint in $UniverseRounds rounds (or a " +
                     "recursive argument's length is not derivable syntactically)")
        for
          a <- alphabet
          ls <- lens
          l <- ls.lift(argIdx).toRight(s"parameter $argIdx is out of range for ${rp.s}")
          n <- universeSize(a.size, l).toRight(
                 s"the universe Σ_{d≤$l} ${a.size}^d exceeds the precision budget")
        yield Universe(a.size, l, n)
end SpatialCost
