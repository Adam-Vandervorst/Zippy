package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** SEMANTIC LAWS OF THE SPATIAL DOMAIN — the executable half of review.md 6.
 *
 *  Four families, each a different failure mode:
 *
 *    1. GALOIS.  `v ∈ γ(α v)`, `α` monotone, `γ` monotone (i.e. `leq ⇒ γ-containment`),
 *       `α(γ t) ⊑ t`, and the adjunction `α S ⊑ t ⟺ S ⊆ γ t`.  γ-containment is DECIDED
 *       exactly on a finite universe of concrete values (all 2^7 space values over {a,b} with
 *       paths of ≤2 items), never by an envelope shortcut.
 *    2. SIMULATION SQUARES.  For EVERY row of `SpatialGamma.ops`: abstract random concrete
 *       operands with α, run the real transfer (`SpatialTyping.infer`), run the real semantics
 *       (`eval`), assert the concrete result is in γ of the abstract one.  This is
 *       `eval(s, concreteEnv) ∈ γ(infer(s, abstractEnv))`, per operator, with counts.
 *    3. TRANSFER OVER NON-EXACT OPERANDS.  `γ(a op# b) ⊇ γ(a) op γ(b)` — the same square but with
 *       the abstract operands drawn from a pool of joined abstractions, so the transfer is exercised
 *       at inputs α never produces.  An α-only test cannot see a transfer that is only sound on
 *       exact inputs.
 *    4. CONDITIONAL REWRITE.  A specialisation agrees with the original on every input satisfying
 *       its precondition, and an input violating it can differ (so the precondition is
 *       load-bearing).
 *
 *  `eval` is used ONLY as ground truth here.  Nothing in `src/main` calls it. */
class SpatialLawCheck extends FunSuite:
  import Space.*
  import Lower.{LenBounds, SizeBounds}
  import SpatialGamma.*
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  // ---------------------------------------------------------------------------------------------
  // generators
  // ---------------------------------------------------------------------------------------------
  private def item(i: Int): PathItem = "i" + i
  /** Concrete values in five regimes, so the caps and degenerate shapes are all hit:
   *  NORMAL (small), WIDE (>MaxHeads=12 distinct heads), DEEP (>MaxDepth=4 items),
   *  LONG (>MaxClasses=24 distinct lengths, so the histogram spills), DEGENERATE (∅, {ε}, ε-inside). */
  private def randValue(rng: java.util.Random): SpaceValue =
    def pick(n: Int) = item(rng.nextInt(n))
    rng.nextInt(10) match
      case 8 =>                                                  // WIDE: forces Shape.MaxHeads spill
        // one path per head, so the 12-head cap is genuinely exceeded, and the tails deliberately
        // disagree about ε (some heads carry a bare head, some a two-item path)
        SpaceValue((0 until (10 + rng.nextInt(10))).map(i =>
          if rng.nextBoolean() then PathValue(List(item(i))) else PathValue(List(item(i), pick(3)))).toSet)
      case 9 =>                                                  // LONG: forces SpaceType spill
        SpaceValue((0 until (1 + rng.nextInt(5))).map(_ =>
          PathValue(List.fill(rng.nextInt(30))(pick(2)))).toSet)
      case 7 =>                                                  // DEGENERATE
        rng.nextInt(4) match
          case 0 => SpaceValue(Set.empty)
          case 1 => SpaceValue(Set(PathValue(Nil)))
          case 2 => SpaceValue(Set(PathValue(Nil), PathValue(List(item(0)))))
          case _ => SpaceValue(Set(PathValue(Nil), PathValue(List(item(0), item(1)))))
      case 6 =>                                                  // DEEP: past Shape.MaxDepth
        SpaceValue((0 until rng.nextInt(6)).map(_ =>
          PathValue(List.fill(rng.nextInt(7))(pick(2)))).toSet)
      case _ =>                                                  // NORMAL
        SpaceValue((0 until rng.nextInt(6)).map(_ =>
          PathValue(List.fill(rng.nextInt(4))(pick(4)))).toSet)

  private def randPathValue(rng: java.util.Random): PathValue =
    PathValue(List.fill(rng.nextInt(3))(item(rng.nextInt(4))))

  private val nestSym = PathRef("h2$")
  private val nestRest = SpaceMention("r2$")

  private def randIterBody(rng: java.util.Random): Space = rng.nextInt(10) match
    case 0 => Space.Singleton(Path.Deref(bindSym))
    case 1 => Space.Mention(bindRest)
    case 2 => Space.TailsUnion(Space.Mention(bindRest))
    case 3 => Space.Wrap(Space.Mention(bindRest), Path.Deref(bindSym))
    case 4 => Space.Union(Space.Singleton(Path.Deref(bindSym)), Space.Mention(bindRest))
    case 5 => Space.Literal(randValue(rng))
    case 6 => Space.Empty
    case 7 => Space.Iteration(Space.Mention(bindRest), nestSym, nestRest, Space.Singleton(Path.Deref(nestSym)))
    case 8 => Space.Intersection(Space.Mention(bindRest), Space.Literal(randValue(rng)))
    case _ => Space.Singleton(Path.Concat(Path.Deref(bindSym), Path.Deref(bindSym)))

  private def randFoldBody(rng: java.util.Random): Space = rng.nextInt(4) match
    case 0 => Space.Singleton(Path.Deref(bindAcc))
    case 1 => Space.Singleton(Path.Concat(Path.Deref(bindAcc), Path.Deref(bindSym)))
    case 2 => Space.Union(Space.Singleton(Path.Deref(bindAcc)), Space.Mention(bindRest))
    case _ => randIterBody(rng)

  /** ONLY non-growing bodies: the concrete `Fixpoint` loops until the iterate stops changing, so a
   *  length-growing body (e.g. `Wrap(rec, p)`) does not terminate at all and would say nothing
   *  about the transfer. */
  private def randFixBody(rng: java.util.Random): Space = rng.nextInt(9) match
    case 0 => Space.Mention(bindRec)
    case 1 => Space.Union(Space.Mention(bindRec), Space.Literal(randValue(rng)))
    case 2 => Space.TailsUnion(Space.Mention(bindRec))
    case 3 => Space.Union(Space.Mention(bindRec), Space.TailsUnion(Space.Mention(bindRec)))
    case 4 => Space.Intersection(Space.Mention(bindRec), Space.Literal(randValue(rng)))
    case 5 => Space.Subtraction(Space.Mention(bindRec), Space.Literal(randValue(rng)))
    case 6 => Space.Unwrap(Space.Mention(bindRec), Path.Constant(randPathValue(rng)))
    case 7 => Space.Restriction(Space.Mention(bindRec), Space.Literal(randValue(rng)))
    case _ => Space.Literal(randValue(rng))

  private def bodyFor(op: Op, rng: java.util.Random): Space = op.body match
    case BodyKind.NoBody => Space.Empty
    case BodyKind.Iter => randIterBody(rng)
    case BodyKind.Fold => randFoldBody(rng)
    case BodyKind.Fix => randFixBody(rng)

  /** build the term + the two environments (abstract and concrete) for one trial */
  private def trial(op: Op, vs: Vector[SpaceValue], qs: Vector[PathValue], body: Space, literalMode: Boolean)
      : (Space, SpatialTyping.Env, PathContext, SpaceContext) =
    val spaces = if literalMode then vs.map(Space.Literal.apply)
                 else vs.indices.map(i => Space.Mention(opSpaces(i))).toVector
    val paths: Vector[Path] = if literalMode then qs.map(Path.Constant.apply)
                              else qs.indices.map(j => Path.Deref(opPaths(j))).toVector
    val node = op.build(spaces, paths, body)
    val lenv = SpatialEnv(routines = routineTable)
    val env =
      if literalMode then SpatialTyping.Env(lenv = lenv)
      else SpatialTyping.Env(spaces = vs.indices.map(i => opSpaces(i) -> alpha(vs(i))).toMap,
                             paths = qs.indices.map(j => opPaths(j) -> qs(j)).toMap, lenv = lenv)
    (node, env,
     PathContextMap(qs.indices.map(j => opPaths(j) -> qs(j)).toMap),
     SpaceContextMap(vs.indices.map(i => opSpaces(i) -> vs(i)).toMap))

  // ---------------------------------------------------------------------------------------------
  // the finite universe on which γ-containment is DECIDED
  // ---------------------------------------------------------------------------------------------
  private lazy val U: Vector[SpaceValue] = SpatialGamma.universe(Vector("a", "b"), 2)

  // =============================================================================================
  // 1. GALOIS
  // =============================================================================================

  test("galois: v ∈ γ(α v) — on the whole finite universe and on the five random regimes") {
    var n = 0
    for v <- U do
      assert(gamma(alpha(v))(v), s"universe value not in γ(α v): ${v.pretty}  α = ${alpha(v).show}")
      n += 1
    val rng = new java.util.Random(1001)
    for _ <- 0 until 4000 do
      val v = randValue(rng)
      val t = alpha(v)
      assert(gamma(t)(v), s"random value not in γ(α v): ${v.pretty}\n  α = ${t.show}")
      assert(gammaMay(t)(v), s"random value not in γ_may(α v): ${v.pretty}")
      n += 1
    println(s"GALOIS/extensive: v ∈ γ(α v) on $n values (universe ${U.size} + 4000 random)")
  }

  test("galois: α on sets is monotone, and is an upper bound of its members") {
    val rng = new java.util.Random(1002)
    var checked = 0
    for _ <- 0 until 600 do
      val s = (0 until (1 + rng.nextInt(4))).map(_ => U(rng.nextInt(U.size))).toSet
      val extra = U(rng.nextInt(U.size))
      val a = alphaSet(s); val b = alphaSet(s + extra)
      // every member of the set is in γ of its abstraction (α is an upper bound)
      for v <- s do assert(gamma(a)(v), s"member not in γ(α S): ${v.pretty}  α S = ${a.show}")
      assert(gamma(b)(extra))
      // monotone: S ⊆ T ⇒ γ(α S) ⊆ γ(α T), decided exactly on U
      assert(gammaLeqOn(U)(a, b),
             s"α not monotone: S=${s.map(_.pretty)} + ${extra.pretty}\n  α S = ${a.show}\n  α T = ${b.show}\n" +
               s"  witness ${gammaLeqWitness(U)(a, b).map(_.pretty)}")
      checked += 1
    println(s"GALOIS/α-monotone: $checked set pairs, γ-containment decided on all ${U.size} universe values each")
  }

  /** A WIDER value pool than [[U]].  `U` is EVERY space value over {a,b} with paths of at most two
   *  items, so for a type whose shape has a closed head set over {a,b} and whose histogram has no
   *  spill bucket, `γ(t) ∩ U = γ(t)` and "contained on U" is containment.  That is NOT true once a
   *  spill bucket or an open head set is present: such a type admits values `U` cannot express, so a
   *  pair that looks contained on `U` may not be contained at all — and then `leq`'s "no" is CORRECT
   *  and nothing should be done about it.  `Wide` exists to separate those two populations, because
   *  otherwise every measurement of "avoidable Unknowns" is inflated by an artifact of `U`'s size.
   *
   *  It is a REFUTATION pool, not a universe: finding `v ∈ γ(a) ∖ γ(b)` in it PROVES non-containment;
   *  finding none proves nothing, and is reported as "not refuted", never as "contained". */
  private lazy val Wide: Vector[SpaceValue] =
    val ps = SpatialGamma.allPaths(Vector("a", "b", "c"), 3)          // 40 paths, lengths 0..3
    val byLen = (0 to 3).map(l => ps.filter(_.items.length == l)).toVector
    val b = Vector.newBuilder[SpaceValue]
    b ++= U
    // structured values that probe ONE class count and ONE spill aggregate at a time
    for l <- 0 to 3; k <- 0 to byLen(l).size do b += SpaceValue(byLen(l).take(k).toSet)
    for l1 <- 0 to 3; k1 <- 0 to 5; l2 <- l1 + 1 to 3; k2 <- 0 to 5 do
      b += SpaceValue((byLen(l1).take(k1) ++ byLen(l2).take(k2)).toSet)
    val rng = new java.util.Random(9099)
    for _ <- 0 until 4000 do
      val p = 1 + rng.nextInt(4)
      b += SpaceValue(ps.filter(_ => rng.nextInt(p) == 0).toSet)
    b.result().distinct

  /** `Some(v)` PROVES `γ(a) ⊄ γ(b)` — so a `leq(a, b) = false` on such a pair is a TRUE negative and
   *  the finite-`U` test's "contained" verdict is the artifact. */
  private def refuteWide(a: SpatialType, b: SpatialType): Option[SpaceValue] =
    val ga = gamma(a); val gb = gamma(b)
    Wide.find(v => ga(v) && !gb(v))

  /** is the COMPONENT contained, as far as `Wide` can tell?  A false negative whose component is not
   *  contained is not the order's fault: only the CONJUNCTION of shape and histogram excludes the
   *  witnesses, and a componentwise order can never see that. */
  private def shapeContainedWide(a: Shape, b: Shape): Boolean =
    !Wide.exists(v => Shape.contains(a, v) && !Shape.contains(b, v))
  /** EXTREMAL members of γ(t) for the histogram component, materialised over fresh items: every
   *  combination of the per-class endpoints, with the spill mass placed at its lower and at its upper
   *  bound, one free length at a time.  Every constraint the right-hand side can state is a per-class
   *  or an aggregate bound, so if containment fails one of these witnesses it. */
  private def extremalMembers(t: SpaceType): Vector[SpaceValue] =
    val cap = 12L
    def paths(l: Long, n: Long): Vector[PathValue] =
      if l == 0L then (if n >= 1 then Vector(PathValue(Nil)) else Vector.empty)
      else (0 until math.min(n, cap).toInt).toVector
        .map(i => PathValue(("e" + i) :: List.fill(l.toInt - 1)("e0")))
    val tracked = t.byLen.keys.filter(_ <= 6L).toVector.sorted
    if tracked.sizeIs > 6 then Vector.empty
    else
      val free =
        if t.rest.hi > 0 && !t.restLens.isEmpty then
          (t.restLens.lo to math.min(t.restLens.hi, 6L)).filter(l => !t.byLen.contains(l)).toVector
        else Vector.empty
      val combos = tracked.foldLeft(Vector(Vector.empty[(Long, Long)])) { (acc, l) =>
        val c = t.byLen(l)
        val opts = Vector(c.lo, if c.hi == Ivl.INF then cap else math.min(c.hi, cap)).distinct
        acc.flatMap(v => opts.map(n => v :+ (l -> n)))
      }
      val plans =
        if free.isEmpty then Vector(Vector.empty[(Long, Long)])
        else
          val amounts = Vector(t.rest.lo, if t.rest.hi == Ivl.INF then cap else math.min(t.rest.hi, cap)).distinct
          (for w <- free; n <- amounts yield Vector(w -> n)) :+ Vector.empty[(Long, Long)]
      val out = Vector.newBuilder[SpaceValue]
      for cb <- combos; sp <- plans do
        val v = SpaceValue((cb ++ sp).flatMap((l, n) => paths(l, n)).toSet)
        if gammaSpace(t, v) then out += v
      out.result().distinct

  /** the histogram component gets `UC` and its own extremal members as well as `Wide`: `Wide`'s
   *  alphabet reaches three paths of a given length only by accident, and `UC` caps counts at three,
   *  so a class bound above that is refutable only by a witness built from the type itself. */
  private def spaceContainedWide(a: SpaceType, b: SpaceType): Boolean =
    !(Wide.iterator ++ UC.iterator ++ extremalMembers(a).iterator)
      .exists(v => gammaSpace(a, v) && !gammaSpace(b, v))

  /** do the two histograms PARTITION the lengths differently — one tracking a class the other only
   *  covers with its spill bucket?  This is review.md 4's named suspect. */
  private def partitionsDiffer(x: SpaceType, y: SpaceType): Boolean =
    (x.rest.hi > 0 || y.rest.hi > 0) && x.byLen.keySet != y.byLen.keySet

  // ---------------------------------------------------------------------------------------------
  // A γ-DIRECTED MEMBER SEARCH.  `U` and `Wide` are fixed pools, so for a type that needs paths
  // LONGER than they carry (a `Composition` result needs length-4 paths; `Wide` stops at 3) they
  // contain no member of γ at all — and then "contained on U" is vacuous, and calling the pair a
  // false negative of `leq` is wrong.  Telling the two apart needs members constructed FROM the
  // type, which is what this does.
  // ---------------------------------------------------------------------------------------------

  /** every path the shape may admit, fresh items standing in for untracked heads.  Every member of
   *  γ(sh) is a subset of this up to renaming those items, so a witness lives among its subsets. */
  private def shapeLanguage(sh: Shape, d: Int, tag: String): Vector[PathValue] =
    if sh.definitelyEmpty || d < 0 then Vector.empty
    else
      val e = if sh.eps.mayBe then Vector(PathValue(Nil)) else Vector.empty
      val hs = sh.heads.toVector.flatMap((h, c) => shapeLanguage(c, d - 1, tag).map(p => PathValue(h :: p.items)))
      val os =
        if sh.others.hi <= 0 || d <= 0 then Vector.empty
        else
          val k = ((sh.others.hi min 3L).toInt) max 1
          (0 until k).toVector.flatMap { i =>
            val h: PathItem = tag + i
            val tails = sh.otherTail match
              case Some(t) => shapeLanguage(t, d - 1, tag + "z")
              case None => SpatialGamma.allPaths(Vector(tag + "y0", tag + "y1"), d - 1)
            tails.map(p => PathValue(h :: p.items))
          }
      e ++ hs ++ os

  private def shuffled(v: Vector[PathValue], rng: java.util.Random): Vector[PathValue] =
    val a = v.toArray
    var i = a.length - 1
    while i > 0 do { val j = rng.nextInt(i + 1); val t = a(i); a(i) = a(j); a(j) = t; i -= 1 }
    a.toVector

  /** MEMBERS of γ(t), built rather than found: take the shape's language and choose, per length, a
   *  count inside the histogram's interval for that length.  Only γ-accepted values are returned, so
   *  every element is a genuine member and an empty result is evidence (not proof) of ⊥. */
  private def sampleMembers(t: SpatialType, n: Int, rng: java.util.Random): Vector[SpaceValue] =
    val lang = shapeLanguage(t.shape, Shape.MaxDepth + 2, "u").distinct
    if lang.isEmpty then Vector.empty
    else
      val byLen = lang.groupBy(_.items.length.toLong).toVector
      val g = gamma(t)
      val out = Vector.newBuilder[SpaceValue]
      // the whole language, and the must-only core, are the two extremal candidates
      for cand <- Vector(SpaceValue(lang.toSet)) if g(cand) do out += cand
      for _ <- 0 until n do
        val picked = Vector.newBuilder[PathValue]
        for (l, ps) <- byLen do
          val c = t.lens.at(l)
          val hi = (if c.hi == Ivl.INF then ps.size.toLong else c.hi min ps.size.toLong).toInt
          val lo = (c.lo min hi.toLong).toInt
          val k = if hi < 0 then 0 else lo + rng.nextInt(hi - lo + 1)
          picked ++= shuffled(ps, rng).take(k)
        val v = SpaceValue(picked.result().toSet)
        if g(v) then out += v
      out.result().distinct

  test("galois: leq ⇒ γ-containment (γ monotone), and leq's incompleteness measured") {
    val rng = new java.util.Random(1003)
    val pool = abstractPool(rng, 1200)
    var sound = 0; var leqTrue = 0; var contTrue = 0; var incomplete = 0
    // THE CAUSE HISTOGRAM (review.md 4, second half).  Every false negative is attributed, and a
    // pair may carry several labels — the totals below are therefore label counts, not pair counts;
    // the pair counts are the `fault:` rows.
    val cause = scala.collection.mutable.LinkedHashMap.empty[String, Int]
    def bump(k: String): Unit = cause(k) = cause.getOrElse(k, 0) + 1
    val witness = scala.collection.mutable.LinkedHashMap.empty[String, String]
    def wit(k: String, s: => String): Unit = if !witness.contains(k) then witness(k) = s
    var trueNeg = 0; var vacuous = 0; var product = 0; var avoidable = 0
    for a <- pool; _ <- 0 until 12 do
      val b = pool(rng.nextInt(pool.size))
      val l = leq(a, b); val c = gammaLeqOn(U)(a, b)
      if l then
        leqTrue += 1
        assert(c, s"leq holds but γ-containment FAILS\n  a = ${a.show}\n  b = ${b.show}\n" +
                  s"  witness ${gammaLeqWitness(U)(a, b).map(_.pretty)}")
        sound += 1
      if c then contTrue += 1
      if c && !l then
        incomplete += 1
        val mrng = new java.util.Random(770000 + incomplete)
        val members = sampleMembers(a, 120, mrng) ++ Wide.filter(gamma(a))
        val off = refuteWide(a, b).orElse(members.find(v => !gamma(b)(v)))
        if off.nonEmpty then
          trueNeg += 1
          bump("TRUE NEGATIVE (refuted off U — leq is right, U is too small)")
          wit("off-U", s"a = ${a.show}\n        b = ${b.show}\n        v = ${off.get.pretty}")
        else if members.isEmpty then
          // no member of γ(a) could be exhibited anywhere: containment on U is VACUOUS.  `a` is ⊥ in
          // fact but not in representation, so the order is asked a question with a trivial answer.
          vacuous += 1
          bump(s"VACUOUS: γ(a) = ∅ (no member exhibited); reduce(a) proves ⊥: " +
               s"${SpatialType.reduce(a).uninhabited}")
          wit("vacuous", s"a = ${a.show}\n        reduce(a) = ${SpatialType.reduce(a).show}")
        else if b.uninhabited then { product += 1; bump("b is ⊥ (uninhabited)") }
        else
          val sm = Shape.leqStrongMask(a.shape, b.shape)
          val lm = SpatialGamma.leqSpaceMask(a.lens, b.lens)
          val sc = sm == 0 || shapeContainedWide(a.shape, b.shape)
          val lc = lm == 0 || spaceContainedWide(a.lens, b.lens)
          bump(s"fault: ${if sm != 0 then "shape" else "-"}/${if lm != 0 then "lens" else "-"}" +
               s"  contained: ${if sc then "shape" else "-"}/${if lc then "lens" else "-"}")
          if sc && sm != 0 || lc && lm != 0 then avoidable += 1 else product += 1
          if sm != 0 then
            if sc then
              for n <- Shape.LeqShapeWhy.show(sm) do bump("AVOIDABLE " + n)
              wit("shape", s"a = ${a.shape.show}\n        b = ${b.shape.show}  [${Shape.LeqShapeWhy.show(sm).mkString(",")}]")
            else bump("component not contained: shape (product interaction)")
          if lm != 0 then
            if lc then
              val tag = if partitionsDiffer(a.lens, b.lens) then " [partitions differ]" else ""
              for n <- SpatialGamma.LeqSpaceWhy.show(lm) do bump("AVOIDABLE " + n + tag)
              wit("lens" + tag, s"a = ${a.lens.show}\n        b = ${b.lens.show}  [${SpatialGamma.LeqSpaceWhy.show(lm).mkString(",")}]")
            else
              bump("component not contained: lens (product interaction)")
              // the ONE remaining class of genuine checker `Unknown`s, so it is worth a named witness:
              // the histogram component alone is NOT contained, and only its conjunction with the
              // shape makes containment hold.  No componentwise order can accept it.
              wit("product-interaction", s"a = ${a.show}\n        b = ${b.show}\n        " +
                s"γ(a) ⊆ γ(b) on U, but γ_hist(a.lens) ⊄ γ_hist(b.lens) — witness for the lens alone: " +
                (UC.iterator ++ extremalMembers(a.lens).iterator)
                  .find(v => gammaSpace(a.lens, v) && !gammaSpace(b.lens, v)).map(_.pretty).getOrElse("?"))
    println(f"GALOIS/γ-monotone: ${pool.size * 12} pairs; leq held $leqTrue%d (all γ-sound); " +
      f"γ-contained-on-U $contTrue%d; leq incomplete on $incomplete%d " +
      f"(${100.0 * incomplete / math.max(1, contTrue)}%.1f%% of contained pairs)")
    // THE HONEST DECOMPOSITION.  The headline percentage is NOT a precision figure: `U` cannot express
    // a member of γ(a) for most of these pairs, so "contained on U" is vacuous there and `leq`'s "no"
    // is correct.  What the order can be blamed for is the AVOIDABLE column, and only that.
    println(f"  of $incomplete: TRUE NEGATIVE (a member of γ(a) ∖ γ(b) exists outside U) $trueNeg%d; " +
      f"γ(a) = ∅ so containment is vacuous $vacuous%d; " +
      f"PRODUCT INTERACTION (neither component is contained — only the conjunction is, which no " +
      f"componentwise order can see) $product%d; AVOIDABLE $avoidable%d " +
      f"(${100.0 * avoidable / math.max(1, contTrue)}%.2f%% of contained pairs)")
    println(s"  CAUSE HISTOGRAM of the $incomplete false negatives (Wide pool = ${Wide.size} values):")
    for (k, v) <- cause.toVector.sortBy(-_._2) do println(f"    $v%5d  $k")
    for (k, s) <- witness do println(s"    witness/$k: $s")
    // THE GATE.  Every false negative must be attributable to something other than the order: a
    // witness outside `U`, an empty γ(a), or a product interaction.  A pair where a COMPONENT is
    // contained and the component order still says no is an avoidable `Unknown` for the checker, and
    // there are to be none.
    assertEquals(trueNeg + vacuous + product + avoidable, incomplete, "a false negative went unclassified")
    assertEquals(avoidable, 0, s"avoidable false negatives: see the AVOIDABLE rows above")
  }

  // =============================================================================================
  // 1b. THE HISTOGRAM ORDER, DECIDED EXACTLY — where review.md 4's named suspect actually lives
  // =============================================================================================
  //
  // `U` is every space value over {a,b} with paths of ≤2 items.  For a SPILL-CARRYING histogram that
  // is useless in both directions: `U` has only two paths per length and no path longer than two, so
  // it can neither confirm nor refute containment for the population review.md 4 blames — and the
  // cause histogram above shows the consequence (73% of the "false negatives" on `U` are pairs where
  // `U` cannot express any member of γ(a) at all).
  //
  // This universe is built for the histogram component instead: EVERY count vector with `c_0 ≤ 1`
  // and `c_l ≤ CountMaxCnt` for `1 ≤ l ≤ CountMaxLen`, materialised as a space value over fresh
  // items and paired with `Shape.top` (which admits everything, so the shape channel is vacuous).
  // For a type whose every bound fits inside those caps — `expressible` — γ(t) is FULLY represented,
  // so containment on this universe IS containment.  No sampling, no artifact, and the spill/tracked
  // partition cases are generated on purpose.
  private val CountMaxLen = 4
  private val CountMaxCnt = 3

  private lazy val UC: Vector[SpaceValue] =
    val byLen: Vector[Vector[PathValue]] = (0 to CountMaxLen).toVector.map { l =>
      if l == 0 then Vector(PathValue(Nil))
      else (0 until CountMaxCnt).toVector.map(i => PathValue(("c" + i) :: List.fill(l - 1)("c0")))
    }
    def go(l: Int): Vector[Vector[PathValue]] =
      if l > CountMaxLen then Vector(Vector.empty)
      else
        val hi = if l == 0 then 1 else CountMaxCnt
        for rest <- go(l + 1); k <- (0 to hi).toVector yield byLen(l).take(k) ++ rest
    go(0).map(ps => SpaceValue(ps.toSet))

  /** is γ(t) FULLY inside [[UC]]?  Then containment decided on `UC` is containment. */
  private def expressible(t: SpaceType): Boolean =
    t.byLen.forall((l, c) => l <= CountMaxLen && c.hi <= CountMaxCnt) &&
      t.rest.hi <= CountMaxCnt && (t.rest.hi == 0 || t.restLens.isEmpty || t.restLens.hi <= CountMaxLen)

  /** histograms in every representation the carrier has: closed supports, spill-only windows,
   *  tracked classes ALONGSIDE a disjoint spill window (the partition cases), and lub/meet results. */
  private def randHist(rng: java.util.Random, depth: Int): SpaceType =
    def iv(): Ivl =
      val x = rng.nextInt(CountMaxCnt + 1); Ivl(x, x + rng.nextInt(CountMaxCnt + 1 - x))
    def win(): LenBounds =
      val x = rng.nextInt(CountMaxLen + 1); LenBounds(x, x + rng.nextInt(CountMaxLen + 1 - x))
    rng.nextInt(if depth <= 0 then 4 else 6) match
      case 0 => SpaceType.closed((0 to CountMaxLen).filter(_ => rng.nextBoolean()).map(l => l.toLong -> iv())*)
      case 1 => SpaceType.bounded(win(), rng.nextInt(CountMaxCnt + 1))
      case 2 => SpaceType.boundedExact(win(), rng.nextInt(CountMaxCnt + 1))
      case 3 =>
        val w = win()
        val cs = (0 to CountMaxLen).filter(l => l < w.lo || l > w.hi).filter(_ => rng.nextBoolean())
          .map(l => l.toLong -> iv())
        SpatialTypes.widen(SpaceType(scala.collection.immutable.SortedMap.from(cs), iv(), w))
      case 4 => lubSpace(randHist(rng, depth - 1), randHist(rng, depth - 1))
      case _ => meetSpace(randHist(rng, depth - 1), randHist(rng, depth - 1)).getOrElse(SpaceType.empty)

  /** WHY γ(t) is empty, when it is — so "the order cannot see that its left side is ⊥" can be split
   *  into the cases a cheap syntactic check catches and the ones needing real reasoning. */
  private def botReason(t: SpaceType): String =
    if t.byLen.exists((_, c) => c.lo > c.hi) then "a class interval is empty (lo > hi)"
    else if t.at(0).lo >= 2 then "the ε class demands ≥2 paths of length 0, and only ONE path has length 0"
    else if t.rest.lo > t.rest.hi then "the spill interval is empty (lo > hi)"
    else if t.rest.lo >= 1 && t.restLens.isEmpty then "a FORCED spill with no window to put it in"
    else if t.rest.lo >= 2 && t.restLens.lo == 0 && t.restLens.hi == 0 then
      "the spill window is {0} and demands ≥2 paths of length 0"
    else "needs real reasoning"

  private def acceptedBits(t: SpaceType): java.util.BitSet =
    val bs = new java.util.BitSet(UC.size)
    for i <- UC.indices if gammaSpace(t, UC(i)) do bs.set(i)
    bs
  private def subsetOf(x: java.util.BitSet, y: java.util.BitSet): Boolean =
    val z = x.clone().asInstanceOf[java.util.BitSet]; z.andNot(y); z.isEmpty

  test("regression: the two REPAIRED false negatives, each decided by exhausting a universe") {
    // These are the two witnesses `SpatialCheckCheck` 4a–4c and 6b are built around.  Before the
    // canonical form, `leqSpace` rejected both because it required the LEFT side's spill window to
    // NEST inside the right side's — and here the right side TRACKS those lengths instead, carrying no
    // spill bucket at all.  Containment is decided below by exhausting every subset of the paths
    // either side can mention, so "the order is right now" is a proof on these two pairs and not an
    // appeal to the aggregate measurement.  THEY ARE THE PAIRS THAT MAKE SpatialCheckCheck 4a/4b/4c
    // AND 6b FAIL, and they are why those four need updating (see the report).
    def decide(a: SpatialType, b: SpatialType, ps: Vector[PathValue]): Option[SpaceValue] =
      var bad: Option[SpaceValue] = None
      for sub <- ps.toSet.subsets() if bad.isEmpty do
        val v = SpaceValue(sub)
        if gamma(a)(v) && !gamma(b)(v) then bad = Some(v)
      bad

    // ---- witness 1 (SpatialCheckCheck 4a-4c): one path, length 1 or 2, exactly one head ----------
    val oneHead = Shape(Presence.No, scala.collection.immutable.SortedMap.empty, Ivl(1, 1), None)
    val a1 = SpatialType(oneHead, SpaceType.boundedExact(LenBounds(1, 2), 1))
    val b1 = SpatialType(oneHead, SpaceType.closed(1L -> Ivl(0, 1), 2L -> Ivl(0, 1)))
    val u1 = Vector(PathValue(Nil), PathValue(List("x")), PathValue(List("y")),
      PathValue(List("x", "x")), PathValue(List("x", "y")), PathValue(List("y", "x")),
      PathValue(List("x", "x", "x")))
    assertEquals(decide(a1, b1, u1), None, s"precondition: ${a1.show} really is contained in ${b1.show}")
    assert(leq(a1, b1), s"the order must now see it: ${a1.show} ⊑ ${b1.show}")

    // ---- witness 2 (SpatialCheckCheck 6b): 12 forced heads + one untracked, 13 length-1 paths -----
    val hs = scala.collection.immutable.SortedMap.from((0 until 12).map(i => (("h" + i): PathItem) -> Shape.epsOnly))
    val mayHs = scala.collection.immutable.SortedMap.from(hs.view.mapValues(_ =>
      Shape(Presence.May, scala.collection.immutable.SortedMap.empty, Ivl.zero, None)))
    val a2 = SpatialType(Shape(Presence.No, hs, Ivl(1, 1), None), SpaceType.boundedExact(LenBounds(1, 1), 13))
    val b2 = SpatialType(Shape(Presence.No, mayHs, Ivl(0, 1), None), SpaceType.closed(1L -> Ivl(13, 13)))
    val u2 = (0 until 12).toVector.map(i => PathValue(List("h" + i))) ++
      Vector(PathValue(Nil), PathValue(List("z0")), PathValue(List("z1")), PathValue(List("h0", "t")))
    assertEquals(decide(a2, b2, u2), None, s"precondition: ${a2.show} really is contained in ${b2.show}")
    assert(leq(a2, b2), s"the order must now see it: ${a2.show} ⊑ ${b2.show}")

    // …and the mechanism is the ALIGNMENT: a single-length spill window IS the tracked class, so the
    // two histograms are literally the same type once canonicalised.
    assertEquals(canonSpace(a2.lens), canonSpace(b2.lens),
      "the spill and the tracked partition denote the same counts, so canonSpace must identify them")
    println(s"REPAIRED: ${a1.lens.show} ⊑ ${b1.lens.show} and ${a2.lens.show} ⊑ ${b2.lens.show} — " +
      s"both decided by exhausting ${1 << u1.size} and ${1 << u2.size} concrete spaces")
  }

  // ---------------------------------------------------------------------------------------------
  // LATENCY of the order's histogram half.  `SpatialType.leq` runs inside every fixpoint, so a
  // canonical form on that path must be paid for out of a MEASURED budget, not assumed free.
  // `oldLeqSpace` is the pre-canonicalisation body, verbatim, so the comparison is head to head.
  // ---------------------------------------------------------------------------------------------
  private def oldLeqSpace(a: SpaceType, b: SpaceType): Boolean =
    val keys = (a.byLen.keySet ++ b.byLen.keySet).toVector
    val pointwise = keys.forall { l => val (x, y) = (a.at(l), b.at(l)); y.lo <= x.lo && x.hi <= y.hi }
    val windowOk =
      a.rest.hi == 0 || a.restLens.isEmpty ||
        (b.rest.hi > 0 && !b.restLens.isEmpty && b.restLens.lo <= a.restLens.lo && a.restLens.hi <= b.restLens.hi)
    var hiOut = if a.rest.hi > 0 then a.rest.hi else 0L
    var loOut =
      if a.rest.lo == 0 || a.restLens.isEmpty then 0L
      else if b.byLen.keysIterator.exists(l => a.restLens.lo <= l && l <= a.restLens.hi) then 0L
      else a.rest.lo
    for (l, c) <- a.byLen if !b.byLen.contains(l) do
      hiOut = Ivl.add(hiOut, c.hi); loOut = Ivl.add(loOut, c.lo)
    pointwise && windowOk && hiOut <= b.rest.hi && b.rest.lo <= loOut

  test("leqSpace latency: the canonical form is paid for out of a measured budget") {
    val rng = new java.util.Random(7)
    def iv() = { val x = rng.nextInt(4); Ivl(x, x + rng.nextInt(4 - x)) }
    val pool = (0 until 400).map { _ =>
      rng.nextInt(3) match
        case 0 => SpaceType.closed((0 to 4).filter(_ => rng.nextBoolean()).map(l => l.toLong -> iv())*)
        case 1 => SpaceType.bounded(LenBounds(rng.nextInt(3), 2 + rng.nextInt(3)), rng.nextInt(4))
        case _ => SpaceType.boundedExact(LenBounds(rng.nextInt(3), 2 + rng.nextInt(3)), rng.nextInt(4))
    }.toVector
    def run(f: (SpaceType, SpaceType) => Boolean): (Double, Int) =
      var acc = 0
      for _ <- 0 until 3; a <- pool; b <- pool do if f(a, b) then acc += 1
      val t0 = System.nanoTime()
      for _ <- 0 until 10; a <- pool; b <- pool do if f(a, b) then acc += 1
      ((System.nanoTime() - t0).toDouble / (10L * pool.size * pool.size), acc)
    val (oldNs, oldAcc) = run(oldLeqSpace)
    val (newNs, newAcc) = run(SpatialGamma.leqSpace)
    println(f"LEQSPACE LATENCY (41%% spill-carrying pool): old ${oldNs}%.0f ns/call, " +
      f"new ${newNs}%.0f ns/call (${newNs / oldNs}%.2fx); accepts old $oldAcc new $newAcc " +
      f"of ${13 * pool.size * pool.size} calls")

    // the pool an ANALYSIS actually produces: a term stays under MaxClasses=24 unless it is huge, so
    // its histogram has no spill bucket and `canonSpace` returns its argument unchanged
    val closed = (0 until 400).map(_ =>
      SpaceType.closed((0 to 4).filter(_ => rng.nextBoolean()).map(l => l.toLong -> iv())*)).toVector
    def runOn(ps: Vector[SpaceType], f: (SpaceType, SpaceType) => Boolean): Double =
      var acc = 0
      for _ <- 0 until 3; a <- ps; b <- ps do if f(a, b) then acc += 1
      val t0 = System.nanoTime()
      for _ <- 0 until 10; a <- ps; b <- ps do if f(a, b) then acc += 1
      (System.nanoTime() - t0).toDouble / (10L * ps.size * ps.size)
    val co = runOn(closed, oldLeqSpace); val cn = runOn(closed, SpatialGamma.leqSpace)
    println(f"LEQSPACE LATENCY (no spill — the common case): old ${co}%.0f ns/call, " +
      f"new ${cn}%.0f ns/call (${cn / co}%.2fx)")

    // and END TO END: `SpatialType.leq` also walks the shape tree, which is what the added histogram
    // work has to be compared against
    val prng = new java.util.Random(11)
    def rv(): SpaceValue = SpaceValue((0 until prng.nextInt(6)).map(_ =>
      PathValue(List.fill(prng.nextInt(4))("i" + prng.nextInt(4)))).toSet)
    val prod = (0 until 300).map(_ => SpatialType.of(rv())).toVector
    var pacc = 0
    // `SpatialType.leq` is `Shape.leqStrong && leqSpace`, and `&&` SHORT-CIRCUITS — so on a pair the
    // shape order already rejects, `leqSpace` is never called and the added cost is not paid at all.
    var reached = 0
    for a <- prod; b <- prod do if Shape.leqStrong(a.shape, b.shape) then reached += 1
    def timed(n: Int)(f: (SpatialType, SpatialType) => Boolean): Double =
      for _ <- 0 until 3; a <- prod; b <- prod do if f(a, b) then pacc += 1
      val t0 = System.nanoTime()
      for _ <- 0 until n; a <- prod; b <- prod do if f(a, b) then pacc += 1
      (System.nanoTime() - t0).toDouble / (n.toLong * prod.size * prod.size)
    val pNs = timed(6)((a, b) => SpatialType.leq(a, b))
    val sNs = timed(6)((a, b) => Shape.leqStrong(a.shape, b.shape))
    val lNs = timed(6)((a, b) => SpatialGamma.leqSpace(a.lens, b.lens))
    println(f"SPATIALTYPE.LEQ END TO END on ${prod.size * prod.size} pairs: leq ${pNs}%.0f ns/call; " +
      f"Shape.leqStrong alone ${sNs}%.0f ns; leqSpace alone ${lNs}%.0f ns; the shape order admits " +
      f"$reached/${prod.size * prod.size} pairs, so leqSpace is REACHED on " +
      f"${100.0 * reached / (prod.size * prod.size)}%.1f%% of calls")
  }

  test("canonSpace preserves γ EXACTLY and is idempotent; unsatSpace only ever proves ⊥") {
    // The normalisation `leqSpace` compares through must not change the MEANING of a type, only its
    // representation — otherwise the order it feeds is unsound in one direction or vacuous in the
    // other.  γ is decided here on the count-vector universe (complete for `expressible` types) and
    // on `U` and `Wide` (which reach shapes and lengths the count universe does not), so the
    // agreement is DECIDED, not sampled.
    val rng = new java.util.Random(1014)
    val ts = (0 until 12000).iterator.map(_ => randHist(rng, 2)).toVector.distinct
    val vs = UC ++ U ++ Wide.take(400)
    var checked = 0L; var changed = 0; var nonIdem = 0; var unsat = 0; var unsatWrong = 0
    var gammaDiff = 0; var firstDiff = ""
    for t <- ts do
      val c = canonSpace(t)
      if c != t then changed += 1
      // IDEMPOTENCE: the canonical form is a fixed point of the rewrite
      if canonSpace(c) != c then
        nonIdem += 1
        if firstDiff.isEmpty then firstDiff = s"canon not idempotent on ${t.show}: ${c.show} -> ${canonSpace(c).show}"
      // γ-PRESERVATION, value by value, in BOTH directions
      for v <- vs do
        val g0 = gammaSpace(t, v); val g1 = gammaSpace(c, v)
        checked += 1
        if g0 != g1 then
          gammaDiff += 1
          if firstDiff.isEmpty then firstDiff = s"γ CHANGED on ${v.pretty}: ${t.show} -> ${c.show}"
      // unsatSpace must only ever claim ⊥ of a type that really has no member
      if unsatSpace(t) then
        unsat += 1
        val w = vs.find(v => gammaSpace(t, v))
        if w.nonEmpty then
          unsatWrong += 1
          if firstDiff.isEmpty then firstDiff = s"unsatSpace claimed ⊥ of ${t.show}, member ${w.get.pretty}"
    println(s"CANON: ${ts.size} histograms, $changed rewritten, $checked (type, value) γ comparisons; " +
      s"γ differences $gammaDiff; non-idempotent $nonIdem; unsatSpace fired $unsat times, wrongly $unsatWrong")
    assertEquals(gammaDiff, 0, s"canonSpace is not γ-preserving: $firstDiff")
    assertEquals(nonIdem, 0, s"canonSpace is not idempotent: $firstDiff")
    assertEquals(unsatWrong, 0, s"unsatSpace is unsound: $firstDiff")
    assert(changed > ts.size / 20, s"only $changed of ${ts.size} were rewritten — the check is vacuous")
  }

  test("the HISTOGRAM order decided EXACTLY: leqSpace is sound, and its false negatives classified") {
    val rng = new java.util.Random(1013)
    val pool = (0 until 6000).iterator.map(_ => randHist(rng, 2)).filter(expressible)
      .toVector.distinct.take(420)
    val acc = pool.map(acceptedBits)
    val cause = scala.collection.mutable.LinkedHashMap.empty[String, Int]
    def bump(k: String): Unit = cause(k) = cause.getOrElse(k, 0) + 1
    val witness = scala.collection.mutable.LinkedHashMap.empty[String, String]
    def wit(k: String, s: => String): Unit = if !witness.contains(k) then witness(k) = s
    var pairs = 0; var held = 0; var contained = 0; var fn = 0; var unsound = 0
    var withSpill = 0
    for t <- pool if t.rest.hi > 0 do withSpill += 1
    for i <- pool.indices; _ <- 0 until 20 do
      val j = rng.nextInt(pool.size)
      val (a, b) = (pool(i), pool(j))
      pairs += 1
      val c = subsetOf(acc(i), acc(j))
      val l = leqSpace(a, b)
      if l then
        held += 1
        // THE SOUNDNESS GATE.  `UC` decides containment for these types, so a `true` here that is not
        // containment is a genuine refutation of the order — not an artifact of a small universe.
        if !c then
          unsound += 1
          wit("UNSOUND", s"a = ${a.show}\n        b = ${b.show}\n        witness = " +
            UC.find(v => gammaSpace(a, v) && !gammaSpace(b, v)).map(_.pretty).getOrElse("?"))
      if c then
        contained += 1
        if !l then
          fn += 1
          val m = SpatialGamma.leqSpaceMask(a, b)
          if acc(i).isEmpty then
            bump("a is genuinely ⊥ (γ(a) = ∅ on a COMPLETE universe)")
            bump("    ⊥ because: " + botReason(a))
          else
            for n <- SpatialGamma.LeqSpaceWhy.show(m) do bump(n)
            if partitionsDiffer(a, b) then
              bump("  …and the two length PARTITIONS differ (spill vs tracked)")
              wit("partitions", s"a = ${a.show}\n        b = ${b.show}  [${SpatialGamma.LeqSpaceWhy.show(m).mkString(",")}]")
            if a.rest.hi > 0 && !a.restLens.isEmpty && a.restLens.lo == a.restLens.hi then
              bump("  …and a's spill window is a SINGLE length (exactly a tracked class)")
            if a.at(0).hi > 1 || b.at(0).hi > 1 then
              bump("  …and an ε class permits >1 path (only one path has length 0)")
            wit("fn", s"a = ${a.show}\n        b = ${b.show}  [${SpatialGamma.LeqSpaceWhy.show(m).mkString(",")}]")
    println(f"HISTOGRAM ORDER (exact): ${pool.size} types ($withSpill with a spill bucket), $pairs pairs " +
      f"over ${UC.size} count vectors; leqSpace held $held; contained $contained; " +
      f"false negatives $fn (${100.0 * fn / math.max(1, contained)}%.1f%% of contained pairs)")
    for (k, v) <- cause.toVector.sortBy(-_._2) do println(f"    $v%5d  $k")
    for (k, s) <- witness do println(s"    witness/$k: $s")
    // SOUNDNESS first, then PRECISION.  Both are gates because this universe DECIDES containment for
    // these types, so neither number is an estimate that a future change may legitimately move.
    assertEquals(unsound, 0, s"leqSpace ACCEPTED a non-containment: ${witness.getOrElse("UNSOUND", "")}")
    assertEquals(fn, 0, "leqSpace is incomplete on a universe that decides the question — see the rows above")
    assert(withSpill > pool.size / 4, s"only $withSpill of ${pool.size} types carry a spill bucket; " +
      "the spill/tracked partition case would go unexercised")
  }

  // =============================================================================================
  // 1c. THE SHAPE ORDER, DECIDED — the other four channels review.md 4 names
  // =============================================================================================
  //
  // `Shape.leqStrong`'s completeness has never been measured: the existing SHAPE ORDER test checks
  // only that the MAY-ONLY sibling `Shape.leq` is γ_may-sound.  This one decides containment on a
  // universe that is COMPLETE for a restricted class of shapes, and the restriction is the whole
  // point — get it wrong and the measurement repeats the very artifact the cause histogram above
  // exposes.  The class: tracked heads drawn from {a, b}, depth ≤ 2, at most ONE untracked head per
  // node, and every open head set carrying a BOUNDED `otherTail` summary.
  //
  // Why that is complete on `U3` (every space value over {a, b, c} with paths of ≤2 items):
  //   - bounded length.  A `None` summary (⊤) admits an untracked head with an ARBITRARY tail, hence
  //     paths of unbounded length, which NO finite universe can express — so ⊤ summaries are excluded
  //     and every admitted path then has at most 2 items.  (That case is genuinely out of scope here,
  //     not silently assumed away: it is stated in the report.)
  //   - bounded alphabet.  γ is invariant under renaming the items a shape does not name, and with at
  //     most one untracked head per node a single representative (`c`) suffices at every level, so
  //     every member of γ(sh) has a renaming inside `U3` and both sides only ever name {a, b}.
  // `SpaceType` plays no part, so what is measured is the shape order alone.
  private lazy val U3: Vector[SpaceValue] = SpatialGamma.universe(Vector("a", "b", "c"), 2)

  private def randShapeD(rng: java.util.Random, d: Int): Shape =
    def pres(): Presence = rng.nextInt(3) match
      case 0 => Presence.No
      case 1 => Presence.May
      case _ => Presence.Must
    if d <= 0 then Shape(pres(), scala.collection.immutable.SortedMap.empty, Ivl.zero, None)
    else
      val hs = scala.collection.immutable.SortedMap.from(
        Vector[PathItem]("a", "b").filter(_ => rng.nextBoolean())
          .map(k => k -> randShapeD(rng, d - 1)).filter(_._2.possiblyNonEmpty))
      // an open head set ALWAYS carries a bounded summary here — see the note above
      val ot = Some(Shape.weaken(randShapeD(rng, d - 1))).filter(_.possiblyNonEmpty)
      val oHi = if ot.isEmpty then 0L else rng.nextInt(2).toLong
      Shape(pres(), hs, Ivl(if oHi == 0 then 0L else rng.nextInt(2).toLong, oHi),
            if oHi == 0 then None else ot)

  test("the SHAPE order decided: leqStrong is sound, and its false negatives classified by channel") {
    val rng = new java.util.Random(1015)
    // LEFT operands come from the restricted (complete-on-U3) class.  RIGHT operands may be anything
    // over the same alphabet — only γ(a) has to fit inside `U3` for a "not refuted" to mean contained —
    // so the right side is drawn from the weakenings, joins and widenings of the left, which is where
    // genuine containments live.  Comparing two independent random shapes almost never yields one.
    val shapes = (0 until 1400).iterator.map(_ => randShapeD(rng, 2)).toVector.distinct.take(240)
    val acc = shapes.map { sh =>
      val bs = new java.util.BitSet(U3.size)
      for i <- U3.indices if Shape.contains(sh, U3(i)) do bs.set(i)
      bs
    }
    val cause = scala.collection.mutable.LinkedHashMap.empty[String, Int]
    def bump(k: String): Unit = cause(k) = cause.getOrElse(k, 0) + 1
    var wit = ""
    var pairs = 0; var held = 0; var contained = 0; var fn = 0; var unsound = 0; var bot = 0
    def bitsOf(sh: Shape): java.util.BitSet =
      val bs = new java.util.BitSet(U3.size)
      for i <- U3.indices if Shape.contains(sh, U3(i)) do bs.set(i)
      bs
    for i <- shapes.indices; _ <- 0 until 60 do
      val j = rng.nextInt(shapes.size)
      val a = shapes(i)
      val b = rng.nextInt(6) match
        case 0 => shapes(j)
        case 1 => Shape.weaken(a)
        case 2 => Shape.weaken(shapes(j))
        case 3 => Shape.joinAlternatives(a, shapes(j))
        case 4 => Shape.widen(a)
        case _ => Shape.joinAlternatives(Shape.weaken(a), shapes(j))
      pairs += 1
      val c = subsetOf(acc(i), bitsOf(b))
      val l = Shape.leqStrong(a, b)
      if l then
        held += 1
        if !c then
          unsound += 1
          if wit.isEmpty then wit = s"UNSOUND ${a.show} ⊑ ${b.show}, witness " +
            U3.find(v => Shape.contains(a, v) && !Shape.contains(b, v)).map(_.pretty).getOrElse("?")
      if c then
        contained += 1
        if !l then
          fn += 1
          if acc(i).isEmpty then { bot += 1; bump("a admits NOTHING (γ(a) = ∅) — vacuous containment") }
          else
            val ns = Shape.LeqShapeWhy.show(Shape.leqStrongMask(a, b))
            for n <- ns do bump(n)
            val key = "w/" + ns.mkString(",")
            if !cause.contains(key) then
              cause(key) = 0
              println(s"      $key: ${a.show}   ⊑   ${b.show}")
    println(f"SHAPE ORDER (decided on ${U3.size} spaces): ${shapes.size} shapes, $pairs pairs; " +
      f"leqStrong held $held; contained $contained; false negatives $fn " +
      f"(${100.0 * fn / math.max(1, contained)}%.1f%% of contained pairs; $bot of them with γ(a) = ∅)")
    for (k, v) <- cause.toVector.sortBy(-_._2) do println(f"    $v%5d  $k")
    assertEquals(unsound, 0, s"Shape.leqStrong ACCEPTED a non-containment: $wit")
    assertEquals(fn, 0, "Shape.leqStrong is incomplete on a universe that decides the question")
    assert(contained > 1000, s"only $contained contained pairs — the completeness claim would be thin")
  }

  test("galois: α(γ t) ⊑ t — reductivity (a failure here is a genuine refutation)") {
    val rng = new java.util.Random(1004)
    val pool = abstractPool(rng, 800)
    var nonTrivial = 0
    for t <- pool do
      val members = U.filter(gamma(t))
      if members.nonEmpty then
        val at = alphaSet(members)
        // α over a SUBSET of γ(t) is ⊑ α(γ t), so if this is not ⊑ t the real property fails too
        assert(gammaLeqOn(U)(at, t),
               s"α(γ t ∩ U) ⋢ t — reductivity refuted\n  t = ${t.show}\n  α = ${at.show}\n" +
                 s"  witness ${gammaLeqWitness(U)(at, t).map(_.pretty)}")
        nonTrivial += 1
    println(s"GALOIS/reductive: α(γ t ∩ U) ⊑ t on $nonTrivial of ${pool.size} abstract elements " +
      s"(the rest have no member in U)")
  }

  test("galois: adjunction α S ⊑ t ⟺ S ⊆ γ t (on the finite universe)") {
    val rng = new java.util.Random(1005)
    val pool = abstractPool(rng, 700)
    var fwd = 0; var bwd = 0
    for t <- pool; _ <- 0 until 8 do
      val s = (0 until (1 + rng.nextInt(3))).map(_ => U(rng.nextInt(U.size))).toSet
      val inGamma = s.forall(gamma(t))
      val a = alphaSet(s)
      val contained = gammaLeqOn(U)(a, t)
      // ⇐ : S ⊆ γ t ⇒ α S ⊑ t.  This is the half that makes α the BEST abstraction.
      if inGamma then
        assert(contained, s"S ⊆ γ t but α S ⋢ t\n  t = ${t.show}\n  α S = ${a.show}\n" +
                          s"  witness ${gammaLeqWitness(U)(a, t).map(_.pretty)}")
        bwd += 1
      // ⇒ : α S ⊑ t ⇒ S ⊆ γ t (immediate from S ⊆ γ(α S), already checked)
      if contained then
        assert(s.forall(gamma(t)), s"α S ⊑ t but a member of S is outside γ t")
        fwd += 1
    println(s"GALOIS/adjunction: ⇐ held on $bwd sets, ⇒ held on $fwd sets (both directions decided on U)")
  }

  test("the code's `within` is NOT γ-containment (upper envelope only)") {
    // review.md: `within` compares upper envelopes and ignores every lower bound
    val a = SpaceType.closed(1L -> Ivl(0, 3))
    val b = SpaceType.closed(1L -> Ivl(2, 5))
    assert(a.within(b), "precondition: within holds on the envelopes")
    val witness = SpaceValue(Set.empty)
    assert(gammaSpace(a, witness), "∅ is in γ(a)")
    assert(!gammaSpace(b, witness), "∅ is NOT in γ(b) — b asserts at least two length-1 paths")
    // the order that IS γ-containment rejects the pair
    assert(!leqSpace(a, b), "leq must reject what within accepts")
    // and `leq` accepts the genuine refinement
    assert(leqSpace(SpaceType.closed(1L -> Ivl(2, 4)), b))
    assert(gammaLeqOn(U)(SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(2, 4))),
                         SpatialType(Shape.top, b)))
    println(s"WITHIN vs LEQ: within(${a.show}, ${b.show}) = true, γ-containment = false, witness = ∅")
  }

  test("`SpatialTyping.withinEnvelope` is WEAKER than γ — the dispatcher gate admits non-members") {
    // a runtime dispatcher built on `satisfies` (SpecializedRoutine.applicableTo) can select a
    // specialisation for an input that does NOT satisfy the precondition it was derived under.
    val t = SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(1, 2), 2L -> Ivl(1, 2)))
    val v = SpaceValue(Set(PathValue(List("a", "b")), PathValue(List("b", "b"))))
    assert(!gamma(t)(v), "v has no length-1 path, so it is not in γ(t)")
    println(s"SATISFIES named witness: t = ${t.show}, v = ${v.pretty} — " +
      s"γ = false, satisfies = ${SpatialTyping.withinEnvelope(v, t)}")
    // the same gap, searched for systematically over the universe
    val rng = new java.util.Random(1006)
    val pool = abstractPool(rng, 300)
    var admits = 0; var rejectsMember = 0; var pairs = 0
    for tt <- pool; v2 <- U do
      pairs += 1
      val g = gamma(tt)(v2); val s = SpatialTyping.withinEnvelope(v2, tt)
      if s && !g then admits += 1
      if g && !s then rejectsMember += 1
    println(s"SATISFIES vs γ: $pairs pairs — satisfies accepts a non-member $admits times; " +
      s"rejects a genuine member $rejectsMember times")
    // THE GATE, in the direction that must always hold: a dispatcher whose test rejects a genuine
    // member of the precondition would silently fall back and lose the specialisation.
    assertEquals(rejectsMember, 0, "satisfies must at least accept every γ-member")
    // the other direction is a FINDING, not a gate: `withinEnvelope` checks the class interval only
    // of the lengths PRESENT in the value, so it accepts values that violate a positive class lower
    // bound.  Certified as a ground statement in proofs/spatial-semantic/gsem_satisfies_weaker.smt2.
    //
    // WHAT CHANGED (review.md 1): no dispatcher is built on this predicate any more.
    // `SpecializedRoutine.applicableTo`, `BoundedRecursion.applicableTo` and
    // `SpatialPipeline.GuardedRoutine.applicableTo` all decide with full γ (`SpatialTyping.accepts`),
    // so the gap measured here is no longer reachable from a guarded specialisation.  The assertion
    // below pins that, so the claim cannot rot back into being true.
    assert(SpatialTyping.SpecializedRoutine(Map(SpaceMention("m") -> t), Routine(RoutinePtr("r"),
             Vector.empty, Vector(SpaceMention("m")), Space.Empty), Vector.empty)
             .applicableTo(Map(SpaceMention("m") -> v)) == false,
           "a guarded dispatcher must REJECT the witness the envelope admits — it must use full γ")
    if admits == 0 then println("  (the envelope/γ gap no longer shows on this pool — recheck the finding)")
  }

  /** abstract elements the order tests run on: α of universe values, joins of a few of them, and
   *  real analysis results — so the pool contains elements α alone never produces. */
  private def abstractPool(rng: java.util.Random, n: Int): Vector[SpatialType] =
    val b = Vector.newBuilder[SpatialType]
    for _ <- 0 until n do
      rng.nextInt(3) match
        case 0 => b += alpha(U(rng.nextInt(U.size)))
        case 1 => b += alphaSet((0 until (2 + rng.nextInt(3))).map(_ => U(rng.nextInt(U.size))).toSet)
        case _ =>
          val v0 = U(rng.nextInt(U.size)); val v1 = U(rng.nextInt(U.size))
          val env = SpatialTyping.Env(spaces = Map(opSpaces(0) -> alpha(v0), opSpaces(1) -> alpha(v1)))
          val op = ops(rng.nextInt(ops.size))
          if op.body == BodyKind.NoBody && op.pathArity == 0 && op.arity <= 2 && op.name != "Call" then
            val node = op.build(Vector(Space.Mention(opSpaces(0)), Space.Mention(opSpaces(1))), Vector.empty, Space.Empty)
            b += SpatialTyping.infer(node, env)
          else b += alpha(v0)
    b.result()

  // =============================================================================================
  // 2. SIMULATION SQUARES — one row per operator
  // =============================================================================================

  // ---------------------------------------------------------------------------------------------
  // REGRESSION REPRODUCERS.  Each of the three below is the minimal witness for an unsoundness this
  // suite FOUND in the 2026-08-07T01:30 revision of SpatialShape.scala (`Shape.restrict`,
  // `Shape.tailsInter`, `Shape.widen`).  All three are repaired in the current revision; the
  // reproducers stay as named regression tests, because random search found each of them only after
  // the generator was pushed into the regime that triggers it.
  // ---------------------------------------------------------------------------------------------

  test("regression: restriction of an OPEN-headed operand by a CLOSED prefix set is not ∅") {
    // was: `keys = x.heads ∩ prefixes.heads` as soon as `prefixes` was closed.  With `x = ⊤` (a free
    // mention) `x.heads` is EMPTY but `x`'s head set is OPEN, so every key was dropped and the
    // result was `Shape.empty` — `Fact.DefinitelyEmpty` for a restriction that keeps {a}.
    val t = Space.Restriction(Space.Mention(SpaceMention("s0")), Space.Literal(SpaceValue(Set(PathValue(List("a"))))))
    val abs = SpatialTyping.infer(t)
    val concrete = eval(t)(using PathContext.emptyMap,
      SpaceContextMap(Map(SpaceMention("s0") -> SpaceValue(Set(PathValue(List("a")))))))
    assertEquals(concrete, SpaceValue(Set(PathValue(List("a")))), "the restriction really does keep {a}")
    assert(!abs.isProvablyEmpty, s"claimed empty: ${abs.show}")
    assert(!Fact.from(abs).contains(Fact.DefinitelyEmpty))
    assert(gamma(abs)(concrete), s"γ violated: ${abs.show} vs ${concrete.pretty}")
  }

  test("regression: TailsIntersection must not intersect over MAY-present heads") {
    // was: the transfer intersected the tail-sets of every head that MAY be present, and
    // intersecting with an extra set only SHRINKS — so head `a` (reduced to may-present by the meet
    // with ⊤) deleted the ε that head `b` really contributes, and the answer was ∅ instead of {ε}.
    val t = Space.TailsIntersection(Space.Intersection(
      Space.Literal(SpaceValue(Set(PathValue(List("a", "x")), PathValue(List("b"))))),
      Space.Mention(SpaceMention("s0"))))
    val abs = SpatialTyping.infer(t)
    val concrete = eval(t)(using PathContext.emptyMap,
      SpaceContextMap(Map(SpaceMention("s0") -> SpaceValue(Set(PathValue(List("b")))))))
    assertEquals(concrete, SpaceValue(Set(PathValue(Nil))), "the real result is {ε}, not ∅")
    assert(!abs.isProvablyEmpty, s"claimed empty: ${abs.show}")
    assert(gamma(abs)(concrete), s"γ violated: ${abs.show} vs {ε}")
  }

  test("regression: the over-cap head summary must not carry a sibling's MUST") {
    // was: `widen` folded the spilled heads' children with `Shape.union`, which is the transfer for
    // `A ∪ B` (ε via `Presence.or`, Must-preserving) and NOT a join.  `under(h)` then handed that
    // summary back as ONE untracked head's tail shape, attributing a12's forced ε to a13.
    val wide = SpaceValue(((0 to 11).map(i => PathValue(List(f"a$i%02d", "z")))
      ++ Vector(PathValue(List("a12")), PathValue(List("a13", "x")))).toSet)
    val sh = Shape.of(wide)
    assertEquals(sh.others.hi, 2L, "precondition: two heads spilled past MaxHeads=12")
    assert(sh.otherTail.forall(t => !t.eps.mustBe), s"summary still forces ε: ${sh.otherTail.map(_.show)}")
    assert(gammaShape(sh, wide), s"v ∉ γ(α v): ${sh.show}")
    assert(gammaShapeMay(sh, wide))
  }

  test("γ agreement: Shape.contains ≡ SpatialGamma.gammaShape (the two copies must not drift)") {
    // SpatialShape.scala keeps a local copy of γ so the domain's own gate is self-contained.  Two
    // copies of a definition is two definitions; this pins them together.
    val rng = new java.util.Random(1007)
    var n = 0
    val shapes = (0 until 400).map(_ => rng.nextInt(3) match
      case 0 => Shape.of(randValue(rng))
      case 1 => Shape.union(Shape.of(randValue(rng)), Shape.of(randValue(rng)))
      case _ => lubShape(Shape.of(randValue(rng)), Shape.of(randValue(rng))))
    for sh <- shapes; v <- Vector(randValue(rng), randValue(rng)) ++ U.take(24) do
      assertEquals(Shape.contains(sh, v), gammaShape(sh, v),
                   s"the two γ definitions disagree on ${sh.show} / ${v.pretty}")
      n += 1
    println(s"γ AGREEMENT: Shape.contains ≡ SpatialGamma.gammaShape on $n (shape, value) pairs")
  }

  test("Shape.leq ⇒ γ_may-containment (the domain's own order is sound for its own γ)") {
    val rng = new java.util.Random(1008)
    val shapes = (0 until 260).map(_ => rng.nextInt(4) match
      case 0 => Shape.of(randValue(rng))
      case 1 => Shape.weaken(Shape.of(randValue(rng)))
      case 2 => Shape.union(Shape.of(randValue(rng)), Shape.of(randValue(rng)))
      case _ => lubShape(Shape.of(randValue(rng)), Shape.of(randValue(rng)))).toVector
    var held = 0; var bad = 0; var w = ""
    for a <- shapes; _ <- 0 until 4 do
      val b = shapes(rng.nextInt(shapes.size))
      if Shape.leq(a, b) then
        held += 1
        val ce = U.find(v => gammaShapeMay(a, v) && !gammaShapeMay(b, v))
        if ce.nonEmpty then
          bad += 1
          if w.isEmpty then w = s"${a.show}  leq  ${b.show}  but ${ce.get.pretty} ∈ γ_may(a) ∖ γ_may(b)"
    println(s"SHAPE ORDER: Shape.leq held on $held pairs; γ_may-containment refuted on $bad" +
      (if w.isEmpty then "" else s"\n      $w"))
    assertEquals(bad, 0, s"Shape.leq is not sound for γ_may: $w")
  }

  /** Rows whose square fails under the MAY-ONLY reading.  Empty: the current revision of
   *  `SpatialShape.scala`/`SpatialTypeSystem.scala` passes every row of the matrix. */
  private val expectedMayUnsound: Set[String] = Set()

  /** does this shape tree contain an over-cap summary node (`others.hi > 0` with an `otherTail`)?
   *  Every strictly-strong (Must-only) failure the matrix finds must be attributable to one — that
   *  is FINDING 3, and it is the gate: an unattributable Must failure is a NEW leak. */
  private def hasSummary(sh: Shape): Boolean =
    (sh.others.hi > 0 && sh.otherTail.nonEmpty) || sh.heads.exists((_, c) => hasSummary(c)) ||
      sh.otherTail.exists(hasSummary)

  /** one square: abstract the operands with α, run the real transfer, run the real semantics,
   *  classify the outcome.  `hist` = the length/count component alone is wrong (stop-ship);
   *  `may` = the may-only content is wrong (stop-ship); `mustCap` = only the Must channel is wrong
   *  AND an over-cap summary node is present (FINDING 3); `mustOther` = only the Must channel is
   *  wrong with NO summary node — an unexplained leak, which is the gate. */
  private final case class Tally(var n: Int = 0, var hist: Int = 0, var may: Int = 0,
                                 var mustCap: Int = 0, var mustOther: Int = 0,
                                 var wHist: String = "", var wMay: String = "", var wMust: String = "")

  private def classify(ta: Tally, node: Space, ins: Vector[SpaceValue], out: SpaceValue, t: SpatialType): Unit =
    ta.n += 1
    def w(tag: String) = s"$tag ${node.show.take(110)} | in=${ins.map(_.pretty).mkString(" ; ")} " +
      s"| out=${out.pretty} | t=${t.show}"
    if !gammaSpace(t.lens, out) then
      ta.hist += 1; if ta.wHist.isEmpty then ta.wHist = w("HIST")
    if !gammaMay(t)(out) then
      ta.may += 1; if ta.wMay.isEmpty then ta.wMay = w("MAY")
    else if !gamma(t)(out) then
      if hasSummary(t.shape) then { ta.mustCap += 1 }
      else { ta.mustOther += 1; if ta.wMust.isEmpty then ta.wMust = w("MUST-UNEXPLAINED") }

  private def report(title: String, tally: scala.collection.mutable.LinkedHashMap[String, Tally]): Unit =
    println(s"$title  (trials | hist-fail | may-fail | must-fail-at-cap | must-fail-unexplained)")
    for (name, ta) <- tally do
      println(f"  $name%-18s ${ta.n}%5d | hist=${ta.hist}%4d | may=${ta.may}%4d | " +
        f"mustCap=${ta.mustCap}%4d | mustOther=${ta.mustOther}%4d")
      for s <- Vector(ta.wHist, ta.wMay, ta.wMust) if s.nonEmpty do println(s"      $s")

  private def gate(tally: scala.collection.mutable.LinkedHashMap[String, Tally]): Unit =
    val histBad = tally.filter(_._2.hist > 0).keys.toSet
    assertEquals(histBad, Set.empty[String], s"the LENGTH/COUNT component is UNSOUND on: $histBad")
    val mayBad = tally.filter(_._2.may > 0).keys.toSet
    assertEquals(mayBad -- expectedMayUnsound, Set.empty[String],
                 s"NEW may-only unsoundness — see the witnesses above: ${mayBad -- expectedMayUnsound}")
    val mustBad = tally.filter(_._2.mustOther > 0).keys.toSet
    assertEquals(mustBad, Set.empty[String],
                 s"Must-channel leak NOT attributable to an over-cap summary (FINDING 3): $mustBad")
    val fixed = expectedMayUnsound -- mayBad
    if fixed.nonEmpty then println(s"  (now may-sound, remove from expectedMayUnsound: $fixed)")

  test("simulation squares: eval(s) ∈ γ(infer(s)) for EVERY operator") {
    val rng = new java.util.Random(2024)
    val trials = 300
    val tally = scala.collection.mutable.LinkedHashMap.from(ops.map(o => o.name -> Tally()))
    for op <- ops; literalMode <- Vector(false, true); _ <- 0 until trials do
      val vs = Vector.fill(op.arity)(randValue(rng))
      val qs = Vector.fill(op.pathArity)(randPathValue(rng))
      val (node, env, pc, sc) = trial(op, vs, qs, bodyFor(op, rng), literalMode)
      classify(tally(op.name), node, vs, eval(node)(using pc, sc, routineTable),
               SpatialTyping.infer(node, env))
    report("SIMULATION SQUARES: eval(s) ∈ γ(infer(s))", tally)
    gate(tally)
  }

  // =============================================================================================
  // 3. TRANSFERS OVER NON-EXACT OPERANDS: γ(a op# b) ⊇ γ(a) op γ(b)
  // =============================================================================================

  test("γ(a op# b) ⊇ γ(a) op γ(b) — transfers at abstract operands α never produces") {
    val rng = new java.util.Random(3030)
    // only the rows whose abstract operands can be supplied as free mentions with no path/body
    val rows = ops.filter(o => o.body == BodyKind.NoBody && o.pathArity == 0 && o.arity >= 1 && o.name != "Call")
    val pool = abstractPool(rng, 250).filter(t => U.exists(gamma(t)))
    val tally = scala.collection.mutable.LinkedHashMap.from(rows.map(o => o.name -> Tally()))
    for op <- rows; _ <- 0 until 900 do
      val as = Vector.fill(op.arity)(pool(rng.nextInt(pool.size)))
      val members = as.map(a => U.filter(gamma(a)))
      if members.forall(_.nonEmpty) then
        val vs = members.map(m => m(rng.nextInt(m.size)))
        val spaces = as.indices.map(i => Space.Mention(opSpaces(i))).toVector
        val node = op.build(spaces, Vector.empty, Space.Empty)
        val env = SpatialTyping.Env(spaces = as.indices.map(i => opSpaces(i) -> as(i)).toMap)
        val concrete = eval(node)(using PathContext.emptyMap,
          SpaceContextMap(vs.indices.map(i => opSpaces(i) -> vs(i)).toMap), PartialFunction.empty)
        classify(tally(op.name), node, vs, concrete, SpatialTyping.infer(node, env))
    report("TRANSFER at NON-EXACT abstract operands: γ(a op# b) ⊇ γ(a) op γ(b)", tally)
    gate(tally)
  }

  test("γ(a op# b) ⊇ γ(a) op γ(b) with OPEN head sets and an otherTail summary") {
    // The universe-driven test above cannot reach the `others`/`otherTail` channels at all: with a
    // two-item alphabet nothing exceeds `Shape.MaxHeads`, so every shape it builds is head-closed.
    // Those are exactly the channels `proofs/spatial-semantic/gsem_l2_union_sound.smt2` shows are
    // delicate, so they get their own generator: operands built from >12-head values (so `mk` spills
    // and produces a summary), and concrete members found by random subset search.
    val rng = new java.util.Random(3131)
    def wide(): SpaceValue =
      SpaceValue((0 until (13 + rng.nextInt(8))).map(i =>
        if rng.nextBoolean() then PathValue(List("h" + i))
        else PathValue(List("h" + i, "t" + rng.nextInt(2)))).toSet)
    val rows = ops.filter(o => o.body == BodyKind.NoBody && o.pathArity == 0 && o.arity >= 1 && o.name != "Call")
    val tally = scala.collection.mutable.LinkedHashMap.from(rows.map(o => o.name -> Tally()))
    var withSummary = 0
    for op <- rows; _ <- 0 until 260 do
      // a non-exact operand with an open head set: the join of two wide abstractions
      val bases = Vector.fill(op.arity)((wide(), wide()))
      val as = bases.map((u, v) => lub(alpha(u), alpha(v)))
      // members of γ: random subsets of the two underlying values' paths that pass γ
      val vs = bases.zip(as).map { case ((u, v), a) =>
        val pool = (u.paths ++ v.paths).toVector
        var found: SpaceValue = u
        var i = 0
        while i < 40 do
          val cand = SpaceValue(pool.filter(_ => rng.nextInt(3) > 0).toSet)
          if gamma(a)(cand) then { found = cand; i = 40 } else i += 1
        found
      }
      if as.exists(a => hasSummary(a.shape)) then withSummary += 1
      if vs.zip(as).forall((v, a) => gamma(a)(v)) then
        val spaces = as.indices.map(i => Space.Mention(opSpaces(i))).toVector
        val node = op.build(spaces, Vector.empty, Space.Empty)
        val env = SpatialTyping.Env(spaces = as.indices.map(i => opSpaces(i) -> as(i)).toMap)
        val concrete = eval(node)(using PathContext.emptyMap,
          SpaceContextMap(vs.indices.map(i => opSpaces(i) -> vs(i)).toMap), PartialFunction.empty)
        classify(tally(op.name), node, vs, concrete, SpatialTyping.infer(node, env))
    report(s"OPEN-HEADED operands ($withSummary of the operand sets carried an otherTail summary)", tally)
    gate(tally)
  }

  // =============================================================================================
  // 4. CONDITIONAL REWRITES
  // =============================================================================================

  test("conditional rewrite: equivalent under the precondition, and the precondition is load-bearing") {
    // ys : only length-2 paths.  Then `ys <| {length-4 prefix}` is provably empty (restriction
    // annihilation), so the whole intermediate computation built on it is dead — but ONLY under
    // that annotation.
    val prefix = PathValue(List("k", "k", "k", "k"))
    val prog = Space.Union(Space.Literal(SpaceValue(Set(PathValue(List("live"))))),
                           Space.Wrap(Space.Restriction(S"ys", Space.Literal(SpaceValue(Set(prefix)))),
                                      Path.Constant(PathValue(List("w")))))
    val pre = SpaceType.closed(2L -> Ivl(0, 9))
    val env = SpatialEnv(spaces = Map(SpaceMention("ys") -> pre))
    val e = SpatialTypes.eliminate(prog, env)
    assert(e.removed.nonEmpty, "the specialisation must fire")
    assertEquals(SpatialTypes.eliminate(prog, SpatialEnv()).removed, Vector.empty,
                 "and it must fire ONLY because of the annotation")
    val preT = SpatialType(Shape.top, pre)
    val rng = new java.util.Random(4040)
    // the input generator MUST be able to violate the precondition in the way that matters (a path
    // that really does start with the length-4 prefix), or "the precondition is load-bearing" is an
    // untested claim
    def input(): SpaceValue = rng.nextInt(3) match
      case 0 => SpaceValue((0 until rng.nextInt(4)).map(_ =>            // conforming: length 2 only
                  PathValue(List("q" + rng.nextInt(3), "q" + rng.nextInt(3)))).toSet)
      case 1 => SpaceValue((0 until (1 + rng.nextInt(3))).map(_ =>      // violating AND observable
                  PathValue(prefix.items ++ List("t" + rng.nextInt(3)))).toSet)
      case _ => randValue(rng)
    var conforming = 0; var violating = 0; var differed = 0
    for _ <- 0 until 3000 do
      val v = input()
      given SpaceContext = SpaceContextMap(Map(SpaceMention("ys") -> v))
      val same = eval(e.residual) == eval(prog)
      if gammaSpace(pre, v) then
        conforming += 1
        assert(same, s"specialisation disagrees on a CONFORMING input ${v.pretty}")
      else
        violating += 1
        if !same then differed += 1
    println(s"CONDITIONAL REWRITE: $conforming conforming inputs all agree; " +
      s"$violating violating inputs, $differed of them DIFFER (the precondition is load-bearing)")
    assert(differed > 0, "if no violating input ever differs the precondition proves nothing")
    // and one explicit witness, so the property is not just a statistic
    locally {
      val bad = SpaceValue(Set(PathValue(prefix.items :+ "tail")))
      assert(!gammaSpace(pre, bad))
      given SpaceContext = SpaceContextMap(Map(SpaceMention("ys") -> bad))
      assertNotEquals(eval(e.residual), eval(prog), "the named witness must differ")
    }
    // the guarded artifact: applicableTo must gate the residual
    val r = Routine(RoutinePtr("f"), Vector.empty, Vector(SpaceMention("ys")), prog)
    val spec = SpatialTyping.SpecializedRoutine(Map(SpaceMention("ys") -> preT),
      Routine(r.name, r.refs, r.mentions, e.residual), Fact.from(SpatialTyping.infer(prog,
        SpatialTyping.Env(spaces = Map(SpaceMention("ys") -> preT)))))
    var gated = 0; var admittedNonMember = 0
    for _ <- 0 until 2000 do
      val v = input()
      val args = Map(SpaceMention("ys") -> v)
      if spec.applicableTo(args) then
        gated += 1
        if !gamma(preT)(v) then admittedNonMember += 1
        given SpaceContext = SpaceContextMap(args)
        assert(eval(spec.residual.body) == eval(prog),
               s"a dispatcher-admitted input disagrees: ${v.pretty}")
    println(s"  SpecializedRoutine.applicableTo admitted $gated/2000 inputs, " +
      s"$admittedNonMember of them outside γ(precondition)")
  }

  test("conditional rewrite on the corpus: annotated specialisation agrees on conforming inputs") {
    val f = new java.io.File(Loaders.repoRoot, "corpus_1000.ser")
    assume(f.exists, "corpus not found")
    val recs = locally {
      val ois = new java.io.ObjectInputStream(new java.io.FileInputStream(f))
      try ois.readObject().asInstanceOf[Vector[FuzzRec]] finally ois.close()
    }
    val rng = new java.util.Random(5050)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector
    var fired = 0; var checks = 0; var conforming = 0
    for r <- recs do
      // the ANNOTATION is the abstraction of one concrete binding — a real precondition, not vacuous
      val base = sNames.map(_ -> randValue(rng)).toMap
      val pvs = pNames.map(_ -> randPathValue(rng)).toMap
      val env = SpatialEnv(spaces = base.view.mapValues(v => SpaceType.of(v)).toMap,
                           paths = pvs.view.mapValues(p => LenBounds(p.items.length, p.items.length)).toMap)
      val e = SpatialTypes.eliminate(r.prog, env)
      if e.removed.nonEmpty then fired += 1
      // the binding the annotation was derived from must agree
      val pc = PathContextMap(pvs)
      locally {
        val sc = SpaceContextMap(base)
        assertEquals(eval(e.residual)(using pc, sc), eval(r.prog)(using pc, sc),
                     s"annotated specialisation changed meaning on ${r.prog.show.take(120)}")
        checks += 1
      }
      // and a DIFFERENT binding that still conforms to the same annotation (same per-length counts,
      // different items) — this is the part an "eliminate on the value it was derived from" test
      // cannot see
      val alt = sNames.map(n => n -> permute(base(n), rng)).toMap
      if sNames.forall(n => gammaSpace(SpaceType.of(base(n)), alt(n))) then
        conforming += 1
        val sc = SpaceContextMap(alt)
        assertEquals(eval(e.residual)(using pc, sc), eval(r.prog)(using pc, sc),
                     s"specialisation disagrees on a DIFFERENT conforming binding for ${r.prog.show.take(120)}")
        checks += 1
    println(s"CORPUS SPECIALISATION: fired on $fired/${recs.size}; $checks differential checks clean " +
      s"($conforming of them on a second conforming binding)")
  }

  /** a value with the SAME per-length counts but different items — still in γ of the annotation */
  private def permute(v: SpaceValue, rng: java.util.Random): SpaceValue =
    val out = scala.collection.mutable.Set.empty[PathValue]
    for p <- v.paths.toVector.sortBy(_.show) do
      var q = PathValue(p.items.map(_ => "z" + rng.nextInt(1000)))
      while out.contains(q) do q = PathValue(p.items.map(_ => "z" + rng.nextInt(1000)))
      out += q
    SpaceValue(out.toSet)
end SpatialLawCheck
