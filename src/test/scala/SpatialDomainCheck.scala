package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==============================================================================================
 *  A3 — THE TWO-TIER CORRELATED DOMAIN, AGAINST ITS ACCEPTANCE SENTENCE.
 *
 *  "lattice and gamma checks pass; exact-tier disjointness and extrema survive depth and
 *  width collapse; summarized results contain all counted outcomes; results are invariant under prior
 *  analyses in the same JVM; every loss of precision is present in the returned analysis certificate."
 *  ============================================================================================== */
class SpatialDomainCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  val rng = new java.util.Random(20260905)
  val items = Vector("a", "b", "c")
  /** a random small space over three items, depth ≤ 2 */
  def randValue(): SpaceValue =
    val all = SpatialGamma.allPaths(items, 2)
    SpaceValue(all.filter(_ => rng.nextInt(4) == 0).toSet)
  /** the finite universe every γ-claim is checked against */
  lazy val universe: Vector[SpaceValue] = SpatialGamma.universe(Vector("a", "b"), 2)

  def gamma(d: Domain, x: XNode): Set[SpaceValue] = universe.filter(v => d.member(x, v)).toSet

  // ---- 1. lattice and gamma ------------------------------------------------------------------------------

  test("γ ∘ α: every value is in the γ of its exact node, and the exact node's γ is that value alone") {
    val d = new Domain
    for _ <- 0 until 200 do
      val v = randValue()
      val x = d.alpha(v)
      assert(d.member(x, v), s"${v.pretty} ∉ γ(α ${v.pretty})")
      assertEquals(d.enumerate(x), Some(Vector(v)), "an exact node enumerates to its one value")
      assertEquals(d.size(x), Ivl(v.paths.size, v.paths.size))
    println(s"DOMAIN: γ∘α exact on 200 random values; arena ${d.arena.size} nodes")
  }

  test("join is an upper bound and meet a lower bound, on the finite universe, both tiers") {
    val d = new Domain(DomainBudget(alternatives = 6))
    var joins = 0; var meets = 0; var widened = 0
    val vs = universe.filter(_ => rng.nextInt(6) == 0).take(40)
    for a <- vs; b <- vs.take(12) do
      val (xa, xb) = (d.alpha(a), d.alpha(b))
      val j = d.join(xa, xb)
      assert((gamma(d, xa) union gamma(d, xb)).subsetOf(gamma(d, j)), s"join not an upper bound: ${a.pretty} ⊔ ${b.pretty}")
      joins += 1
      d.meet(xa, xb) match
        case Some(m) => assert((gamma(d, xa) intersect gamma(d, xb)).subsetOf(gamma(d, m))); meets += 1
        case None => assert((gamma(d, xa) intersect gamma(d, xb)).isEmpty, "⊥ meet of two values with a common member")
      // the summarized tier: join through the projection
      val (sa, sb) = (d.arena.summ(d.summary(xa), Cause.Literal), d.arena.summ(d.summary(xb), Cause.Literal))
      val sj = d.join(sa, sb)
      assert((gamma(d, sa) union gamma(d, sb)).subsetOf(gamma(d, sj)), "summarized join not an upper bound")
      d.meet(sa, sb).foreach(m => assert((gamma(d, sa) intersect gamma(d, sb)).subsetOf(gamma(d, m)), "summarized meet not a lower bound"))
      // exact ⊓ summarized filters by γ
      d.meet(xa, sb).foreach(m => assert((gamma(d, xa) intersect gamma(d, sb)).subsetOf(gamma(d, m))))
    // a chain of joins past the alternatives budget widens, and the widening is still an upper bound
    var acc: XNode = d.alpha(vs.head)
    for v <- vs.tail do acc = d.join(acc, d.alpha(v))
    for v <- vs do assert(d.member(acc, v), s"a widened join lost ${v.pretty}")
    widened = d.certificate.widenings.length
    assert(widened > 0, "40 alternatives under a budget of 6 must widen")
    println(s"DOMAIN: $joins joins, $meets meets sound on the universe; $widened widening(s) recorded: ${d.certificate.widenings.head.show}")
  }

  test("the order is sound: leq(a, b) ⇒ γ(a) ⊆ γ(b), and the projection is ⊒ its node") {
    val d = new Domain
    val vs = universe.filter(_ => rng.nextInt(5) == 0).take(30)
    val nodes = vs.map(d.alpha(_)) ++ vs.take(5).map(v => d.arena.summ(SpatialType.of(v), Cause.Literal)) :+
      d.join(d.alpha(vs(0)), d.alpha(vs(1)))
    var decided = 0
    for a <- nodes; b <- nodes if d.leq(a, b) do
      decided += 1
      assert(gamma(d, a).subsetOf(gamma(d, b)), s"leq claimed but γ(a) ⊄ γ(b): ${a.show} vs ${b.show}")
    for a <- nodes do
      val s = d.arena.summ(d.summary(a), Cause.Summarised(a.id))
      assert(d.leq(a, s), s"a node is below its projection: ${a.show} vs ${s.show}")
      assert(gamma(d, a).subsetOf(gamma(d, s)))
    println(s"DOMAIN: $decided leq decisions sound; projections dominate their nodes")
  }

  test("the exact-tier operations are EXACT: γ(op#) equals the image, for every binary and unary operation") {
    val d = new Domain
    val vs = universe.filter(_ => rng.nextInt(7) == 0).take(14)
    val binops: Vector[(String, (XNode, XNode) => XNode, (Space, Space) => Space)] = Vector(
      ("union", d.union, Space.Union.apply), ("inter", d.inter, Space.Intersection.apply),
      ("sub", d.sub, Space.Subtraction.apply), ("restrict", d.restrict, Space.Restriction.apply),
      ("raff", d.raff, Space.Raffination.apply), ("comp", d.comp, Space.Composition.apply))
    val s0 = SpaceMention("s0"); val s1 = SpaceMention("s1")
    var checks = 0
    for (name, op, term) <- binops; a <- vs; b <- vs do
      val r = op(d.alpha(a), d.alpha(b))
      val truth = eval(term(Space.Mention(s0), Space.Mention(s1)))(using PathContextMap(Map.empty), SpaceContextMap(Map(s0 -> a, s1 -> b)), PartialFunction.empty)
      assertEquals(d.enumerate(r), Some(Vector(truth)), s"$name(${a.pretty}, ${b.pretty}) = ${truth.pretty} but the domain says ${r.show}")
      checks += 1
    val unops: Vector[(String, XNode => XNode, Space => Space)] = Vector(
      ("tails-union", d.tailsUnion, Space.TailsUnion.apply), ("tails-inter", d.tailsInter, Space.TailsIntersection.apply),
      ("wrap-ab", d.wrap(List("a", "b"), _), x => Space.Wrap(x, Path.Constant(p("a", "b")))),
      ("unwrap-a", d.unwrap(_, List("a")), x => Space.Unwrap(x, Path.Constant(p("a")))),
      ("range-first", d.range(_, 0, 1), x => Space.Range(x, 0, 1)), ("range-last", d.range(_, -1, 0), x => Space.Range(x, -1, 0)),
      ("range-mid", d.range(_, 2, 4), x => Space.Range(x, 2, 4)))
    for (name, op, term) <- unops; a <- vs do
      val r = op(d.alpha(a))
      val truth = eval(term(Space.Mention(s0)))(using PathContextMap(Map.empty), SpaceContextMap(Map(s0 -> a)), PartialFunction.empty)
      assertEquals(d.enumerate(r), Some(Vector(truth)), s"$name(${a.pretty}) = ${truth.pretty} but the domain says ${r.show}")
      checks += 1
    // and over CHOICES: the image of the alternatives is contained (and, choice-free operands aside, equal)
    val c1 = d.join(d.alpha(vs(0)), d.alpha(vs(1))); val c2 = d.join(d.alpha(vs(2)), d.alpha(vs(3)))
    for (name, op, term) <- binops do
      val r = op(c1, c2)
      for a <- Vector(vs(0), vs(1)); b <- Vector(vs(2), vs(3)) do
        val truth = eval(term(Space.Mention(s0), Space.Mention(s1)))(using PathContextMap(Map.empty), SpaceContextMap(Map(s0 -> a, s1 -> b)), PartialFunction.empty)
        assert(d.member(r, truth), s"$name over choices lost ${truth.pretty}")
        checks += 1
    assert(d.certificate.exact, s"no widening should be needed here: ${d.certificate.show}")
    println(s"DOMAIN: $checks exact-tier operation checks against eval")
  }

  // ---- 2. survival of disjointness and extrema past the shape caps --------------------------------------

  test("exact-tier disjointness and extrema SURVIVE depth and width collapse") {
    val d = new Domain
    // 15-deep paths — past Shape.MaxDepth — and 40 heads — past Shape.MaxHeads
    def deep(tag: String, n: Int): SpaceValue = SpaceValue((0 until n).map(i => PathValue(tag :: (1 to 14).map(j => s"x${(i + j) % 7}").toList)).toSet)
    val a = deep("L", 6); val b = deep("R", 6)
    val (xa, xb) = (d.alpha(a), d.alpha(b))
    assert(DomainFacts.headDisjoint(d, xa, xb), "exact head sets decide disjointness")
    assertEquals(DomainFacts.orderMin(d, xa), Some(a.paths.min(using pathValueOrdering)))
    assertEquals(DomainFacts.orderMax(d, xb), Some(b.paths.max(using pathValueOrdering)))
    assertEquals(DomainFacts.fibre(d, xa, List("L")), Ivl(6, 6))
    // the SUMMARIZED reading of the same nodes has collapsed the depth and lost the extrema …
    val (sa, sb) = (d.summary(xa), d.summary(xb))
    println(s"DOMAIN: 15-deep summaries — shape depth ${sa.shape.depth} (cap ${Shape.MaxDepth}); orderMin=${sa.shape.orderMin.map(_.show)}")
    // … but the head-set disjointness survives THROUGH the summaries too (the certificate tier, 1C.1)
    assert(sa.shape.possibleHeads.exists(x => sb.shape.possibleHeads.exists(y => (x intersect y).isEmpty)),
           "summarized head disjointness")
    // width: 40 heads
    val wide = SpaceValue((0 until 40).map(i => p(s"h$i", "t")).toSet)
    val xw = d.alpha(wide)
    assertEquals(DomainFacts.fanOut(d, xw), Ivl(40, 40))
    assertEquals(DomainFacts.orderMin(d, xw), Some(p("h0", "t")))
    assertEquals(DomainFacts.orderMax(d, xw), Some(p("h9", "t")))
    val sw = d.summary(xw)
    println(s"DOMAIN: 40-head summary — headCount ${sw.headCount.show}, tracked ${sw.shape.heads.size} (cap ${Shape.MaxHeads}); exact fan-out ${DomainFacts.fanOut(d, xw).show}")
    // a Range on the exact tier stays exact where the summary can only bracket
    val first = d.range(xw, 0, 1)
    assertEquals(d.enumerate(first), Some(Vector(sv(p("h0", "t")))))
    assertEquals(d.size(first), Ivl(1, 1))
    // and the per-prefix fibres puzzle15 needs: one tile per cell in the exact tier, whatever the depth
    val cells = (0 until 16).map(i => s"c$i")
    val board = SpaceValue(cells.zipWithIndex.map((c, i) => PathValue(List(c, s"tile$i"))).toSet)
    val xboard = d.alpha(board)
    for c <- cells do assertEquals(DomainFacts.fibre(d, xboard, List(c)), Ivl(1, 1), s"cell $c holds one tile")
    val product = cells.map(c => d.unwrap(xboard, List(c))).reduce(d.comp)
    assertEquals(d.size(product), Ivl(1, 1), "the 16-fold composition of one-tile fibres is one path, exactly")
    assert(d.certificate.exact)
    println(s"DOMAIN: 16 one-tile fibres compose to size ${d.size(product).show} exactly (no Shape.top)")
  }

  // ---- 3. the summarized tier contains every counted outcome ------------------------------------------------

  test("summarized results contain all counted outcomes: sampled inputs in γ(input), outputs in γ(output)") {
    val d = new Domain
    val s0 = SpaceMention("s0"); val s1 = SpaceMention("s1")
    // an input DECLARED by a summary: at most 3 paths of length 1 or 2 over {a,b}
    val declared = SpatialType(Shape.top, SpaceType.bounded(Lower.LenBounds(1, 2), 3))
    val ia = d.inputSummary(s0, declared); val ib = d.inputSummary(s1, declared)
    val ops: Vector[(String, (Abs, Abs) => Abs, (Space, Space) => Space)] = Vector(
      ("union", d.unionA, Space.Union.apply), ("inter", d.interA, Space.Intersection.apply),
      ("sub", d.subA, Space.Subtraction.apply), ("restrict", d.restrictA, Space.Restriction.apply),
      ("comp", d.compA, Space.Composition.apply))
    val samples = universe.filter(v => SpatialType.accepts(declared, v))
    assert(samples.length > 10)
    var checked = 0
    for (name, op, term) <- ops do
      val out = op(ia, ib)
      for a <- samples; b <- samples.take(8) do
        val truth = eval(term(Space.Mention(s0), Space.Mention(s1)))(using PathContextMap(Map.empty), SpaceContextMap(Map(s0 -> a, s1 -> b)), PartialFunction.empty)
        assert(d.member(out, truth), s"$name: ${truth.pretty} ∉ γ(${out.show}) for inputs ${a.pretty}, ${b.pretty}")
        checked += 1
    // mixed: an exact operand against a summarized one
    val xa = d.literal(sv(p("a"), p("b", "a")))
    for (name, op, term) <- ops do
      val out = op(xa, ib)
      for b <- samples do
        val truth = eval(term(Space.Mention(s0), Space.Mention(s1)))(using PathContextMap(Map.empty), SpaceContextMap(Map(s0 -> sv(p("a"), p("b", "a")), s1 -> b)), PartialFunction.empty)
        assert(d.member(out, truth), s"$name (exact × summary): ${truth.pretty} ∉ γ(${out.show})")
        checked += 1
    println(s"DOMAIN: $checked summarized outcomes contained")
  }

  // ---- 4. invariance under prior analyses -----------------------------------------------------------------------

  test("results are INVARIANT under prior analyses in the same JVM") {
    def run(): (Abs, DomainCert, String) =
      val d = new Domain(DomainBudget(alternatives = 4))
      val s0 = SpaceMention("s0")
      var acc = d.input(s0, sv(p("a", "x"), p("b")))
      for i <- 0 until 9 do acc = d.joinA(acc, d.literal(sv(p(s"k$i"), p("b"))))
      val r = d.unionA(d.compA(acc, d.literal(sv(p("z")))), d.tailsUnionA(acc))
      (r, d.certificate, r.show)
    val first = run()
    // churn: many unrelated analyses and arenas in between
    for i <- 0 until 20 do
      val d = new Domain
      var x: XNode = d.alpha(randValue())
      for _ <- 0 until 30 do x = d.union(x, d.alpha(randValue()))
      SpatialTyping.infer(Space.Union(Space.Literal(randValue()), Space.Literal(randValue())))
    val second = run()
    assertEquals(second._1.node.key, first._1.node.key, "the abstract value changed with process history")
    assertEquals(second._1.alias, first._1.alias)
    assertEquals(second._2, first._2, "the certificate changed with process history")
    assertEquals(second._3, first._3)
    println(s"DOMAIN: invariant — ${first._2.widenings.length} widening(s), value ${first._3.take(80)}")
  }

  // ---- 5. every precision loss is in the certificate --------------------------------------------------------------

  test("every loss of precision is a NAMED widening in the certificate, with before/after facts") {
    val d = new Domain(DomainBudget(alternatives = 3))
    val s0 = SpaceMention("s0")
    val x = d.input(s0, sv(p("a"), p("b", "c")))
    // three exact alternatives fit; the fourth crosses the budget
    var acc = x
    for i <- 0 until 2 do acc = d.joinA(acc, d.literal(sv(p(s"q$i"))))
    assert(d.certificate.exact, "three alternatives fit the budget of 3")
    acc = d.joinA(acc, d.literal(sv(p("q9"), p("q8", "r"))))
    val cert = d.certificate
    assertEquals(cert.widenings.length, 1)
    val w = cert.widenings.head
    assertEquals(w.reason, "alternatives-budget")
    assert(w.afterSize.lo <= w.beforeSize.lo && w.afterSize.hi >= w.beforeSize.hi, "a widening may not tighten a must fact")
    assert(w.before.nonEmpty && w.after.nonEmpty)
    // the after value is summarized and still contains every alternative
    for v <- Vector(sv(p("a"), p("b", "c")), sv(p("q0")), sv(p("q1")), sv(p("q9"), p("q8", "r"))) do
      assert(d.member(acc, v), s"widened value lost ${v.pretty}")
    // an operation past the budget names the operation
    val d2 = new Domain(DomainBudget(alternatives = 2))
    val c1 = d2.join(d2.alpha(sv(p("a"))), d2.alpha(sv(p("b"))))
    val c2 = d2.join(d2.alpha(sv(p("c"))), d2.alpha(sv(p("d"))))
    d2.union(c1, c2)
    assert(d2.certificate.widenings.exists(_.reason == "alternatives-budget(union)"), d2.certificate.show)
    // the iteration widening is named too
    val d3 = new Domain(DomainBudget(alternatives = 1))
    val w3 = d3.widen(d3.alpha(sv(p("a"))), d3.alpha(sv(p("a"), p("a", "b"))))
    assert(d3.certificate.widenings.exists(_.reason == "iteration-widening"), d3.certificate.show)
    assert(d3.member(w3, sv(p("a"), p("a", "b"))) && d3.member(w3, sv(p("a"))))
    println(s"DOMAIN: ${cert.show}\nDOMAIN: ${d2.certificate.widenings.head.show}\nDOMAIN: ${d3.certificate.widenings.head.show}")
  }

  // ---- 6. the alias channel and the n-ary facts ----------------------------------------------------------------------

  test("aliasing, proven reuse and distinct live operands") {
    val d = new Domain
    val s0 = SpaceMention("s0"); val s1 = SpaceMention("s1")
    val a = d.input(s0, sv(p("a", "x"), p("b")))
    val a2 = d.input(s0, sv(p("a", "x"), p("b")))
    val b = d.input(s1, sv(p("c")))
    assert(DomainFacts.mustAlias(a, a2) && DomainFacts.mayAlias(a, a2))
    assert(!DomainFacts.mayAlias(a, b), "two inputs are different objects")
    // x ∪ x IS x; x ∪ (subset of x) IS x by the identity case; x ∪ y is fresh
    val u1 = d.unionA(a, a2)
    assertEquals(u1.alias, Alias.Is(s0)); assert(u1.node eq a.node)
    val sub = d.literal(sv(p("b")))
    val u2 = d.unionA(a, sub)
    assertEquals(u2.alias, Alias.Is(s0), "the executors return the left operand by pointer when the right is absorbed")
    assertEquals(DomainFacts.provenReuse(u2, Vector(a, sub)), Some(0))
    val u3 = d.unionA(a, b)
    assertEquals(u3.alias, Alias.Fresh)
    assertEquals(DomainFacts.provenReuse(u3, Vector(a, b)), None)
    // n-ary: the same object three times is ONE live operand; three different objects are three
    assertEquals(DomainFacts.distinctLive(d, Vector(a, a2, a)), Ivl(1, 1))
    assertEquals(DomainFacts.distinctLive(d, Vector(a, b, d.literal(sv(p("z"))))), Ivl(3, 3))
    // an operand that may be empty counts in `may` but not in `must`
    val maybe = d.inputSummary(SpaceMention("m"), SpatialType(Shape.top, SpaceType.bounded(Lower.LenBounds(1, 1), 2)))
    assertEquals(DomainFacts.distinctLive(d, Vector(a, maybe)), Ivl(1, 2))
    println("DOMAIN: alias channel — must/may aliasing, proven reuse, distinct live operands as specified")
  }

  test("the provenance DAG: every node knows its cause, and shared subtries are one node") {
    val d = new Domain
    val s0 = SpaceMention("s0")
    val a = d.input(s0, sv(p("a", "x"), p("b", "x")))
    val t = a.node.asInstanceOf[XTrie]
    assert(t.children("a") eq t.children("b"), "two equal tails are one hash-consed node")
    assertEquals(d.arena.cause(a.node.id), Cause.Input(s0))
    val u = d.union(a.node, d.alpha(sv(p("c"))))
    d.arena.cause(u.id) match
      case Cause.Op("union", ops) => assertEquals(ops, Vector(a.node.id, d.alpha(sv(p("c"))).id))
      case other => fail(s"unexpected cause ${other.show}")
    println(s"DOMAIN: arena ${d.arena.size} nodes; cause of the union: ${d.arena.cause(u.id).show}")
  }
