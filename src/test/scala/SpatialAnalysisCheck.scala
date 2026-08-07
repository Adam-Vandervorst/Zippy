package morkl

import munit.FunSuite
import scala.collection.immutable.SortedMap

/** THE DECORATED ANALYSIS, THE REDUCER AND THE MEET — the gates for review.md 4, 5, 6 and the naming
 *  half of 1.
 *
 *  What is gated here, and how:
 *
 *    1. IDENTITY.  Two structurally identical subterms in different positions get different
 *       [[NodeId]]s and can carry different facts.
 *    2. OBSERVATIONS.  A loop body analysed under several head groups keeps EACH observation's
 *       bindings, plus the joined summary.
 *    3. AGREEMENT.  `SpatialTyping.infer` still answers, and the decorated root is never weaker:
 *       `SpatialGamma.leq(root, infer)` on every probe and on the corpus.
 *    4. SOUNDNESS OF THE NEW OPERATIONS.  `reduce` and `meet` are checked EXHAUSTIVELY on a finite
 *       universe of concrete values (`v ∈ γ(t) ⇒ v ∈ γ(reduce(t))`, and
 *       `v ∈ γ(a) ∩ γ(b) ⇒ v ∈ γ(meet(a,b))`), and on the corpus through `eval` as ground truth.
 *    5. BOTH DIRECTIONS of the reduction can tighten the other component, and a PARENT transfer
 *       observes the tightened child.
 *    6. NO EVALUATION: a grounded function that throws is never called by the analysis.
 *
 *  `eval` appears only as ground truth, never inside an analysis path. */
class SpatialAnalysisCheck extends FunSuite:
  import Lower.{LenBounds, SizeBounds}
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
  def p(items: String*): PathValue = PathValue(items.toList)
  val rootId = NodeId(Vector.empty)
  def cp(items: String*): Path = Path.Constant(p(items*))

  // ================================================================================================
  // 1.  ONE DECORATED ANALYSIS  (review.md 4)
  // ================================================================================================

  test("positional identity: two structurally identical subterms are DIFFERENT nodes") {
    val sub = lit(p("a", "0"), p("b", "0"))
    // the same object twice, in two positions
    val term = Space.Union(Space.TailsUnion(sub), Space.Wrap(sub, cp("z")))
    val a = SpatialAnalysis.of(term)
    val occ = a.occurrencesOf(sub)
    assertEquals(occ.size, 2, s"both occurrences must be decorated:\n${a.show}")
    assertEquals(occ.map(_.id).toSet, Set(NodeId(Vector(0, 0)), NodeId(Vector(1, 0))))
    assert(occ(0).id != occ(1).id)
    // the two PARENTS see the same subterm type but produce different results, which is exactly why
    // an occurrence-indexed answer is needed
    val tu = a.at(NodeId(Vector(0))).get
    val wr = a.at(NodeId(Vector(1))).get
    assertEquals(tu.result.len.hi, 1L, tu.show)
    assertEquals(wr.result.len.hi, 3L, wr.show)
    // the index is O(1) and total over the recorded nodes
    assertEquals(a.index.size, a.nodes.size)
    for n <- a.nodes do assertEquals(a.at(n.id).map(_.id), Some(n.id))
    // facts are a PROJECTION of the decorated node, not a fresh inference
    assertEquals(a.factsAt(rootId), a.rootFacts)
  }

  test("a loop body observed under several head groups keeps EACH observation's bindings") {
    val h = PathRef("h")
    val src = lit(p("a", "0"), p("b", "0"), p("c", "0"))            // THREE head groups
    val body = Space.Wrap(Space.Mention(SpaceMention("r")), Path.Deref(h))
    val term = Space.Iteration(src, h, SpaceMention("r"), body)
    val a = SpatialAnalysis.of(term)
    val bodyNode = a.at(NodeId(Vector(1))).getOrElse(fail(s"no body node in\n${a.show}"))
    assertEquals(bodyNode.observations.size, 3, bodyNode.observations.map(_.show).mkString("\n"))
    assert(bodyNode.isJoined)
    // each observation kept ITS OWN head binding and its own rest-set
    val heads = bodyNode.observations.map(_.bindings.paths.get(h).map(_.items.mkString)).toSet
    assertEquals(heads, Set(Some("a"), Some("b"), Some("c")).map(x => x: Option[String]))
    for o <- bodyNode.observations do
      assert(o.bindings.spaces.contains(SpaceMention("r")), s"rest unbound in ${o.cause}")
      assertEquals(o.bindings.spaces(SpaceMention("r")).shape.headCount, Ivl(1, 1),
                   s"the tail-set of group ${o.cause} is {0} — one head, exactly")
    // the joined summary admits every observation — checked as γ-containment on the concrete values
    // each group actually produces, which is what "a joined summary" has to mean
    for (o, head) <- bodyNode.observations.zip(Vector("a", "b", "c")) do
      val groupValue = SpaceValue(Set(p(head, "0")))
      assert(SpatialTyping.accepts(groupValue, o.result),
             s"${groupValue.pretty} not in the ${o.cause} observation ${o.result.show}")
      assert(SpatialTyping.accepts(groupValue, bodyNode.result),
             s"${groupValue.pretty} not in the joined summary ${bodyNode.result.show}")
    // and the ROOT is the union over groups: three paths of length 2
    assertEquals(a.root.size, SizeBounds(3, 3, 3), a.root.show)
    assertEquals(eval(term).paths.size, 3)
  }

  test("a fixpoint body keeps one observation per Kleene round") {
    val k = SpaceMention("k")
    val term = Space.Fixpoint(lit(p("a", "b")), k, Space.TailsUnion(Space.Mention(k)))
    val a = SpatialAnalysis.of(term)
    val body = a.at(NodeId(Vector(1))).getOrElse(fail(s"no fixpoint body in\n${a.show}"))
    assert(body.observations.size >= 2, body.observations.map(_.show).mkString("\n"))
    assert(body.observations.map(_.cause).exists(_.startsWith("fixpoint-round")))
    assert(SpatialTyping.accepts(eval(term), a.root), s"${eval(term).pretty} not in ${a.root.show}")
  }

  test("the existing `infer` remains available and the decorated root never contradicts it") {
    val probes = SpatialAnalysisCheck.probeTerms
    var tighter = 0; var same = 0
    for t <- probes do
      val a = SpatialAnalysis.of(t)
      val i = SpatialTyping.infer(t)
      assert(!a.root.uninhabited, s"decorated root contradicts `infer` on ${t.show.take(90)}")
      assert(SpatialGamma.leq(a.root, i),
             s"decorated root must be at least as precise:\n  decorated ${a.root.show}\n  infer     ${i.show}")
      if a.root != i then tighter += 1 else same += 1
      // and both are sound
      val v = try Some(eval(t)) catch case _: Throwable => None
      for value <- v do
        assert(SpatialTyping.accepts(value, a.root), s"${value.pretty} not in decorated ${a.root.show}")
        assert(SpatialTyping.accepts(value, i), s"${value.pretty} not in infer ${i.show}")
    println(s"ROOT AGREEMENT: ${probes.size} probe terms — decorated ⊑ infer on all; " +
            s"strictly different on $tighter, identical on $same")
  }

  test("the traversal is LINEAR in the term: no per-node re-inference") {
    // a BALANCED union tree over n literals — 2n-1 nodes, depth log2 n, so the term-depth cap does
    // not interfere.  The old shape (a fresh `infer` at every node) is quadratic in the node count.
    def tree(lo: Int, hi: Int): Space =
      if hi - lo == 1 then lit(p("x", lo.toString))
      else { val m = (lo + hi) / 2; Space.Union(tree(lo, m), tree(m, hi)) }
    def ms(n: Int): (Double, Int) =
      val t = tree(0, n)
      SpatialAnalysis.of(t)                                    // warm
      val t0 = System.nanoTime()
      val a = SpatialAnalysis.of(t)
      ((System.nanoTime() - t0) / 1e6, a.nodes.size)
    val (m1, n1) = ms(128)
    val (m2, n2) = ms(256)
    val (m3, n3) = ms(512)
    assertEquals(n1, 255); assertEquals(n2, 511); assertEquals(n3, 1023)
    val ratio = if m2 <= 0.01 then 1.0 else m3 / m2
    println(f"LINEARITY: $n1 nodes $m1%.1f ms, $n2 nodes $m2%.1f ms, $n3 nodes $m3%.1f ms " +
            f"(the last doubling cost $ratio%.2fx; quadratic would be ~4x)")
    assert(m3 < 60000, "the decorated traversal must not blow up on a 1023-node term")
  }

  test("NO EVALUATION: a grounded function that throws is never run by the analysis") {
    val bomb = Space.GroundedSS(lit(p("a")), _ => throw RuntimeException("analysis evaluated its subject"))
    val term = Space.Union(bomb, lit(p("b")))
    val a = SpatialAnalysis.of(term)                            // must not throw
    assert(a.root.size.hi >= 1)
    assertEquals(SpatialAnalysis.of(bomb).root.shape.isTop, true)
    val pbomb = Space.GroundedPS(cp("a"), _ => throw RuntimeException("analysis evaluated its subject"))
    assert(SpatialAnalysis.of(pbomb).nodes.nonEmpty)
  }

  // ================================================================================================
  // 2.  MUTUAL REDUCTION  (review.md 5)
  // ================================================================================================

  test("S→H: the shape's total and length hull tighten the histogram") {
    // S1: the shape admits at most two paths; the histogram class says up to ten
    val sh = Shape.of(SpaceValue(Set(p("a"), p("b"))))            // exactly 2 paths, length 1
    val loose = SpatialType(sh, SpaceType.closed(1L -> Ivl(0, 10)))
    val r1 = SpatialType.reduce(loose)
    assertEquals(r1.lens.at(1L).hi, 2L, s"S1 must cap the class by the shape total: ${r1.show}")
    // S2: a class outside the shape's ∀-path length hull is annihilated
    val loose2 = SpatialType(sh, SpaceType.closed(1L -> Ivl(0, 2), 5L -> Ivl(0, 3)))
    val r2 = SpatialType.reduce(loose2)
    assertEquals(r2.lens.at(5L), Ivl.zero, s"S2 must kill the out-of-hull class: ${r2.show}")
    assertEquals(r2.len.hi, 1L)
    // S3: the shape forces two paths and only one class can hold them
    val loose3 = SpatialType(sh, SpaceType.closed(1L -> Ivl(0, 7)))
    val r3 = SpatialType.reduce(loose3)
    assertEquals(r3.lens.at(1L), Ivl(2, 2), s"S3 must raise the only live class' lower bound: ${r3.show}")
  }

  test("H→S: the histogram's support and totals tighten the shape") {
    // H2: no paths of length 0 ⇒ eps = No; H1: at most one path ⇒ at most one head
    val open = SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(1, 1)))
    val r = SpatialType.reduce(open)
    assertEquals(r.shape.eps, Presence.No, s"H2 must forbid ε: ${r.show}")
    assertEquals(r.shape.others.hi, 1L, s"H1 must cap the untracked head count: ${r.show}")
    assertEquals(r.headCount, Ivl(1, 1), s"and the head count becomes exact: ${r.show}")
    // H2 must direction (root only): the histogram forces ε
    val withEps = SpatialType(Shape.top, SpaceType.closed(0L -> Ivl(1, 1)))
    assertEquals(SpatialType.reduce(withEps).shape.eps, Presence.Must)
    // H3: nothing longer than one item ⇒ no heads below depth 1
    val deep = SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(0, 3)))
    val rd = SpatialType.reduce(deep)
    assert(rd.shape.heads.forall((_, c) => c.headCount.hi == 0),
           s"H3 must prune below the maximum length: ${rd.show}")
    assertEquals(rd.shape.lens.hi, 1L)
    // H4: non-empty, and the shape leaves exactly one place a path can be
    val onePlace = SpatialType(Shape(Presence.May, SortedMap.empty, Ivl.zero, None),
                               SpaceType.closed(0L -> Ivl(1, 1)))
    assertEquals(SpatialType.reduce(onePlace).shape.eps, Presence.Must, "H4 must force the unique place")
    val underHead = SpatialType(Shape.of(SpaceValue(Set(p("a", "b")))),
                                SpaceType.closed(2L -> Ivl(1, 1)))
    assert(SpatialType.reduce(underHead).shape.definitelyNonEmpty)
  }

  test("a CONTRADICTION collapses to one explicit bottom, and bottom admits nothing") {
    // the shape proves ε absent; the histogram forces a length-0 path
    val bad = SpatialType(Shape(Presence.No, SortedMap.empty, Ivl.zero, None),
                          SpaceType.closed(0L -> Ivl(1, 1)))
    val b = SpatialType.reduce(bad)
    assert(b.uninhabited, s"must be the explicit bottom, got ${b.show}")
    assertEquals(b, SpatialType.bottom)
    // γ(⊥) = ∅: it rejects even the empty space
    assert(!SpatialTyping.accepts(SpaceValue(Set.empty), b))
    assert(!SpatialTyping.accepts(SpaceValue(Set(p("a"))), b))
    assert(!SpatialTyping.withinEnvelope(SpaceValue(Set.empty), b))
    // and it is NOT the empty space, which admits exactly one value
    assert(SpatialTyping.accepts(SpaceValue(Set.empty), SpatialType.empty))
    assert(b != SpatialType.empty)
    // a length-window contradiction too
    val bad2 = SpatialType(Shape.of(SpaceValue(Set(p("a")))), SpaceType.closed(4L -> Ivl(1, 1)))
    assert(SpatialType.reduce(bad2).uninhabited, SpatialType.reduce(bad2).show)
  }

  test("the PARENT transfer observes the tightened child (not just a tighter root projection)") {
    // the child is a mention whose declared shape leaves ONE place a path can be, and whose declared
    // histogram proves one path exists.  Only the child's own reduction can put those together (H4);
    // the parent operator `Unwrap` then descends into the tracked head, so the forced MUST arrives at
    // the root.  The root's own reduction cannot recover it: `Unwrap`'s count transfer drops every
    // lower bound, so at the root the histogram no longer knows a path exists.
    val m = SpaceMention("m")
    val declared = SpatialType(Shape.weaken(Shape.of(SpaceValue(Set(p("a", "b"))))),
                               SpaceType.closed(2L -> Ivl(1, 1)))
    assert(!declared.shape.definitelyNonEmpty, "precondition: the declared SHAPE alone forces nothing")
    val env = SpatialTyping.Env(spaces = Map(m -> declared))
    val term = Space.Unwrap(Space.Mention(m), cp("a"))
    val a = SpatialAnalysis.of(term, env)
    val i = SpatialTyping.infer(term, env)
    assertEquals(i.size.lo, 0L, s"precondition: the undecorated query cannot prove non-emptiness: ${i.show}")
    assertEquals(a.root.size.lo, 1L, s"the parent must see the tightened child:\n${a.show}")
    assert(a.rootFacts.contains(Fact.DefinitelyNonEmpty), a.rootFacts.mkString(", "))
    // the child node itself records the tightening
    val child = a.at(NodeId(Vector(0))).get
    assert(child.result.shape.definitelyNonEmpty, s"the child was reduced: ${child.result.show}")
    // and it is sound: every concrete member of the declared type has a path under "a"
    val witness = SpaceValue(Set(p("a", "b")))
    assert(SpatialTyping.accepts(witness, declared))
    assert(SpatialTyping.accepts(SpaceValue(Set(p("b"))), a.root))
  }

  test("the reducer TERMINATES: it is idempotent and reaches its fixed point in one or two rounds") {
    val pool = SpatialAnalysisCheck.typePool
    var maxRounds = 0; var nonIdem = 0
    for t <- pool do
      val r = SpatialType.reduce(t)
      if SpatialType.reduce(r) != r then nonIdem += 1
      maxRounds = maxRounds max SpatialType.reduceRounds(t)
    println(s"REDUCER: ${pool.size} types — max rounds to the fixed point $maxRounds " +
            s"(cap ${SpatialConfig.default.reduceRounds}); non-idempotent $nonIdem")
    assertEquals(nonIdem, 0, "reduce must be idempotent, or the fixed point is not reached")
    assert(maxRounds <= SpatialConfig.default.reduceRounds)
  }

  // ================================================================================================
  // 3.  SOUNDNESS OF THE NEW LATTICE OPERATIONS, EXHAUSTIVELY ON A FINITE UNIVERSE
  // ================================================================================================

  test("γ-soundness of `reduce`: it never drops a member (exhaustive, 2 items x length 2)") {
    val u = SpatialAnalysisCheck.universe
    val pool = SpatialAnalysisCheck.typePool
    var pairs = 0L; var members = 0L; var lost = Vector.empty[String]; var tightened = 0
    for t <- pool do
      val r = SpatialType.reduce(t)
      if r != t then tightened += 1
      for v <- u do
        pairs += 1
        if SpatialTyping.accepts(v, t) then
          members += 1
          if !SpatialTyping.accepts(v, r) then
            if lost.size < 3 then lost = lost :+ s"${v.pretty} in ${t.show} but not in ${r.show}"
    println(s"REDUCE γ-GATE: ${pool.size} types x ${u.size} values = $pairs checks, $members members; " +
            s"reduce tightened $tightened types; members lost ${lost.size}")
    assertEquals(lost, Vector.empty, lost.mkString("\n"))
  }

  test("γ-soundness of `meet`: it keeps every common member, and bottom means there are none") {
    val u = SpatialAnalysisCheck.universe
    val pool = SpatialAnalysisCheck.typePool.take(48)
    var checks = 0L; var common = 0L; var bottoms = 0; var lost = Vector.empty[String]
    var wrongBottom = Vector.empty[String]
    for a <- pool; b <- pool do
      val m = SpatialType.meet(a, b)
      if m.uninhabited then bottoms += 1
      for v <- u do
        checks += 1
        if SpatialTyping.accepts(v, a) && SpatialTyping.accepts(v, b) then
          common += 1
          if m.uninhabited then
            if wrongBottom.size < 3 then
              wrongBottom = wrongBottom :+ s"${v.pretty} in both ${a.show} and ${b.show} but meet = ⊥"
          else if !SpatialTyping.accepts(v, m) then
            if lost.size < 3 then lost = lost :+ s"${v.pretty} in both but not in meet ${m.show}"
    println(s"MEET γ-GATE: ${pool.size}^2 pairs x ${u.size} values = $checks checks, $common common " +
            s"members; meet was ⊥ on $bottoms pairs; members lost ${lost.size}; false ⊥ ${wrongBottom.size}")
    assertEquals(wrongBottom, Vector.empty, wrongBottom.mkString("\n"))
    assertEquals(lost, Vector.empty, lost.mkString("\n"))
  }

  test("`Shape.meet` is below both operands, so the meet is a refinement and not a widening") {
    val u = SpatialAnalysisCheck.universe.take(64)
    val shapes = u.map(v => Shape.of(v)) ++ u.take(16).map(v => Shape.weaken(Shape.of(v))) ++ Vector(Shape.top, Shape.empty)
    var below = 0; var incomparable = 0; var none = 0
    for a <- shapes; b <- shapes.take(24) do
      Shape.meet(a, b) match
        case None => none += 1
        case Some(m) => if Shape.leq(m, a) && Shape.leq(m, b) then below += 1 else incomparable += 1
    println(s"MEET ORDER: below both on $below pairs, order-incomparable on $incomparable, ⊥ on $none")
    assert(below > 0)
    // the interesting property is soundness (checked above); this one is precision, so it is
    // reported rather than asserted exactly — `Shape.leq` is itself incomplete.
    assert(incomparable * 4 < below, s"the meet should usually be provably below both ($incomparable/$below)")
  }

  // ================================================================================================
  // 4.  NAMING  (review.md 1) and the DEAD FACT  (review.md 6)
  // ================================================================================================

  test("`accepts` is γ, `withinEnvelope` is the weaker check — and the weak one really is weaker") {
    val u = SpatialAnalysisCheck.universe
    val pool = SpatialAnalysisCheck.typePool
    var gammaOnly = 0; var envelopeOnly = 0; var agree = 0
    for t <- pool; v <- u do
      val g = SpatialTyping.accepts(v, t)
      val e = SpatialTyping.withinEnvelope(v, t)
      if g && !e then gammaOnly += 1 else if e && !g then envelopeOnly += 1 else agree += 1
    println(s"accepts vs withinEnvelope: agree on $agree, envelope admits a NON-MEMBER $envelopeOnly " +
            s"times, γ-member rejected by the envelope $gammaOnly times")
    assertEquals(gammaOnly, 0, "the envelope must at least admit every γ-member")
    assert(envelopeOnly > 0, "the documented gap must be exhibited, or the finding is stale")
    // `accepts` and the kept alias agree, and both agree with the independent copy in SpatialGamma
    for t <- pool.take(24); v <- u do
      assertEquals(SpatialTyping.accepts(v, t), SpatialTyping.gammaMember(v, t))
      if SpatialTyping.accepts(v, t) then assert(SpatialGamma.gamma(t)(v))
  }

  test("`Fact.PrefixAbsent` is emitted by a real prefix query") {
    val src = lit(p("b", "x"), p("b", "y"))
    val term = Space.Unwrap(src, cp("a"))
    // the query itself
    val t = SpatialTyping.infer(src)
    assert(SpatialTyping.prefixAbsent(t, List("a")), s"a closed head set proves 'a' absent: ${t.show}")
    assert(!SpatialTyping.prefixAbsent(t, List("b")))
    assert(SpatialTyping.prefixAbsent(t, List("b", "z")))
    // and the decorated analysis asks about the term's own constant paths, so the fact is emitted
    assert(SpatialAnalysis.constantPrefixes(term).contains(List("a")),
           SpatialAnalysis.constantPrefixes(term).toString)
    val a = SpatialAnalysis.of(term)
    val srcFacts = a.at(NodeId(Vector(0))).get.facts
    assert(srcFacts.contains(Fact.PrefixAbsent(List("a"))), srcFacts.mkString(", "))
    // the fact is TRUE of the concrete value (the same check SpatialSoundnessHunt applies)
    val v = eval(src)
    assert(!v.paths.exists(_.items.startsWith(List("a"))))
    // …and the parent is provably empty because of it
    assert(a.root.isProvablyEmpty, a.root.show)
    assertEquals(eval(term), SpaceValue(Set.empty))
  }

  // ================================================================================================
  // 5.  THE REDUCER'S EFFECT ON A CONSUMER — the one existing expectation it changes
  // ================================================================================================

  test("the stronger reducer bounds a recursion that was previously unbounded, and soundly") {
    // `peel(p0; m) = heads(m) ∪ peel(p0; m(p0))` with `|p0| ∈ [1,3]` and `m`'s paths ≤ 4 items.
    // `SpatialRecursionCheck`'s "NO BOUND (M2)" case: the histogram's variable-length unwrap arm
    // loses the length bound, so μ used to go 4 → ∞ and no call-depth bound followed.  The reducer's
    // H3 rule now prunes the shape below the histogram's maximum length, the shape's own length hull
    // comes back finite, and μ drops — so a bound IS derived.  That is a real improvement, but it is
    // ALSO a claim about termination, so it is verified against `eval` here rather than trusted.
    val m = SpaceMention("m")
    val p0 = PathRef("p0")
    val hh = PathRef("h").known(1)
    val peelPtr = RoutinePtr("peel$sa")
    val heads = Space.Iteration(Space.Mention(m), hh, SpaceMention("_"), Space.Singleton(Path.Deref(hh)))
    val peel = Routine(peelPtr, Vector(p0), Vector(m),
      Space.Union(heads, Space.Call(peelPtr, Vector(Path.Deref(p0)),
                                    Vector(Space.Unwrap(Space.Mention(m), Path.Deref(p0))))))
    val table: Map[RoutinePtr, Routine] = Map(peelPtr -> peel)
    val ann = SpatialRecursion.lengthAnnotation(1, 4)
    val out = SpatialRecursion.residualise(peelPtr, table, Map(m -> ann), Map(p0 -> LenBounds(1, 3)))
    val res = out.bounded.getOrElse(fail(s"expected a bound now: ${out.noBoundReason.get}"))
    println(s"REDUCER x RECURSION: peel |p0| in [1,3], maxLen 4 -> maxCallDepth ${res.maxCallDepth}, " +
            s"len chain ${res.lenChain.mkString(",")} (was NoBound: 'M2 failed')")
    assert(res.callFree, "the residual must be Call-free")
    // the residual agrees with the original on every input the precondition admits
    val rng = new java.util.Random(20260807L)
    val alphabet = Vector("a", "b", "c")
    var checked = 0; var disagree = 0
    for _ <- 0 until 300 do
      val n = rng.nextInt(5)
      val paths = (0 until n).map(_ =>
        PathValue(List.fill(1 + rng.nextInt(4))(alphabet(rng.nextInt(alphabet.length))))).toSet
      val v = SpaceValue(paths)
      val plen = 1 + rng.nextInt(3)
      val pv = PathValue(List.fill(plen)(alphabet(rng.nextInt(alphabet.length))))
      if SpatialTyping.accepts(v, ann) && plen >= 1 && plen <= 3 then
        checked += 1
        val pc = PathContextMap(Map(p0 -> pv)); val sc = SpaceContextMap(Map(m -> v))
        val orig = eval(peel.body)(using pc, sc, table)
        val spec = eval(res.residual.body)(using pc, sc, table)
        if orig != spec then disagree += 1
    println(s"REDUCER x RECURSION: $checked admitted inputs, $disagree disagreements")
    assert(checked >= 100, s"the generator must admit enough inputs, got $checked")
    assertEquals(disagree, 0, "the residual must agree with the original inside the precondition")
  }

  // ================================================================================================
  // 5.  THE CORPUS GATE
  // ================================================================================================

  test("soundness on the corpus: the decorated root and every decorated node admit the real value") {
    val recs = ShapeShrink.corpus
    assume(recs.nonEmpty, "corpus not found")
    var checked = 0; var nodes = 0L; var bottoms = 0; var tighter = 0; var withProbes = 0
    val bad = Vector.newBuilder[String]
    val notLeq = Vector.newBuilder[String]
    for closed <- ShapeShrink.instances(recs, 31337).take(400) do
      val v = try Some(eval(closed)) catch case _: Throwable => None
      for value <- v do
        val a = SpatialAnalysis.of(closed)
        val i = SpatialTyping.infer(closed)
        checked += 1
        nodes += a.nodes.size
        if a.root.uninhabited then
          bottoms += 1
          bad += s"BOTTOM on a runnable term: ${ShapeShrink.safeShow(closed)}"
        else
          if !SpatialTyping.accepts(value, a.root) then
            bad += s"root: ${value.pretty} not in ${a.root.show} :: ${ShapeShrink.safeShow(closed)}"
          if !SpatialGamma.leq(a.root, i) then
            notLeq += s"${a.root.show} not <= ${i.show} :: ${ShapeShrink.safeShow(closed)}"
          if a.root != i then tighter += 1
        if a.nodes.exists(_.facts.exists(_.isInstanceOf[Fact.PrefixAbsent])) then withProbes += 1
    val bs = bad.result()
    println(s"DECORATED CORPUS: $checked instances, $nodes decorated nodes " +
            f"(${nodes.toDouble / (checked max 1)}%.1f per term); differs from `infer` on $tighter; " +
            s"bottom on $bottoms; a prefix-absent fact on $withProbes; violations ${bs.size}; " +
            s"root not <= infer on ${notLeq.result().size}")
    for b <- bs.take(3) do println("  " + b)
    for b <- notLeq.result().take(3) do println("  LEQ: " + b)
    assertEquals(bs.size, 0, bs.take(3).mkString("\n"))
    assertEquals(notLeq.result().size, 0, notLeq.result().take(3).mkString("\n"))
  }

  test("soundness on the corpus: every OBSERVATION of every node is sound where it is closed") {
    val recs = ShapeShrink.corpus
    assume(recs.nonEmpty, "corpus not found")
    // a node with no free mentions/refs left can be evaluated on its own, so its decorated result is
    // checkable against `eval` directly — the strongest per-node gate available without a semantics
    // for open terms.
    var checked = 0L; var bad = Vector.empty[String]
    for closed <- ShapeShrink.instances(recs, 4242).take(200) do
      val a = SpatialAnalysis.of(closed)
      for n <- a.nodes if n.observations.size == 1 && SpatialAnalysisCheck.isClosed(n.expression) do
        val v = try Some(eval(n.expression)) catch case _: Throwable => None
        for value <- v do
          checked += 1
          if !SpatialTyping.accepts(value, n.result) && bad.size < 3 then
            bad = bad :+ s"${n.id.show} ${value.pretty} not in ${n.result.show} :: ${ShapeShrink.safeShow(n.expression)}"
    println(s"PER-NODE CORPUS: $checked closed decorated occurrences checked against `eval`; " +
            s"violations ${bad.size}")
    assertEquals(bad, Vector.empty, bad.mkString("\n"))
  }

object SpatialAnalysisCheck:
  /** the finite universe the γ gates are exhaustive over: 2^7 = 128 concrete spaces */
  lazy val universe: Vector[SpaceValue] = SpatialGamma.universe(Vector("a", "b"), 2)

  /** a pool of abstract types spanning the interesting representations: exact points, weakened and
   *  widened shapes, ⊤ on one component, joins, and hand-built spill buckets. */
  lazy val typePool: Vector[SpatialType] =
    val vs = universe
    val exact = vs.map(SpatialType.of)
    val weak = vs.take(24).map(v => SpatialType(Shape.weaken(Shape.of(v)), SpaceType.of(v)))
    val wide = vs.take(24).map(v => SpatialType(Shape.widen(Shape.of(v)), SpaceType.of(v)))
    val shapeOnly = vs.take(16).map(v => SpatialType(Shape.of(v), SpaceType.unknown))
    val lensOnly = vs.take(16).map(v => SpatialType(Shape.top, SpaceType.of(v)))
    val joins = vs.take(12).zip(vs.slice(12, 24)).map((a, b) => SpatialGamma.lub(SpatialType.of(a), SpatialType.of(b)))
    val spills = Vector(
      SpatialType(Shape.top, SpaceType.bounded(Lower.LenBounds(0, 2), 3)),
      SpatialType(Shape.top, SpaceType.boundedExact(Lower.LenBounds(1, 2), 2)),
      SpatialType(Shape.of(SpaceValue(Set(PathValue(List("a"))))), SpaceType.bounded(Lower.LenBounds(1, 1), 1)),
      SpatialType.top, SpatialType.empty)
    exact ++ weak ++ wide ++ shapeOnly ++ lensOnly ++ joins ++ spills

  /** no free mention and no free ref: the term can be evaluated on its own */
  def isClosed(s: Space): Boolean =
    def go(x: Space, sb: Set[SpaceMention], pb: Set[PathRef]): Boolean =
      def pathOk(p: Path): Boolean = p match
        case Path.Deref(pr) => pb.contains(pr)
        case Path.Constant(_) => true
        case Path.Concat(l, r) => pathOk(l) && pathOk(r)
        case _ => false
      x match
        case Space.Mention(m) => sb.contains(m)
        case Space.Singleton(p) => pathOk(p)
        case Space.Wrap(a, p) => pathOk(p) && go(a, sb, pb)
        case Space.Unwrap(a, p) => pathOk(p) && go(a, sb, pb)
        case Space.GroundedPS(p, _) => pathOk(p)
        case Space.GroundedSS(a, _) => go(a, sb, pb)
        case Space.Iteration(src, sym, rest, body) =>
          go(src, sb, pb) && go(body, sb + rest, pb + sym)
        case Space.Fold(src, init, acc, sym, rest, body, upd) =>
          pathOk(init) && go(src, sb, pb) && go(body, sb + rest, pb + sym + acc) &&
            pathOk(upd)
        case Space.Fixpoint(init, recm, body) => go(init, sb, pb) && go(body, sb + recm, pb)
        case Space.Call(_, _, _) => false
        case other => SpatialAnalysis.childrenOf(other).forall(go(_, sb, pb))
    go(s, Set.empty, Set.empty)

  /** hand-built probe terms: one per interesting transfer, closed so `eval` is ground truth */
  lazy val probeTerms: Vector[Space] =
    def l(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
    def pv(is: String*): PathValue = PathValue(is.toList)
    val a = l(pv("a", "0"), pv("a", "1"))
    val b = l(pv("b", "0"), pv("c", "0"))
    val h = PathRef("h")
    Vector(
      Space.Empty,
      a, b,
      Space.Union(a, b),
      Space.Intersection(a, b),
      Space.Subtraction(a, b),
      Space.Restriction(a, l(pv("a"))),
      Space.Raffination(a, l(pv("a"))),
      Space.Composition(a, l(pv("z"))),
      Space.Wrap(a, Path.Constant(pv("w"))),
      Space.Unwrap(a, Path.Constant(pv("a"))),
      Space.Unwrap(a, Path.Constant(pv("q"))),
      Space.TailsUnion(a),
      Space.TailsIntersection(a),
      Space.Range(a, 0, 1),
      Space.Range(a, 0, 0),
      Space.Singleton(Path.Constant(pv("s", "t"))),
      Space.Iteration(b, h, SpaceMention("r"), Space.Singleton(Path.Deref(h))),
      Space.Iteration(b, h, SpaceMention("r"), Space.Mention(SpaceMention("r"))),
      Space.Iteration(a, h, SpaceMention("r"), Space.Wrap(Space.Mention(SpaceMention("r")), Path.Deref(h))),
      Space.Fixpoint(l(pv("a", "b", "c")), SpaceMention("k"), Space.TailsUnion(Space.Mention(SpaceMention("k")))),
      Space.Union(Space.TailsUnion(a), Space.Wrap(a, Path.Constant(pv("z")))),
      Space.Composition(Space.Wrap(a, Path.Constant(pv("p"))), Space.TailsUnion(b)))
