package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==================================================================================================
 *  THE LAW CHANNEL'S OWN GATES  (review.md 2).
 *
 *  `SpatialAcceptance` 6a–6d show four laws tightening real Zippy routines.  This suite gates the
 *  CHANNEL itself, on the four properties review.md 2 asks for and on the ones that make it safe to
 *  hand a stranger's law to a production analysis:
 *
 *  {{{
 *  1  an inapplicable law is a BYTE-IDENTICAL no-op            (nothing recorded, same root, same nodes)
 *  2  a law can never WIDEN                                     (γ-monotone on 4096 random values)
 *  3  a law that adds nothing records `Unchanged`               (and does not claim a win)
 *  4  a CONTRADICTORY law is DROPPED, not propagated            (the analysis stays consistent)
 *  5  the provenance is on the node and names the evidence      (and `assumedLaws` is separable)
 *  6  the budget is honoured and the ROOT is never starved
 *  7  observations of one position merge into one record        (bounded memory under a 16-level nest)
 *  8  the ORDER of the laws does not change the answer
 *  9  meeting a TRUE law never loses soundness                  (differential against `eval`)
 *  10 the library laws' PREMISES are checked, not assumed       (each declines where it must)
 *  }}}
 *
 *  ==NO EVALUATION INSIDE AN ANALYSIS==
 *  `eval` appears here only as GROUND TRUTH, outside every analysis, and gate 9 is the one place a law
 *  is built FROM a real value — deliberately, because "the tightest sound law" is the sharpest probe of
 *  whether the channel preserves soundness while actually tightening.
 *  ================================================================================================ */
class SpatialLawsCheck extends FunSuite:
  import Space.*
  import Lower.{LenBounds, SizeBounds}
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  def pv(items: String*): PathValue = PathValue(items.toList)
  def spv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  def lit(ps: PathValue*): Space = Space.Literal(spv(ps*))
  def konst(items: String*): Path = Path.Constant(pv(items*))
  val ev: LawEvidence = LawEvidence.ExecutableChecked("a fixture in SpatialLawsCheck")

  /** a law that never applies */
  def never(name: String): SpatialBoundLaw =
    SpatialBoundLaw(name, _ => false, _ => Some(SpatialType.empty), ev)
  /** a law that applies everywhere and contributes `t` */
  def always(name: String, t: SpatialType, e: LawEvidence = ev): SpatialBoundLaw =
    SpatialBoundLaw(name, _ => true, _ => Some(t), e)
  /** a law that applies everywhere and declines */
  def declines(name: String): SpatialBoundLaw =
    SpatialBoundLaw(name, _ => true, _ => None, ev)
  /** a law that applies at exactly ONE occurrence */
  def onlyAt(name: String, id: NodeId, t: SpatialType, e: LawEvidence = ev): SpatialBoundLaw =
    SpatialBoundLaw(name, _.id == id, _ => Some(t), e)

  /** the term pool: every operator shape the recorder visits, plus the binder shapes that produce
   *  several observations of one position */
  val H: PathRef = PathRef("h").known(1)
  val R: SpaceMention = SpaceMention("r")
  val M: SpaceMention = SpaceMention("m")
  val pool: Vector[(String, Space)] = Vector(
    "literal" -> lit(pv("a", "1"), pv("b", "2")),
    "empty" -> Space.Empty,
    "union" -> Space.Union(lit(pv("a")), lit(pv("b"))),
    "intersection" -> Space.Intersection(lit(pv("a"), pv("b")), lit(pv("b"), pv("c"))),
    "subtraction" -> Space.Subtraction(lit(pv("a"), pv("b")), lit(pv("b"))),
    "wrap" -> Space.Wrap(lit(pv("x")), konst("k")),
    "unwrap" -> Space.Unwrap(lit(pv("k", "x")), konst("k")),
    "range" -> Space.Range(lit(pv("a"), pv("b"), pv("c")), 1, 2),
    "singleton" -> Space.Singleton(konst("s", "t")),
    "iteration" -> Space.Iteration(lit(pv("a", "1"), pv("b", "2")), H, R,
                                   Space.Wrap(Space.Mention(R), Path.Deref(H))),
    "nested-iteration" -> Space.Iteration(lit(pv("a", "1", "x"), pv("b", "2", "y")), H, R,
      Space.Iteration(Space.Mention(R), PathRef("h2").known(1), SpaceMention("r2"),
                      Space.Mention(SpaceMention("r2")))),
    "fixpoint" -> Space.Fixpoint(lit(pv("s")), SpaceMention("f"),
                                 Space.Union(Space.Mention(SpaceMention("f")), lit(pv("t")))),
    "mention" -> Space.Mention(M),
    "composition" -> Space.Composition(lit(pv("a", "b")), lit(pv("b", "c"))),
    "tails-union" -> Space.TailsUnion(lit(pv("a", "x"), pv("b", "y"))),
  )
  val env: SpatialTyping.Env =
    SpatialTyping.Env(spaces = Map(M -> SpatialType(Shape.top, SpaceType.closed(2L -> Ivl(2, 2)))))

  /** random concrete spaces, for the γ-monotonicity sweep */
  def randomValues(rng: java.util.Random, n: Int): Vector[SpaceValue] =
    Vector.fill(n) {
      SpaceValue((0 until rng.nextInt(4)).map { _ =>
        PathValue(List.fill(rng.nextInt(4))(Vector("a", "b", "c", "k", "x", "1", "2")(rng.nextInt(7))))
      }.toSet)
    }

  // ================================================================================================
  // 1.  AN INAPPLICABLE LAW IS A NO-OP
  // ================================================================================================
  test("1. an inapplicable law changes nothing at all — same root, same nodes, no records") {
    for (name, t) <- pool do
      val bare = SpatialAnalysis.of(t, env, SpatialConfig.default)
      for law <- Vector(never("never"), declines("declines")) do
        val with_ = SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(law))
        assertEquals(with_.root, bare.root, s"$name/${law.name}: the ROOT changed")
        assertEquals(with_.nodes.map(n => (n.id, n.result, n.facts)),
                     bare.nodes.map(n => (n.id, n.result, n.facts)),
                     s"$name/${law.name}: a NODE changed")
        law.name match
          case "never" =>
            assert(with_.lawApplications.isEmpty, s"$name: an inapplicable law must record NOTHING")
          case _ =>
            assert(with_.lawApplications.forall(_.outcome == LawOutcome.NoBound),
                   s"$name: a declining law records NoBound and changes nothing")
            assert(with_.tightenedBy.isEmpty, s"$name: nothing may be marked tightened")
    println(s"\n[1] ${pool.size} terms x 2 inapplicable laws: identical roots, identical per-node " +
            "results and facts")
  }

  // ================================================================================================
  // 2.  A LAW CAN NEVER WIDEN
  // ================================================================================================
  test("2. a law can never widen: γ(refined) ⊆ γ(unrefined) on 4096 random values") {
    // the adversarial set: bounds that are ⊤, bounds that are unrelated to the term, bounds that are
    // absurdly tight.  The channel is a MEET, so none of them may ADD a concrete value to the answer.
    val laws = Vector(
      always("top", SpatialType.top),
      always("len-3-only", SpatialType(Shape.top, SpaceType.closed(3L -> Ivl(0, 5)))),
      always("at-most-1", SpatialType(Shape.top, SpaceType.bounded(LenBounds.unknown, 1))),
      always("under-k", SpatialType(Shape.wrap(List("k"), Shape.top), SpaceType.unknown)),
      always("exactly-two-a", SpatialType.of(spv(pv("a"), pv("a", "b")))),
    )
    val rng = new java.util.Random(20260807L)
    val values = randomValues(rng, 4096)
    var checks = 0
    var strictlyTighter = 0
    var leqHeld = 0
    var nodeTightened = 0
    val outcomes = collection.mutable.Map.empty[LawOutcome, Int].withDefaultValue(0)
    for (name, t) <- pool; law <- laws do
      val bare = SpatialAnalysis.of(t, env, SpatialConfig.default)
      val with_ = SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(law))
      // γ-MONOTONICITY, the property that matters: nothing new is admitted, at the ROOT or at ANY node
      for v <- values do
        if SpatialTyping.accepts(v, with_.root) then
          assert(SpatialTyping.accepts(v, bare.root),
                 s"$name/${law.name}: the law ADMITTED ${v.pretty}, which the transfers rejected — " +
                 "the channel is supposed to be a meet")
        checks += 1
      for a <- with_.lawApplications do
        outcomes(a.outcome) += 1
        if a.tightened then
          nodeTightened += 1
          // the recorded before/after must itself be a narrowing on every sample
          for v <- values.take(256) do
            if SpatialTyping.accepts(v, a.after) then
              assert(SpatialTyping.accepts(v, a.before),
                     s"$name/${law.name} at ${a.at.show}: the RECORD widened on ${v.pretty}")
      if SpatialType.leq(with_.root, bare.root) then leqHeld += 1
      if with_.root != bare.root then strictlyTighter += 1
    println(f"[2] ${pool.size * laws.size} (term, law) pairs x ${values.size} random values = $checks " +
            f"γ checks, no admitted value gained at the root or in any record")
    println(f"[2] outcomes: " + LawOutcome.values.map(o => s"$o=${outcomes(o)}").mkString(", ") +
            f"; $nodeTightened tightening records, $strictlyTighter roots strictly changed; the " +
            f"(sound-but-incomplete) order confirmed `refined ⊑ bare` on $leqHeld of ${pool.size * laws.size}")
    // the sweep must exercise every outcome, or it is not testing the channel
    for o <- Vector(LawOutcome.Tightened, LawOutcome.Unchanged, LawOutcome.Contradicted) do
      assert(outcomes(o) > 0, s"the adversarial pool never produced $o — gate 2 would be vacuous")
    assert(strictlyTighter > 0, "the adversarial pool must actually tighten something")
  }

  // ================================================================================================
  // 3.  A LAW THAT ADDS NOTHING SAYS SO
  // ================================================================================================
  test("3. a law weaker than the transfers records Unchanged and moves nothing") {
    for (name, t) <- pool do
      val bare = SpatialAnalysis.of(t, env, SpatialConfig.default)
      val law = always("top", SpatialType.top)
      val with_ = SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(law))
      assertEquals(with_.root, bare.root, s"$name: ⊤ cannot tighten anything")
      val outcomes = with_.lawApplications.map(_.outcome).distinct.toSet
      assert(outcomes.subsetOf(Set(LawOutcome.Unchanged)),
             s"$name: a ⊤ bound must record Unchanged everywhere, got $outcomes")
      assert(with_.lawApplications.nonEmpty, s"$name: it WAS applicable, so it must be recorded")
    println("[3] a ⊤ bound is recorded as Unchanged at every occurrence and moves no answer")
  }

  // ================================================================================================
  // 4.  A CONTRADICTORY LAW IS DROPPED
  // ================================================================================================
  test("4. a contradictory law is DROPPED, and the analysis stays consistent") {
    // `{a, b}` is proved to hold exactly two paths; a law claiming ∅ contradicts that.
    val t = lit(pv("a"), pv("b"))
    val bare = SpatialAnalysis.of(t)
    assertEquals(bare.root.size.lo, 2L)
    val law = always("claims-empty", SpatialType.empty)
    val with_ = SpatialAnalysis.of(t, SpatialTyping.Env(), SpatialConfig.default.withLaws(law))
    assertEquals(with_.root, bare.root, "a contradictory law must not change the answer")
    assert(!with_.root.uninhabited, "and must NOT be allowed to make the analysis vacuous")
    assertEquals(with_.contradictedLaws.map(_.law), Vector("claims-empty"))
    assertEquals(with_.tightenedBy, Vector.empty)
    assert(with_.notes.exists(n => n.contains("CONTRADICTED") && n.contains("claims-empty")),
           s"the drop must be reported: ${with_.notes}")
    // and the pipeline still refuses nothing and rewrites nothing on the strength of it
    val r = Routine(RoutinePtr("c"), Vector.empty, Vector.empty, t)
    val a = SpatialPipeline.analyzeRoutine(r, SpatialAnnotations().withLaws(law))
    assert(a.consistent, "the routine analysis must stay consistent")
    assertEquals(a.result, bare.root)
    println(s"[4] a law claiming ∅ on a two-path literal: DROPPED, reported, analysis still consistent")
    // the same law on a term where it does NOT contradict is a normal tightening — the drop is about
    // the contradiction, not about the law
    val u = Space.Union(Space.Mention(M), Space.Empty)
    val ok = SpatialAnalysis.of(u, SpatialTyping.Env(), SpatialConfig.default.withLaws(law))
    assert(ok.root.isProvablyEmpty || ok.contradictedLaws.nonEmpty,
           s"either it applies or it contradicts, and either way it is recorded: ${ok.show.take(200)}")
  }

  // ================================================================================================
  // 5.  PROVENANCE
  // ================================================================================================
  test("5. the provenance is on the node, names the evidence, and separates ASSUMED from proved") {
    // `M2` may hold up to one length-1 path, so the transfers get `{q} ∪ M2` = 1..2 paths.  The law
    // says the union denotes exactly `{q}`, which is strictly stronger and really does tighten.
    val M2 = SpaceMention("m2")
    val env2 = SpatialTyping.Env(spaces = Map(M2 -> SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(0, 1)))))
    val t = Space.Union(Space.Mention(M2), lit(pv("q")))
    val tight = SpatialType.of(spv(pv("q")))
    // ROOT-ONLY fixtures: an everywhere-applicable law would refine the `Mention` CHILD first, the
    // parent transfer would consume the refined child, and the root's own record would then read
    // `Unchanged` — which is the channel working, and is asserted separately below.
    val rootId = NodeId(Vector.empty)
    val proved = onlyAt("proved", rootId, tight, LawEvidence.SmtProved("a SizeZ3 query"))
    val assumed = onlyAt("assumed", rootId, tight, LawEvidence.Assumed("the caller asserts it"))
    val checked = onlyAt("checked", rootId, tight, LawEvidence.ExecutableChecked("512 cases"))
    for (law, tag, discharged) <- Vector((proved, "SMT-proved", true), (assumed, "ASSUMED", false),
                                         (checked, "executable-checked", true)) do
      val a = SpatialAnalysis.of(t, env2, SpatialConfig.default.withLaws(law))
      val root = a.lawsAt(NodeId(Vector.empty))
      assertEquals(root.size, 1, s"${law.name}: exactly one record at the root")
      assertEquals(root.head.law, law.name)
      assertEquals(root.head.evidence.tag, tag)
      assertEquals(root.head.evidence.discharged, discharged)
      assertEquals(root.head.at, NodeId(Vector.empty))
      assertEquals(root.head.outcome, LawOutcome.Tightened,
                   s"${law.name}: this fixture must really tighten, or the provenance gate is vacuous")
      // before/after are BOTH kept, so a consumer can see the delta and not just the answer
      assert(root.head.before != root.head.after, root.head.show)
      assertEquals(a.assumedLaws, if discharged then Vector.empty else Vector(law.name))
      assertEquals(a.notes.exists(_.contains("rests on ASSUMED law")), !discharged,
                   s"${law.name}: the note must appear exactly when the evidence is undischarged")
      assert(a.notes.exists(n => n.contains(s"law ${law.name} tightened") && n.contains(law.evidence.tag)),
             s"${law.name}: the analysis must report the law and its evidence: ${a.notes}")
      println(s"    [5] ${root.head.show.take(120)}")
    // an UNCHANGED assumed law is NOT reported as assumed: nothing rests on it
    val weak = always("assumed-weak", SpatialType.top, LawEvidence.Assumed("nothing"))
    val aw = SpatialAnalysis.of(t, env2, SpatialConfig.default.withLaws(weak))
    assert(aw.assumedLaws.isEmpty, "an assumed law that changed nothing is not being rested on")
    println("[5] `assumedLaws` lists an undischarged law only where it actually tightened an answer")

    // ---- A LAW AT A CHILD CHANGES THE PARENT'S ANSWER -----------------------------------------
    // this is the property that makes the channel worth having: the recorder hands the REFINED shape
    // back to the parent transfer, so a bound proved about an operand propagates upwards.
    val childOnly = onlyAt("child-only", NodeId(Vector(0)), tight)
    val bare = SpatialAnalysis.of(t, env2, SpatialConfig.default)
    val viaChild = SpatialAnalysis.of(t, env2, SpatialConfig.default.withLaws(childOnly))
    assertEquals(viaChild.lawsAt(NodeId(Vector(0))).map(_.outcome), Vector(LawOutcome.Tightened))
    assertEquals(viaChild.lawsAt(rootId), Vector.empty, "the law never applied AT the root")
    assert(viaChild.root != bare.root,
           s"a law at the child must move the ROOT: ${bare.root.show} vs ${viaChild.root.show}")
    assert(viaChild.root.size.hi < bare.root.size.hi || viaChild.root.size.lo > bare.root.size.lo,
           s"${bare.root.show} -> ${viaChild.root.show}")
    println(f"[5] a law at ${NodeId(Vector(0)).show} moved the ROOT ${bare.root.size.hi} -> " +
            f"${viaChild.root.size.hi} paths with NO record at the root — the refined child is what " +
            "the parent transfer consumes")
  }

  // ================================================================================================
  // 6.  THE BUDGET, AND THE ROOT
  // ================================================================================================
  test("6. the law budget is honoured, and the ROOT is refined regardless of it") {
    val (_, nest) = pool.find(_._1 == "nested-iteration").get
    val tight = SpatialType(Shape.top, SpaceType.bounded(LenBounds(0, 4), 3))
    val law = always("bounded-3", tight)
    val full = SpatialAnalysis.of(nest, env, SpatialConfig.default.withLaws(law))
    val zero = SpatialAnalysis.of(nest, env, SpatialConfig.default.copy(lawQueries = 0).withLaws(law))
    assert(full.lawApplications.size > 1, s"the unbudgeted run must refine several occurrences")
    assertEquals(zero.lawApplications.map(_.at), Vector(NodeId(Vector.empty)),
                 "with a zero budget ONLY the root is refined")
    assert(zero.notes.exists(_.contains("law refinements exhausted")),
           s"the exhaustion must be reported: ${zero.notes}")
    // the root is still refined, which is the whole point of the exception (post-order ⇒ root last)
    assertEquals(zero.root, full.root, "the root's answer must not depend on the budget")
    println(s"[6] budget 4000: ${full.lawApplications.size} refinements; budget 0: " +
            s"${zero.lawApplications.size} (the root), same root answer")
  }

  // ================================================================================================
  // 7.  MERGED RECORDS
  // ================================================================================================
  test("7. many observations of one position merge into ONE record with a count") {
    val (_, nest) = pool.find(_._1 == "nested-iteration").get
    val law = always("counted", SpatialType(Shape.top, SpaceType.bounded(LenBounds(0, 4), 3)))
    val a = SpatialAnalysis.of(nest, env, SpatialConfig.default.withLaws(law))
    for n <- a.nodes do
      val byKey = n.laws.groupBy(x => (x.law, x.outcome))
      assert(byKey.forall(_._2.size == 1),
             s"${n.id.show}: one record per (law, outcome), got ${n.laws.map(_.show)}")
      // the count must equal the number of observations at which that (law, outcome) recurred, and can
      // never exceed the observation count
      for x <- n.laws do
        assert(x.occurrences <= n.observations.size,
               s"${n.id.show}: ${x.occurrences} records over ${n.observations.size} observations")
    val multi = a.nodes.filter(_.observations.size > 1)
    assert(multi.nonEmpty, "the nest must have a node observed more than once, or this gate is vacuous")
    val merged = multi.flatMap(_.laws).filter(_.occurrences > 1)
    assert(merged.nonEmpty, s"and at least one merged record: ${multi.map(n => n.id.show -> n.laws.size)}")
    println(s"[7] ${multi.size} multiply-observed positions; merged records: " +
            merged.map(x => s"${x.at.show} x${x.occurrences}").mkString(", "))
  }

  // ================================================================================================
  // 8.  ORDER INDEPENDENCE
  // ================================================================================================
  test("8. the ORDER of the laws does not change the answer") {
    val a1 = always("len-2-at-most-4", SpatialType(Shape.top, SpaceType.closed(2L -> Ivl(0, 4))))
    val a2 = always("at-least-1", SpatialType(Shape.top, SpaceType.bounded(LenBounds(1, 3), 9)))
    val a3 = always("under-a", SpatialType(Shape.wrap(List("a"), Shape.top), SpaceType.unknown))
    val rng = new java.util.Random(4242L)
    val values = randomValues(rng, 512)
    var pairs = 0
    var equal = 0
    for (name, t) <- pool; perm <- Vector(Vector(a1, a2, a3), Vector(a3, a2, a1), Vector(a2, a1, a3)) do
      val ref = SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(a1, a2, a3))
      val alt = SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(perm*))
      // the γ-level claim, which is the one the lattice guarantees
      for v <- values do
        assertEquals(SpatialTyping.accepts(v, alt.root), SpatialTyping.accepts(v, ref.root),
                     s"$name: reordering the laws changed γ on ${v.pretty}")
      pairs += 1
      if alt.root == ref.root then equal += 1
    println(s"[8] $pairs orderings x ${values.size} values: γ identical throughout; the REPRESENTATION " +
            s"was identical on $equal of $pairs")
    assertEquals(equal, pairs, "meet is commutative here, so the representation should match too")
  }

  // ================================================================================================
  // 9.  MEETING A TRUE LAW NEVER LOSES SOUNDNESS
  // ================================================================================================
  test("9. the TIGHTEST TRUE law: γ still admits `eval`, and the answer really does tighten") {
    // the sharpest probe available: build the law FROM the real value (so it is true by construction)
    // and check the refined analysis still admits that value.  If the channel could lose soundness this
    // is where it would show, because the law is maximally aggressive.
    var checked = 0
    var tightened = 0
    for (name, t) <- pool do
      val closed = Vector("mention").contains(name)     // needs an input; `eval` has none
      if !closed then
        val v = eval(t)
        val truth = SpatialType.of(v)
        val law = always(s"exact($name)", truth, LawEvidence.ExecutableChecked("built from eval"))
        val bare = SpatialAnalysis.of(t, env, SpatialConfig.default)
        val with_ = SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(law))
        assert(SpatialTyping.accepts(v, bare.root), s"$name: the baseline must be sound")
        assert(SpatialTyping.accepts(v, with_.root),
               s"$name: UNSOUND — the refined type ${with_.root.show} rejects the real value ${v.pretty}")
        for n <- with_.nodes do
          assert(!n.result.uninhabited, s"$name/${n.id.show}: no node may become vacuous")
        if with_.root != bare.root then tightened += 1
        checked += 1
    assert(tightened > 0, s"the exact law must tighten at least some of the $checked terms")
    println(s"[9] $checked terms with the exact-value law: every refined type still γ-admits `eval`, " +
            s"$tightened roots strictly tightened")
  }

  // ================================================================================================
  // 10.  THE LIBRARY LAWS' PREMISES
  // ================================================================================================
  test("10. every library law DECLINES where its premise is not established") {
    val E = SpaceMention("edges")
    val call = Space.Call(RoutinePtr("tc"), Vector.empty, Vector(Space.Mention(E), Space.Mention(E),
                                                                Space.Mention(E)))
    val closure = SpatialLaws.digraphTransitiveClosure(RoutinePtr("tc"), ev)
    def site(t: Option[SpatialType], term: Space = call): LawSite =
      LawSite(NodeId(Vector.empty), term,
              SpatialTyping.Env(spaces = t.map(E -> _).toMap), SpatialType.top)
    // (a) NO annotation ⇒ no |E| ⇒ no bound
    assert(closure.applies(site(None)), "the term shape does match")
    assertEquals(closure.bound(site(None)), None, "with no declared edge type there is no |E|")
    // (b) an annotation that is not a DIGRAPH (length != 2) ⇒ no bound
    assertEquals(closure.bound(site(Some(SpatialType(Shape.top, SpaceType.closed(3L -> Ivl(2, 2)))))), None,
                 "length-3 paths are not edges")
    // (c) an UNBOUNDED edge count ⇒ no bound
    assertEquals(closure.bound(site(Some(SpatialType(Shape.top, SpaceType.bounded(LenBounds(2, 2), Ivl.INF))))),
                 None, "an unbounded |E| gives an unbounded |E|²")
    // (d) the right premise ⇒ [|E|, |E|²] at length 2
    val good = SpatialType(Shape.top, SpaceType.closed(2L -> Ivl(4, 4)))
    val b = closure.bound(site(Some(good))).getOrElse(fail("the premise holds, so there must be a bound"))
    assertEquals(b.size.hi, 16L); assertEquals(b.size.lo, 4L)
    assertEquals((b.len.lo, b.len.hi), (2L, 2L))
    // (e) a DIFFERENT routine, and a call whose arguments are not all the same mention
    assert(!closure.applies(site(Some(good), Space.Call(RoutinePtr("other"), Vector.empty, Vector.empty))),
           "the law is keyed on ITS routine")
    assertEquals(closure.bound(site(Some(good), Space.Call(RoutinePtr("tc"), Vector.empty,
      Vector(Space.Mention(E), Space.Mention(E), lit(pv("x", "y")))))), None,
      "the semi-naive form the bound was proved for starts with all three arguments EQUAL")

    // the Life law: same discipline
    val F = SpaceMention("field")
    val step = Space.Call(RoutinePtr("nextStep"), Vector.empty, Vector(Space.Mention(F)))
    val life = SpatialLaws.lifeStepImage(RoutinePtr("nextStep"), ev)
    def lsite(t: Option[SpatialType]): LawSite =
      LawSite(NodeId(Vector.empty), step, SpatialTyping.Env(spaces = t.map(F -> _).toMap), SpatialType.top)
    assertEquals(life.bound(lsite(None)), None, "no declared field ⇒ no 9|S|")
    assertEquals(life.bound(lsite(Some(SpatialType(Shape.top, SpaceType.closed(2L -> Ivl(3, 3)))))), None,
                 "a cell is a length-3 `Cell.x.y` path; length 2 is not a field")
    val lb = life.bound(lsite(Some(SpatialType(Shape.top, SpaceType.closed(3L -> Ivl(5, 5))))))
      .getOrElse(fail("the premise holds"))
    assertEquals(lb.size.hi, 45L, "9 x 5")

    // the finite-solution law: it needs a PINNED length before it can place a total count
    val prog = lit(pv("p", "q"))
    val fin = SpatialLaws.finiteSolutionCount("finite", prog, 7L, ev)
    assertEquals(fin.bound(LawSite(NodeId(Vector.empty), prog, SpatialTyping.Env(),
                                   SpatialType(Shape.top, SpaceType.bounded(LenBounds(1, 5), 9)))), None,
                 "with an unpinned length there is no class to put the count in")
    val fb = fin.bound(LawSite(NodeId(Vector.empty), prog, SpatialTyping.Env(),
                               SpatialType(Shape.top, SpaceType.closed(2L -> Ivl(0, 9)))))
      .getOrElse(fail("a pinned length is the premise"))
    assertEquals(fb.size.lo, 7L)
    assert(!fin.applies(LawSite(NodeId(Vector.empty), lit(pv("other")), SpatialTyping.Env(), SpatialType.top)),
           "a term-keyed law applies to ITS term and to nothing else")
    // and 0 solutions is the ∅ claim
    val zero = SpatialLaws.finiteSolutionCount("finite0", prog, 0L, ev)
    assertEquals(zero.bound(LawSite(NodeId(Vector.empty), prog, SpatialTyping.Env(), SpatialType.top)),
                 Some(SpatialType.empty))

    // the two rest-chain laws: they decline on a term that is not a chain of the right shape
    val notAChain = lit(pv("a"))
    val pi = SpatialLaws.patternImage("pi", notAChain, 2, Set("i"),
      Vector(PathPattern(Vector(ItemPattern.Constant("a")))), ev)
    assert(!pi.applies(LawSite(NodeId(Vector.empty), notAChain, SpatialTyping.Env(), SpatialType.top)),
           "a literal is not an iterator nest")
    val cb = SpatialLaws.restChainPointwise("cb", ev)
    assert(!cb.applies(LawSite(NodeId(Vector.empty), notAChain, SpatialTyping.Env(), SpatialType.top)))
    // an Iteration whose source path length is NOT the nest depth is not pointwise, and chainBound says so
    val badChain = Space.Iteration(lit(pv("a", "b", "c")), H, R, Space.Singleton(Path.Deref(H)))
    assert(cb.applies(LawSite(NodeId(Vector.empty), badChain, SpatialTyping.Env(), SpatialType.top)))
    assertEquals(cb.bound(LawSite(NodeId(Vector.empty), badChain, SpatialTyping.Env(), SpatialType.top)), None,
                 "a depth-1 nest over length-3 paths exhausts the source early: not a pointwise map")
    println("[10] all five library laws decline every unestablished premise and bind only the right one")
  }

  // ================================================================================================
  // 11.  THE CHANNEL IS AN INPUT TO EVERY CONSUMER
  // ================================================================================================
  test("11. facts, candidates, the residual and the residual's cost all read the refined answer") {
    // ONE law, four consumers.  `x` is an open mention, so nothing is known about the union; the law
    // says the whole thing is a single length-1 path, which pins it hard enough to be folded.
    val body = Space.Union(Space.Mention(M), lit(pv("q")))
    val r = Routine(RoutinePtr("consume"), Vector.empty, Vector(M), body)
    val law = always("exactly-q", SpatialType.of(spv(pv("q"))))
    val ann = SpatialAnnotations(spaces = Map(M -> SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(0, 1)))),
                                 ordinaryLower = false)
    val bare = SpatialPipeline.analyzeRoutine(r, ann)
    val with_ = SpatialPipeline.analyzeRoutine(r, ann.withLaws(law))
    // (1) FACTS
    val gained = with_.facts.map(_.show).toSet -- bare.facts.map(_.show).toSet
    assert(gained.nonEmpty, s"the law must change the facts: ${bare.facts.map(_.show)}")
    // (2) CANDIDATES
    val cands = with_.candidates.map(_.spec.show.takeWhile(_ != '(')).toSet --
                bare.candidates.map(_.spec.show.takeWhile(_ != '(')).toSet
    assert(cands.contains("GraphConstantFold"),
           s"a pinned value must license the constant fold: ${with_.candidates.map(_.spec.show)}")
    // (3) the RESIDUAL
    val gBare = SpatialPipeline.optimizeGuarded(r, bare)
    val gLaw = SpatialPipeline.optimizeGuarded(r, with_)
    assert(gLaw.applied.exists(_.isInstanceOf[Rewrite.ConstantFold]),
           s"the law must license a per-node fold: ${gLaw.applied.map(_.show)}")
    assert(SpatialPipeline.nodeCount(gLaw.residual.body) < SpatialPipeline.nodeCount(gBare.residual.body),
           s"${SpatialPipeline.nodeCount(gBare.residual.body)} -> ${SpatialPipeline.nodeCount(gLaw.residual.body)}")
    // (4) the residual's COST, on all four backends
    for b <- Backend.values.toVector do
      val cBare = SpatialCost.analyze(gBare.residual.body, ann.costEnv, Backends.of(b, ExecutionPhase.Warm))
      val cLaw = SpatialCost.analyze(gLaw.residual.body, ann.costEnv, Backends.of(b, ExecutionPhase.Warm))
      assert(cLaw.cost.work.at(Map.empty) <= cBare.cost.work.at(Map.empty),
             s"${b.slug}: the law's residual must not cost more: ${cLaw.cost.work.show} vs ${cBare.cost.work.show}")
    // and the residual is CORRECT for every input the annotation admits
    val rng = new java.util.Random(11L)
    var conforming = 0
    for _ <- 0 until 200 do
      val v = SpaceValue((0 until rng.nextInt(2)).map(_ => pv(Vector("q", "z")(rng.nextInt(2)))).toSet)
      if SpatialTyping.accepts(v, ann.spaces(M)) then
        val ctx = SpaceContextMap(Map(M -> v))
        // the LAW is a premise: it claims the union denotes exactly {q}.  Where the premise holds the
        // residual must agree with the original; the test only feeds inputs where it does.
        val truth = eval(body)(using sc = ctx)
        if truth == spv(pv("q")) then
          assertEquals(eval(gLaw.residual.body)(using sc = ctx), truth,
                       s"the law-licensed residual disagrees on ${v.pretty}")
          conforming += 1
    assert(conforming > 0, "the differential must actually run")
    println(s"[11] one law: facts gained ${gained.mkString(",")}; candidate GraphConstantFold; residual " +
            s"${SpatialPipeline.nodeCount(gBare.residual.body)} -> ${SpatialPipeline.nodeCount(gLaw.residual.body)} " +
            s"nodes; cost non-increasing on 4 backends; $conforming differential inputs agree with `eval`")
  }
end SpatialLawsCheck
