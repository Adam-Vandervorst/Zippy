package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==================================================================================================
 *  THE LAW CHANNEL'S OWN GATES.
 *
 *  `SpatialAcceptance` 6a–6d show four laws tightening real Zippy routines.  This suite gates the
 *  CHANNEL itself, on the four properties the review asks for and on the ones that make it safe to
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
 *  8  the ORDER of the laws does not change the answer          (on a BASELINE-SENSITIVE law set)
 *  9  meeting a TRUE law never loses soundness                  (differential against `eval`)
 *  10 the library laws' PREMISES are checked, not assumed       (each declines where it must)
 *  12 an UNDISCHARGED law licenses NOTHING                      (the review the reviewer's own attack)
 *  }}}
 *
 *  ==8 AND 12 ARE THE TWO the review ADDED, AND BOTH USED TO BE VACUOUS==
 *  Gate 8 previously permuted laws whose `bound` ignores `site.inferred`, so every permutation met the
 *  same bounds and the gate could not fail however the engine folded them.  It now permutes a law set in
 *  which one law's bound is ENABLED by another's — the shape `SpatialLaws.finiteSolutionCount` has — which
 *  is the case a left fold gets wrong.  Gate 12 runs the exact attack the review describes: an
 *  always-applicable ASSUMED law claiming a live `Mention` is empty, through `optimizeGuarded` and through
 *  `SpatialCheck`, with `eval` as ground truth on the residual.
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

  /** A BASELINE-SENSITIVE LAW — the shape that makes order independence a real property and not a
   *  remark about commutativity.  Its `bound` READS `site.inferred` and declines unless the ∀-path length
   *  is PINNED, exactly as `SpatialLaws.finiteSolutionCount` does ("with no pinned length there is no
   *  class to put the count in").  Under a left fold over the law vector, whether it contributes depends
   *  on whether a length-pinning law happens to precede it. */
  def whenPinned(name: String, cap: Long, e: LawEvidence = ev): SpatialBoundLaw =
    SpatialBoundLaw(name, _ => true,
      site =>
        val ln = site.inferred.len
        if ln.isEmpty || ln.lo != ln.hi then None
        else Some(SpatialType(Shape.top, SpaceType.closed(ln.lo -> Ivl(0, cap)))),
      e)
  /** …and the law that PINS the length, i.e. the one that ENABLES the above */
  def pinLen(name: String, l: Long): SpatialBoundLaw =
    always(name, SpatialType(Shape.top, SpaceType.bounded(LenBounds(l, l), Ivl.INF)))

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
      // …and the most adversarial bound of all, on UNDISCHARGED evidence: the production policy must
      // refuse it outright, so it can neither widen nor narrow
      always("assumed-empty", SpatialType.empty, LawEvidence.Assumed("an axiom nobody discharged")),
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
    for o <- Vector(LawOutcome.Tightened, LawOutcome.Unchanged, LawOutcome.Contradicted,
                    LawOutcome.Refused) do
      assert(outcomes(o) > 0, s"the adversarial pool never produced $o — gate 2 would be vacuous")
    assert(strictlyTighter > 0, "the adversarial pool must actually tighten something")
    // the ASSUMED law never moved anything, at any occurrence of any term
    val refusals = pool.map((n, t) =>
      SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(laws.last)))
    for (a, (n, t)) <- refusals.zip(pool) do
      assertEquals(a.root, SpatialAnalysis.of(t, env, SpatialConfig.default).root,
                   s"$n: an UNDISCHARGED law moved the answer")
      assert(a.lawApplications.forall(_.outcome == LawOutcome.Refused), s"$n: ${a.lawApplications}")
      assert(a.assumedLaws.isEmpty, s"$n: ${a.assumedLaws}")
    println(s"[2] the ASSUMED ∅ bound was REFUSED at all ${refusals.map(_.lawApplications.size).sum} " +
            s"applicable occurrences of ${pool.size} terms and moved no root")
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
    val bareRoot = SpatialAnalysis.of(t, env2, SpatialConfig.default).root
    for (law, tag, discharged) <- Vector((proved, "SMT-proved", true), (assumed, "ASSUMED", false),
                                         (checked, "executable-checked", true)) do
      val a = SpatialAnalysis.of(t, env2, SpatialConfig.default.withLaws(law))
      val root = a.lawsAt(NodeId(Vector.empty))
      assertEquals(root.size, 1, s"${law.name}: exactly one record at the root")
      assertEquals(root.head.law, law.name)
      assertEquals(root.head.evidence.tag, tag)
      assertEquals(root.head.evidence.discharged, discharged)
      assertEquals(root.head.at, NodeId(Vector.empty))
      // ---- THE EVIDENCE POLICY, ENFORCED ---------------------------------------------
      // The three fixtures contribute the SAME bound and differ only in their justification, so this is
      // the policy and nothing else: the discharged two tighten, the ASSUMED one is REFUSED and the
      // answer stays the transfers'.
      if discharged then
        assertEquals(root.head.outcome, LawOutcome.Tightened,
                     s"${law.name}: a DISCHARGED bound must license the narrowing")
        assert(root.head.before != root.head.after, root.head.show)
        assert(a.root != bareRoot, s"${law.name}: the fixture must really move the root")
        assert(a.notes.exists(n => n.contains(s"law ${law.name} tightened") &&
                                   n.contains(law.evidence.tag)),
               s"${law.name}: the analysis must report the law and its evidence: ${a.notes}")
      else
        assertEquals(root.head.outcome, LawOutcome.Refused,
                     s"${law.name}: an UNDISCHARGED bound must be refused, not met")
        assertEquals(root.head.before, root.head.after,
                     s"${law.name}: a refused bound moved the recorded type")
        assertEquals(a.root, bareRoot, s"${law.name}: a refused bound moved the ROOT")
        // …and the report says what a discharged proof obligation would have bought, so the cost of the
        // missing proof is visible rather than silent
        assert(root.head.why.contains("REFUSED") && root.head.why.contains("would have given"),
               s"${law.name}: ${root.head.why}")
      // nothing rests on an undischarged axiom, under any of the three
      assertEquals(a.assumedLaws, Vector.empty,
                   s"${law.name}: no answer may rest on an undischarged axiom under the production policy")
      assert(!a.notes.exists(_.contains("rests on ASSUMED law")), a.notes.mkString("; "))
      println(s"    [5] ${root.head.show.take(140)}")
    // an UNCHANGED assumed law is NOT reported as assumed: nothing rests on it
    val weak = always("assumed-weak", SpatialType.top, LawEvidence.Assumed("nothing"))
    val aw = SpatialAnalysis.of(t, env2, SpatialConfig.default.withLaws(weak))
    assert(aw.assumedLaws.isEmpty, "an assumed law that changed nothing is not being rested on")
    println("[5] the SAME bound on three justifications: the two DISCHARGED ones tighten, the ASSUMED " +
            "one is REFUSED — `assumedLaws` is empty by construction under the production policy")

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
  test("8. the ORDER of the laws does not change the answer — on a BASELINE-SENSITIVE law set") {
    // ---- (a) THE FIXTURE IS NON-VACUOUS: one law is ENABLED by another --------------------------
    // `cnt` reads `site.inferred` and declines unless the ∀-path length is pinned; `pin` pins it.  Under
    // a left fold, `[pin, cnt]` produces a count bound and `[cnt, pin]` does not — which is precisely why
    // "meet is commutative" was never the order-independence argument.
    val M3 = SpaceMention("m3")
    val env3 = SpatialTyping.Env(spaces =
      Map(M3 -> SpatialType(Shape.top, SpaceType.bounded(LenBounds(1, 2), 4))))
    val t3 = Space.Mention(M3)
    val pin = pinLen("pin-len-2", 2L)
    val cnt = whenPinned("at-most-1-when-pinned", 1L)
    val bare3 = SpatialAnalysis.of(t3, env3, SpatialConfig.default)
    val alone = SpatialAnalysis.of(t3, env3, SpatialConfig.default.withLaws(cnt))
    assertEquals(alone.lawsAt(NodeId(Vector.empty)).map(_.outcome), Vector(LawOutcome.NoBound),
                 s"the fixture is vacuous unless `cnt` DECLINES on the transfers' own answer: " +
                   s"${alone.lawsAt(NodeId(Vector.empty)).map(_.show)}")
    assertEquals(alone.root, bare3.root, "…and therefore changes nothing on its own")
    val ab = SpatialAnalysis.of(t3, env3, SpatialConfig.default.withLaws(pin, cnt))
    val ba = SpatialAnalysis.of(t3, env3, SpatialConfig.default.withLaws(cnt, pin))
    val abRoot = ab.lawsAt(NodeId(Vector.empty))
    assert(abRoot.exists(a => a.law == cnt.name && a.outcome == LawOutcome.Tightened),
           s"the SATURATION must let the enabled law fire in a later round: ${abRoot.map(_.show)}")
    assertEquals(ab.root, ba.root,
                 s"permuting the law set changed the ANSWER: ${ab.root.show} vs ${ba.root.show}")
    assertEquals(ab.lawsAt(NodeId(Vector.empty)).toSet, ba.lawsAt(NodeId(Vector.empty)).toSet,
                 "…and it must not change the audit trail either")
    assert(ab.root.size.hi <= 1L, s"the enabled bound must really bite: ${ab.root.show}")
    println(s"[8a] `${cnt.name}` alone: NoBound.  With `${pin.name}`, in BOTH orders: " +
            s"${ab.root.size.hi} path(s) max, identical records — the saturation reaches the same " +
            "fixpoint from either permutation")

    // ---- (b) EVERY permutation of a three-law set, one of them baseline-sensitive, over the pool ----
    val a1 = always("len-2-at-most-4", SpatialType(Shape.top, SpaceType.closed(2L -> Ivl(0, 4))))
    val a2 = always("at-least-1", SpatialType(Shape.top, SpaceType.bounded(LenBounds(1, 3), 9)))
    val a3 = whenPinned("at-most-3-when-pinned", 3L)
    val rng = new java.util.Random(4242L)
    val values = randomValues(rng, 512)
    var pairs = 0
    var equal = 0
    var recordsEqual = 0
    val perms = Vector(a1, a2, a3).permutations.toVector
    assertEquals(perms.size, 6)
    for (name, t) <- pool; perm <- perms do
      val ref = SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(a1, a2, a3))
      val alt = SpatialAnalysis.of(t, env, SpatialConfig.default.withLaws(perm*))
      // the γ-level claim…
      for v <- values do
        assertEquals(SpatialTyping.accepts(v, alt.root), SpatialTyping.accepts(v, ref.root),
                     s"$name: reordering the laws changed γ on ${v.pretty}")
      // …and the REPRESENTATION, which is what a consumer downstream actually compares
      assertEquals(alt.root, ref.root, s"$name: reordering the laws changed the representation")
      pairs += 1
      if alt.root == ref.root then equal += 1
      if alt.lawApplications.toSet == ref.lawApplications.toSet then recordsEqual += 1
    println(s"[8b] $pairs orderings (all 6 permutations x ${pool.size} terms) x ${values.size} values: " +
            s"γ identical throughout; the REPRESENTATION identical on $equal of $pairs; the AUDIT TRAIL " +
            s"identical on $recordsEqual of $pairs")
    assertEquals(equal, pairs, "the saturation must be a function of the law SET")
    assertEquals(recordsEqual, pairs, "…and so must its audit trail")
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
    // WHICH per-node rewrite the law licenses moved when the relational frontier became a rewrite
    // consumer: the law pins a value, and the frontier then decides the enclosing ring node outright
    // (`Union = L`) instead of the folder replacing the pinned operand by a `Literal`.  Either is the
    // law being consumed at a node; what must not happen is neither.
    assert(gLaw.applied.exists {
             case _: Rewrite.ConstantFold | _: Rewrite.FrontierIdentity | _: Rewrite.EliminateEmpty => true
             case _ => false },
           s"the law must license a per-node rewrite: ${gLaw.applied.map(_.show)}")
    assert(SpatialPipeline.nodeCount(gLaw.residual.body) < SpatialPipeline.nodeCount(gBare.residual.body),
           s"${SpatialPipeline.nodeCount(gBare.residual.body)} -> ${SpatialPipeline.nodeCount(gLaw.residual.body)}")
    // (4) the residual's COST, on all four backends
    for b <- Backend.values.toVector do
      val cBare = CostSem.analyze(gBare.residual.body, ann.costInputs, b, ann.routines)
      val cLaw = CostSem.analyze(gLaw.residual.body, ann.costInputs, b, ann.routines)
      assert(cLaw.work.hi <= cBare.work.hi,
             s"${b.slug}: the law's residual must not cost more: ${cLaw.work.show} vs ${cBare.work.show}")
    // and the residual is CORRECT for every input the annotation admits
    val rng = new java.util.Random(11L)
    var conforming = 0
    for _ <- 0 until 200 do
      val v = SpaceValue((0 until rng.nextInt(2)).map(_ => pv(Vector("q", "z")(rng.nextInt(2)))).toSet)
      if SpatialTyping.accepts(v, ann.spaces(M)) then
        val ctx = SpaceContextMap(Map(M -> v))
        // THE LAW IS A PREMISE, AND `always` PUTS IT AT EVERY NODE — including the bare `Mention(M)`.
        // So the premise is "`M` denotes {q}" (whence the union does too), not merely "the union
        // denotes {q}": an input with `M = ∅` satisfies the ROOT reading and violates the one the law
        // actually makes at the leaf.  The residual is licensed by the law as stated, so the
        // differential must feed only inputs under which the law is true WHERE IT APPLIES.  (This
        // matters now that the consumer moved: the old residual `Literal({q})` happened to agree with
        // `eval` on `M = ∅` as well, which made the weaker filter look sufficient.)
        val truth = eval(body)(using sc = ctx)
        if v == spv(pv("q")) then
          assertEquals(truth, spv(pv("q")), "the premise really does hold on this input")
          assertEquals(eval(gLaw.residual.body)(using sc = ctx), truth,
                       s"the law-licensed residual disagrees on ${v.pretty}")
          conforming += 1
    assert(conforming > 0, "the differential must actually run")
    println(s"[11] one law: facts gained ${gained.mkString(",")}; candidate GraphConstantFold; residual " +
            s"${SpatialPipeline.nodeCount(gBare.residual.body)} -> ${SpatialPipeline.nodeCount(gLaw.residual.body)} " +
            s"nodes; cost non-increasing on 4 backends; $conforming differential inputs agree with `eval`")
  }

  // ================================================================================================
  // 12.  AN UNDISCHARGED LAW LICENSES NOTHING          (the review the reviewer's own attack)
  // ================================================================================================
  test("12. an ASSUMED law claiming a live Mention is empty licenses NO rewrite and NO certificate") {
    // THE ATTACK, verbatim from the review: an always-applicable ASSUMED law claims a live `Mention`
    // denotes ∅.  Before, the meet accepted it ("a law cannot widen"), `optimizeGuarded` erased the term,
    // and `SpatialCheck` certified the residual without naming the law.  Every step of that chain is
    // gated below, and `eval` is the ground truth on the residual.
    val m = SpaceMention("m")
    val body: Space = Space.Mention(m)
    val lie = SpatialBoundLaw("lie", _ => true, _ => Some(SpatialType.empty),
                              LawEvidence.Assumed("unchecked"))
    val base = SpatialAnnotations(spaces = Map(m -> SpatialType.top))
    val r = Routine(RoutinePtr("r"), Vector.empty, Vector(m), body)

    // (1) THE ANSWER DOES NOT MOVE, and the refusal is on the record with what it cost
    val bare = SpatialPipeline.analyzeRoutine(r, base)
    val a = SpatialPipeline.analyzeRoutine(r, base.withLaws(lie))
    assertEquals(a.result, bare.result, "an UNDISCHARGED bound moved the answer")
    assert(!a.result.isProvablyEmpty, s"the live mention must not be provably empty: ${a.result.show}")
    val apps = a.decorated.lawApplications.filter(_.law == "lie")
    assert(apps.nonEmpty, "the refusal must be RECORDED, not silently skipped")
    assert(apps.forall(_.outcome == LawOutcome.Refused), apps.map(_.show).mkString("; "))
    assert(apps.forall(_.why.contains("REFUSED")), apps.head.why)
    assert(apps.exists(_.why.contains("would have given")),
           s"the report must say what the missing proof obligation cost: ${apps.map(_.why)}")
    assertEquals(a.decorated.assumedLaws, Vector.empty)

    // (2) THE OPTIMIZER DOES NOT ERASE THE TERM — with `eval` as ground truth on real inputs
    val g = SpatialPipeline.optimizeGuarded(r, a)
    var agreed = 0
    for items <- Vector(List("a"), List("b", "c"), List()) do
      val input = SpaceValue(Set(PathValue(items)))
      val ctx = SpaceContextMap(Map(m -> input))
      val truth = eval(body)(using sc = ctx)
      assertEquals(eval(g.residual.body)(using sc = ctx), truth,
                   s"the residual erased a live mention on ${input.pretty}: ${g.residual.body}")
      assert(truth == input)
      agreed += 1
    assert(!g.applied.exists(_.isInstanceOf[Rewrite.ConstantFold]),
           s"an undischarged law must license no fold: ${g.applied.map(_.show)}")

    // (3) THE CHECKER DOES NOT CERTIFY ∅
    val sig = SpatialSignature(Map.empty, Map(m -> SpatialType.top), SpatialType.empty)
    val rep = SpatialCheck.report(r, sig, cfg = SpatialConfig.default.withLaws(lie))
    assert(!rep.check.isProved, s"the checker certified a signature the law lied about: ${rep.check.show}")
    // …and the refusal reaches the USER, not only the internal record: a law that silently did nothing
    // is indistinguishable from a law that was never consulted
    assert(rep.diagnosis.notes.exists(n => n.contains("was REFUSED") && n.contains("lie")),
           s"the report must name the refused law:\n${rep.diagnosis.notes.mkString("\n")}")

    // (4) THE REFUSAL IS LOAD-BEARING: under `TrustAll` the very same bound IS met (so (1)-(3) are not
    //     passing because the law is inert), and even then a certificate REFUSES to name it and the
    //     verdict is downgraded rather than annotated.
    val site = LawSite(NodeId(Vector.empty), body, base.env(), SpatialType.top)
    val (refused, refusedApps) = SpatialLaws.refine(Vector(lie), site)
    assertEquals(refused, SpatialType.top, "the production policy refuses the bound")
    assertEquals(refusedApps.map(_.outcome), Vector(LawOutcome.Refused))
    val (trusted, trustedApps) = SpatialLaws.refine(Vector(lie), site, LawEvidencePolicy.TrustAll)
    assert(trusted.isProvablyEmpty, s"TrustAll must actually meet the bound: ${trusted.show}")
    assertEquals(trustedApps.map(_.outcome), Vector(LawOutcome.Tightened))
    assert(trustedApps.head.assumed, "…and the tightening is marked as resting on an axiom")
    intercept[IllegalArgumentException](
      CheckCertificate(order = "anything", inferred = SpatialType.empty, declared = SpatialType.empty,
                       channels = Vector.empty, assumptions = Vector.empty, facts = Vector.empty,
                       corroboration = None, laws = trustedApps, exhaustion = None))
    val (v, d) = SpatialCheck.types(SpatialType.empty, SpatialType.empty, laws = trustedApps)
    assert(v.isUnknown, s"a verdict resting on an undischarged axiom must not be Proved: ${v.show}")
    assert(d.notes.exists(_.contains("REFUSED")), d.notes.mkString("; "))
    // …and the same law with its obligation DISCHARGED does license the narrowing, so the policy is
    // about the EVIDENCE and not about the law
    val honest = lie.copy(evidence = LawEvidence.ExecutableChecked("all inputs, exhaustively"))
    val (met, metApps) = SpatialLaws.refine(Vector(honest), site)
    assert(met.isProvablyEmpty && metApps.map(_.outcome) == Vector(LawOutcome.Tightened))
    println(s"[12] the the review attack: bound REFUSED at ${apps.size} occurrence(s); residual agrees " +
            s"with `eval` on $agreed inputs; no ConstantFold; checker ${rep.check.show.linesIterator.next()
              .take(40)}; TrustAll DOES meet it (so the refusal is load-bearing) and the certificate " +
            "still refuses")
  }
end SpatialLawsCheck
