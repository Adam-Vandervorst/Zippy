package morkl

import munit.FunSuite
import Lower.LenBounds

/** THE CONSUMER-FACING SPATIAL TYPECHECKER — the acceptance suite for the review.
 *
 *  The review lists five tests and they are the acceptance criteria; each has its own section below,
 *  numbered to match:
 *
 *    1. concrete membership accepts EXACTLY γ, including the tracked lower bound of an ABSENT length
 *       class (the clause the weaker envelope check skips);
 *    2. an inferred output below the declared output returns `Proved`, with a certificate that names
 *       the order it discharged and every assumption it rests on;
 *    3. a finite witness returns `Refuted` — and the witness is re-validated here, so `Refuted` cannot
 *       be produced by a bug in the searcher;
 *    4. a KNOWN `leq` false negative returns `Unknown`, NEVER `Refuted`.  "Known" is not asserted: the
 *       γ-containment the order fails to see is DECIDED exhaustively on a finite universe first;
 *    5. diagnostics identify the failing channel, the assumption relied on, and the source node.
 *
 *  Plus the gates that make those five mean something:
 *
 *    6. the CHANNEL MIRRORS never disagree with the predicates they explain (`accepts`, `leq`), over a
 *       randomized pool — a diagnosis that can drift from its law is worse than none;
 *    7. the REFUTER NEVER FABRICATES: over the same pool, no pair whose γ-containment holds on the
 *       finite universe is ever `Refuted`;
 *    8. NO EVALUATION — a grounded function that throws is never called by any entry point here;
 *    9. a VACUOUS ⊥ is `Unknown`, not `Proved`;
 *   10. ABSTRACT ≠ SEMANTIC: a routine that is `Refuted` abstractly and yet satisfies its signature on
 *       EVERY concrete input, with `eval` as ground truth.  This is the distinction the API's wording
 *       claims, demonstrated rather than asserted.
 *
 *  ==AND THE COMBINED PRODUCT QUERY==
 *  §4 used to end at "the product-interaction class is `Unknown`, and that is honest".  It is now DECIDED:
 *  when the inferred type's shape has CLOSED head sets, `γ(inferred)` is enumerated in full and every
 *  member is tested with the product γ, so a containment visible only to the CONJUNCTION of shape and
 *  histogram is proved rather than shrugged at.  The gates that make that trustworthy:
 *
 *    4b/4c — the pair 4a proves `leq` misses is now `Proved`, with the enumeration in the certificate; and
 *            with `ProductSearch.off` the old honest `Unknown` comes back verbatim;
 *    4f    — SOUNDNESS: on every pair whose enumeration fits inside `U`, the complete enumeration and `U`
 *            agree exactly on `|γ(a)|` and on the containment.  `U` decides, so a completeness bug shows;
 *    4g    — an OPEN head set (⊤, spilled width, capped depth) is DECLINED, and both budgets are honoured.
 *
 *  4d measures the residual incompleteness rate on the diagnostic pool and NAMES the reason for every pair
 *  it still cannot decide, so "sound but incomplete" stays a number.  5d additionally gates that a
 *  certificate names every semantic law it depended on.
 *
 *  `eval` appears in §10 only, as ground truth. Nothing in `src/main/scala/SpatialCheck.scala` calls it. */
class SpatialCheckCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  def lit(ps: PathValue*): Space = Space.Literal(sv(ps*))
  def cp(items: String*): Path = Path.Constant(p(items*))
  val rootId = NodeId(Vector.empty)

  /** the finite universe on which γ-containment is DECIDED (all 2^7 spaces over {a,b} with ≤2 items) */
  lazy val U: Vector[SpaceValue] = SpatialGamma.TestOnly.universe(Vector("a", "b"), 2)

  /** EXACT γ-containment on `U`, decided with the product's own γ — `SpatialTyping.accepts`, the same
   *  predicate the checker uses.  A `false` here is a genuine refutation; a `true` is containment ON
   *  `U`, which is what "known false negative" has to mean to be checkable. */
  def containedOnU(a: SpatialType, b: SpatialType): Boolean =
    U.forall(v => !SpatialTyping.accepts(v, a) || SpatialTyping.accepts(v, b))
  def witnessOnU(a: SpatialType, b: SpatialType): Option[SpaceValue] =
    U.find(v => SpatialTyping.accepts(v, a) && !SpatialTyping.accepts(v, b))

  // ---- a randomized pool of abstract elements spanning every representation ------------------------
  def randValue(rng: java.util.Random): SpaceValue =
    def pick = "" + ('a' + rng.nextInt(3)).toChar
    rng.nextInt(8) match
      case 0 => sv()
      case 1 => sv(p())
      case 2 => sv(p(pick), p())
      case 3 => SpaceValue((0 until (13 + rng.nextInt(4))).map(i => p("h" + i)).toSet)   // > MaxHeads
      case 4 => SpaceValue((0 until (1 + rng.nextInt(3))).map(_ =>
                  PathValue(List.fill(rng.nextInt(7))(pick))).toSet)                     // > MaxDepth
      case _ => SpaceValue((0 until rng.nextInt(5)).map(_ =>
                  PathValue(List.fill(rng.nextInt(3))(pick))).toSet)

  def pool(rng: java.util.Random, n: Int): Vector[SpatialType] =
    val out = Vector.newBuilder[SpatialType]
    out += SpatialType.top; out += SpatialType.empty; out += SpatialType.bottom
    // hand-built spill-carrying types: the representation the order is incomplete on
    out += SpatialType(Shape.top, SpaceType.bounded(LenBounds(1, 2), 2))
    out += SpatialType(Shape.top, SpaceType.boundedExact(LenBounds(1, 2), 1))
    out += SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(1, 2), 2L -> Ivl(0, 1)))
    while out.result().size < n do
      val v = randValue(rng)
      val a = SpatialGamma.alpha(v)
      out += a
      rng.nextInt(5) match
        case 0 => out += SpatialType.widen(a)
        case 1 => out += SpatialGamma.lub(a, SpatialGamma.alpha(randValue(rng)))
        case 2 => out += SpatialType.meet(a, SpatialGamma.lub(a, SpatialGamma.alpha(randValue(rng))))
        case 3 => out += SpatialType.reduce(SpatialType(a.shape, SpaceType.unknown))
        case _ => out += SpatialType.reduce(SpatialType(Shape.weaken(a.shape), a.lens))
    out.result().take(n)

  // ================================================================================================
  // 1.  CONCRETE MEMBERSHIP ACCEPTS EXACTLY γ            (the review required test 1)
  // ================================================================================================

  test("1a. concrete membership is EXACT on point types: accepts(v, α w) ⟺ v == w") {
    // completeness, not just soundness: a sound-but-incomplete membership test would accept values
    // other than `w` here, and the `SpatialCheck.value` API promises it does not.
    var accepted = 0
    for w <- U do
      val t = SpatialGamma.alpha(w)
      for v <- U do
        val got = SpatialCheck.value(v, t).accepted
        assertEquals(got, v == w,
          s"membership is not exact: ${v.pretty} against α(${w.pretty}) = ${t.show} gave $got\n" +
            SpatialCheck.value(v, t).show)
        if got then accepted += 1
    assertEquals(accepted, U.size, "each point type must accept exactly one value")
    println(s"MEMBERSHIP/exact: ${U.size} point types x ${U.size} values = ${U.size * U.size} " +
      s"decisions, accepted exactly $accepted (one per type)")
  }

  test("1b. the TRACKED LOWER BOUND of an ABSENT length class is enforced — the envelope's gap") {
    // `t` demands at least one path of ONE item and at least one of TWO.  `v` has two two-item paths
    // and NO one-item path, so it is outside γ — and the envelope check cannot see it, because it only
    // validates the classes the value actually populates.
    val t = SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(1, 2), 2L -> Ivl(1, 2)))
    val v = sv(p("a", "b"), p("b", "b"))
    assert(!SpatialTyping.accepts(v, t), "γ must reject a value that leaves a lower-bounded class empty")
    assert(SpatialTyping.withinEnvelope(v, t), "precondition: the ENVELOPE check admits this non-member")
    val checked = SpatialCheck.value(v, t)
    assert(!checked.accepted, checked.show)
    val chans = checked match
      case ValueCheck.Rejected(_, _, cs) => cs
      case _ => Vector.empty
    assert(chans.exists(_.channel == ResultChannel.LengthClass(1L)),
           s"the diagnosis must name the length-1 class:\n${checked.show}")
    assert(chans.exists(c => c.channel == ResultChannel.LengthClass(1L) && c.why.contains("NONE")),
           s"…and say the class is EMPTY in the value:\n${checked.show}")
    println(s"MEMBERSHIP/absent-class: ${checked.show}")

    // the same gap, measured: how often does the envelope admit a NON-member over the pool x U?
    val rng = new java.util.Random(90210)
    val ts = pool(rng, 160)
    var pairs = 0; var gap = 0; var agree = 0
    for a <- ts; v2 <- U do
      val g = SpatialTyping.accepts(v2, a)
      val e = SpatialTyping.withinEnvelope(v2, a)
      assert(!g || e, s"γ must imply the envelope: ${v2.pretty} / ${a.show}")
      if g == e then agree += 1 else gap += 1
      pairs += 1
    println(f"MEMBERSHIP/envelope gap: $pairs%d (type, value) pairs; agree $agree%d; the ENVELOPE " +
      f"admits a NON-MEMBER on $gap%d (${100.0 * gap / pairs}%.2f%%) — the reason `accepts` is the " +
      "predicate this checker uses")
  }

  test("1c. accepts is the componentwise γ plus the reduced projections, and never weaker") {
    val rng = new java.util.Random(4242)
    val ts = pool(rng, 200)
    var both = 0; var strongerOnly = 0
    for a <- ts; v <- U do
      val strong = SpatialTyping.accepts(v, a)
      val comp = SpatialGamma.gamma(a)(v)
      // the product's γ additionally checks `size`/`len`, so it can only be STRONGER
      assert(!strong || comp, s"accepts admitted a value the componentwise γ rejects: ${v.pretty} / ${a.show}")
      if strong then both += 1 else if comp then strongerOnly += 1
    println(s"MEMBERSHIP/projections: accepted $both; the reduced projections rejected a further " +
      s"$strongerOnly value(s) the componentwise conjunction admits")
  }

  test("1d. α is extensive and its sets are accepted (the membership side of the Galois pair)") {
    for v <- U do assert(SpatialCheck.value(v, SpatialGamma.alpha(v)).accepted, v.pretty)
    val rng = new java.util.Random(7)
    var sets = 0
    for _ <- 0 until 300 do
      val s = (0 until (1 + rng.nextInt(4))).map(_ => U(rng.nextInt(U.size))).toSet
      val a = SpatialGamma.alphaSet(s)
      for v <- s do
        assert(SpatialCheck.value(v, a).accepted,
               s"member of S not accepted by α S:\n${SpatialCheck.value(v, a).show}")
      sets += 1
    println(s"MEMBERSHIP/galois: all ${U.size} point abstractions accepted, and every member of " +
      s"$sets random sets accepted by its α")
  }

  // ================================================================================================
  // 2.  AN INFERRED OUTPUT BELOW THE DECLARED OUTPUT IS `Proved`   (required test 2)
  // ================================================================================================

  /** a routine whose body is a literal, and a declaration strictly looser than what it produces */
  val provedRoutine: Routine =
    Routine(RoutinePtr("pair"), Vector.empty, Vector(SpaceMention("s")),
            Space.Union(lit(p("a", "0")), lit(p("a", "1"))))

  test("2a. an inferred output strictly below the declared output returns Proved, with a certificate") {
    val declared = SpatialType(Shape.top, SpaceType.closed(2L -> Ivl(0, 4)))
    val sig = SpatialSignature(Map.empty, Map(SpaceMention("s") -> SpatialType.top), declared)
    val rep = SpatialCheck.report(provedRoutine, sig)
    rep.check match
      case SpatialCheck.Proved(inferred, cert) =>
        assert(SpatialType.leq(inferred, declared), "the order really holds")
        assert(!SpatialType.leq(declared, inferred), "and it is STRICT — the inferred type is sharper")
        assert(!inferred.uninhabited, "a Proved must not be the vacuous ⊥ proof")
        assert(cert.order.contains("leq"), cert.order)
        assert(cert.assumptions.contains(SpatialAssumption.TransferSoundness))
        assert(cert.assumptions.exists {
          case SpatialAssumption.InputSpaceAnnotation(m, _) => m == SpaceMention("s")
          case _ => false }, cert.show)
        assert(cert.assumptions.exists { case SpatialAssumption.AnalysisBudgets(_) => true; case _ => false })
        // A `Proved` CARRIES AN INDEPENDENT CHECK — either the COMPLETE product enumeration (when the
        // inferred shape's head sets are closed, which they are here) or the bounded corroboration.  Both
        // exist to catch an unsound order rather than to decide the question; the complete one subsumes
        // the bounded one, so exactly one is run.
        assert(cert.exhaustion.exists(_.decidesContainment) ||
                 cert.corroboration.exists(c => c.witness.isEmpty && c.completeOnUniverse),
               s"a Proved must carry a clean independent check:\n${cert.show}")
        assert(cert.corroboration.forall(_.witness.isEmpty), "no check may find a counterexample")
        assert(cert.exhaustion.forall(_.witness.isEmpty))
        // …and NO semantic law was involved, which the certificate says explicitly rather than by omission
        assertEquals(cert.laws, Vector.empty)
        assertEquals(cert.lawAssumptions, Vector.empty)
        assert(cert.show.contains("laws depended on: NONE"), cert.show)
        assert(cert.facts.contains(Fact.MaximumPathLength(2L)), cert.facts.map(_.show).mkString(","))
        assertEquals(rep.diagnosis.failures, Vector.empty, "a Proved has no failing channel")
        assertEquals(rep.diagnosis.notes.filter(_.contains("ALARM")), Vector.empty)
        println(s"PROVED:\n${cert.show}")
      case other => fail(s"expected Proved, got ${other.show}")
  }

  test("2b. Proved survives every declaration between the inferred type and ⊤") {
    val inferred = SpatialTyping.infer(provedRoutine.body)
    val ladder = Vector(
      "exact"   -> inferred,
      "counts"  -> SpatialType(inferred.shape, SpaceType.closed(2L -> Ivl(1, 3))),
      "shape ⊤" -> SpatialType(Shape.top, SpaceType.closed(2L -> Ivl(0, 9))),
      "⊤"       -> SpatialType.top)
    for (name, declared) <- ladder do
      val sig = SpatialSignature(Map.empty, Map(SpaceMention("s") -> SpatialType.top), declared)
      val got = SpatialCheck.checkRoutine(provedRoutine, sig)
      assert(got.isProved, s"$name should be provable, got ${got.show}")
    println(s"PROVED/ladder: ${ladder.map(_._1).mkString(", ")} — all Proved")
  }

  // ================================================================================================
  // 3.  A FINITE WITNESS RETURNS `Refuted`                        (required test 3)
  // ================================================================================================

  val mS: SpaceMention = SpaceMention("s")
  /** the identity routine: its inferred output IS its declared input */
  val idRoutine: Routine = Routine(RoutinePtr("id"), Vector.empty, Vector(mS), Space.Mention(mS))

  test("3a. a declaration the inferred type genuinely exceeds returns Refuted, with a real witness") {
    // the input may be {a} or {b}; the declaration insists on {a}
    val inT = SpatialGamma.lub(SpatialGamma.alpha(sv(p("a"))), SpatialGamma.alpha(sv(p("b"))))
    val declared = SpatialGamma.alpha(sv(p("a")))
    val sig = SpatialSignature(Map.empty, Map(mS -> inT), declared)
    val rep = SpatialCheck.report(idRoutine, sig)
    rep.check match
      case SpatialCheck.Refuted(inferred, w) =>
        // the witness is RE-VALIDATED here: `Refuted` cannot come from a bug in the searcher
        assert(SpatialTyping.accepts(w, inferred), s"witness ${w.pretty} must inhabit ${inferred.show}")
        assert(!SpatialTyping.accepts(w, declared), s"witness ${w.pretty} must NOT inhabit ${declared.show}")
        assert(!SpatialType.leq(inferred, declared), "and the order must agree it is not provable")
        // a `Refuted` always reports the query that found the witness, whichever decided
        val by = rep.diagnosis.decidedBy.getOrElse(fail("a Refuted must report the query that decided"))
        assert(rep.diagnosis.product.exists(_.refutes) || rep.diagnosis.search.exists(_.refutes), by)
        println(s"REFUTED: ${rep.check.show}\n  $by")
      case other => fail(s"expected Refuted, got ${other.show}")
  }

  test("3b. every finite witness the search returns is a genuine member of the gap") {
    // over the pool: whenever the checker says Refuted, the witness validates, and the search's own
    // universe really contains it
    val rng = new java.util.Random(31337)
    val ts = pool(rng, 90)
    var refuted = 0; var proved = 0; var unknown = 0; var byExhaustion = 0
    for a <- ts; _ <- 0 until 4 do
      val b = ts(rng.nextInt(ts.size))
      SpatialCheck.types(a, b)._1 match
        case SpatialCheck.Refuted(_, w) =>
          assert(SpatialTyping.accepts(w, a), s"bad witness ${w.pretty}: not in ${a.show}")
          assert(!SpatialTyping.accepts(w, b), s"bad witness ${w.pretty}: is in ${b.show}")
          refuted += 1
        case SpatialCheck.Proved(_, c) =>
          // TWO grounds are legitimate, and a `Proved` must rest on one of them: the sound componentwise
          // order, or a COMPLETE enumeration of γ(a) with no counterexample in it.
          assert(SpatialType.leq(a, b) || c.exhaustion.exists(_.decidesContainment),
                 s"Proved without the order AND without a complete enumeration: ${a.show} ⊑ ${b.show}")
          assert(c.corroboration.forall(_.witness.isEmpty))
          assert(c.exhaustion.forall(_.witness.isEmpty))
          if !SpatialType.leq(a, b) then byExhaustion += 1
          proved += 1
        case SpatialCheck.Unknown(_, r) =>
          assert(!SpatialType.leq(a, b) || a.uninhabited ||
                   SpatialCheck.decide(a, b).exists(_.vacuous),
                 s"Unknown although the order proved it: $r")
          unknown += 1
    println(s"THREE-WAY: ${refuted + proved + unknown} pairs — Proved $proved (of which $byExhaustion " +
      s"the componentwise order does NOT prove), Refuted $refuted (every witness re-validated), " +
      s"Unknown $unknown")
  }

  // ================================================================================================
  // 4.  A KNOWN `leq` FALSE NEGATIVE RETURNS `Unknown`, NEVER `Refuted`   (required test 4)
  // ================================================================================================

  /** FALSE NEGATIVE A — a PRODUCT INTERACTION, and NOT a repairable one.
   *
   *  HISTORY, because it matters for what this test is allowed to claim.  This used to be a spill window
   *  against tracked classes: `a` said "exactly one path of one or two items" with the SPILL bucket and
   *  `b` said it with two TRACKED classes, and `SpatialGamma.leqSpace` demanded `a`'s window nest inside
   *  `b`'s.  THAT ONE WAS FIXED — `leqSpace` now decides the spill-vs-tracked partition (`canonSpace`
   *  plus the window decomposition in `leqSpaceMask`), and `SpatialLawCheck`'s two order tests measure
   *  ZERO false negatives on universes that DECIDE containment.  Re-pointing this test at a still-open
   *  false negative was the honest response; asserting the repaired one would have been asserting a bug.
   *
   *  THE ONE HERE IS DIFFERENT IN KIND.  Both types carry the SAME shape, which pins the value to
   *  exactly `{ε, a, b}` — so `γ(a) = γ(b) = {fnV}`, a single space, and containment is not merely "true
   *  on a finite universe" but true outright.  `a` states the count as a spill bucket of exactly 3 paths
   *  over lengths [0, 1]; `b` states it as one path of 0 items and two of 1.  The HISTOGRAM alone does
   *  not contain: `a.lens` admits the count vector (0 at length 0, 3 at length 1), which `b.lens`
   *  rejects.  Only the conjunction with the SHAPE — which forbids a second path under any head — rules
   *  that vector out.  No COMPONENTWISE order (and `SpatialType.leq` is `Shape.leqStrong` ×
   *  `leqSpace`) can see this, so it is not a defect to be repaired in `leqSpace`: it is the product
   *  structure, and the class `SpatialLawCheck` names PRODUCT INTERACTION (52 of its 202 residual
   *  false negatives, against 0 avoidable ones). */
  val fnV: SpaceValue = sv(p(), p("a"), p("b"))
  /** the shape that pins the value: ε, a and b PRESENT, nothing else permitted */
  val fnShape: Shape = SpatialGamma.alpha(fnV).shape
  /** the count as a SPILL bucket: exactly 3 paths, spread over lengths [0, 1] */
  val fnA: SpatialType = SpatialType.reduce(SpatialType(fnShape, SpaceType.unknown))
  /** the same count as TRACKED classes: one path of 0 items, two of 1 */
  val fnB: SpatialType = SpatialGamma.alpha(fnV)

  test("4a. the false negative is REAL: γ-containment holds and the order does not see it") {
    assert(!SpatialType.leq(fnA, fnB), s"precondition: the order rejects ${fnA.show} ⊑ ${fnB.show}")
    // DECIDED, not merely "contained on U": the shape pins both sides to the single value `fnV`, and
    // `U` contains it, so these two counts are the same set and the order's `false` is incompleteness.
    val ma = U.filter(SpatialTyping.accepts(_, fnA))
    val mb = U.filter(SpatialTyping.accepts(_, fnB))
    assertEquals(ma, Vector(fnV), s"γ(a) ∩ U must be exactly {${fnV.pretty}}: ${ma.map(_.pretty)}")
    assertEquals(mb, Vector(fnV), s"γ(b) ∩ U must be exactly {${fnV.pretty}}: ${mb.map(_.pretty)}")
    assert(containedOnU(fnA, fnB),
           s"γ-containment must genuinely hold; witness ${witnessOnU(fnA, fnB).map(_.pretty)}")
    // WHY no repair of `leqSpace` can close it: the HISTOGRAM halves are not in the order either way,
    // and the shape halves are equal — so the containment is only visible to the conjunction.
    assert(!SpatialGamma.leqSpace(fnA.lens, fnB.lens), "precondition: the histogram half must reject")
    assert(Shape.leqStrong(fnA.shape, fnB.shape), "precondition: the shape half must hold")
    val chans = SpatialChannels.orderFailures(fnA, fnB)
    assert(chans.nonEmpty, "a rejected pair must name at least one channel")
    assert(chans.forall(_.channel.isInstanceOf[ResultChannel.LengthClass]),
           s"only the length classes may object here: ${chans.map(_.show).mkString("; ")}")
    // and every one of them is marked sufficient-only, BECAUSE the shape half is contained
    assert(chans.forall(_.sufficientOnly), chans.map(_.show).mkString("\n"))
    println(s"FALSE NEGATIVE A (product interaction): ${fnA.show} ⊑ ${fnB.show}\n  leq = false, " +
      s"γ(a) = γ(b) = {${fnV.pretty}} (decided on ${U.size} values)\n  " +
      chans.map(_.show).mkString("\n  "))
  }

  test("4b. …and the COMBINED shape×histogram query DECIDES it: Proved, with a complete enumeration") {
    // THIS IS the FIX.  The pair is a genuine `leq` false negative (4a proves that) and it used
    // to come back `Unknown` — "the bounded universe cannot see a witness, so nothing is claimed either
    // way".  The product query does not compare the components at all: it ENUMERATES γ(fnA) — which the
    // closed shape makes finite and provably complete — and tests each member with the full product γ.
    val d = SpatialCheck.decide(fnA, fnB).getOrElse(fail("the closed shape must admit an enumeration"))
    assertEquals(d.paths.toSet, Set(p(), p("a"), p("b")),
                 s"the closed shape admits exactly ε, a and b: ${d.paths.map(_.show)}")
    assertEquals(d.members, 1L, s"γ(fnA) is the single value ${fnV.pretty}: ${d.show}")
    assert(d.witness.isEmpty && d.decidesContainment, d.show)
    // the enumeration agrees with the independent decision on U, which is ground truth here
    assertEquals(d.members, U.count(SpatialTyping.accepts(_, fnA)).toLong,
                 "the complete enumeration must find exactly the members U finds")

    val (verdict, diag) = SpatialCheck.types(fnA, fnB)
    assert(!verdict.isRefuted, s"a false negative must NEVER be Refuted:\n${verdict.show}")
    assert(verdict.isProved, s"the product query must DECIDE this pair now:\n${verdict.show}")
    val cert = verdict match { case SpatialCheck.Proved(_, c) => c; case _ => fail("unreachable") }
    assert(!SpatialType.leq(fnA, fnB), "…while the componentwise order still does not prove it")
    assert(cert.order.contains("EXHAUSTION"), cert.order)
    assert(cert.exhaustion.exists(_.decidesContainment), cert.show)
    assertEquals(diag.failures, Vector.empty, "a Proved has no failing channel")
    assertEquals(diag.product.map(_.members), Some(1L))
    println(s"FALSE NEGATIVE A decided: ${verdict.show}")

    // and turning the product query OFF restores the honest `Unknown`, with the same wording as before —
    // so the improvement is the QUERY and not a relaxed verdict
    val (off, offDiag) = SpatialCheck.types(fnA, fnB, product = ProductSearch.off)
    assert(off.isUnknown, off.show)
    val reason = off match { case SpatialCheck.Unknown(_, r) => r; case _ => "" }
    assert(reason.contains("NOT PROVED and NOT refuted"), reason)
    assert(reason.contains("SUFFICIENT CONDITION ONLY"), reason)
    assert(offDiag.search.exists(_.completeOnUniverse), offDiag.show)
    println(s"FALSE NEGATIVE A with ProductSearch.off: ${off.show.linesIterator.next().take(150)}")
  }

  test("4c. the same false negative through a real ROUTINE (the identity over a declared mention)") {
    // the routine entry point, not the type-pair one: `routine(s) = s` infers its input's declared type
    // exactly, so this is the false negative above arriving through `SpatialCheck.report`.
    val r = Routine(RoutinePtr("id"), Vector.empty, Vector(mS), Space.Mention(mS))
    val sig = SpatialSignature(Map.empty, Map(mS -> fnA), fnB)
    val rep = SpatialCheck.report(r, sig)
    // THE SAME CLAIM, NOT THE SAME CARRIER.  `SpatialCheck.report` runs
    // `SpatialType.reduce`, whose `constrainShape` now installs a CERTIFICATE where the declaration
    // carried none — `fnA`'s children have `Cert.top` and the inferred ones have `{ε}`, because the
    // length constraint proves those levels hold nothing but the empty path.  That is `reduce` doing
    // its job, so the assertion is on the claim: identical on every channel `show` renders, and
    // inferred ⊑ declared in the strong-γ order.  Structural equality of the two carriers would fail
    // for a strictly better answer, which is the one thing this assertion must not do.
    assertEquals(rep.inferred.show, fnA.show,
                 s"the routine really does infer the false-negative type: ${rep.inferred.show}")
    assert(SpatialType.leq(rep.inferred, fnA),
           s"the inferred type must be at least as strong as the declaration: ${rep.inferred.show}")
    assert(!rep.check.isRefuted)
    assert(rep.check.isProved, s"the product query must decide it through the routine too: ${rep.check.show}")
    assert(rep.diagnosis.product.exists(_.decidesContainment), rep.diagnosis.show)
    // …and the declaration the proof is MODULO is still named as an assumption
    assert(rep.diagnosis.assumptions.exists {
      case SpatialAssumption.InputSpaceAnnotation(m, t) => m == mS && t == fnA
      case _ => false }, rep.diagnosis.show)
    // with the product query off, the routine route reproduces the old Unknown and its channel diagnosis
    val off = SpatialCheck.report(r, sig, product = ProductSearch.off)
    assert(off.check.isUnknown, s"expected Unknown, got ${off.check.show}")
    assert(off.diagnosis.failures.nonEmpty &&
             off.diagnosis.failures.forall(_.channel.isInstanceOf[ResultChannel.LengthClass]),
           off.diagnosis.failures.map(_.show).mkString("; "))
    assert(off.diagnosis.failures.forall(_.sufficientOnly),
           off.diagnosis.failures.map(_.show).mkString("; "))
    println(s"FALSE NEGATIVE A via routine:\n${rep.show}")
  }

  /** FALSE NEGATIVE B — the whole family, HUNTED rather than guessed.
   *
   *  A hand-picked second example kept going stale: `x ∪ x` against an exact declaration looks like it
   *  should be one (the union transfer's class upper is `hi_a + hi_b`), but the bidirectional reducer
   *  caps it back with the shape's total upper and the order then succeeds.  So this enumerates the
   *  false negatives instead — pairs where γ-containment is DECIDED true on the finite universe and the
   *  order still says no — measures the rate the way the review does, attributes each to its channels,
   *  and asserts the property that matters for every one of them at once. */
  test("4d. leq's incompleteness, measured and attributed — and NONE of it becomes a type error") {
    // THE DIAGNOSTIC POOL the review quotes: 62 γ-contained pairs with γ(a) ∩ U inhabited, of which the
    // componentwise order misses 10 (16.1%).  Those 10 all used to be `Unknown`; this test now also
    // measures how many the COMBINED product query DECIDES, and names the reason for every one it cannot.
    val rng = new java.util.Random(606060)
    val ts = pool(rng, 130)
    var decidedProved = 0; var stillUnknown = 0; var unknownBefore = 0
    var reasons = Map.empty[String, Int]
    // "γ-contained on U" only says something when γ(a) ∩ U is INHABITED: a type with no member in the
    // universe (a 13-head one, say) is vacuously contained in everything and would inflate the rate.
    def inhabitedOnU(t: SpatialType): Boolean = U.exists(SpatialTyping.accepts(_, t))
    var pairs = 0; var vacuous = 0; var contained = 0; var leqHeld = 0; var falseNeg = 0
    var byKind = Map.empty[String, Int]
    var examples = Map.empty[String, String]
    for a <- ts; _ <- 0 until 8 do
      val b = ts(rng.nextInt(ts.size))
      pairs += 1
      val leq = SpatialType.leq(a, b)
      val live = inhabitedOnU(a)
      val cont = containedOnU(a, b)
      if leq then
        leqHeld += 1
        // the order is SOUND: whatever it proves, γ-containment on U agrees
        assert(cont || a.uninhabited,
               s"leq held but γ-containment on U fails: ${a.show} ⊑ ${b.show}\n  witness " +
                 s"${witnessOnU(a, b).map(_.pretty)}")
      if cont && !live then vacuous += 1
      if cont && live then
        contained += 1
        if !leq then
          falseNeg += 1
          val chans = SpatialChannels.orderFailures(a, b)
          assert(chans.nonEmpty, s"a rejected pair with no named channel: ${a.show} ⊑ ${b.show}")
          for k <- chans.map(_.channel.kind).distinct do
            byKind = byKind.updated(k, byKind.getOrElse(k, 0) + 1)
            if !examples.contains(k) then examples = examples.updated(k, s"${a.show}  ⊑  ${b.show}")
          // THE property, unchanged and non-negotiable: a false negative is never a TYPE ERROR
          val v = SpatialCheck.types(a, b)._1
          // BEFORE/AFTER, measured in the same run rather than remembered: `ProductSearch.off` IS the old
          // behaviour, byte for byte, so the delta below is the product query's and nothing else's.
          val before = SpatialCheck.types(a, b, product = ProductSearch.off)._1
          assert(!before.isProved, s"the componentwise checker cannot prove a leq-rejected pair: " +
            s"${before.show}")
          if before.isUnknown then unknownBefore += 1
          v match
            case SpatialCheck.Refuted(_, w) =>
              assert(!U.contains(w), s"REFUTED a γ-contained pair with a witness inside U: ${w.pretty}")
              assert(SpatialTyping.accepts(w, a) && !SpatialTyping.accepts(w, b))
            case SpatialCheck.Proved(_, c) =>
              // …and a `Proved` on a pair the ORDER rejects may only come from a COMPLETE enumeration
              assert(c.exhaustion.exists(_.decidesContainment),
                     s"Proved a leq-rejected pair without a complete enumeration:\n${c.show}")
              assert(SpatialCheck.decide(a, b).exists(d => d.witness.isEmpty && d.members > 0))
              decidedProved += 1
            case SpatialCheck.Unknown(_, r) =>
              stillUnknown += 1
              // EVERY remaining Unknown must NAME why the product query could not decide it, and the
              // reason has to be in the user-facing text and not only in an internal API
              val why = SpatialCheck.declined(a, b).getOrElse(
                fail(s"the query CAN decide this pair, so Unknown is wrong:\n$r"))
              assert(r.contains(why), s"the reason must reach the user:\n  reason: $why\n  said: $r")
              reasons = reasons.updated(why, reasons.getOrElse(why, 0) + 1)
              println(f"  STILL UNKNOWN: ${a.show}%-64s  ⊑  ${b.show}%-40s  because $why")
    assert(falseNeg > 0, "the pool must exhibit the order's incompleteness at all")
    println(f"FALSE NEGATIVES: $pairs%d pairs; leq held $leqHeld%d (ALL γ-sound on U); " +
      f"$contained%d pairs are γ-contained with γ(a) ∩ U inhabited ($vacuous%d further pairs are " +
      f"contained only vacuously and are excluded); of those, leq misses $falseNeg%d " +
      f"(${100.0 * falseNeg / math.max(1, contained)}%.1f%%) — and NONE became a type error")
    println(f"PRODUCT DECISION on those $falseNeg%d false negatives: PROVED $decidedProved%d, still " +
      f"Unknown $stillUnknown%d, the rest Refuted by a witness OUTSIDE U.")
    for (r, n) <- reasons.toVector.sortBy(-_._2) do println(f"  undecided x$n%-3d because $r")
    println(f"UNKNOWN RATE over the $contained%d γ-contained pairs of the diagnostic pool: " +
      f"$unknownBefore%d (${100.0 * unknownBefore / math.max(1, contained)}%.1f%%) BEFORE " +
      f"(ProductSearch.off = the componentwise checker) -> $stillUnknown%d " +
      f"(${100.0 * stillUnknown / math.max(1, contained)}%.1f%%) AFTER the combined shape×histogram query")
    assert(stillUnknown < unknownBefore, s"the product query must decide something: $unknownBefore -> " +
      s"$stillUnknown")
    for (k, n) <- byKind.toVector.sortBy(-_._2) do
      println(f"  channel $k%-22s $n%4d   e.g. ${examples(k).take(120)}")
  }

  test("4e. THE REFUTER NEVER FABRICATES: no γ-contained pair on the universe is ever Refuted") {
    // this is the property that makes `Refuted` trustworthy, and the one the review insists on: a
    // `false` from the order must not become a type error.
    val rng = new java.util.Random(5150)
    val ts = pool(rng, 110)
    var contained = 0; var containedRefuted = 0; var containedProved = 0; var containedUnknown = 0
    var byProduct = 0
    for a <- ts; _ <- 0 until 6 do
      val b = ts(rng.nextInt(ts.size))
      if containedOnU(a, b) then
        contained += 1
        val (v, d) = SpatialCheck.types(a, b)
        v match
          case SpatialCheck.Refuted(_, w) =>
            // only legitimate if the witness lies OUTSIDE U — neither query's universe is U's.  This is
            // also the sharpest soundness gate on the COMPLETE enumeration: a bug in its completeness
            // argument would show up here as a witness inside U on a U-contained pair.
            assert(!U.contains(w),
                   s"FABRICATED refutation: ${w.pretty} ∈ U, γ-contained pair ${a.show} ⊑ ${b.show}" +
                     s"\n  decided by ${d.decidedBy.getOrElse("nothing")}")
            assert(SpatialTyping.accepts(w, a) && !SpatialTyping.accepts(w, b),
                   s"FABRICATED refutation: ${w.pretty} is not in the gap")
            containedRefuted += 1
          case SpatialCheck.Proved(_, c) =>
            if c.exhaustion.exists(_.decidesContainment) then byProduct += 1
            containedProved += 1
          case SpatialCheck.Unknown(_, _) => containedUnknown += 1
    println(s"REFUTER/no-fabrication: $contained γ-contained pairs on U — Proved $containedProved " +
      s"($byProduct with a COMPLETE product enumeration), Unknown $containedUnknown, Refuted " +
      s"$containedRefuted (each by a witness outside U, re-validated)")
  }

  test("4f. the COMPLETE product enumeration is SOUND: cross-validated against U, which decides") {
    // The `Proved`-by-exhaustion branch is a proof, so it needs an independent check of its completeness
    // argument, not just of its arithmetic.  U is that check on every pair whose paths fit inside it: U is
    // ALL 2^7 spaces over {a, b} with ≤ 2 items, so when the enumeration's alphabet and lengths sit inside
    // U's, γ(a) ∩ U is the whole of γ(a) and the two must agree exactly.
    val rng = new java.util.Random(24680)
    val ts = pool(rng, 150)
    var decided = 0; var comparable = 0; var refutedByProduct = 0; var vacuousByProduct = 0
    for a <- ts; _ <- 0 until 6 do
      val b = ts(rng.nextInt(ts.size))
      SpatialCheck.decide(a, b) match
        case None => ()
        case Some(d) =>
          decided += 1
          if d.refutes then
            val w = d.witness.get
            assert(SpatialTyping.accepts(w, a) && !SpatialTyping.accepts(w, b),
                   s"the product witness ${w.pretty} is not in the gap ${a.show} ∖ ${b.show}")
            refutedByProduct += 1
          if d.vacuous then
            // a complete enumeration with no member: U must find none either
            assertEquals(U.count(SpatialTyping.accepts(_, a)), 0,
                         s"the enumeration called γ(a) empty and U disagrees: ${a.show}\n  ${d.show}")
            vacuousByProduct += 1
          // ---- THE COMPLETENESS CROSS-CHECK, on the pairs whose universe fits inside U ---------------
          val insideU = d.paths.forall(pv => pv.items.length <= 2 && pv.items.forall(Set("a", "b")))
          if insideU then
            comparable += 1
            // `members` is EXACT only when the scan ran to the end; a witness stops it, and the count is
            // then a lower bound (which is all the refutation needs)
            if d.witness.isEmpty then
              assertEquals(d.members, U.count(SpatialTyping.accepts(_, a)).toLong,
                           s"the COMPLETE enumeration and U disagree on |γ(a)| for ${a.show}\n  ${d.show}")
            else
              assert(d.members <= U.count(SpatialTyping.accepts(_, a)).toLong,
                     s"the truncated enumeration overcounted |γ(a)| for ${a.show}\n  ${d.show}")
            if d.decidesContainment then
              assert(containedOnU(a, b),
                     s"the enumeration PROVED containment that U refutes: ${a.show} ⊑ ${b.show}; " +
                       s"witness ${witnessOnU(a, b).map(_.pretty)}\n  ${d.show}")
            if d.refutes then
              assert(!containedOnU(a, b),
                     s"the enumeration REFUTED containment that U proves: ${a.show} ⊑ ${b.show}\n${d.show}")
    assert(decided > 0 && comparable > 0, s"the gate must not be vacuous: decided $decided, " +
      s"comparable $comparable")
    println(s"PRODUCT/soundness: ${decided} pairs decided by a complete enumeration " +
      s"($refutedByProduct refuted, $vacuousByProduct vacuous); $comparable of them have a universe " +
      s"inside U and every one agrees with U on |γ(a)| and on the containment")
  }

  test("4g. what the query CANNOT decide is DECLINED with a named reason, never guessed") {
    // The completeness argument needs a bounded depth, a bounded cardinality, and few enough fresh items.
    // Each failure mode is exercised, and each has to DECLINE rather than answer.
    val cases = Vector(
      "⊤ (unbounded length)" -> SpatialType.top,
      "unbounded cardinality" ->
        SpatialType(Shape.top, SpaceType.bounded(LenBounds(1, 2), Ivl.INF)))
    for (name, t) <- cases do
      assertEquals(SpatialCheck.decide(t, SpatialType.empty), None, s"$name must be DECLINED")
      assert(SpatialCheck.declined(t, SpatialType.empty).nonEmpty, name)
      println(s"  declined [$name]: ${SpatialCheck.declined(t, SpatialType.empty).get}")
    // …and a decidable one IS decided, so the gate above is about the limits and not about always refusing
    val closed = SpatialGamma.alpha(sv(p("a"), p("b", "c")))
    val d = SpatialCheck.decide(closed, SpatialType.top).getOrElse(fail("a closed shape must decide"))
    assertEquals(d.paths.toSet, Set(p("a"), p("b", "c")))
    assert(d.decidesContainment, d.show)
    assertEquals(SpatialCheck.declined(closed, SpatialType.top), None)
    // AN OPEN NODE IS NOT AUTOMATICALLY FATAL (this is what deciding the depth-cap class rests on): a
    // shape the carrier's MaxDepth collapsed still decides, because finitely many FRESH items cover the
    // untracked heads — up to a permutation neither γ can see.
    val deepV = sv(PathValue(List("a", "b", "a", "b", "a")))
    val deep = SpatialGamma.alpha(deepV)
    assert(!deep.shape.headsClosed || deep.shape.depth <= Shape.MaxDepth)
    val dd = SpatialCheck.decide(deep, SpatialType.empty).getOrElse(
      fail(s"a depth-capped shape must still decide: ${SpatialCheck.declined(deep, SpatialType.empty)}"))
    assert(dd.refutes, s"a 5-item path really is outside the empty type: ${dd.show}")
    val w = dd.witness.get
    assert(SpatialTyping.accepts(w, deep) && !SpatialTyping.accepts(w, SpatialType.empty), w.pretty)
    println(s"  depth-capped (5-item path, MaxDepth=${Shape.MaxDepth}) DECIDED: ${dd.show}")
    // both budgets are honoured rather than blown
    val many = SpatialType.reduce(SpatialType(Shape.weaken(
      Shape.of(SpaceValue((0 until 10).map(i => p("k" + i)).toSet))), SpaceType.unknown))
    assertEquals(SpatialCheck.decide(many, SpatialType.top, ProductSearch(maxPaths = 4)), None,
                 "a path set past maxPaths must be declined")
    assert(SpatialCheck.declined(many, SpatialType.top, ProductSearch(maxPaths = 4)).exists(
             _.contains("maxPaths")))
    assertEquals(SpatialCheck.decide(many, SpatialType.top,
                                     ProductSearch(maxPaths = 16, maxCandidates = 8L)), None,
                 "an enumeration past maxCandidates must be declined")
    // THE FRESH-ITEM BUDGET BITES ONLY WHERE THE HEADS ARE GENUINELY ANONYMOUS.  A ⊤ head set names
    // nothing, so a complete alphabet needs fresh items and `maxFresh = 0` declines…
    val anon = SpatialType.reduce(SpatialType(Shape.top, SpaceType.exact(1L, 1L)))
    assert(SpatialCheck.declined(anon, SpatialType.empty, ProductSearch(maxFresh = 0)).exists(
             _.contains("maxFresh")), "the fresh-item budget must be honoured too")
    // …while the DEPTH-CAPPED shape needs none at all any more: channel (e) names the heads the
    // collapse dropped, so its alphabet is finite and known and the query decides on a zero budget.
    assertEquals(SpatialCheck.declined(deep, SpatialType.empty, ProductSearch(maxFresh = 0)), None,
                 s"a NAMED spill needs no fresh item: ${deep.shape.show}")
    println(s"PRODUCT/declines: every limit declines with a named reason; a closed ${d.paths.size}-path " +
      "shape and a depth-capped one both decide; maxPaths/maxCandidates/maxFresh all honoured")
  }

  // ================================================================================================
  // 5.  DIAGNOSTICS IDENTIFY CHANNEL, ASSUMPTION AND NODE          (required test 5)
  // ================================================================================================

  test("5a. the failing channel, the source NODE and the assumption relied on there") {
    // the width enters at the MENTION, which is child 1 of the union — not at the root
    val body = Space.Union(lit(p("a", "0")), Space.Mention(mS))
    val r = Routine(RoutinePtr("widen"), Vector.empty, Vector(mS), body)
    val inT = SpatialGamma.alpha(sv(p("b", "0")))
    val declared = SpatialGamma.alpha(sv(p("a", "0")))
    val rep = SpatialCheck.report(r, SpatialSignature(Map.empty, Map(mS -> inT), declared))

    // (i) CHANNEL — the declared head set is closed on {a} and the inferred type adds `b`
    assert(rep.diagnosis.channels.contains(ResultChannel.UntrackedCount(Nil)),
           s"channels were ${rep.diagnosis.channels.map(_.show)}")
    // (ii) NODE — the untracked-head count is already wrong at the mention, position /1
    val blame = rep.diagnosis.blame.filter(_.channel == ResultChannel.UntrackedCount(Nil))
    assert(blame.nonEmpty, rep.diagnosis.show)
    assertEquals(blame.map(_.node).toSet, Set(NodeId(Vector(1))),
      s"the source node must be the mention at /1, got ${blame.map(_.node.show)}\n${rep.diagnosis.show}")
    // the literal operand is NOT blamed: it is inside the declared head set
    assert(!rep.diagnosis.blame.exists(_.node == NodeId(Vector(0))), rep.diagnosis.show)
    // (iii) ASSUMPTION — the analysis relied on the declared type of `s` at that node
    assertEquals(blame.map(_.assumption).toSet,
                 Set(SpatialAssumption.InputSpaceAnnotation(mS, inT)),
                 rep.diagnosis.show)
    assert(blame.head.expression.contains("s"), blame.head.show)
    println(s"DIAGNOSTICS:\n${rep.show}")
  }

  test("5b. a ⊤-producing occurrence is named with the assumption that produced the ⊤") {
    var called = 0
    val bomb: SpaceValue => SpaceValue = (v: SpaceValue) => { called += 1; v }
    val body = Space.Union(lit(p("a", "0")), Space.GroundedSS(lit(p("z")), bomb))
    val r = Routine(RoutinePtr("opaque"), Vector.empty, Vector.empty, Space.Empty).copy(body = body)
    val declared = SpatialGamma.alpha(sv(p("a", "0")))
    val rep = SpatialCheck.report(r, SpatialSignature(Map.empty, Map.empty, declared))
    assertEquals(called, 0, "the analysis must NOT have run the grounded function")
    assert(rep.diagnosis.assumptions.contains(SpatialAssumption.OpaqueGrounded), rep.diagnosis.show)
    val g = rep.diagnosis.blame.filter(_.assumption == SpatialAssumption.OpaqueGrounded)
    assert(g.nonEmpty, s"the grounded occurrence must be blamed:\n${rep.diagnosis.show}")
    assertEquals(g.map(_.node).toSet, Set(NodeId(Vector(1))), g.map(_.show).mkString("\n"))
    println(s"DIAGNOSTICS/⊤: ${g.map(_.show).mkString("\n  ")}")
  }

  test("5c. a self-call is named as RecursionWidened, not silently inlined") {
    val self = RoutinePtr("rec")
    val body = Space.Union(lit(p("a")), Space.Call(self, Vector.empty, Vector(Space.Mention(mS))))
    val r = Routine(self, Vector.empty, Vector(mS), body)
    val sig = SpatialSignature(Map.empty, Map(mS -> SpatialType.top), SpatialGamma.alpha(sv(p("a"))))
    val rep = SpatialCheck.report(r, sig, { case `self` => r })
    assert(rep.diagnosis.assumptions.contains(SpatialAssumption.RecursionWidened(self)),
           rep.diagnosis.show)
    // ==A RECURSIVE ROUTINE *CAN* BE PROVED NOW, AND THE ASSUMPTION IS STILL NAMED ==
    //
    // This used to assert `!rep.check.isProved` — "a recursive routine cannot be proved by this
    // checker" — because the self-call widened to ⊤.  `SpatialRecursion.summaryAt` is the production
    // consumer of the CERTIFIED summaries at that point, so the self-call carries a real type and the
    // verdict is PROVED with `inferred shape {a·{ε!}}  lens {len 1: [1, 1]}`.
    //
    // WHAT THIS TEST IS ACTUALLY FOR SURVIVES INTACT, and it is the assertion above: the self-call is
    // NAMED as `RecursionWidened` in the diagnosis rather than silently inlined.  A proof that rests
    // on a summary must say so, and it does.  So the pair asserted here is "provable AND the premise
    // is named", which is strictly more than "not provable".
    assert(rep.check.isProved,
           s"a recursive routine's contract is provable through the certified summary ( " +
           s"1D.1); if the consumer is removed this is the gate that reports it: ${rep.check.show}")
    assert(rep.diagnosis.assumptions.contains(SpatialAssumption.RecursionWidened(self)),
           s"the self-call must still be NAMED as a premise even when the summary proves the " +
           s"contract — a proof that does not say what it rests on is the thing this test exists " +
           s"to prevent: ${rep.diagnosis.show}")
    println(s"DIAGNOSTICS/recursion: ${rep.check.show}")
  }

  test("5d. every SpatialAssumption case is actually EMITTED — none is a dead promise") {
    // The review objects to `Fact.PrefixAbsent` being a public case `Fact.from` never emits.  The same
    // must not be true of the premises a certificate names, so each one is produced here.
    var seen = Set.empty[String]
    def note(as: Vector[SpatialAssumption]): Unit = seen = seen ++ as.map(_.productPrefix)

    // annotated + unannotated inputs, a known callee, an unknown callee, a self-call, a fixpoint and
    // an iteration — all in one body
    val self = RoutinePtr("everything")
    val other = RoutinePtr("callee")
    val absent = RoutinePtr("nowhere")
    val declaredM = SpaceMention("known")
    val openM = SpaceMention("unknown")
    val q = PathRef("q")
    val otherR = Routine(other, Vector.empty, Vector(SpaceMention("x")),
                         Space.TailsUnion(Space.Mention(SpaceMention("x"))))
    val undeclared = PathRef("undeclared")
    val parts = Vector(
      Space.Mention(declaredM),                                              // InputSpaceAnnotation
      Space.Mention(openM),                                                  // MissingSpaceAnnotation
      Space.Call(other, Vector.empty, Vector(Space.Mention(declaredM))),     // RoutineBody
      Space.Call(absent, Vector.empty, Vector(Space.Mention(declaredM))),    // MissingRoutine
      Space.Call(self, Vector.empty, Vector(Space.Mention(declaredM))),      // RecursionWidened
      Space.Fixpoint(Space.Mention(declaredM), SpaceMention("rec"),          // FixpointPostFixpoint
                     Space.TailsUnion(Space.Mention(SpaceMention("rec")))),
      Space.Iteration(Space.Mention(declaredM), PathRef("h"), SpaceMention("rest"),  // HeadGroupUnion
                      Space.Mention(SpaceMention("rest"))),
      Space.Singleton(Path.Deref(q)),                                        // InputPathAnnotation
      Space.Singleton(Path.Deref(undeclared)))                               // MissingPathAnnotation
    val body = parts.reduce(Space.Union.apply)
    val r = Routine(self, Vector(q, undeclared), Vector(declaredM, openM), body)
    val sig = SpatialSignature(Map(q -> PathType.opaque(1, 2)),
                               Map(declaredM -> SpatialGamma.alpha(sv(p("a", "b")))), SpatialType.empty)
    val rep = SpatialCheck.report(r, sig, { case `other` => otherR })
    note(rep.diagnosis.assumptions)
    note(rep.diagnosis.blame.map(_.assumption))

    // …and a run whose traversal genuinely hits a budget, for BudgetTop
    val deep = (0 until 12).foldLeft(lit(p("a")))((acc, _) => Space.TailsUnion(acc))
    val tight = SpatialConfig(termDepth = 3, nodeBudget = 8)
    val repB = SpatialCheck.report(Routine(RoutinePtr("deep"), Vector.empty, Vector.empty, deep),
                                   SpatialSignature.of(SpatialType.empty), PartialFunction.empty,
                                   WitnessSearch.default, tight)
    note(repB.diagnosis.assumptions)
    note(repB.diagnosis.blame.map(_.assumption))
    // …and a signature that declares a KNOWN path value, for the other InputPathAnnotation shape
    note(SpatialCheck.report(Routine(RoutinePtr("k"), Vector(q), Vector.empty,
                                     Space.Singleton(Path.Deref(q))),
                             SpatialSignature(Map(q -> PathType.known(p("a"))), Map.empty,
                                              SpatialType.empty)).diagnosis.assumptions)

    // …and a run under a DISCHARGED semantic law that tightens, for LawBound: the review requires a
    // certificate to NAME every law it depended on, so the premise has to exist and has to be emitted.
    val lm = SpaceMention("lawful")
    val lr = Routine(RoutinePtr("lawful"), Vector.empty, Vector(lm), Space.Mention(lm))
    val law = SpatialBoundLaw("at-most-one-path", _ => true,
      _ => Some(SpatialType(Shape.top, SpaceType.bounded(LenBounds.unknown, 1))),
      LawEvidence.SmtProved("a SizeZ3 query over the declared bound"))
    val lawRep = SpatialCheck.report(lr, SpatialSignature(Map.empty, Map(lm -> SpatialType.top),
                                                          SpatialType.top),
                                     cfg = SpatialConfig.default.withLaws(law))
    note(lawRep.diagnosis.assumptions)
    assert(lawRep.check.isProved, lawRep.check.show)
    val lawCert = lawRep.check match { case SpatialCheck.Proved(_, c) => c; case _ => fail("unreachable") }
    assert(lawCert.laws.exists(a => a.law == "at-most-one-path" && a.tightened),
           s"the certificate must NAME the law it depended on:\n${lawCert.show}")
    assertEquals(lawCert.lawAssumptions.map {
                   case SpatialAssumption.LawBound(n, e, _) => (n, e.tag); case _ => ("", "") },
                 Vector(("at-most-one-path", "SMT-proved")))
    assert(lawCert.show.contains("laws depended on: at-most-one-path"), lawCert.show)

    val all = Set("InputSpaceAnnotation", "InputPathAnnotation", "MissingSpaceAnnotation",
                  "MissingPathAnnotation", "TransferSoundness", "AnalysisBudgets", "BudgetTop",
                  "RoutineBody", "MissingRoutine", "RecursionWidened", "OpaqueGrounded",
                  "FixpointPostFixpoint", "HeadGroupUnion", "LawBound")
    val missingCases = all -- seen
    assertEquals(missingCases, Set("OpaqueGrounded"),
      s"every assumption case except OpaqueGrounded (covered by 5b) must be emitted here; missing " +
        s"$missingCases, seen $seen")
    println(s"ASSUMPTIONS: ${seen.size} of ${all.size} cases emitted here " +
      s"(OpaqueGrounded is covered by 5b) — none is a dead promise")
  }

  // ================================================================================================
  // 6.  THE MIRRORS NEVER DISAGREE WITH THE PREDICATES THEY EXPLAIN
  // ================================================================================================

  test("6a. the membership mirror agrees with γ on every (type, value) pair") {
    val rng = new java.util.Random(1234)
    val ts = pool(rng, 200)
    var n = 0
    for a <- ts; v <- U do
      SpatialCheck.mirrorNote(v, a) match
        case Some(note) => fail(note)
        case None => n += 1
    println(s"MIRROR/membership: $n pairs, the channel mirror agrees with `accepts` on all of them")
  }

  test("6b. the order mirror agrees with `leq` on every pair") {
    val rng = new java.util.Random(2345)
    val ts = pool(rng, 200)
    var n = 0; var failing = 0
    for a <- ts; _ <- 0 until 10 do
      val b = ts(rng.nextInt(ts.size))
      SpatialCheck.orderMirrorNote(a, b) match
        case Some(note) => fail(note)
        case None => n += 1; if !SpatialType.leq(a, b) then failing += 1
    println(s"MIRROR/order: $n pairs, the channel mirror agrees with `leq` on all of them " +
      s"($failing rejected pairs, each with at least one named channel)")
  }

  // ================================================================================================
  // 8.  NO EVALUATION
  // ================================================================================================

  test("8. no entry point ever runs the program: a grounded bomb that throws is never called") {
    val boom: SpaceValue => SpaceValue = _ => throw RuntimeException("the checker evaluated its subject")
    val pboom: PathValue => SpaceValue = _ => throw RuntimeException("the checker evaluated its subject")
    val body = Space.Union(Space.GroundedSS(lit(p("a")), boom),
                           Space.Iteration(Space.GroundedPS(cp("q"), pboom), PathRef("h"),
                                           SpaceMention("rest"), Space.Mention(SpaceMention("rest"))))
    val r = Routine(RoutinePtr("bomb"), Vector.empty, Vector.empty, body)
    for declared <- Vector(SpatialType.top, SpatialGamma.alpha(sv(p("a"))), SpatialType.empty) do
      val rep = SpatialCheck.report(r, SpatialSignature(Map.empty, Map.empty, declared))
      assert(rep.check.isProved || rep.check.isRefuted || rep.check.isUnknown)
    // and the two type-level entry points, on types derived from the same term
    val t = SpatialTyping.infer(body)
    SpatialCheck.types(t, SpatialType.top)
    SpatialCheck.types(t, SpatialType.empty)
    SpatialCheck.searchWitness(t, SpatialType.empty, WitnessSearch.default)
    for v <- U.take(20) do SpatialCheck.value(v, t)
    println("NO EVALUATION: checkRoutine / types / searchWitness / value all ran on a term whose " +
      "grounded functions throw — none was called")
  }

  // ================================================================================================
  // 9.  A VACUOUS ⊥ IS `Unknown`, NOT `Proved`
  // ================================================================================================

  test("9. ⊥ ⊑ everything, so an unsatisfiable annotation must NOT read as Proved") {
    assert(SpatialType.leq(SpatialType.bottom, SpatialType.empty), "precondition: ⊥ is below everything")
    for declared <- Vector(SpatialType.top, SpatialType.empty, SpatialGamma.alpha(sv(p("a")))) do
      val (v, _) = SpatialCheck.types(SpatialType.bottom, declared)
      assert(v.isUnknown, s"⊥ against ${declared.show} must be Unknown, got ${v.show}")
      val reason = v match { case SpatialCheck.Unknown(_, r) => r; case _ => "" }
      assert(reason.contains("VACUOUS"), reason)
    // and through a routine whose annotations contradict each other: a mention declared to hold at
    // least two one-item paths AND at most one path in total
    val bad = SpatialType(Shape.top, SpaceType.closed(1L -> Ivl(2, 2)))
      .copy(shape = Shape.of(sv(p("a"))))         // shape says exactly {a}: one path, not two
    val r = Routine(RoutinePtr("contra"), Vector.empty, Vector(mS), Space.Mention(mS))
    val rep = SpatialCheck.report(r, SpatialSignature(Map.empty, Map(mS -> bad), SpatialType.top))
    println(s"VACUOUS: contradictory annotation ⇒ inferred ${rep.inferred.show}; verdict " +
      s"${rep.check.show.linesIterator.next()}")
    if rep.inferred.uninhabited then assert(rep.check.isUnknown, rep.check.show)
  }

  // ================================================================================================
  // 10.  ABSTRACT CONFORMANCE IS NOT SEMANTIC CONFORMANCE   (`eval` as ground truth ONLY)
  // ================================================================================================

  test("10. a routine `Refuted` abstractly can satisfy its signature on EVERY concrete input") {
    // `(s ∪ {c}) ∖ {c}` denotes `s` exactly (no input may contain `c`), but the subtraction transfer
    // must give up every MUST claim — a subtraction can delete anything — so the inferred type admits
    // ∅, which the declaration rejects.  The abstract gap is real; the routine is correct.
    val body = Space.Subtraction(Space.Union(Space.Mention(mS), lit(p("c"))), lit(p("c")))
    val r = Routine(RoutinePtr("roundtrip"), Vector.empty, Vector(mS), body)
    val inT = SpatialGamma.lub(SpatialGamma.alpha(sv(p("a"))), SpatialGamma.alpha(sv(p("b"))))
    val sig = SpatialSignature(Map.empty, Map(mS -> inT), inT)
    val rep = SpatialCheck.report(r, sig)
    println(s"ABSTRACT vs SEMANTIC: inferred ${rep.inferred.show}\n  declared ${inT.show}")
    assert(rep.check.isRefuted || rep.check.isUnknown,
           s"the analysis cannot prove this one: ${rep.check.show}")

    // GROUND TRUTH: run the routine on EVERY concrete input the declaration admits, and check the
    // real output against the declared result type.  This is the only `eval` in this file.
    val inputs = U.filter(SpatialTyping.accepts(_, inT))
    assert(inputs.nonEmpty, "the input type must be inhabited on U")
    var conform = 0
    for v <- inputs do
      val out = eval(body)(using PathContextMap(Map.empty), SpaceContextMap(Map(mS -> v)),
                           PartialFunction.empty)
      assert(SpatialTyping.accepts(out, sig.result),
             s"ground truth: input ${v.pretty} produced ${out.pretty}, outside ${sig.result.show}")
      conform += 1
    val verdict = if rep.check.isRefuted then "Refuted" else "Unknown"
    rep.check match
      case SpatialCheck.Refuted(inferred, w) =>
        assert(SpatialTyping.accepts(w, inferred) && !SpatialTyping.accepts(w, sig.result))
        // the witness is a SPURIOUS member: no input produces it
        val produced = inputs.exists { v =>
          eval(body)(using PathContextMap(Map.empty), SpaceContextMap(Map(mS -> v)),
                     PartialFunction.empty) == w }
        assert(!produced, s"the witness ${w.pretty} IS produced — this would be a semantic refutation")
        println(s"ABSTRACT vs SEMANTIC: verdict $verdict with witness ${w.pretty}; that value is " +
          s"produced by NONE of the $conform admissible inputs, all of which conform — exactly the " +
          "abstract/semantic distinction the API documents")
      case _ =>
        println(s"ABSTRACT vs SEMANTIC: verdict $verdict; all $conform admissible inputs conform")
  }

  // ================================================================================================
  // 11.  THE SEARCH REPORTS ITS NUMBERS INSTEAD OF HANGING  (the search's stated contract)
  // ================================================================================================

  test("11. the bounded search reports path count, space count and budget, and stops on the budget") {
    val a = SpatialType.top
    val b = SpatialGamma.alpha(sv(p("a")))
    val wide = WitnessSearch(maxItems = 3, maxLen = 3, maxPaths = 20, maxCandidates = 64L)
    val r = SpatialCheck.searchWitness(a, b, wide)
    println(s"SEARCH/budget: ${r.show}")
    assert(r.examined <= wide.maxCandidates + 1, r.show)
    // ⊤ against ⊤ has NO head items, so its universe is one fresh item and three paths — the budget
    // never even engages.  A search that must genuinely exhaust one needs a wide alphabet AND no gap to
    // find, so compare a type with itself: γ(t) ∖ γ(t) is empty by construction.
    val wideT = SpatialType.reduce(SpatialType(
      Shape.weaken(Shape.of(sv(p("a"), p("b", "b"), p("c", "c", "c")))), SpaceType.unknown))
    val hard = SpatialCheck.searchWitness(wideT, wideT,
                                          WitnessSearch(maxItems = 3, maxLen = 2, maxPaths = 13,
                                                        maxCandidates = 50L))
    assert(hard.witness.isEmpty, hard.show)
    assert(hard.universe.spaceCount > 1000, s"the universe must be big enough to exhaust: ${hard.show}")
    assert(hard.exhaustedBudget, s"a 50-candidate budget must not claim completeness:\n${hard.show}")
    assert(!hard.completeOnUniverse)
    println(s"SEARCH/exhausted: ${hard.show}")
    // …and the report distinguishes that from a genuinely complete pass
    val small = SpatialCheck.searchWitness(SpatialGamma.alpha(sv(p("a"))), SpatialType.top,
                                           WitnessSearch(maxItems = 2, maxLen = 1, maxPaths = 4,
                                                         maxCandidates = 10000L))
    assert(small.completeOnUniverse, small.show)
    println(s"SEARCH/complete: ${small.show}")
    // …and from the case where the universe could not hold a member of the inferred type AT ALL, where
    // "no witness" is vacuous and must NOT read as an exhaustive pass.  The subject has to be one the
    // PRODUCT query cannot decide either, or its complete enumeration answers first — see the
    // 16-head case just below, which is exactly that and no longer reaches this path.
    val wideOpen = SpatialType.reduce(SpatialType(Shape.top, SpaceType.exact(1L, 40L)))
    val vacuousSearch = SpatialCheck.searchWitness(wideOpen, SpatialType.empty,
                                                   WitnessSearch(maxItems = 2, maxLen = 1, maxPaths = 4,
                                                                 maxCandidates = 10000L))
    assert(vacuousSearch.outOfScope, vacuousSearch.show)
    assert(!vacuousSearch.completeOnUniverse,
           s"a universe that cannot hold a member must not claim completeness:\n${vacuousSearch.show}")
    assert(vacuousSearch.witness.isEmpty)
    val (v2, _) = SpatialCheck.types(wideOpen, SpatialType.empty,
                                     WitnessSearch(maxItems = 2, maxLen = 1, maxPaths = 4))
    assert(v2.isUnknown, v2.show)
    val r2 = v2 match { case SpatialCheck.Unknown(_, r) => r; case _ => "" }
    assert(r2.contains("could not look"), r2)
    println(s"SEARCH/out-of-scope: ${vacuousSearch.show}")
    // A 16-HEAD TYPE IS PAST `Shape.MaxHeads`, AND THE WIDTH SPILL NOW NAMES WHAT IT DROPPED.  That
    // certificate is what makes the alphabet finite and known, so `plan` can build a COMPLETE path set
    // over it (12 tracked + 4 spilled) and the product query decides the pair outright — with a real
    // member as the witness, not a shrug.  Before channel (e) the spilled heads were anonymous, the
    // walk needed 16 fresh items, and the answer was "could not look".
    val wide16 = SpatialGamma.alpha(SpaceValue((0 until 16).map(i => p("h" + i)).toSet))
    assert(wide16.shape.certNames.isDefined, s"the spill must name its keys: ${wide16.shape.show}")
    assertEquals(SpatialCheck.plan(wide16, SpatialType.empty, ProductSearch.default).map(_.size),
                 Right(16), s"the complete path set must include the SPILLED heads: ${wide16.shape.show}")
    val (v16, _) = SpatialCheck.types(wide16, SpatialType.empty,
                                      WitnessSearch(maxItems = 2, maxLen = 1, maxPaths = 4))
    assert(v16.isRefuted, s"a complete enumeration must decide it: ${v16.show}")
    println(s"SEARCH/named-spill: ${v16.show}")
    // a type whose SHORTEST path is longer than the caller's maxLen: the ceiling is raised to that
    // length rather than leaving the universe empty, because that is the only length worth looking at
    val deepT = SpatialType.reduce(SpatialType(Shape.top, SpaceType.exact(9L, 1L)))
    val raised = SpatialCheck.searchWitness(deepT, SpatialType.empty,
                                            WitnessSearch(maxItems = 2, maxLen = 2, maxPaths = 8,
                                                          maxCandidates = 10000L))
    assertEquals(raised.universe.lens, LenBounds(9, 9), raised.show)
    assert(raised.universe.truncated, "the universe is no longer the full one over its alphabet")
    assert(raised.refutes, s"a 9-item path really is outside the empty type: ${raised.show}")
    assertEquals(raised.witness.map(_.paths.head.items.length), Some(9), raised.show)
    println(s"SEARCH/raised-ceiling: ${raised.show}")
    // …but past the hard construction cap the universe IS empty, and that reads as out-of-scope
    val tooDeep = SpatialType.reduce(SpatialType(Shape.top, SpaceType.exact(200L, 1L)))
    val unreachable = SpatialCheck.searchWitness(tooDeep, SpatialType.empty, WitnessSearch())
    assert(unreachable.universe.paths.isEmpty, unreachable.show)
    assert(unreachable.universe.truncated, unreachable.show)
    assert(unreachable.outOfScope && !unreachable.completeOnUniverse && !unreachable.refutes,
           unreachable.show)
    assert(SpatialCheck.types(tooDeep, SpatialType.empty)._1.isUnknown)
    println(s"SEARCH/unreachable-length: ${unreachable.show}")
  }

  test("11c. the signature is the pipeline's SpatialAnnotations plus a result — one representation") {
    val q = PathRef("q"); val z = PathRef("z")
    val sig = SpatialSignature(Map(q -> PathType.known(p("a", "b")), z -> PathType.opaque(0, 3)),
                               Map(mS -> SpatialGamma.alpha(sv(p("a")))), SpatialType.top)
    val ann = sig.annotations()
    assertEquals(ann.paths, Map(q -> p("a", "b")))
    assertEquals(ann.pathLens, Map(z -> LenBounds(0, 3)))
    assertEquals(ann.spaces, sig.spaces)
    // the round trip is the identity, and both sides produce the SAME analysis environment
    assertEquals(SpatialSignature.from(ann, sig.result), sig)
    val a = ann.env()
    val b = sig.env()
    assertEquals(a.spaces, b.spaces)
    assertEquals(a.paths, b.paths)
    assertEquals(a.opaque, b.opaque)
    assertEquals(a.lengths.paths, b.lengths.paths)
    assertEquals(a.lengths.spaces, b.lengths.spaces)
    // a ref the pipeline lists in BOTH maps is opaque on both sides, because `Env` reads it that way
    val both = SpatialAnnotations(paths = Map(q -> p("a")), pathLens = Map(q -> LenBounds(1, 4)))
    val back = SpatialSignature.from(both, SpatialType.top)
    assertEquals(back.paths(q), PathType.opaque(1, 4))
    assertEquals(back.env().paths.get(q), None)
    assertEquals(both.env().paths.get(q).isDefined && both.env().opaque.contains(q), true,
                 "precondition: the pipeline's env also shadows the known value with the opaque bound")
    println("SIGNATURE/bridge: SpatialSignature <-> SpatialAnnotations round-trips and yields the " +
      "identical SpatialTyping.Env")
  }

  test("11b. a PathType cannot declare a value that violates its own length bound") {
    intercept[IllegalArgumentException](PathType(Some(p("a", "b")), LenBounds(1, 1)))
    assertEquals(PathType.known(p("a", "b")).len, LenBounds(2, 2))
    assertEquals(PathType.opaque(1, 3).value, None)
    // the signature's env keeps ONE source of truth for a path's length
    val q = PathRef("q")
    val e = SpatialSignature(Map(q -> PathType.known(p("a", "b"))), Map.empty, SpatialType.top).env()
    assertEquals(e.paths.get(q), Some(p("a", "b")))
    assertEquals(e.opaque.get(q), None)
    assertEquals(e.lengths.paths.get(q), Some(LenBounds(2, 2)))
    val o = SpatialSignature(Map(q -> PathType.opaque(1, 3)), Map.empty, SpatialType.top).env()
    assertEquals(o.paths.get(q), None)
    assertEquals(o.lengths.paths.get(q), Some(LenBounds(1, 3)))
    println("SIGNATURE: PathType is self-consistent and `env` derives lengths from one place")
  }
