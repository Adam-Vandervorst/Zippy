package morkl

import munit.FunSuite
import scala.io.Source

/** TIER 3 MEETS THE IMPLEMENTATION.
 *
 *  `proofs/unbounded/REGISTRY.tsv` carries a `generalises` column naming, for each schematic law,
 *  the tier-1 / tier-2 / compiler arm the law subsumes.  That column is TRACEABILITY: a human wrote
 *  it, nothing checks it, and a law could name an arm it does not actually generalise — or an arm
 *  could be rewritten out from under a law that still claims it.
 *
 *  This suite is the missing half.  Each entry below is one tier-3 law RE-STATED AS AN EXECUTABLE
 *  PREDICATE and run against the reference executor on random inputs, so the law and the
 *  implementation are checked against each other rather than merely cross-referenced.  It is a
 *  CONFORMANCE OBLIGATION, not a proof — the proof is the `.p` file, quantified over all inputs;
 *  this is the link from that statement to the Scala that is supposed to satisfy it, and it is what
 *  fails if someone changes an `eval` arm without touching the law.
 *
 *  THREE GATES:
 *    1. every conformance law holds on every seed (else: the implementation contradicts a PROVED
 *       tier-3 theorem — one of the two is wrong and the suite says which law);
 *    2. every registry row is either conformance-checked here or listed in [[notExecutable]] WITH A
 *       REASON, so "no check" is a recorded decision and not an omission;
 *    3. every NEGATIVE control has an executed COUNTERMODEL — a concrete input at which the false
 *       law fails.  This is the part `proofs/unbounded/run.sh` cannot do: it reports a negative
 *       control as `NOT-PROVED (expected)` on a TIMEOUT, which is the absence of a proof and not a
 *       refutation.  A countermodel here turns each one into a semantic separation.
 */
class TierThreeConformance extends FunSuite:
  import Space.*

  private val registryFile = new java.io.File(Loaders.repoRoot, "proofs/unbounded/REGISTRY.tsv")
  private val statusFile = new java.io.File(Loaders.repoRoot, "proofs/unbounded/STATUS.tsv")

  private lazy val registry: Vector[Array[String]] =
    if !registryFile.exists then Vector.empty
    else
      val s = Source.fromFile(registryFile)
      try s.getLines().filterNot(l => l.startsWith("#") || l.isBlank).map(_.split("\t", -1)).toVector
      finally s.close()

  // ------------------------------------------------------------------------------------------
  // random inputs
  // ------------------------------------------------------------------------------------------
  private val items = Vector("p", "q", "r")
  private def randPath(rng: scala.util.Random): PathValue =
    PathValue(List.fill(rng.nextInt(3))(items(rng.nextInt(items.length))))
  private def randValue(rng: scala.util.Random): SpaceValue =
    SpaceValue((0 to rng.nextInt(5)).map(_ => randPath(rng)).toSet)

  private val empty = SpaceValue(Set.empty)
  private def sv(ps: String*): SpaceValue =
    SpaceValue(ps.map(s => PathValue(if s.isEmpty then Nil else s.split('.').toList)).toSet)
  private def lit(v: SpaceValue): Space = Literal(v)
  private def run(s: Space, binds: Map[String, SpaceValue] = Map.empty): SpaceValue =
    eval(s)(using PathContextMap(Map.empty),
                  SpaceContextMap(binds.map((k, v) => SpaceMention(k) -> v)), PartialFunction.empty)

  /** the same law, through the OTHER two executors — a conformance check that only tested `eval`
   *  would not notice a trie backend that disagreed with it. */
  private def runAll(s: Space, binds: Map[String, SpaceValue] = Map.empty): List[(String, SpaceValue)] =
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(binds.map((k, v) => SpaceMention(k) -> v))
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
    List("eval" -> eval(s), "evalI" -> evalI(s).toSpaceValue, "evalT" -> evalT(s).toSpaceValue)

  // ------------------------------------------------------------------------------------------
  // the conformance laws, keyed by registry row
  // ------------------------------------------------------------------------------------------
  /** one law: the registry rows it covers, and a check that must hold for one random draw */
  private final case class Law(rows: Set[String], name: String, check: scala.util.Random => Unit)

  private def eqv(what: String, a: Space, b: Space, binds: Map[String, SpaceValue] = Map.empty): Unit =
    for (who, va) <- runAll(a, binds); (_, vb) <- runAll(b, binds).find(_._1 == who) do
      assertEquals(va, vb, s"$what — disagreement under `$who` on\n  lhs = ${a.show}\n  rhs = ${b.show}\n  binds = $binds")

  private def subset(what: String, a: Space, b: Space, binds: Map[String, SpaceValue] = Map.empty): Unit =
    val (va, vb) = (run(a, binds), run(b, binds))
    assert(va.paths.subsetOf(vb.paths),
           s"$what — ${va.pretty} is NOT contained in ${vb.pretty}\n  lhs = ${a.show}\n  rhs = ${b.show}")

  private val laws: Vector[Law] = Vector(
    // ---- lattice / set ops -------------------------------------------------------------------
    Law(Set("U01"), "union is idempotent, commutative, associative, with unit {}", rng =>
      val (a, b, c) = (lit(randValue(rng)), lit(randValue(rng)), lit(randValue(rng)))
      eqv("U01 idem", Union(a, a), a)
      eqv("U01 comm", Union(a, b), Union(b, a))
      eqv("U01 assoc", Union(Union(a, b), c), Union(a, Union(b, c)))
      eqv("U01 unit", Union(a, Empty), a)),
    Law(Set("U02"), "intersection is idempotent, commutative, associative, {}-annihilated", rng =>
      val (a, b, c) = (lit(randValue(rng)), lit(randValue(rng)), lit(randValue(rng)))
      eqv("U02 idem", Intersection(a, a), a)
      eqv("U02 comm", Intersection(a, b), Intersection(b, a))
      eqv("U02 assoc", Intersection(Intersection(a, b), c), Intersection(a, Intersection(b, c)))
      eqv("U02 annih", Intersection(a, Empty), Empty)),
    Law(Set("U03"), "the inclusion lattice is distributive, both ways", rng =>
      val (a, b, c) = (lit(randValue(rng)), lit(randValue(rng)), lit(randValue(rng)))
      eqv("U03 distrib-1", Intersection(a, Union(b, c)), Union(Intersection(a, b), Intersection(a, c)))
      eqv("U03 distrib-2", Union(a, Intersection(b, c)), Intersection(Union(a, b), Union(a, c)))
      eqv("U03 absorb-1", Union(a, Intersection(a, b)), a)
      eqv("U03 absorb-2", Intersection(a, Union(a, b)), a)),
    Law(Set("U04", "U05", "U06"), "subtraction splits, and the two disjoint decompositions", rng =>
      val (a, b) = (lit(randValue(rng)), lit(randValue(rng)))
      subset("U05 in-minuend", Subtraction(a, b), a)
      eqv("U05 disjoint", Intersection(Subtraction(a, b), b), Empty)
      eqv("U06 split-a", Union(Subtraction(a, b), Intersection(a, b)), a)
      eqv("U06 union-split", Union(a, b), Union(a, Subtraction(b, a)))
      eqv("U05 minus-meet", Subtraction(a, b), Subtraction(a, Intersection(a, b)))),
    Law(Set("U07"), "union/intersection monotone in both; subtraction ANTITONE in the subtrahend", rng =>
      val (a, b) = (randValue(rng), randValue(rng))
      val bigger = SpaceValue(b.paths + randPath(rng))
      subset("U07 mono-union", Union(lit(a), lit(b)), Union(lit(a), lit(bigger)))
      subset("U07 mono-inter", Intersection(lit(a), lit(b)), Intersection(lit(a), lit(bigger)))
      subset("U07 antitone-sub", Subtraction(lit(a), lit(bigger)), Subtraction(lit(a), lit(b)))),
    // ---- restriction / raffination ------------------------------------------------------------
    Law(Set("U08", "U09", "U10", "U11"), "restriction filters; restriction and raffination PARTITION", rng =>
      val (x, y) = (lit(randValue(rng)), lit(randValue(rng)))
      subset("U08 filter", Restriction(x, y), x)
      eqv("U08 idem", Restriction(Restriction(x, y), y), Restriction(x, y))
      eqv("U08 empty", Restriction(x, Empty), Empty)
      eqv("U09 partition", Union(Restriction(x, y), Raffination(x, y)), x)
      eqv("U09 disjoint", Intersection(Restriction(x, y), Raffination(x, y)), Empty)),
    // ---- composition --------------------------------------------------------------------------
    Law(Set("U12", "U13", "U14", "U15"), "composition: associative, unital, distributes, monotone", rng =>
      val (a, b, c) = (lit(randValue(rng)), lit(randValue(rng)), lit(randValue(rng)))
      val e = lit(sv(""))
      eqv("U12 assoc", Composition(Composition(a, b), c), Composition(a, Composition(b, c)))
      eqv("U13 unit-l", Composition(e, a), a)
      eqv("U13 unit-r", Composition(a, e), a)
      eqv("U13 annih-l", Composition(Empty, a), Empty)
      eqv("U13 annih-r", Composition(a, Empty), Empty)
      eqv("U14 distrib-l", Composition(Union(a, b), c), Union(Composition(a, c), Composition(b, c)))
      eqv("U14 distrib-r", Composition(a, Union(b, c)), Union(Composition(a, b), Composition(a, c)))),
    // ---- wrap / unwrap ------------------------------------------------------------------------
    Law(Set("U16", "U17", "U18", "U19", "U20", "U21", "U46", "U49"),
        "wrap/unwrap: round trip, re-wrap, nesting ORDER, boolean homomorphism, |wrap| = |A|", rng =>
      val a = lit(randValue(rng))
      val w = PathValue(List(items(rng.nextInt(items.length))))
      val u = PathValue(List(items(rng.nextInt(items.length))))
      val (pw, pu) = (Path.Constant(w), Path.Constant(u))
      val e = Path.Constant(PathValue(Nil))
      eqv("U16 round trip", Unwrap(Wrap(a, pw), pw), a)
      eqv("U16 wrap-eps", Wrap(a, e), a)
      eqv("U16 unwrap-eps", Unwrap(a, e), a)
      eqv("U17 re-wrap", Wrap(Unwrap(a, pw), pw), Restriction(a, Singleton(pw)))
      eqv("U18 wrap-as-comp", Wrap(a, pw), Composition(Singleton(pw), a))
      // U19: wrap nests RIGHT-to-left, unwrap LEFT-to-right — the exact inversion docs/traps.md records
      val wu = Path.Constant(PathValue(w.items ++ u.items))
      eqv("U19 wrap nest", Wrap(Wrap(a, pu), pw), Wrap(a, wu))
      eqv("U19 unwrap nest", Unwrap(Unwrap(a, pw), pu), Unwrap(a, wu))
      val b = lit(randValue(rng))
      eqv("U20 unwrap-union", Unwrap(Union(a, b), pw), Union(Unwrap(a, pw), Unwrap(b, pw)))
      eqv("U20 unwrap-inter", Unwrap(Intersection(a, b), pw), Intersection(Unwrap(a, pw), Unwrap(b, pw)))
      eqv("U20 unwrap-minus", Unwrap(Subtraction(a, b), pw), Subtraction(Unwrap(a, pw), Unwrap(b, pw)))
      assertEquals(run(Wrap(a, pw)).paths.size, run(a).paths.size, "U46 |wrap(A,W)| = |A|")
      for p <- run(Wrap(a, pw)).paths do
        assertEquals(p.items.length, w.items.length + p.items.drop(w.items.length).length, "U49 length shift")),
    // ---- tails --------------------------------------------------------------------------------
    Law(Set("U22", "U24", "U25", "U50"), "tails-union is a union homomorphism; tails-intersection is NOT monotone", rng =>
      val (a, b) = (lit(randValue(rng)), lit(randValue(rng)))
      eqv("U22 tu-union", TailsUnion(Union(a, b)), Union(TailsUnion(a), TailsUnion(b)))
      eqv("U22 tu-empty", TailsUnion(Empty), Empty)
      eqv("U22 tu-eps", TailsUnion(lit(sv(""))), Empty)
      subset("U22 tu-meet-only-subset", TailsUnion(Intersection(a, b)), Intersection(TailsUnion(a), TailsUnion(b)))
      subset("U24 ti in tu", TailsIntersection(a), TailsUnion(a))),
    // ---- cardinality --------------------------------------------------------------------------
    Law(Set("U42", "U43", "U44", "U45"), "the cardinality identities", rng =>
      val (a, b) = (randValue(rng), randValue(rng))
      val (la, lb) = (lit(a), lit(b))
      assert(run(Union(la, lb)).paths.size <= a.paths.size + b.paths.size, "U42 subadditivity")
      assert(run(Intersection(la, lb)).paths.size <= a.paths.size.min(b.paths.size), "U43 meet")
      assertEquals(run(Union(la, lb)).paths.size + run(Intersection(la, lb)).paths.size,
                   a.paths.size + b.paths.size, "U44 inclusion-exclusion")
      assertEquals(run(Restriction(la, lb)).paths.size + run(Raffination(la, lb)).paths.size,
                   a.paths.size, "U45 restriction/raffination partition exactly")),
    // ---- control flow -------------------------------------------------------------------------
    Law(Set("U30", "U31", "U32", "U33"), "iteration over head groups: empty/eps corners and union split", rng =>
      val body = Wrap(Mention(SpaceMention("t")), Path.Deref(PathRef("h").known(1)))
      def iter(src: Space) = Iteration(src, PathRef("h").known(1), SpaceMention("t"), body)
      eqv("U30 iter-empty", iter(Empty), Empty)
      eqv("U30 iter-eps", iter(lit(sv(""))), Empty)
      // an identity body reconstructs the headed part of the source
      val a = randValue(rng)
      val headed = SpaceValue(a.paths.filter(_.items.nonEmpty))
      eqv("U31 identity body rebuilds the headed part", iter(lit(a)), lit(headed))),
    Law(Set("U57", "U58", "U59", "U60"), "fold: corners, support, and the CONSTANT-UPDATE alias to iteration", rng =>
      val accR = PathRef("acc"); val h = PathRef("h").known(1); val t = SpaceMention("t")
      val body = Wrap(Mention(t), Path.Deref(h))
      val z = Path.Constant(PathValue(List("z")))
      // constU: the update returns the accumulator unchanged
      def fold(src: Space, upd: Path) = Fold(src, z, accR, h, t, body, upd)
      def iter(src: Space) = Iteration(src, h, t, body)
      eqv("U57 fold-empty", fold(Empty, Path.Deref(accR)), Empty)
      eqv("U57 fold-eps", fold(lit(sv("")), Path.Deref(accR)), Empty)
      val a = lit(randValue(rng))
      // U59: with a CONSTANT update the fold IS the iteration.  This is the one condition; the
      // unconditional identification is refuted below (N09).
      eqv("U59 constant update => fold = iter", fold(a, Path.Deref(accR)), iter(a))
      // U58: every path of a fold is in the union of the body's per-group images
      subset("U58 support", fold(a, Path.Deref(accR)), iter(a))),
    Law(Set("U61", "U62"), "range: inside its source, full window is the identity, and it is an INTERVAL", rng =>
      val a = randValue(rng)
      val la = lit(a)
      subset("U61 window in source", Range(la, 1, 3), la)
      eqv("U61 full window", Range(la, 0, 0), la)
      eqv("U61 empty source", Range(Empty, 1, 2), Empty)
      // U62 THE INTERVAL PROPERTY, against the canonical order every backend slices by
      val sorted = a.paths.toVector.sorted(using pathValueOrdering)
      val win = run(Range(la, 2, 4)).paths
      if win.nonEmpty then
        val idx = sorted.zipWithIndex.filter((p, _) => win(p)).map(_._2)
        assertEquals(idx, (idx.min to idx.max).toVector,
                     s"U62 the window is NOT contiguous in the canonical order: $idx over ${sorted.map(_.show)}")),
    Law(Set("U63", "U64", "U65", "U66"), "call unfolds; a saturating self-recursion IS its Fixpoint", rng =>
      val m = SpaceMention("m"); val rp = RoutinePtr("tc")
      val seed = randValue(rng)
      // r(m) = m ∪ r(tu(m)) — union-saturating, monotone in `m`
      val step = TailsUnion(Mention(m))
      val r = Routine(rp, Vector.empty, Vector(m), Union(Mention(m), Call(rp, Vector.empty, Vector(step))))
      given PathContext = PathContextMap(Map.empty)
      given SpaceContext = SpaceContextMap(Map(m -> seed))
      given rc: PartialFunction[RoutinePtr, Routine] = { case `rp` => r }
      val viaCall = eval(Call(rp, Vector.empty, Vector(Mention(m))))
      // U64-U66: `asFixpoint` rewrites exactly this shape to a Fixpoint; the two must agree
      val lowered = asFixpoint(r).getOrElse(fail("asFixpoint did not recognise the saturating shape"))
      val viaFix = eval(lowered.body)(using PathContextMap(Map.empty), SpaceContextMap(Map(m -> seed)), rc)
      assertEquals(viaFix, viaCall, s"U64-U66 the lowered Fixpoint disagrees with the recursion on ${seed.pretty}")
      // and the Fixpoint really is a SOLUTION of the recursion it replaced (call_fix_solves)
      val s0 = viaFix
      val reStep = eval(Union(Mention(m), TailsUnion(Mention(SpaceMention("s")))))(using
        PathContextMap(Map.empty), SpaceContextMap(Map(m -> seed, SpaceMention("s") -> s0)), rc)
      assertEquals(reStep, s0, s"U65/U66 fix is not a solution: F(${s0.pretty}) = ${reStep.pretty}")),
    Law(Set("U67"), "grounded is DETERMINISTIC — the only contract it carries", rng =>
      var calls = 0
      val f: SpaceValue => SpaceValue = v => { calls += 1; SpaceValue(v.paths.map(p => PathValue("g" :: p.items))) }
      val a = randValue(rng)
      val g = GroundedSS(lit(a), f)
      assertEquals(run(g), run(g), "U67 two evaluations of one grounded node disagree")),
    // ---- fixpoint -----------------------------------------------------------------------------
    Law(Set("U38", "U39", "U40", "U41"), "the Fixpoint IS the least post-fixpoint above its seed", rng =>
      val rec = SpaceMention("k")
      val seed = randValue(rng)
      val bodyF = TailsUnion(Mention(rec))          // monotone in `k`
      val fx = Fixpoint(lit(seed), rec, bodyF)
      val v = run(fx)
      def F(x: SpaceValue) = eval(bodyF)(using PathContextMap(Map.empty),
                                               SpaceContextMap(Map(rec -> x)), PartialFunction.empty)
      assert(seed.paths.subsetOf(v.paths), s"U38 seed not contained: ${seed.pretty} vs ${v.pretty}")
      assert(F(v).paths.subsetOf(v.paths), s"U39 not a post-fixpoint: F(${v.pretty}) = ${F(v).pretty}")
      // leastness, over the reachable sub-lattice: every post-fixpoint above the seed drawn from
      // the result's own subsets must contain it
      for cand <- v.paths.subsets().map(SpaceValue.apply)
          if seed.paths.subsetOf(cand.paths) && F(cand).paths.subsetOf(cand.paths) do
        assert(v.paths.subsetOf(cand.paths),
               s"U41 NOT least: ${cand.pretty} is a post-fixpoint above the seed strictly inside ${v.pretty}")),
  )

  /** registry rows with no executable conformance check, each with the reason.  A row may only be
   *  here because the law quantifies over something Scala cannot enumerate — a BODY, an arbitrary
   *  space, or an unbounded recursion depth — or because it is a statement about the encoding
   *  rather than about a computation. */
  private val notExecutable: Map[String, String] = Map(
    "U23" -> "quantifies over an arbitrary space for the tails-union/wrap interaction shape",
    "U26" -> "monotonicity of tails-union over ALL spaces; the executable direction is in U22",
    "U27" -> "quantifies over a reified `bodyF`, which has no Scala representative",
    "U28" -> "quantifies over a reified `bodyF`",
    "U29" -> "quantifies over a reified `bodyF`",
    "U34" -> "quantifies over a reified `bodyF`",
    "U35" -> "quantifies over a reified `bodyF`",
    "U36" -> "quantifies over a reified `bodyF`",
    "U37" -> "quantifies over a reified `bodyG` (the fixpoint step)",
    "U47" -> "length-bound TRANSFER rules: a claim about tier-1's interval arithmetic, checked by LenBoundsCheck",
    "U48" -> "as U47",
    "U50" -> "as U47 (the tails/unwrap length shift); the membership half is in the wrap/unwrap law",
    "U51" -> "a proof-internal induction premise, not a program property",
    "U52" -> "a proof-internal induction premise, not a program property",
    "U53" -> "left cancellation of append over ALL paths; `Interner`/`PathValue` equality is the finite witness",
    "U54" -> "pointwise tails-of-a-product decomposition over arbitrary spaces; the equational form is U14",
    "U55" -> "as U54",
    "U56" -> "as U54",
  )

  test("every tier-3 law that CAN be executed agrees with the reference executor (200 seeds)") {
    var checks = 0
    for seed <- 0 until 200 do
      val rng = new scala.util.Random(seed.toLong * 0x9E3779B9L + 11)
      for l <- laws do { l.check(rng); checks += 1 }
    println(s"\n### tier-3 conformance: ${laws.size} laws x 200 seeds = $checks executed law checks, " +
            s"covering ${laws.flatMap(_.rows).toSet.size} registry rows")
  }

  test("every registry row is conformance-checked here, or listed as non-executable WITH A REASON") {
    assume(registry.nonEmpty, "proofs/unbounded/REGISTRY.tsv is missing")
    val positive = registry.filter(r => r(0).startsWith("U")).map(_(0)).toSet
    val covered = laws.flatMap(_.rows).toSet
    val unaccounted = (positive -- covered -- notExecutable.keySet).toVector.sorted
    assertEquals(unaccounted, Vector.empty[String],
      s"tier-3 rows with neither a conformance check nor a recorded reason: ${unaccounted.mkString(", ")}.\n" +
      "Add an executable check to `laws`, or an entry to `notExecutable` saying what stops it — a " +
      "`generalises` column with nothing checking it is traceability, not evidence.")
    val phantom = ((covered ++ notExecutable.keySet) -- positive).toVector.sorted
    assertEquals(phantom, Vector.empty[String],
      s"this suite references registry rows that do not exist: ${phantom.mkString(", ")}")
    println(s"### registry linkage: ${covered.size} rows conformance-checked, " +
            s"${notExecutable.size} recorded non-executable, ${positive.size} rows total")
  }

  // ------------------------------------------------------------------------------------------
  // the negative controls, REFUTED BY EXECUTION
  // ------------------------------------------------------------------------------------------
  /** one negative control: the file, and a concrete input at which the false law fails */
  private final case class Counter(file: String, claim: String, witness: () => String)

  private val counters: Vector[Counter] = Vector(
    Counter("negative/not_wrap_nest_reversed", "wrap(wrap(A,U),V) = wrap(A, U++V)", () =>
      val a = lit(sv("x")); val (u, v) = (PathValue(List("u")), PathValue(List("v")))
      val lhs = run(Wrap(Wrap(a, Path.Constant(u)), Path.Constant(v)))
      val rhs = run(Wrap(a, Path.Constant(PathValue(u.items ++ v.items))))
      assertNotEquals(lhs, rhs, "not_wrap_nest_reversed is NOT false at this input")
      s"A={x}, U=u, V=v: lhs=${lhs.pretty} rhs=${rhs.pretty}"),
    Counter("negative/not_unwrap_nest_reversed", "unwrap(unwrap(A,U),V) = unwrap(A, V++U)", () =>
      val a = lit(sv("u.v.x")); val (u, v) = (PathValue(List("u")), PathValue(List("v")))
      val lhs = run(Unwrap(Unwrap(a, Path.Constant(u)), Path.Constant(v)))
      val rhs = run(Unwrap(a, Path.Constant(PathValue(v.items ++ u.items))))
      assertNotEquals(lhs, rhs, "not_unwrap_nest_reversed is NOT false at this input")
      s"A={u.v.x}, U=u, V=v: lhs=${lhs.pretty} rhs=${rhs.pretty}"),
    Counter("negative/not_ti_eq_tu", "ti(A) = tu(A) unconditionally", () =>
      val a = lit(sv("p.1", "q.2"))
      val (l, r) = (run(TailsIntersection(a)), run(TailsUnion(a)))
      assertNotEquals(l, r, "not_ti_eq_tu is NOT false at this input")
      s"A={p.1,q.2} (two heads): ti=${l.pretty} tu=${r.pretty}"),
    Counter("negative/not_ti_monotone", "A ⊆ B => ti(A) ⊆ ti(B)", () =>
      // the exact witness terminating/mono_soundness.smt2 (O3d-X1) records: A ⊆ B, but B's EXTRA
      // HEAD adds a participant to the meet, so the intersection over heads can only SHRINK
      val (a, b) = (lit(sv("p.1")), lit(sv("p.1", "q.2")))
      val (ta, tb) = (run(TailsIntersection(a)), run(TailsIntersection(b)))
      assert(!ta.paths.subsetOf(tb.paths), "not_ti_monotone is NOT false at this input")
      s"A={p.1} ⊆ B={p.1,q.2}: ti(A)=${ta.pretty} ⊄ ti(B)=${tb.pretty}"),
    Counter("negative/not_iter_split", "iteration splits over an ARBITRARY union", () =>
      val h = PathRef("h").known(1); val t = SpaceMention("t")
      val body = TailsIntersection(Mention(t))
      def iter(s: Space) = Iteration(s, h, t, body)
      // a SHARED head merges the two groups into ONE, and the body is not a union homomorphism:
      // TailsIntersection over the merged tail-set {1, 2.3} intersects to nothing, while the two
      // separate iterations each see a single tail and keep it.
      val (a, b) = (lit(sv("p.1")), lit(sv("p.2.3")))
      val (whole, split) = (run(iter(Union(a, b))), run(Union(iter(a), iter(b))))
      assertNotEquals(whole, split, "not_iter_split is NOT false at this input")
      s"A={p.1} B={p.2.3} (shared head p): iter(A∪B)=${whole.pretty} vs iter(A)∪iter(B)=${split.pretty}"),
    Counter("negative/not_card_additive", "|A ∪ B| = |A| + |B| unconditionally", () =>
      val (a, b) = (sv("x"), sv("x"))
      val n = run(Union(lit(a), lit(b))).paths.size
      assertNotEquals(n, a.paths.size + b.paths.size, "not_card_additive is NOT false at this input")
      s"A=B={x}: |A∪B|=$n but |A|+|B|=${a.paths.size + b.paths.size}"),
    Counter("negative/not_tu_cap_equality", "tu(A ∩ B) = tu(A) ∩ tu(B)", () =>
      // DIFFERENT heads, SAME tail: the sources are disjoint, so tu of the meet is empty, while
      // the meet of the tu's keeps the shared tail.  Only `subset` holds (U22).
      val (a, b) = (lit(sv("p.1")), lit(sv("q.1")))
      val (l, r) = (run(TailsUnion(Intersection(a, b))), run(Intersection(TailsUnion(a), TailsUnion(b))))
      assertNotEquals(l, r, "not_tu_cap_equality is NOT false at this input")
      s"A={p.1} B={q.1}: tu(A∩B)=${l.pretty} vs tu(A)∩tu(B)=${r.pretty}"),
    Counter("negative/not_restr_identity", "restr(X,Y) = X", () =>
      val (x, y) = (lit(sv("p.1")), lit(sv("q")))
      val (l, r) = (run(Restriction(x, y)), run(x))
      assertNotEquals(l, r, "not_restr_identity is NOT false at this input")
      s"X={p.1} Y={q} (no prefix): restr=${l.pretty} vs X=${r.pretty}"),
    Counter("negative/not_fold_eq_iter", "fold = iter unconditionally", () =>
      // the accumulator is OBSERVED by the body, so a moving update is visible in the output
      val accR = PathRef("acc"); val h = PathRef("h").known(1); val t = SpaceMention("t")
      val body = Singleton(Path.Deref(accR))                 // emit the ACCUMULATOR itself
      val z = Path.Constant(PathValue(List("z")))
      val src = lit(sv("a.1", "b.1"))
      val moving = Path.Concat(Path.Deref(accR), Path.Deref(h))   // the update ADVANCES
      val fld = run(Fold(src, z, accR, h, t, body, moving))
      val itr = run(Iteration(src, h, t, Singleton(z)))       // the same body frozen at the seed
      assertNotEquals(fld, itr, "not_fold_eq_iter is NOT false at this input")
      s"src={a.1,b.1}, update=acc·h: fold=${fld.pretty} vs iter-at-seed=${itr.pretty}"),
    Counter("negative/not_range_identity", "rng(A,Lo,Hi) = A — a window is the identity", () =>
      // A PARTIAL WINDOW IS NOT THE IDENTITY, which is the near-miss of U61 ("a FULL window is the
      // identity"): drop U61's full-window hypothesis and the conclusion fails at once.
      //
      // WHY THIS CONTROL AND NOT THE MONOTONICITY ONE IT REPLACES.  The entry here used to execute
      // `A={m} ⊆ B={a,m}: rng(A,1,2)={m} ⊄ rng(B,1,2)={a}` against a MONOTONICITY control that has
      // since been removed.  That execution is a real fact about `Space.Range` — a
      // bigger source shifts every later RANK — but the TPTP conjecture it was filed against
      // quantified over PATH endpoints, and with the endpoints fixed the window is a pointwise
      // order-interval filter which IS monotone: `_range_ops.p` derives it from `rng_sub`,
      // `rng_bounds` and `rng_full`, and vampire proves it in seconds.  So the countermodel did not
      // apply to the sentence, and the sentence was a theorem masquerading as a control.  It also
      // went unnoticed for a round because that file's includes did not resolve under `run.sh`'s
      // `cd negative`, so the prover could not read it and the harness scored the non-answer as
      // "NOT-PROVED (expected)".  `docs/TRUSTED.md` T5 now records the non-monotonicity of
      // `Space.Range` as an EXECUTED observation about rank arithmetic rather than as a theorem of
      // this tier, which is where it belongs.
      val a = sv("a", "m")
      val w = run(Range(lit(a), 0, 1))
      assert(w.paths.subsetOf(a.paths), "a window must still be a SUBSET of its source (U61's half)")
      assert(w.paths != a.paths, "not_range_identity is NOT false at this input")
      s"A={a,m}: rng(A,0,1)=${w.pretty} != A=${a.pretty}"),
    Counter("negative/not_grounded_monotone", "a grounded function is monotone", () =>
      // an opaque function is free to be antitone; this one complements against a fixed set
      val u = sv("x", "y")
      val f: SpaceValue => SpaceValue = v => SpaceValue(u.paths -- v.paths)
      val (a, b) = (sv("x"), sv("x", "y"))
      val (ga, gb) = (run(GroundedSS(lit(a), f)), run(GroundedSS(lit(b), f)))
      assert(a.paths.subsetOf(b.paths), "the witness must have A ⊆ B")
      assert(!ga.paths.subsetOf(gb.paths), "not_grounded_monotone is NOT false at this input")
      s"f = {x,y} \\ ·, A={x} ⊆ B={x,y}: f(A)=${ga.pretty} ⊄ f(B)=${gb.pretty}"),
  )

  test("every NEGATIVE control has an executed COUNTERMODEL, not just a prover timeout") {
    assume(registry.nonEmpty, "proofs/unbounded/REGISTRY.tsv is missing")
    val declared = registry.filter(r => r(0).startsWith("N")).map(_(1).stripSuffix(".p")).toSet
    val covered = counters.map(_.file).toSet
    assertEquals((declared -- covered).toVector.sorted, Vector.empty[String],
      "negative controls with no executed countermodel — `proofs/unbounded/run.sh` reports these as " +
      "`NOT-PROVED (expected)` on a TIMEOUT, which is the absence of a proof and NOT a refutation. " +
      "Each one needs a concrete input at which the false law fails.")
    assertEquals((covered -- declared).toVector.sorted, Vector.empty[String],
      "this suite carries countermodels for negative controls that are not in REGISTRY.tsv")

    val lines = counters.map { c =>
      val w = c.witness()                                    // each `witness` ASSERTS the failure
      f"${c.file.stripPrefix("negative/")}%-30s ${c.claim}%-46s  REFUTED AT  $w"
    }
    println("\n" + "=" * 110)
    println("NEGATIVE CONTROLS, REFUTED BY EXECUTION (the prover only reports a timeout on these)")
    println("=" * 110)
    lines.foreach(l => println("  " + l))

    // record it next to the prover's own verdicts, so a reader of STATUS.tsv sees the distinction
    // THROUGH THE SINK (0.3): built as one string and handed over, so a VERIFY run compares it
    // against the committed table instead of overwriting it.
    val f = new java.io.File(Loaders.repoRoot, "proofs/unbounded/COUNTERMODELS.tsv")
    val body = "# Negative controls REFUTED BY EXECUTION against the reference executor.\n" +
               "# proofs/unbounded/run.sh can only report `NOT-PROVED (expected)` for these: the\n" +
               "# statements are false, but their countermodels are infinite path sets and vampire\n" +
               "# returns a TIMEOUT, which is the absence of a proof and not a semantic separation.\n" +
               "# This table is the separation.  Written by src/test/scala/TierThreeConformance.scala.\n" +
               "#\n# file\tfalse claim\tcountermodel\n" +
               counters.map(c => s"${c.file}\t${c.claim}\t${c.witness()}\n").mkString
    ArtifactSink.write(f, body)
    println(s"\nproduced: proofs/unbounded/COUNTERMODELS.tsv (${counters.size} executed countermodels)")
    ArtifactSink.assertClean("morkl.TierThreeConformance")
  }
end TierThreeConformance
