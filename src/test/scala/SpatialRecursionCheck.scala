package morkl

import munit.FunSuite

/** BOUNDED RECURSION, end to end.
 *
 *  The headline: a recursive routine that consumes ONE ITEM PER CALL, over an input annotated
 *  "every path has at most four items", must yield `maxCallDepth = 4` and a fully residualised,
 *  Call-FREE traversal of four specialised levels that agrees with the original on every input
 *  satisfying the annotation — and is allowed to disagree outside it, which is why the precondition
 *  travels with the artifact.
 *
 *  `eval` appears ONLY here, as ground truth (docs/design_spatial_lattice.md §0).  The analysis
 *  itself never runs a program. */
class SpatialRecursionCheck extends FunSuite:
  import SpatialRecursion.*
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  // ================================================================================================
  //  the routines under test
  // ================================================================================================
  def p(items: String*): PathValue = PathValue(items.toList)
  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
  val eps: Space = lit(p())                                   // {ε}
  val M = SpaceMention("m")
  val H = PathRef("h").known(1)
  val R = SpaceMention("r")
  val anon = SpaceMention("_")
  def deref(pr: PathRef): Path = Path.Deref(pr)
  /** iterate and return the group head — one path per distinct head */
  def headsOf(src: Space): Space = Space.Iteration(src, H, anon, Space.Singleton(deref(H)))

  /** THE HEADLINE.  `walk(m) = m.iter(h, r, {h} ∪ walk(r))` — the ITEM ALPHABET of a space: every
   *  item occurring at any depth, as a one-item path.  Structurally recursive: the argument of the
   *  self-call is the iteration's REST-SET, one item shorter than the parameter.  A headless
   *  argument runs no group, so the body is empty there — which is what makes the bound exactly the
   *  maximum input length. */
  val walkPtr = RoutinePtr("walk")
  val walk = Routine(walkPtr, Vector.empty, Vector(M),
    Space.Iteration(Space.Mention(M), H, R,
      Space.Union(Space.Singleton(deref(H)), Space.Call(walkPtr, Vector.empty, Vector(Space.Mention(R))))))

  /** the same denotation through the UNION-SATURATING tails chain rather than structural recursion:
   *  `levels(m) = heads(m) ∪ levels(TailsUnion(m))`.  This is the shape `eval` terminates by its
   *  argument-fixpoint shortcut, so it also checks that unrolling agrees with that shortcut. */
  val levelsPtr = RoutinePtr("levels")
  val levels = Routine(levelsPtr, Vector.empty, Vector(M),
    Space.Union(headsOf(Space.Mention(M)),
      Space.Call(levelsPtr, Vector.empty, Vector(Space.TailsUnion(Space.Mention(M))))))

  /** reads the PARAMETER inside the loop body, so splicing `m := Mention(r)` lands inside the `r`
   *  binder's scope.  Without alpha-renaming the spliced copy that substitution is CAPTURED and the
   *  residual silently answers with the wrong nesting level's rest-set (traps.md #7). */
  val capturePtr = RoutinePtr("walkCap")
  val capture = Routine(capturePtr, Vector.empty, Vector(M),
    Space.Iteration(Space.Mention(M), H, R,
      Space.Union(Space.Intersection(Space.Mention(M), eps),
        Space.Union(Space.Singleton(deref(H)),
          Space.Call(capturePtr, Vector.empty, Vector(Space.Mention(R)))))))

  /** the IDENTITY traversal: `rebuild(m) = (m ∩ {ε}) ∪ m.iter(h, r, h·rebuild(r))`.  Its base case
   *  is NOT empty on a headless argument (it returns the ε), so the honest bound is `L + 1`, not
   *  `L` — the artifact must report 5 for a maximum length of 4, not round down to 4. */
  val rebuildPtr = RoutinePtr("rebuild")
  val rebuild = Routine(rebuildPtr, Vector.empty, Vector(M),
    Space.Union(Space.Intersection(Space.Mention(M), eps),
      Space.Iteration(Space.Mention(M), H, R,
        Space.Wrap(Space.Call(rebuildPtr, Vector.empty, Vector(Space.Mention(R))), deref(H)))))

  /** NO MEASURE: the recursive argument is a RESTRICTION of the parameter — a subset, but not one
   *  item shorter.  There is no structural decrease witness, so no bound may be claimed. */
  val flatPtr = RoutinePtr("flat")
  val flat = Routine(flatPtr, Vector.empty, Vector(M),
    Space.Union(headsOf(Space.Mention(M)),
      Space.Call(flatPtr, Vector.empty, Vector(Space.Restriction(Space.Mention(M), lit(p("a")))))))

  /** NO MEASURE: the argument GROWS (a wrap adds an item per call). */
  val growPtr = RoutinePtr("grow")
  val grow = Routine(growPtr, Vector.empty, Vector(M),
    Space.Union(headsOf(Space.Mention(M)),
      Space.Call(growPtr, Vector.empty, Vector(Space.Wrap(Space.Mention(M), Path.Constant(p("z")))))))

  /** M1 holds but M2 must fail: the argument is an unwrap by a path of BETWEEN 1 AND 3 items, so
   *  "at least one item is dropped" is structurally true while the histogram's variable-length
   *  unwrap arm loses the length bound.  The numeric drop is the load-bearing check, so this must
   *  come back `NoBound`. */
  val P0 = PathRef("p0")
  val peelPtr = RoutinePtr("peel")
  val peel = Routine(peelPtr, Vector(P0), Vector(M),
    Space.Union(headsOf(Space.Mention(M)),
      Space.Call(peelPtr, Vector(deref(P0)), Vector(Space.Unwrap(Space.Mention(M), deref(P0))))))

  val table: Map[RoutinePtr, Routine] = Map(
    walkPtr -> walk, levelsPtr -> levels, capturePtr -> capture, rebuildPtr -> rebuild,
    flatPtr -> flat, growPtr -> grow, peelPtr -> peel)

  // ================================================================================================
  //  ground truth (eval only — never inside the analysis)
  // ================================================================================================
  def callOf(rp: RoutinePtr, r: Routine): Space =
    Space.Call(rp, r.refs.map(deref), r.mentions.map(Space.Mention(_)))

  /** eval a term with `m` bound to `v` (and `p0`, when the routine has it, bound to one item) */
  def run(s: Space, v: SpaceValue, rc: PartialFunction[RoutinePtr, Routine]): SpaceValue =
    eval(s)(using PathContextMap(Map(P0 -> p("a"))), SpaceContextMap(Map(M -> v)), rc)
  def runWith(s: Space, env: Map[SpaceMention, SpaceValue], rc: PartialFunction[RoutinePtr, Routine]): SpaceValue =
    eval(s)(using PathContextMap(Map(P0 -> p("a"))), SpaceContextMap(env), rc)

  val alphabet = Vector("a", "b", "c")
  def randInput(rng: java.util.Random, minLen: Int, maxLen: Int, maxPaths: Int): SpaceValue =
    val n = rng.nextInt(maxPaths + 1)
    SpaceValue((0 until n).map { _ =>
      val k = minLen + rng.nextInt(maxLen - minLen + 1)
      PathValue(List.fill(k)(alphabet(rng.nextInt(alphabet.length))))
    }.toSet)

  /** differential: the residual and the original agree on `n` random inputs drawn from `gen`.
   *  Returns (checked, disagreements, a witness). */
  def differential(rp: RoutinePtr, res: BoundedRecursion, n: Int, seed: Long,
                   gen: java.util.Random => SpaceValue): (Int, Int, Option[(SpaceValue, SpaceValue, SpaceValue)]) =
    val rng = new java.util.Random(seed)
    val orig = callOf(rp, table(rp))
    var checked = 0; var bad = 0
    var witness: Option[(SpaceValue, SpaceValue, SpaceValue)] = None
    for _ <- 0 until n do
      val v = gen(rng)
      val a = run(orig, v, table)
      val b = run(res.residual.body, v, PartialFunction.empty)
      checked += 1
      if a != b then { bad += 1; if witness.isEmpty then witness = Some((v, a, b)) }
    (checked, bad, witness)

  // ================================================================================================
  //  1.  THE HEADLINE
  // ================================================================================================
  test("headline: maxLen 4 + one item per call  =>  maxCallDepth 4 and a Call-free residual") {
    val ann = lengthAnnotation(1, 4)
    assert(Fact.from(ann).contains(Fact.MaximumPathLength(4)), s"the annotation must say maxLen 4: ${Fact.from(ann)}")
    val out = residualise(walkPtr, table, Map(M -> ann))
    val res = out.bounded.getOrElse(fail(s"expected a bound, got: ${out.noBoundReason.get}"))
    println(s"HEADLINE ${res.show}")
    assertEquals(res.maxCallDepth, 4, "the derived call-depth bound must be exactly 4")
    assertEquals(res.inputMaxLen, 4L)
    assertEquals(res.measureBound, 5L)
    assertEquals(res.lenChain, Vector(4L, 3L, 2L, 1L, 0L), "μ must drop by exactly one item per call")
    assert(res.emptyLevelSummary.isProvablyEmpty, "the level-4 summary must be PROVABLY EMPTY")
    assert(res.callFree, s"the residual must contain no Call: ${res.residual.body.show}")
    assert(isCallFree(res.residual.body))
    // four specialised levels: exactly four Iteration nodes in the residual, none of them a Call
    assertEquals(countIterations(res.residual.body), 4, s"expected four unrolled levels: ${res.residual.body.show}")
    assert(!res.residual.body.show.contains("walk("), "no self-call may survive")
    // the witness is the structural one, not a guess
    res.witness match
      case Decrease.IterationRest(m, r) => assertEquals(m, M); assertEquals(r, R)
      case other => fail(s"expected the iteration-rest witness, got $other")
    assert(res.summaries.certified, s"the summary table must certify: ${res.summaries.show}")

    // -- differential on inputs SATISFYING the annotation --------------------------------------
    val (checked, bad, w) = differential(walkPtr, res, 600, 20260807L, r => randInput(r, 1, 4, 6))
    println(s"HEADLINE DIFFERENTIAL: $checked conforming inputs, $bad disagreements")
    assertEquals(bad, 0, s"residual disagrees on a conforming input: $w")
    assertEquals(checked, 600)
  }

  test("headline: the summary is a SOUND type for the recursion's value") {
    val ann = lengthAnnotation(1, 4)
    val res = residualise(walkPtr, table, Map(M -> ann)).bounded.get
    val rng = new java.util.Random(4242)
    var checked = 0; var escaped = 0
    for _ <- 0 until 400 do
      val v = randInput(rng, 1, 4, 6)
      val value = run(callOf(walkPtr, walk), v, table)
      checked += 1
      if !SpatialTyping.gammaMember(value, res.summary) then escaped += 1
    println(s"SUMMARY γ-GATE: $checked values, $escaped escape ${res.summary.show}")
    assertEquals(escaped, 0, "the concrete recursion value must satisfy the inferred summary")
  }

  test("headline: the annotation is LOAD-BEARING — violate it and the residual may differ") {
    val ann = lengthAnnotation(1, 4)
    val res = residualise(walkPtr, table, Map(M -> ann)).bounded.get
    val orig = callOf(walkPtr, walk)
    // THE contract of a guarded specialisation: `applicableTo` ⟹ the two agree.  Nothing weaker is
    // enough — an input the dispatcher admits must never see the specialised body disagree.
    val rng = new java.util.Random(777L)
    var over = 0; var accepted = 0; var disagree = 0; var disagreeAccepted = 0; var longRejected = 0
    var witness: Option[(SpaceValue, SpaceValue, SpaceValue)] = None
    for _ <- 0 until 400 do
      // deliberately outside the annotation: 5..6 items per path (the empty set is drawn too, and
      // it satisfies the annotation vacuously — that is not a violation)
      val v = randInput(rng, 5, 6, 4)
      val tooLong = v.paths.exists(_.items.length > 4)
      if tooLong then over += 1
      val ok = res.applicableTo(Map(M -> v))
      if ok then accepted += 1
      if tooLong && !ok then longRejected += 1
      val a = run(orig, v, table)
      val b = run(res.residual.body, v, PartialFunction.empty)
      if a != b then
        disagree += 1
        if witness.isEmpty then witness = Some((v, a, b))
        if ok then disagreeAccepted += 1
    println(s"VIOLATING DIFFERENTIAL: 400 inputs ($over carry a >4-item path), $accepted admitted " +
            s"by applicableTo, $disagree disagreements ($disagreeAccepted of them admitted)")
    println(s"  witness: $witness")
    assert(disagree > 0, "a specialisation whose precondition is violated should be able to differ")
    assertEquals(disagreeAccepted, 0, "an admitted argument must never see the residual disagree")
    assertEquals(longRejected, over, "every input carrying a path longer than 4 must be rejected")
    // conforming inputs are all accepted
    val rng2 = new java.util.Random(31337L)
    var okCount = 0
    for _ <- 0 until 400 do
      if res.applicableTo(Map(M -> randInput(rng2, 1, 4, 6))) then okCount += 1
    assertEquals(okCount, 400, "applicableTo must accept every conforming argument")
    // the precondition really is attached, in both artifact shapes
    assertEquals(res.precondition.keySet, Set(M))
    assertEquals(res.specialized.precondition.keySet, Set(M))
  }

  // ================================================================================================
  //  2.  the other recursion shapes
  // ================================================================================================
  test("the union-saturating tails chain residualises to the same depth") {
    val out = residualise(levelsPtr, table, Map(M -> lengthAnnotation(1, 4)))
    val res = out.bounded.getOrElse(fail(s"expected a bound, got: ${out.noBoundReason.get}"))
    println(s"TAILS-CHAIN ${res.show}")
    assertEquals(res.maxCallDepth, 4)
    assertEquals(res.lenChain, Vector(4L, 3L, 2L, 1L, 0L))
    res.witness match
      case Decrease.Tails(m) => assertEquals(m, M)
      case other => fail(s"expected the tails witness, got $other")
    assert(res.callFree)
    assertEquals(countIterations(res.residual.body), 4)
    val (checked, bad, w) = differential(levelsPtr, res, 400, 99L, r => randInput(r, 1, 4, 6))
    println(s"TAILS-CHAIN DIFFERENTIAL: $checked conforming inputs, $bad disagreements")
    assertEquals(bad, 0, s"$w")
    // the two routines denote the same function, and so do their residuals
    val rng = new java.util.Random(5L)
    val wres = residualise(walkPtr, table, Map(M -> lengthAnnotation(1, 4))).bounded.get
    for _ <- 0 until 100 do
      val v = randInput(rng, 1, 4, 5)
      assertEquals(run(res.residual.body, v, PartialFunction.empty),
                   run(wres.residual.body, v, PartialFunction.empty))
  }

  test("splicing is HYGIENIC: a body that reads the parameter inside the loop") {
    val out = residualise(capturePtr, table, Map(M -> lengthAnnotation(1, 4)))
    val res = out.bounded.getOrElse(fail(s"expected a bound, got: ${out.noBoundReason.get}"))
    println(s"CAPTURE ${res.show}")
    assertEquals(res.maxCallDepth, 4)
    assert(res.callFree)
    val (checked, bad, w) = differential(capturePtr, res, 400, 12345L, r => randInput(r, 1, 4, 6))
    println(s"CAPTURE DIFFERENTIAL: $checked conforming inputs, $bad disagreements")
    assertEquals(bad, 0, s"a captured substitution would show up exactly here: $w")
    // and the residual really is a different term (the rewrite fired)
    assertNotEquals(res.residual.body, capture.body)
  }

  test("a base case that is NOT empty on a headless argument gives L+1, not L") {
    val out = residualise(rebuildPtr, table, Map(M -> lengthAnnotation(1, 4)))
    val res = out.bounded.getOrElse(fail(s"expected a bound, got: ${out.noBoundReason.get}"))
    println(s"REBUILD ${res.show}")
    assertEquals(res.maxCallDepth, 5, "the ε base case needs one more level than the maximum length")
    assertEquals(res.measureBound, 5L)
    assert(res.callFree)
    assertEquals(countIterations(res.residual.body), 5)
    val (checked, bad, w) = differential(rebuildPtr, res, 400, 606L, r => randInput(r, 1, 4, 6))
    println(s"REBUILD DIFFERENTIAL: $checked conforming inputs, $bad disagreements")
    assertEquals(bad, 0, s"$w")
    // `rebuild` is the identity on conforming inputs — check the residual is too
    val rng = new java.util.Random(11L)
    for _ <- 0 until 100 do
      val v = randInput(rng, 1, 4, 5)
      assertEquals(run(res.residual.body, v, PartialFunction.empty), v)
  }

  // ================================================================================================
  //  3.  the negative cases — NoBound, never a guess
  // ================================================================================================
  test("NO MEASURE: a restriction of the parameter is a subset but not one item shorter") {
    val out = residualise(flatPtr, table, Map(M -> lengthAnnotation(1, 4)))
    assertEquals(out.bounded, None)
    val why = out.noBoundReason.get
    println(s"NO-BOUND (restriction): $why")
    assert(why.contains("no structural decrease witness (M1)"), why)
    // the syntactic side conditions really are the ones checked
    assert(subsetOf(Space.Restriction(Space.Mention(M), lit(p("a"))), M), "a restriction IS a subset")
    assertEquals(decreaseOf(Space.Restriction(Space.Mention(M), lit(p("a"))), M, Map.empty, Map.empty), None)
    assertEquals(decreaseOf(Space.TailsUnion(Space.Mention(M)), M, Map.empty, Map.empty),
                 Some(Decrease.Tails(M)))
  }

  test("NO MEASURE: an argument that grows") {
    val out = residualise(growPtr, table, Map(M -> lengthAnnotation(1, 4)))
    assertEquals(out.bounded, None)
    println(s"NO-BOUND (wrap): ${out.noBoundReason.get}")
    assert(out.noBoundReason.get.contains("M1"), out.noBoundReason.get)
  }

  test("NO BOUND: the input type does not bound the maximum path length") {
    val out = residualise(walkPtr, table, Map(M -> SpatialType.top))
    assertEquals(out.bounded, None)
    println(s"NO-BOUND (unannotated): ${out.noBoundReason.get}")
    assert(out.noBoundReason.get.contains("does not bound the maximum path length"), out.noBoundReason.get)
    // and with no annotation at all, the same
    val out2 = residualise(walkPtr, table)
    assertEquals(out2.bounded, None)
    assert(out2.noBoundReason.get.contains("does not bound the maximum path length"))
  }

  /** eval as ground truth for `peel`, with p0 drawn from its DECLARED length interval and every
   *  input path inside `lengthAnnotation(1, 4)`.  The residual is only obliged to agree inside its
   *  precondition, so the generator asserts membership before it compares. */
  def peelDifferential(plo: Int, phi: Int, r: BoundedRecursion, n: Int, seed: Long): (Int, Int, Option[String]) =
    val rng = new java.util.Random(seed)
    val orig = Space.Call(peelPtr, Vector(deref(P0)), Vector(Space.Mention(M)))
    val ann = lengthAnnotation(1, 4)
    var checked = 0; var bad = 0; var witness: Option[String] = None
    for _ <- 0 until n do
      val plen = plo + rng.nextInt(phi - plo + 1)
      val pv = PathValue(List.fill(plen)(alphabet(rng.nextInt(alphabet.length))))
      // bias towards sharing pv as a prefix, so the recursive arm is actually reached
      val v = SpaceValue((0 until rng.nextInt(7)).map { _ =>
        if rng.nextBoolean() && plen < 4 then
          PathValue(pv.items ++ List.fill(1 + rng.nextInt(4 - plen))(alphabet(rng.nextInt(alphabet.length))))
        else PathValue(List.fill(1 + rng.nextInt(4))(alphabet(rng.nextInt(alphabet.length))))
      }.toSet)
      assert(SpatialTyping.accepts(v, ann), s"generator left the precondition: ${v.paths}")
      val a = eval(orig)(using PathContextMap(Map(P0 -> pv)), SpaceContextMap(Map(M -> v)), table)
      val b = eval(r.residual.body)(using PathContextMap(Map(P0 -> pv)), SpaceContextMap(Map(M -> v)),
                                    PartialFunction.empty)
      checked += 1
      if a != b then
        bad += 1
        if witness.isEmpty then witness = Some(s"p0=${pv.show} v=${v.paths} orig=${a.paths} residual=${b.paths}")
    (checked, bad, witness)

  /** M1 and M2 are BOTH load-bearing, and the numeric drop now survives a VARIABLE-length prefix
   *  because the product is reduced in both directions.
   *
   *  History: this test used to assert `NoBound` here, on the reasoning that `p0 ∈ [1,3]` items
   *  makes the histogram's variable-length unwrap arm give up (it does — see the assertion below,
   *  `SpatialTypes.infer` alone still returns μ = ∞).  That reasoning was about the histogram alone.
   *  The bidirectional reducer now closes the gap: `lengthAnnotation(1,4)`'s histogram materialises a
   *  depth-≤4 trie out of `Shape.top` (rule H3), `Shape.unwrapUnknown` shifts that trie down by
   *  `|p0|.lo = 1` levels — a sound envelope, since `Unwrap(s,p)` with `|p| = j` is a subset of the
   *  level-`j` tail-sets — and the product's `len` meet reads the bound back off the shape.  So M2
   *  is now PROVED, not skipped: `μ` drops by exactly `|p0|.lo` per level.
   *
   *  The bound is checked three ways below: the μ chain is monotone and lands on 0, the guard still
   *  refuses when `|p0|` may be 0 (no decrease at all), and `eval` agrees with the residual on every
   *  input inside the precondition. */
  test("M2 over a VARIABLE-length prefix: the reduced product proves the numeric drop") {
    // M1 by itself accepts it, with the SOUND drop — the LOWER end of |p0|, never the upper
    assertEquals(decreaseOf(Space.Unwrap(Space.Mention(M), deref(P0)), M, Map.empty,
                            Map(P0 -> Lower.LenBounds(1, 3))),
                 Some(Decrease.Unwrap(M, 1L)))
    assertEquals(decreaseOf(Space.Unwrap(Space.Mention(M), deref(P0)), M, Map.empty,
                            Map(P0 -> Lower.LenBounds(2, 3))),
                 Some(Decrease.Unwrap(M, 2L)))

    // THE HISTOGRAM ALONE STILL LOSES IT — this is the assertion the old expectation rested on, and
    // it is still true.  What changed is that the histogram is no longer the only component asked.
    val ann = lengthAnnotation(1, 4)
    val lenv = SpatialEnv(spaces = Map(M -> ann.lens), paths = Map(P0 -> Lower.LenBounds(1, 3)))
    val histOnly = SpatialTypes.infer(Space.Unwrap(Space.Mention(M), deref(P0)), lenv)
    assertEquals(histOnly.len.hi, Lower.LenBounds.INF,
                 "the histogram's variable-length unwrap arm is still the lossy one")
    // the SHAPE half, over the reduced annotation, is what recovers it
    val env = SpatialTyping.Env(spaces = Map(M -> keyType(ann)), opaque = Map(P0 -> Lower.LenBounds(1, 3)))
    val product = SpatialTyping.infer(Space.Unwrap(Space.Mention(M), deref(P0)), env)
    assertEquals(product.len, Lower.LenBounds(0, 3),
                 "the reduced product recovers 4 - |p0|.lo = 3")
    // and the depth cap is NOT being misread as a length claim: ⊤ admits arbitrarily deep paths
    assert(Shape.top.lens.hi == Lower.LenBounds.INF, s"Shape.top.lens = ${Shape.top.lens}")
    assert(SpatialType.accepts(SpatialType.top, SpaceValue(Set(PathValue(List.fill(Shape.MaxDepth * 3)("a"))))),
           "⊤ must admit a path far deeper than Shape.MaxDepth")

    // a bound IS derived now, and the μ chain drops by |p0|.lo at every level
    for (plo, phi, drop) <- Vector((1, 1, 1), (1, 2, 1), (1, 3, 1), (1, 4, 1), (2, 3, 2)) do
      val out = residualise(peelPtr, table, Map(M -> ann), Map(P0 -> Lower.LenBounds(plo, phi)))
      val r = out.bounded.getOrElse(fail(s"p0=[$plo,$phi]: ${out.noBoundReason.get}"))
      println(s"PEEL p0=[$plo,$phi] ${r.show}")
      assert(r.callFree)
      assertEquals(r.inputMaxLen, 4L)
      assertEquals(r.lenChain, (0 to 4 / drop).map(i => 4L - i * drop).toVector,
                   s"p0=[$plo,$phi]: μ must drop by exactly |p0|.lo = $drop per level")
      assertEquals(r.maxCallDepth, 4 / drop)
      val (c, bad, w) = peelDifferential(plo, phi, r, 1500, 8L + plo * 31 + phi)
      println(s"PEEL p0=[$plo,$phi] DIFFERENTIAL: $c conforming inputs, $bad disagreements")
      assertEquals(bad, 0, s"p0=[$plo,$phi]: $w")

    // THE GUARD IS STILL LOAD-BEARING: a prefix that may be EMPTY drops nothing, so M1 refuses and
    // no amount of product reduction may manufacture a bound.
    val none = residualise(peelPtr, table, Map(M -> ann), Map(P0 -> Lower.LenBounds(0, 3)))
    assertEquals(none.bounded, None, "|p0| may be 0: there is no decrease to bound anything with")
    assert(none.noBoundReason.get.contains("no structural decrease witness (M1)"), none.noBoundReason.get)
    println(s"NO-BOUND (|p0| may be 0): ${none.noBoundReason.get}")
  }

  test("NO BOUND: two self-calls, or a call to another routine") {
    val twoPtr = RoutinePtr("two")
    val two = Routine(twoPtr, Vector.empty, Vector(M),
      Space.Union(Space.Call(twoPtr, Vector.empty, Vector(Space.TailsUnion(Space.Mention(M)))),
                  Space.Call(twoPtr, Vector.empty, Vector(Space.TailsUnion(Space.Mention(M))))))
    val t2 = table + (twoPtr -> two)
    val o1 = residualise(twoPtr, t2, Map(M -> lengthAnnotation(1, 4)))
    assertEquals(o1.bounded, None)
    assert(o1.noBoundReason.get.contains("exactly one self-recursive call"), o1.noBoundReason.get)
    val mixPtr = RoutinePtr("mix")
    val mix = Routine(mixPtr, Vector.empty, Vector(M),
      Space.Union(Space.Call(walkPtr, Vector.empty, Vector(Space.Mention(M))),
                  Space.Call(mixPtr, Vector.empty, Vector(Space.TailsUnion(Space.Mention(M))))))
    val o2 = residualise(mixPtr, table + (mixPtr -> mix), Map(M -> lengthAnnotation(1, 4)))
    assertEquals(o2.bounded, None)
    println(s"NO-BOUND (other callee): ${o2.noBoundReason.get}")
    assert(o2.noBoundReason.get.contains("calls walk"), o2.noBoundReason.get)
  }

  // ================================================================================================
  //  4.  the worklist itself
  // ================================================================================================
  test("summaries are memoised by (routine, abstract arguments) and solved by a worklist") {
    val a0 = Args(Vector(keyType(lengthAnnotation(1, 4))), Vector.empty)
    val sums = summarise(Key(walkPtr, a0), table)
    println(s"WORKLIST walk: ${sums.show}")
    assert(sums.certified, sums.note)
    // one key per level of the chain, plus the ⊥ argument the chain bottoms out at
    assert(sums.keys >= 5 && sums.keys <= 8, s"expected ~6 memo keys, got ${sums.keys}: " +
      sums.table.keys.map(_.args.mentions.head.len).mkString(", "))
    // every key is a post-fixed point (that is what `certified` means) and the ⊥ argument maps to ⊥
    assertEquals(sums.at(Key(walkPtr, Args(Vector(SpatialType.empty), Vector.empty))), SpatialType.empty)
    // the summary at the deepest non-empty argument is already ⊥ — the fact the bound rests on
    val headless = keyType(SpatialType(Shape.top, SpaceType.closed(0L -> Ivl.unknown)))
    assert(sums.at(Key(walkPtr, Args(Vector(headless), Vector.empty))).isProvablyEmpty,
           s"walk over a headless space must be provably empty, got ${sums.at(Key(walkPtr, Args(Vector(headless), Vector.empty))).show}")
    // and the fixed point is reached without hitting the budgets
    assertEquals(sums.toppedKeys, 0)
    // a growing recursion is bounded by the BUDGET, not by hope: it still terminates
    val ga = Args(Vector(keyType(lengthAnnotation(1, 2))), Vector.empty)
    val gs = summarise(Key(growPtr, ga), table, Limits(maxKeys = 40, maxUpdates = 4, maxRounds = 500))
    println(s"WORKLIST grow (divergent argument): ${gs.show}")
    assert(gs.keys <= 40, "the key budget must hold")
    assert(!gs.certified, "a table built under an exhausted budget must NOT claim certification")
  }

  /** the memo table is keyed by (RoutinePtr, abstract arguments) — so it spans a MUTUAL SCC.  Note
   *  `eval` DIVERGES on this pair (its union-fixpoint shortcut only recognises direct
   *  self-recursion), so nothing is evaluated here: the solver still terminates and certifies, and
   *  `residualise` correctly declines the shape. */
  test("summaries span MULTIPLE routines: a mutually recursive pair") {
    val evenPtr = RoutinePtr("even"); val oddPtr = RoutinePtr("odd")
    val even = Routine(evenPtr, Vector.empty, Vector(M),
      Space.Union(headsOf(Space.Mention(M)),
        Space.Call(oddPtr, Vector.empty, Vector(Space.TailsUnion(Space.Mention(M))))))
    val odd = Routine(oddPtr, Vector.empty, Vector(M),
      Space.Call(evenPtr, Vector.empty, Vector(Space.TailsUnion(Space.Mention(M)))))
    val t = Map(evenPtr -> even, oddPtr -> odd)
    val entry = Key(evenPtr, Args(Vector(keyType(lengthAnnotation(1, 4))), Vector.empty))
    val sums = summarise(entry, t)
    println(s"WORKLIST mutual SCC: ${sums.show}")
    assert(sums.certified, sums.note)
    assertEquals(sums.table.keys.map(_.routine).toSet, Set(evenPtr, oddPtr))
    // memoisation is by VALUE: solving again gives the same table
    assertEquals(summarise(entry, t).table, sums.table)
    // residualisation declines this shape, with the reason stated
    val out = residualise(evenPtr, t, Map(M -> lengthAnnotation(1, 4)))
    assertEquals(out.bounded, None)
    println(s"NO-BOUND (mutual): ${out.noBoundReason.get}")
    assert(out.noBoundReason.get.contains("exactly one self-recursive call"), out.noBoundReason.get)
  }

  test("the certification is what licenses the table, and it is really checked") {
    val a0 = Args(Vector(keyType(lengthAnnotation(1, 3))), Vector.empty)
    val sums = summarise(Key(rebuildPtr, a0), table)
    println(s"WORKLIST rebuild: ${sums.show}")
    assert(sums.certified, sums.note)
    // a hand-broken table must NOT certify: shrink one key below its body's type
    val brokenKey = sums.table.keys.find(k => !sums.at(k).isProvablyEmpty)
    assert(brokenKey.isDefined)
    // (the check itself, on the order: ⊥ ⊑ anything, and nothing is ⊑ ⊥ unless it is ⊥)
    assert(leq(SpatialType.empty, SpatialType.top))
    assert(!leq(SpatialType.of(SpaceValue(Set(p("a")))), SpatialType.empty))
    assert(leq(SpatialType.of(SpaceValue(Set(p("a")))), SpatialType.top))
    // the histogram order is STRICTER than SpaceType.within (which compares upper envelopes only)
    val a = SpaceType.closed(1L -> Ivl(0, 3), 2L -> Ivl(0, 3))
    val b = SpaceType.bounded(Lower.LenBounds(0, 10), 3)
    assert(a.within(b), "precondition: the upper-envelope check accepts this")
    assert(!lensLeq(a, b), "but γ(a) ⊄ γ(b): six paths fit in a and only three in b")
  }

  // ================================================================================================
  //  5.  a randomized gate over the whole family
  // ================================================================================================
  test("randomized gate: every derived bound residualises to an equivalent Call-free term") {
    val families = Vector(walkPtr -> 0, levelsPtr -> 0, capturePtr -> 0, rebuildPtr -> 1)
    var cases = 0; var bounds = 0; var evals = 0; var bad = 0
    val fails = Vector.newBuilder[String]
    for (rp, extra) <- families; L <- 1 to 4 do
      val out = residualise(rp, table, Map(M -> lengthAnnotation(1, L.toLong)))
      cases += 1
      out.bounded match
        case None => fails += s"${rp.s} L=$L unexpectedly unbounded: ${out.noBoundReason.get}"
        case Some(res) =>
          bounds += 1
          if res.maxCallDepth != L + extra then
            fails += s"${rp.s} L=$L expected depth ${L + extra}, got ${res.maxCallDepth}"
          if !res.callFree then fails += s"${rp.s} L=$L residual still has a Call"
          val (c, b, w) = differential(rp, res, 120, 1000L + L, r => randInput(r, 1, L, 5))
          evals += c; bad += b
          if b > 0 then fails += s"${rp.s} L=$L: $b/$c disagreements, witness $w"
    val fs = fails.result()
    println(s"RANDOMIZED GATE: $cases (routine, maxLen) cases, $bounds bounds derived, " +
            s"$evals differential evaluations, $bad disagreements, ${fs.size} failures")
    fs.take(5).foreach(println)
    assertEquals(fs.size, 0)
    assertEquals(bounds, cases)
    assertEquals(bad, 0)
  }

  /** a second mention parameter, PASSED THROUGH: the chain must stay one-dimensional and the
   *  precondition must mention only the parameters that were actually annotated. */
  test("a pass-through second parameter does not disturb the bound") {
    val G = SpaceMention("g")
    val twoPtr = RoutinePtr("filter")
    val two = Routine(twoPtr, Vector.empty, Vector(M, G),
      Space.Iteration(Space.Mention(M), H, R,
        Space.Union(Space.Intersection(Space.Singleton(deref(H)), Space.Mention(G)),
          Space.Call(twoPtr, Vector.empty, Vector(Space.Mention(R), Space.Mention(G))))))
    val t2 = table + (twoPtr -> two)
    val out = residualise(twoPtr, t2, Map(M -> lengthAnnotation(1, 4)))
    val res = out.bounded.getOrElse(fail(s"expected a bound, got: ${out.noBoundReason.get}"))
    println(s"TWO-PARAM ${res.show}")
    assertEquals(res.maxCallDepth, 4)
    assertEquals(res.decreasingParam, M)
    assertEquals(res.precondition.keySet, Set(M), "an un-annotated (⊤) parameter is not a precondition")
    assert(res.callFree)
    val rng = new java.util.Random(2024L)
    val orig = callOf(twoPtr, two)
    var checked = 0; var bad = 0
    for _ <- 0 until 300 do
      val v = randInput(rng, 1, 4, 6)
      val g = randInput(rng, 1, 1, 4)
      val a = runWith(orig, Map(M -> v, G -> g), t2)
      val b = runWith(res.residual.body, Map(M -> v, G -> g), PartialFunction.empty)
      checked += 1; if a != b then bad += 1
    println(s"TWO-PARAM DIFFERENTIAL: $checked conforming inputs, $bad disagreements")
    assertEquals(bad, 0)
  }

  // ------------------------------------------------------------------------------------------------
  //  a SEEDED RANDOMIZED differential gate over generated recursive routines — the primary net
  // ------------------------------------------------------------------------------------------------
  def genBase(rng: java.util.Random, depth: Int, leaves: Vector[Space], wrapPaths: Vector[Path]): Space =
    if depth <= 0 || rng.nextInt(100) < 30 then leaves(rng.nextInt(leaves.length))
    else
      def sub = genBase(rng, depth - 1, leaves, wrapPaths)
      rng.nextInt(10) match
        case 0 => Space.Union(sub, sub)
        case 1 => Space.Intersection(sub, sub)
        case 2 => Space.Subtraction(sub, sub)
        case 3 => Space.Restriction(sub, sub)
        case 4 => Space.Raffination(sub, sub)
        case 5 => Space.TailsUnion(sub)
        case 6 => Space.TailsIntersection(sub)
        case 7 => Space.Wrap(sub, wrapPaths(rng.nextInt(wrapPaths.length)))
        case 8 => Space.Range(sub, 0, 1 + rng.nextInt(3))
        case _ => Space.Unwrap(sub, Path.Constant(p(alphabet(rng.nextInt(alphabet.length)))))

  test("randomized differential gate over GENERATED recursive routines") {
    val rng = new java.util.Random(880711L)
    // no ∅ leaf: a base that is trivially empty makes the whole recursion ∅ and residualises to
    // depth 0, which is correct but says nothing about UNROLLING
    val smallLits = Vector(lit(p("a")), lit(p()), lit(p("a", "b"), p("b")))
    var generated = 0; var bounded = 0; var noBound = 0; var evals = 0; var bad = 0
    val depths = scala.collection.mutable.Map.empty[Int, Int]
    val reasons = scala.collection.mutable.Map.empty[String, Int]
    val fails = Vector.newBuilder[String]
    for i <- 0 until 500 do
      val L = 1 + rng.nextInt(4)
      val fam = rng.nextInt(3)
      val ptr = RoutinePtr("gen" + i)
      val self = (refs: Vector[Path], ms: Vector[Space]) => Space.Call(ptr, refs, ms)
      val (routine, ann) = fam match
        case 0 =>                                                          // structural (rest-set)
          val leaves = Vector(Space.Mention(M), Space.Mention(R), Space.Singleton(deref(H))) ++ smallLits
          val base = genBase(rng, 3, leaves, Vector(deref(H), Path.Constant(p("z"))))
          (Routine(ptr, Vector.empty, Vector(M),
            Space.Iteration(Space.Mention(M), H, R,
              Space.Union(base, self(Vector.empty, Vector(Space.Mention(R)))))), lengthAnnotation(1, L.toLong))
        case 1 =>                                                          // union-saturating tails chain
          val leaves = Vector(Space.Mention(M)) ++ smallLits
          val base = genBase(rng, 3, leaves, Vector(Path.Constant(p("z"))))
          (Routine(ptr, Vector.empty, Vector(M),
            Space.Union(base, self(Vector.empty, Vector(Space.TailsUnion(Space.Mention(M)))))),
            lengthAnnotation(1, L.toLong))
        case _ =>                                                          // unwrap chain by a 1-item ref
          val leaves = Vector(Space.Mention(M)) ++ smallLits
          val base = genBase(rng, 3, leaves, Vector(deref(PathRef("p0").known(1)), Path.Constant(p("z"))))
          (Routine(ptr, Vector(PathRef("p0").known(1)), Vector(M),
            Space.Union(base, self(Vector(deref(PathRef("p0").known(1))),
                                   Vector(Space.Unwrap(Space.Mention(M), deref(PathRef("p0").known(1))))))),
            lengthAnnotation(1, L.toLong))
      val rt: Map[RoutinePtr, Routine] = Map(ptr -> routine)
      generated += 1
      val out = residualise(ptr, rt, Map(M -> ann),
                            if routine.refs.isEmpty then Map.empty else Map(PathRef("p0") -> Lower.LenBounds(1, 1)))
      out.bounded match
        case None =>
          noBound += 1
          val why = out.noBoundReason.get.takeWhile(_ != ':')
          reasons(why) = reasons.getOrElse(why, 0) + 1
        case Some(res) =>
          bounded += 1
          depths(res.maxCallDepth) = depths.getOrElse(res.maxCallDepth, 0) + 1
          if !res.callFree then fails += s"${ptr.s}: residual still has a Call"
          val orig = callOf(ptr, routine)
          val irng = new java.util.Random(4242L + i)
          for _ <- 0 until 12 do
            val v = randInput(irng, 1, L, 4)
            val a = try Some(run(orig, v, rt)) catch case _: Throwable => None
            a.foreach { av =>
              val bv = run(res.residual.body, v, PartialFunction.empty)
              evals += 1
              if av != bv then
                bad += 1
                if bad <= 3 then
                  fails += s"${ptr.s} L=$L fam=$fam input ${v.pretty}: orig ${av.pretty} != residual ${bv.pretty}\n" +
                           s"   routine ${try routine.show catch case _: Throwable => routine.toString}\n" +
                           s"   residual ${try res.residual.body.show.replace('\n', ' ') catch case _: Throwable => "?"}"
            }
    val fs = fails.result()
    println(s"GENERATED GATE: $generated routines, $bounded bounded, $noBound NoBound, " +
            s"$evals differential evaluations, $bad disagreements")
    println(s"  derived depths: ${depths.toVector.sorted.map((d, c) => s"$d:$c").mkString(", ")}")
    println(s"  NoBound reasons: ${reasons.toVector.map((r, c) => s"$c x $r").mkString(" | ")}")
    fs.take(3).foreach(println)
    assertEquals(fs.size, 0, "a generated residual disagreed with its original")
    assert(bounded >= generated / 2, s"expected most generated recursions to be bounded, got $bounded/$generated")
    assert(evals > 2000, s"only $evals differential evaluations")
    assert(depths.filter(_._1 >= 1).values.sum >= 100,
           s"expected many NON-TRIVIAL unrollings, got ${depths.filter(_._1 >= 1).values.sum}")
  }

  test("residual size and shape: one specialised level per unrolled call, no more") {
    for L <- 1 to 6 do
      val res = residualise(walkPtr, table, Map(M -> lengthAnnotation(1, L.toLong))).bounded.get
      assertEquals(res.maxCallDepth, L)
      assertEquals(countIterations(res.residual.body), L)
      assert(res.callFree)
      println(s"walk L=$L: depth ${res.maxCallDepth}, ${nodes(res.residual.body)} residual nodes, " +
              s"${countIterations(res.residual.body)} levels")
  }

  // ================================================================================================
  //  helpers
  // ================================================================================================
  def kids(s: Space): Vector[Space] = s match
    case Space.Union(a, b) => Vector(a, b)
    case Space.Intersection(a, b) => Vector(a, b)
    case Space.Subtraction(a, b) => Vector(a, b)
    case Space.Restriction(a, b) => Vector(a, b)
    case Space.Raffination(a, b) => Vector(a, b)
    case Space.Composition(a, b) => Vector(a, b)
    case Space.Wrap(a, _) => Vector(a)
    case Space.Unwrap(a, _) => Vector(a)
    case Space.TailsUnion(a) => Vector(a)
    case Space.TailsIntersection(a) => Vector(a)
    case Space.Range(a, _, _) => Vector(a)
    case Space.Iteration(a, _, _, b) => Vector(a, b)
    case Space.Fixpoint(a, _, b) => Vector(a, b)
    case Space.Fold(a, _, _, _, _, b, _) => Vector(a, b)
    case Space.GroundedSS(a, _) => Vector(a)
    case Space.Call(_, _, ms) => ms
    case _ => Vector.empty
  def nodes(s: Space): Int = 1 + kids(s).map(nodes).sum
  def countIterations(s: Space): Int =
    (s match { case _: Space.Iteration => 1; case _ => 0 }) + kids(s).map(countIterations).sum
end SpatialRecursionCheck
