package morkl

import munit.FunSuite

/** ==============================================================================================
 *  EVERY GENERIC TERM TRAVERSAL IS TOTAL OVER THE `Space` STRUCTURE — mechanically, not by review.
 *
 *  ==THE BUG THIS EXISTS FOR==
 *  `collect` — the traversal EVERY loop-invariance test in `Lower` is written in
 *  (`IterUnion_Indep`, `IterComposition_Indep`, `cleanSpace` and through it `IterCompRight_Hoist`,
 *  `TransposeSemijoin`) — had no `Space.Raffination` arm.  It fell into the `case x => x`
 *  catch-all, so the whole subtree under a `\|` was INVISIBLE.  A body that used an iteration
 *  binder under a raffination therefore looked loop-invariant, the hoist moved it out of its own
 *  binder, and the residual carried a dangling `Deref` that only failed at `evalI`:
 *
 *      java.util.NoSuchElementException: key not found: PathRef(h418115)
 *
 *  It survived because the program fuzzer could not draw a `Raffination`.  The moment the
 *  generator gained the operator, the 1000-program corpus gate found it in 10 programs on the
 *  first run.  `docs/traps.md` §7 names this family; this suite is its mechanical form.
 *
 *  ==THE METHOD==
 *  For each `Space` constructor, build a term that PUTS A MARKER in each of its subterm positions
 *  — a free `Mention` and a free `Deref` — and assert that every traversal reports the marker.  A
 *  missing arm cannot then be a silent wrong answer: it is a red test naming the constructor and
 *  the traversal.
 *  ============================================================================================== */
class TraversalTotality extends FunSuite:
  import Space.*

  val mM: SpaceMention = SpaceMention("$marker$")
  val mR: PathRef = PathRef("$markerRef$")
  /** the marker subterm: a free mention AND a free deref, so one probe covers both traversals */
  val marker: Space = Intersection(Mention(mM), Singleton(Path.Deref(mR)))

  val filler: Space = Literal(SpaceValue(Set(PathValue(List("z")))))
  val cp: Path = Path.Constant(PathValue(List("k")))

  /** every constructor, with the marker in EVERY subterm position it has.  A constructor whose
   *  positions are all leaves (`Empty`, `Mention`, `Literal`) is listed with `Nil`. */
  def probes: Vector[(String, Vector[Space])] = Vector(
    "Union" -> Vector(Union(marker, filler), Union(filler, marker)),
    "Intersection" -> Vector(Intersection(marker, filler), Intersection(filler, marker)),
    "Subtraction" -> Vector(Subtraction(marker, filler), Subtraction(filler, marker)),
    "Restriction" -> Vector(Restriction(marker, filler), Restriction(filler, marker)),
    "Raffination" -> Vector(Raffination(marker, filler), Raffination(filler, marker)),
    "Composition" -> Vector(Composition(marker, filler), Composition(filler, marker)),
    "Wrap" -> Vector(Wrap(marker, cp)),
    "Unwrap" -> Vector(Unwrap(marker, cp)),
    "TailsUnion" -> Vector(TailsUnion(marker)),
    "TailsIntersection" -> Vector(TailsIntersection(marker)),
    "Range" -> Vector(Range(marker, 0, 2)),
    "Iteration" -> Vector(Iteration(marker, PathRef("h"), SpaceMention("t"), filler),
                          Iteration(filler, PathRef("h"), SpaceMention("t"), marker)),
    "Fixpoint" -> Vector(Fixpoint(marker, SpaceMention("r"), filler),
                         Fixpoint(filler, SpaceMention("r"), marker)),
    "Fold" -> Vector(
      Fold(marker, cp, PathRef("a"), PathRef("h"), SpaceMention("t"), filler, cp),
      Fold(filler, cp, PathRef("a"), PathRef("h"), SpaceMention("t"), marker, cp)),
    "Call" -> Vector(Call(RoutinePtr("r"), Vector.empty, Vector(marker))),
    "GroundedSS" -> Vector(GroundedSS(marker, identity)),
  )

  /** the constructors a probe list must cover: everything in the enum that HAS a subterm.
   *  `Empty` / `Mention` / `Singleton` / `Literal` / `GroundedPS` are leaves or path-only. */
  val mustCover: Set[String] = Set("Union", "Intersection", "Subtraction", "Restriction",
    "Raffination", "Composition", "Wrap", "Unwrap", "TailsUnion", "TailsIntersection", "Range",
    "Iteration", "Fixpoint", "Fold", "Call", "GroundedSS")

  test("the probe table covers every Space constructor that has a subterm") {
    assertEquals(probes.map(_._1).toSet, mustCover,
                 "a constructor was added to `Space` without a totality probe")
  }

  test("collect sees a marker in EVERY subterm position of EVERY constructor") {
    // `collect` is the traversal `Lower`'s loop-invariance tests are written in.  A position it
    // does not visit is a position where a binder use is invisible to `IterUnion_Indep`.
    val missed = Vector.newBuilder[String]
    for (name, ts) <- probes; (t, i) <- ts.zipWithIndex do
      val (so, po) = collect(t)({ case Mention(`mM`) => () }, { case Path.Deref(`mR`) => () })
      if so.isEmpty then missed += s"$name#$i: collect missed the free Mention"
      if po.isEmpty then missed += s"$name#$i: collect missed the free Deref"
    assertEquals(missed.result(), Vector.empty[String],
      "collect is NOT total — a loop-invariance test written with it will hoist a body out of its " +
      "own binder:\n  " + missed.result().mkString("\n  "))
  }

  test("subs rewrites a marker in EVERY subterm position of EVERY constructor") {
    val replaced: Space = Literal(SpaceValue(Set(PathValue(List("REPLACED")))))
    val missed = Vector.newBuilder[String]
    for (name, ts) <- probes; (t, i) <- ts.zipWithIndex do
      val out = subs(t)(spost = { case Mention(`mM`) => replaced })
      val (so, _) = collect(out)({ case Mention(`mM`) => () }, PartialFunction.empty)
      if so.nonEmpty then missed += s"$name#$i: subs did not reach the marker"
    assertEquals(missed.result(), Vector.empty[String],
      "subs is NOT total — a rewrite will silently skip a subterm:\n  " + missed.result().mkString("\n  "))
  }

  test("Matching.freeMentions / freeRefs see a marker in EVERY subterm position") {
    val missed = Vector.newBuilder[String]
    for (name, ts) <- probes; (t, i) <- ts.zipWithIndex do
      if !Matching.freeMentions(t).contains(mM) then missed += s"$name#$i: freeMentions missed it"
      if !Matching.freeRefs(t).contains(mR) then missed += s"$name#$i: freeRefs missed it"
    assertEquals(missed.result(), Vector.empty[String],
      "a free-variable walk is NOT total — the supercompiler's hygiene rests on these:\n  " +
      missed.result().mkString("\n  "))
  }

  test("SizeZ3.children reaches a marker in EVERY subterm position") {
    // the child enumerator `SpatialPipeline.nodeCount` and the corpus census are built on
    val missed = Vector.newBuilder[String]
    def reaches(s: Space): Boolean =
      s == marker || SizeZ3.children(s).exists(reaches)
    for (name, ts) <- probes; (t, i) <- ts.zipWithIndex do
      if !reaches(t) then missed += s"$name#$i"
    assertEquals(missed.result(), Vector.empty[String],
      "SizeZ3.children is NOT total — node counts and the SMT size encoding under-count:\n  " +
      missed.result().mkString("\n  "))
  }

  test("REGRESSION: no optimiser pass hoists a binder use out of its own binder") {
    // The exact shape the corpus found, minimised: the OUTER binder `h` is used under a
    // RAFFINATION inside the INNER iteration's body.  Before `collect` gained its `Raffination`
    // arm, `IterUnion_Indep` judged the inner iteration loop-invariant in `h` and hoisted it out,
    // leaving `Deref(h)` unbound.
    val h = PathRef("h").known(1)
    val t = SpaceMention("t")
    val h2 = PathRef("h2").known(1)
    val t2 = SpaceMention("t2")
    val s0 = Mention(SpaceMention("s0"))
    val src = Literal(SpaceValue(Set(PathValue(List("a", "b")), PathValue(List("c", "d")))))
    val invariant: Space = Subtraction(s0, filler)
    val usesH: Space = Intersection(s0, Raffination(Singleton(Path.Deref(h)), filler))
    val prog: Space = Iteration(src, h, t, Iteration(src, h2, t2, Union(invariant, usesH)))

    def leaked(s: Space): Set[PathRef] = Matching.freeRefs(s) -- Matching.freeRefs(prog)
    val red = SC.reduce(prog)
    assertEquals(leaked(red), Set.empty[PathRef],
                 s"SC.reduce leaked a binder: ${leaked(red)}\n  ${red.show}")
    val opt = Routine(RoutinePtr("t"), Vector.empty, Matching.freeMentionsV(prog), prog)
      .optimized(using PartialFunction.empty)
    assertEquals(leaked(opt.body), Set.empty[PathRef],
                 s"Routine.optimized leaked a binder: ${leaked(opt.body)}\n  ${opt.body.show}")
    val sc = SC.supercompile(prog, PartialFunction.empty)
    assertEquals(leaked(sc.top), Set.empty[PathRef],
                 s"SC.supercompile leaked a binder: ${leaked(sc.top)}\n  ${sc.top.show}")
    // and the meaning is preserved on a concrete input
    val env = SpaceContextMap(Map(SpaceMention("s0") ->
      SpaceValue(Set(PathValue(List("a")), PathValue(List("z")), PathValue(Nil)))))
    val truth = eval(prog)(using PathContextMap(Map.empty), env, PartialFunction.empty)
    for (name, out) <- Vector("SC.reduce" -> red, "optimized" -> opt.body, "supercompile" -> sc.top) do
      assertEquals(eval(out)(using PathContextMap(Map.empty), env, PartialFunction.empty), truth,
                   s"$name changed the meaning")
  }
end TraversalTotality
