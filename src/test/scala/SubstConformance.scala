package morkl

import munit.FunSuite

/** O6a — CAPTURE-AVOIDING SUBSTITUTION, CHECKED AGAINST THE IMPLEMENTATION.
 *
 *  `terminating/REGISTRY.tsv` row O6a is the beta-soundness of acyclic inlining:
 *
 *      [[Call r(a; s)]]  =  [[ body_r [x := a, m := s] ]]      with capture-avoiding substitution
 *                                                              under Iteration/Fold/Fixpoint binders
 *
 *  It is OPEN as a theorem, and the registry says why: it needs a first-order model of the
 *  substitution FUNCTION, and a model that agreed with `substPathRef`/`substMention`/`Lower.inline`
 *  by construction would prove nothing about them.  `proofs/unbounded/call_unfold.p` (U63) proves
 *  the semantic half — a call IS its body applied to the argument — but in that encoding a body
 *  already IS its semantic function, so substitution is application and the syntactic half is
 *  invisible there.
 *
 *  THIS SUITE IS THE SYNTACTIC HALF, AS A DIFFERENTIAL.  It is not a proof and does not claim to be
 *  one; it is the check that closes the loop O6a leaves open, over randomly generated programs that
 *  deliberately shadow their binders:
 *
 *    1. SUBSTITUTION COMMUTES WITH EVALUATION.  `eval(subst(body, m, arg))` under an environment
 *       equals `eval(body)` under that environment extended with `m -> eval(arg)`.  This is O6a's
 *       statement, instance by instance, and it is what an inlining pass needs.
 *    2. CAPTURE IS AVOIDED.  When the substituted name is SHADOWED by an `Iteration`/`Fold`/
 *       `Fixpoint` binder, substitution must not reach inside — and the differential above is what
 *       detects it if it does, because the shadowed occurrence would start reading the argument.
 *       Generation is biased to produce exactly that shape, and the suite REPORTS how many programs
 *       actually contained a shadowing binder so "0 shadowing cases" cannot pass unnoticed.
 *    3. INLINING AGREES WITH CALLING.  `eval(Call(r, ...))` equals `eval(inlineCalls(Call(r, ...)))`
 *       and equals `eval` of the whole program after `Lower.inline` — the actual pass, not a
 *       re-implementation of it.
 *    4. THE SAME, THROUGH ALL THREE EXECUTORS, so a backend that disagreed about a binder would
 *       not hide behind `eval`.
 *
 *  A NEGATIVE CONTROL keeps it from being vacuous: a deliberately capture-UNSAFE substitution
 *  (one that ignores shadowing) must be caught by check 1 on at least one generated program.  If it
 *  is not, the generator is not producing the shapes this suite exists to test.
 */
class SubstConformance extends FunSuite:
  import Space.*

  private val items = Vector("a", "b", "c")
  private val freeMentionNames = Vector("m", "n")

  private def randPath(rng: scala.util.Random): PathValue =
    PathValue(List.fill(1 + rng.nextInt(2))(items(rng.nextInt(items.length))))
  private def randValue(rng: scala.util.Random): SpaceValue =
    SpaceValue((0 to rng.nextInt(4)).map(_ => randPath(rng)).toSet)

  /** A random program over the mentions `vars` and path refs `pvars`, biased towards SHADOWING:
   *  an `Iteration`/`Fold`/`Fixpoint` binder re-binds a name that is already free, which is the
   *  only shape in which capture-avoidance is observable at all. */
  private def randSpace(depth: Int, vars: Vector[String], pvars: Vector[String],
                        shadow: String, rng: scala.util.Random): Space =
    def leaf(): Space = rng.nextInt(6) match
      case 0 => Empty
      case 1 => Literal(randValue(rng))
      case 2 | 3 if vars.nonEmpty => Mention(SpaceMention(vars(rng.nextInt(vars.length))))
      case 4 if pvars.nonEmpty => Singleton(Path.Deref(PathRef(pvars(rng.nextInt(pvars.length))).known(1)))
      case _ => Singleton(Path.Constant(randPath(rng)))
    if depth <= 0 then leaf()
    else
      def sub() = randSpace(depth - 1, vars, pvars, shadow, rng)
      // NO `Composition`.  It CONCATENATES paths, so nesting it inside a `Fixpoint` grows the path
      // length every round and the least post-fixpoint is infinite — the generator would hand
      // `eval` a non-terminating program.  Composition's own substitution behaviour is structural
      // and identical to the other binary arms, so nothing is lost by leaving it out here; it is
      // covered by `AlgebraicLaws` and by the tier-3 conformance suite.
      rng.nextInt(13) match
        case 0 => Union(sub(), sub())
        case 1 => Intersection(sub(), sub())
        case 2 => Subtraction(sub(), sub())
        case 3 => Restriction(sub(), sub())
        case 4 => Raffination(sub(), sub())
        case 5 => Wrap(sub(), Path.Constant(randPath(rng)))
        case 6 => Unwrap(sub(), Path.Constant(randPath(rng)))
        case 7 => TailsUnion(sub())
        case 8 => TailsIntersection(sub())
        case 9 | 10 | 11 =>
          // SHADOWING ITERATION: `rest` re-binds the very name being substituted.  `Iteration` is
          // TOTAL and terminating on every source, so it is the one binder that is safe to put in a
          // random generator.  `Fold` and `Fixpoint` shadowing is covered by the EXPLICIT table
          // [[shadowingPrograms]] below instead: a randomly generated `Fixpoint` body is a
          // recurrence whose termination is exactly what nothing here can guarantee, and a
          // generator that can emit a divergent program is a generator that hangs the suite rather
          // than testing it.
          val h = s"h${rng.nextInt(1000)}"
          Iteration(sub(), PathRef(h).known(1), SpaceMention(shadow),
                    randSpace(depth - 1, vars :+ shadow, pvars :+ h, shadow, rng))
        case _ =>
          val h = s"h${rng.nextInt(1000)}"; val t = s"t${rng.nextInt(1000)}"
          Iteration(sub(), PathRef(h).known(1), SpaceMention(t),
                    randSpace(depth - 1, vars :+ t, pvars :+ h, shadow, rng))

  /** THE RECURSIVE BINDERS, EXPLICITLY.  One program per shadowing shape, each small enough to
   *  read and each TERMINATING by construction, so the differential covers `Fold` and `Fixpoint`
   *  capture without a generator that can emit a divergent recurrence.  `m` is the substituted
   *  name and is SHADOWED in every one of them. */
  private def shadowingPrograms: Vector[(String, Space)] =
    val m = SpaceMention("m")
    val mm: Space = Mention(m)
    val h = PathRef("h").known(1)
    val acc = PathRef("acc")
    val k = Path.Constant(PathValue(List("a")))
    Vector(
      "Fixpoint rebinds m; body reads the SHADOWED m (must not see the argument)" ->
        Fixpoint(Literal(SpaceValue(Set(PathValue(List("a", "b"))))), m,
                 Union(mm, TailsUnion(mm))),
      "Fixpoint rebinds m; the SEED reads the FREE m (must see the argument)" ->
        Fixpoint(mm, m, Union(mm, TailsUnion(mm))),
      "Fixpoint rebinds m; the seed reads the free m AND the body the shadowed one" ->
        Fixpoint(Wrap(mm, k), m, Union(mm, TailsUnion(mm))),
      "Iteration rebinds m as `rest`; body reads the SHADOWED m" ->
        Iteration(Literal(SpaceValue(Set(PathValue(List("a", "b")), PathValue(List("c", "d"))))),
                  h, m, Wrap(mm, Path.Deref(h))),
      "Iteration rebinds m; the SOURCE reads the FREE m" ->
        Iteration(mm, h, m, TailsUnion(mm)),
      "Fold rebinds m as `rest`; body reads the SHADOWED m" ->
        Fold(Literal(SpaceValue(Set(PathValue(List("a", "b")), PathValue(List("c", "d"))))),
             k, acc, h, m, Union(mm, Singleton(Path.Deref(acc))), Path.Deref(acc)),
      "Fold rebinds m; the SOURCE reads the FREE m" ->
        Fold(mm, k, acc, h, m, Union(mm, Singleton(Path.Deref(acc))), Path.Deref(acc)),
      "nested: Iteration inside a Fixpoint, both rebinding m" ->
        Fixpoint(Literal(SpaceValue(Set(PathValue(List("a", "b"))))), m,
                 Union(mm, Iteration(mm, h, m, TailsUnion(mm)))),
    )

  /** does `s` bind `name` anywhere — i.e. is there a shadowing occurrence to get wrong? */
  private def shadowsAnywhere(s: Space, name: String): Boolean = s match
    case Iteration(src, _, rest, b) => rest.s == name || shadowsAnywhere(src, name) || shadowsAnywhere(b, name)
    case Fixpoint(i, rec, b) => rec.s == name || shadowsAnywhere(i, name) || shadowsAnywhere(b, name)
    case Fold(src, _, _, _, rest, b, _) => rest.s == name || shadowsAnywhere(src, name) || shadowsAnywhere(b, name)
    case Union(a, b) => shadowsAnywhere(a, name) || shadowsAnywhere(b, name)
    case Intersection(a, b) => shadowsAnywhere(a, name) || shadowsAnywhere(b, name)
    case Subtraction(a, b) => shadowsAnywhere(a, name) || shadowsAnywhere(b, name)
    case Restriction(a, b) => shadowsAnywhere(a, name) || shadowsAnywhere(b, name)
    case Raffination(a, b) => shadowsAnywhere(a, name) || shadowsAnywhere(b, name)
    case Composition(a, b) => shadowsAnywhere(a, name) || shadowsAnywhere(b, name)
    case Wrap(src, _) => shadowsAnywhere(src, name)
    case Unwrap(src, _) => shadowsAnywhere(src, name)
    case TailsUnion(src) => shadowsAnywhere(src, name)
    case TailsIntersection(src) => shadowsAnywhere(src, name)
    case Range(x, _, _) => shadowsAnywhere(x, name)
    case _ => false

  /** THE CAPTURE-UNSAFE SUBSTITUTION, for the negative control: replace EVERY `Mention(m)`,
   *  shadowing binders included.  This is the bug O6a is about, written down so the suite can
   *  demonstrate it catches it. */
  private def unsafeSubst(s: Space, m: SpaceMention, arg: Space): Space =
    def go(x: Space): Space = x match
      case Mention(`m`) => arg
      case Union(a, b) => Union(go(a), go(b))
      case Intersection(a, b) => Intersection(go(a), go(b))
      case Subtraction(a, b) => Subtraction(go(a), go(b))
      case Restriction(a, b) => Restriction(go(a), go(b))
      case Raffination(a, b) => Raffination(go(a), go(b))
      case Composition(a, b) => Composition(go(a), go(b))
      case Wrap(src, p) => Wrap(go(src), p)
      case Unwrap(src, p) => Unwrap(go(src), p)
      case TailsUnion(src) => TailsUnion(go(src))
      case TailsIntersection(src) => TailsIntersection(go(src))
      case Iteration(src, sym, rest, b) => Iteration(go(src), sym, rest, go(b))     // WRONG: ignores `rest`
      case Fixpoint(i, rec, b) => Fixpoint(go(i), rec, go(b))                       // WRONG: ignores `rec`
      case Fold(src, ini, acc, sym, rest, b, upd) => Fold(go(src), ini, acc, sym, rest, go(b), upd)
      case Range(x, lo, hi) => Range(go(x), lo, hi)
      case other => other
    go(s)

  private def ev(s: Space, binds: Map[SpaceMention, SpaceValue]): SpaceValue =
    eval(s)(using PathContextMap(Map.empty), SpaceContextMap(binds), PartialFunction.empty)

  private val SEEDS = 300

  // ------------------------------------------------------------------------------------------
  test("O6a differential: substitution COMMUTES WITH EVALUATION, shadowing binders included") {
    var shadowing = 0
    var checked = 0
    val target = SpaceMention("m")
    for seed <- 0 until SEEDS do
      val rng = new scala.util.Random(seed.toLong * 0x2545F491L + 3)
      val body = randSpace(2, freeMentionNames, Vector.empty, "m", rng)
      val argValue = randValue(rng)
      val arg: Space = Literal(argValue)
      val outer = freeMentionNames.map(n => SpaceMention(n) -> randValue(rng)).toMap
      if shadowsAnywhere(body, "m") then shadowing += 1
      // (1) substitute, then evaluate  ==  evaluate with the name bound
      val substituted = AgnosticPipeline.substMention(body, target, arg)
      val lhs = ev(substituted, outer - target)
      val rhs = ev(body, outer + (target -> argValue))
      assertEquals(lhs, rhs,
        s"O6a FAILS at seed $seed: substituting `m := ${argValue.pretty}` then evaluating gives " +
        s"${lhs.pretty}, binding `m` gives ${rhs.pretty}\n  body = ${body.show}")
      checked += 1
    println(s"\n### O6a differential: $checked programs, $shadowing of them SHADOW `m` under an " +
            s"Iteration/Fold/Fixpoint binder")
    assert(shadowing >= SEEDS / 10,
           s"only $shadowing of $SEEDS generated programs shadow the substituted name — the generator " +
           "is not producing the shape this suite exists to test, so a pass means little")
  }

  test("O6a differential: the RECURSIVE binders, explicitly — Fold and Fixpoint shadowing") {
    val target = SpaceMention("m")
    val progs = shadowingPrograms
    for (why, body) <- progs do
      assert(shadowsAnywhere(body, "m"), s"`$why` does not actually shadow `m`")
      for argValue <- Vector(SpaceValue(Set.empty),
                             SpaceValue(Set(PathValue(List("z")))),
                             SpaceValue(Set(PathValue(List("a", "b")), PathValue(List("z"))))) do
        val substituted = AgnosticPipeline.substMention(body, target, Literal(argValue))
        val lhs = ev(substituted, Map.empty)
        val rhs = ev(body, Map(target -> argValue))
        assertEquals(lhs, rhs,
          s"O6a FAILS on `$why` at m = ${argValue.pretty}: substituting gives ${lhs.pretty}, " +
          s"binding gives ${rhs.pretty}\n  body = ${body.show}")
        // and the capture-UNSAFE substitution must be caught on at least the shapes where the
        // shadowed occurrence is actually reachable — checked in aggregate below
      end for
    // the control, on this table: an unsafe substitution must disagree somewhere
    val caught = for (why, body) <- progs; argValue <- Vector(SpaceValue(Set(PathValue(List("z")))))
                     if
                       val bad = unsafeSubst(body, target, Literal(argValue))
                       val l = try Some(ev(bad, Map.empty)) catch case _: Throwable => None
                       l.forall(_ != ev(body, Map(target -> argValue)))
                 yield why
    println(s"\n### O6a explicit binders: ${progs.size} shadowing programs x 3 arguments; the " +
            s"capture-UNSAFE substitution is caught on ${caught.size} of ${progs.size}")
    assert(caught.nonEmpty,
           "the capture-unsafe substitution disagrees with `eval` on NONE of the explicit " +
           "shadowing programs — then this table cannot detect a capture bug")
  }

  test("O6a differential: the capture-UNSAFE substitution is CAUGHT (the control)") {
    val target = SpaceMention("m")
    var caught = 0
    var shadowing = 0
    for seed <- 0 until SEEDS do
      val rng = new scala.util.Random(seed.toLong * 0x2545F491L + 3)
      val body = randSpace(2, freeMentionNames, Vector.empty, "m", rng)
      val argValue = randValue(rng)
      val arg: Space = Literal(argValue)
      val outer = freeMentionNames.map(n => SpaceMention(n) -> randValue(rng)).toMap
      if shadowsAnywhere(body, "m") then
        shadowing += 1
        val bad = unsafeSubst(body, target, arg)
        val lhs = try Some(ev(bad, outer - target)) catch case _: Throwable => None
        val rhs = ev(body, outer + (target -> argValue))
        if lhs.forall(_ != rhs) then caught += 1
    println(s"### the capture-UNSAFE substitution disagrees with `eval` on $caught of the " +
            s"$shadowing shadowing programs")
    assert(caught > 0,
           "the deliberately capture-unsafe substitution was NEVER caught — then check 1 above " +
           "cannot detect a capture bug and the differential is vacuous")
  }

  test("O6a differential: INLINING a real routine agrees with CALLING it, through all executors") {
    val m = SpaceMention("m")
    var checked = 0
    for seed <- 0 until 200 do
      val rng = new scala.util.Random(seed.toLong * 0x85EBCA6BL + 5)
      val body = randSpace(2, Vector("m"), Vector.empty, "m", rng)
      val rp = RoutinePtr(s"r$seed")
      val r = Routine(rp, Vector.empty, Vector(m), body)
      given rc: PartialFunction[RoutinePtr, Routine] = { case `rp` => r }
      val argValue = randValue(rng)
      val prog: Space = Call(rp, Vector.empty, Vector(Literal(argValue)))
      given PathContext = PathContextMap(Map.empty)
      given SpaceContext = SpaceContextMap(Map.empty)
      val viaCall = eval(prog)
      // `Lower.inline` / `inlineCalls` is THE PASS, not a re-implementation of it
      val inlined = inlineCalls(prog, rc)
      assert(!inlined.show.contains(rp.s), s"inlineCalls left a Call to ${rp.s} behind")
      val viaInline = eval(inlined)
      assertEquals(viaInline, viaCall,
        s"O6a FAILS at seed $seed: inlining the routine changes its meaning\n  body = ${body.show}")
      // and the two trie backends must agree with both
      assertEquals(evalI(inlined).toSpaceValue, viaCall, s"evalI disagrees after inlining (seed $seed)")
      assertEquals(evalT(inlined).toSpaceValue, viaCall, s"evalT disagrees after inlining (seed $seed)")
      checked += 1
    println(s"### inlining conformance: $checked routines, call vs inline vs 3 executors")
  }
end SubstConformance
