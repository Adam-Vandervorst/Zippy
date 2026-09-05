package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==================================================================================================
 *  CAPTURE, SHADOWING AND SIMULTANEITY — THE THREE THINGS `SubstConformance` CANNOT SEE.
 *
 *  ==WHY A SECOND SUBSTITUTION SUITE==
 *  `SubstConformance` is a randomized differential: it checks `eval(subst(body, m, arg))` against
 *  `eval(body)` under an extended environment, over generated programs biased to shadow their
 *  binders.  It found three real bugs and it is the right tool for the semantic statement.  But it
 *  has one structural blind spot addressed by **it substitutes closed
 *  `Literal`s only, so it cannot see capture.**  Capture needs a replacement with a FREE name that an
 *  inner binder can swallow; a closed replacement has none, so every capture-avoidance clause in the
 *  substitution is unexercised by that suite.
 *
 *  This suite supplies the three cases that need OPEN replacements or a term-level comparison:
 *
 *   A. CAPTURE.  A free name of the replacement meeting an inner binder of the same name.  The binder
 *      must be alpha-renamed; the substituted occurrence must still refer to the OUTER name.  Checked
 *      both syntactically (the binder's name changed) and semantically (the denotation is the one the
 *      outer name gives, not the loop variable's).
 *   B. SHADOWING.  The mirror image: an inner binder that REBINDS the substituted name.  Substitution
 *      must NOT descend into its scope.  Shadowing and capture are separate hazards and a
 *      substitution can get one right and the other wrong — three of the tree's four implementations
 *      did exactly that.
 *   C. SIMULTANEITY — the `g(y,x)` case.  Sequential composition of single substitutions is not
 *      simultaneous substitution, and the two differ precisely when an argument mentions another
 *      formal.  `Lower.inline` bound its arguments in a loop and collapsed `g(b, a)`'s two arguments
 *      into one variable; this is the regression.
 *
 *  ==EVERY BINDING FORM, AND ALL SIX BINDERS==
 *  `Iteration` binds `symbol` (a path ref) and `rest` (a mention); `Fixpoint` binds `rec` (a
 *  mention); `Fold` binds `acc`, `symbol` (path refs) and `rest` (a mention).  Each is exercised for
 *  capture and for shadowing separately, because the two sorts take different code paths in `Subst`
 *  (`rangeMentions`/`rangeRefs`, `keepM`/`keepP`) and a fix to one has repeatedly not been a fix to
 *  the other.
 *
 *  ==THE ORACLE IS THE EXECUTOR, WHEREVER ONE EXISTS==
 *  A syntactic check ("the binder was renamed") pins the mechanism; a denotational check
 *  (`eval` agrees with the environment-extension reading) pins the meaning.  Where a case is closed
 *  enough to run, BOTH are asserted, through `eval`, `evalI` and `execZ` — because a backend that
 *  disagreed about a binder would otherwise hide behind the reference evaluator.
 *  ================================================================================================== */
class SubstCapture extends FunSuite:
  import Space.*

  def p(items: String*): PathValue = PathValue(items.toList)
  def lit(ps: PathValue*): Space = Literal(SpaceValue(ps.toSet))
  def M(n: String): Space = Mention(SpaceMention(n))
  def D(n: String): Path = Path.Deref(PathRef(n))
  val K: Path = Path.Constant(p("k"))

  given PathContext = PathContextMap(Map.empty)
  given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty

  /** every binder name occurring in `s`, in traversal order */
  def bindersOf(s: Space): Vector[String] =
    val out = Vector.newBuilder[String]
    def gp(x: Path): Unit = x match
      case Path.Concat(l, r) => gp(l); gp(r)
      case Path.GroundedPP(q, _) => gp(q)
      case Path.GroundedSP(q, _) => go(q)
      case _ => ()
    def go(x: Space): Unit = x match
      case Iteration(src, sym, rest, b) => go(src); out += sym.s; out += rest.s; go(b)
      case Fixpoint(i, rec, b) => go(i); out += rec.s; go(b)
      case Fold(src, ini, acc, sym, rest, t, u) =>
        go(src); gp(ini); out += acc.s; out += sym.s; out += rest.s; go(t); gp(u)
      case Union(a, b) => go(a); go(b)
      case Intersection(a, b) => go(a); go(b)
      case Subtraction(a, b) => go(a); go(b)
      case Restriction(a, b) => go(a); go(b)
      case Raffination(a, b) => go(a); go(b)
      case Composition(a, b) => go(a); go(b)
      case Wrap(a, q) => go(a); gp(q)
      case Unwrap(a, q) => go(a); gp(q)
      case TailsUnion(a) => go(a)
      case TailsIntersection(a) => go(a)
      case Range(a, _, _) => go(a)
      case Call(_, refs, ms) => refs.foreach(gp); ms.foreach(go)
      case GroundedPS(q, _) => gp(q)
      case GroundedSS(q, _) => go(q)
      case Empty | Literal(_) | Mention(_) | Singleton(_) => ()
    go(s)
    out.result()

  /** the free space mentions of `s`, as names */
  def freeM(s: Space): Set[String] = Matching.freeMentions(s).map(_.s)
  /** the free path refs of `s`, as names */
  def freeR(s: Space): Set[String] = Matching.freeRefs(s).map(_.s)

  // ================================================================================================
  // A. CAPTURE — an OPEN replacement meeting an inner binder of the same name.
  // ================================================================================================

  test("A1. Iteration's `rest` is alpha-renamed when the replacement's free mention would be caught") {
    // body:  Union(Mention("outer"), Iteration(src, y, rest, Mention("rest")))
    // subst: outer := Mention("rest")            <-- FREE `rest`, and the Iteration binds `rest`
    val body = Union(M("outer"), Iteration(lit(p("a")), PathRef("y"), SpaceMention("rest"), M("rest")))
    val out = Subst.mention(body, SpaceMention("outer"), M("rest"))
    // the substituted occurrence must still be the OUTER `rest`, i.e. free in the result
    assert(freeM(out).contains("rest"),
      s"the replacement's free `rest` is no longer free — it was CAPTURED by the Iteration.\n  $out")
    // and the binder must have been renamed away from `rest`
    assert(!bindersOf(out).contains("rest"),
      s"the Iteration still binds `rest`, so the replacement's free occurrence is captured.\n  $out")
    assert(bindersOf(out).exists(_.startsWith("~")),
      s"no fresh `~`-prefixed binder appears, so no alpha-rename happened.\n  $out")
  }

  test("A2. Iteration's `symbol` is alpha-renamed when the replacement's free REF would be caught") {
    // subst on the PATH side: the replacement path mentions `y`, and the Iteration binds `y`.
    val body = Union(Singleton(D("outerRef")), Iteration(lit(p("a")), PathRef("y"), SpaceMention("r"),
                                                          Singleton(D("y"))))
    val out = Subst.pathRef(body, PathRef("outerRef"), D("y"))
    assert(freeR(out).contains("y"),
      s"the replacement's free ref `y` was CAPTURED by the Iteration's symbol.\n  $out")
    assert(!bindersOf(out).contains("y"), s"the Iteration still binds `y`.\n  $out")
  }

  test("A3. Fixpoint's `rec` is alpha-renamed on capture") {
    val body = Union(M("outer"), Fixpoint(lit(p("a")), SpaceMention("rec"), M("rec")))
    val out = Subst.mention(body, SpaceMention("outer"), M("rec"))
    assert(freeM(out).contains("rec"), s"the replacement's free `rec` was CAPTURED.\n  $out")
    assert(!bindersOf(out).contains("rec"), s"the Fixpoint still binds `rec`.\n  $out")
  }

  test("A4. Fold's THREE binders are each alpha-renamed on capture, independently") {
    def fold(inner: Space, upd: Path) =
      Fold(lit(p("a")), K, PathRef("acc"), PathRef("sym"), SpaceMention("rest"), inner, upd)
    // (a) `rest` — a mention replacement
    val bodyR = Union(M("outer"), fold(M("rest"), K))
    val outR = Subst.mention(bodyR, SpaceMention("outer"), M("rest"))
    assert(freeM(outR).contains("rest") && !bindersOf(outR).contains("rest"),
      s"Fold's `rest` did not avoid capture.\n  $outR")
    // (b) `acc` — a ref replacement
    val bodyA = Union(Singleton(D("outerRef")), fold(Empty, D("acc")))
    val outA = Subst.pathRef(bodyA, PathRef("outerRef"), D("acc"))
    assert(freeR(outA).contains("acc") && !bindersOf(outA).contains("acc"),
      s"Fold's `acc` did not avoid capture.\n  $outA")
    // (c) `symbol` — a ref replacement
    val bodyS = Union(Singleton(D("outerRef")), fold(Singleton(D("sym")), K))
    val outS = Subst.pathRef(bodyS, PathRef("outerRef"), D("sym"))
    assert(freeR(outS).contains("sym") && !bindersOf(outS).contains("sym"),
      s"Fold's `symbol` did not avoid capture.\n  $outS")
  }

  test("A5. capture avoidance PRESERVES the binder's hints") {
    // `lengthHint`/`sizeHint` are facts about the VALUE a name denotes, not about the name.  A rename
    // that dropped them would weaken every size and length bound downstream with no test failing:
    // the terms still denote the same thing, only the ANALYSIS gets worse.
    val body = Union(M("outer"), Iteration(lit(p("a")), PathRef("y").known(1),
                                            SpaceMention("rest").known(7), M("rest")))
    val out = Subst.mention(body, SpaceMention("outer"), M("rest"))
    val renamed = out match
      case Union(_, Iteration(_, sym, rest, _)) => (sym, rest)
      case other => fail(s"unexpected shape: $other")
    assertEquals(renamed._2.sizeHint, 7L,
      "the renamed `rest` lost its sizeHint — every size bound below it silently weakens")
    assertEquals(renamed._1.lengthHint, 1,
      "the un-renamed `symbol` lost its lengthHint")
  }

  test("A6. capture avoidance is SEMANTICS-PRESERVING, through all three executors") {
    // A closed instance of A1's shape.  `outer` is bound to a literal by the environment; if the
    // Iteration captured it, the body would read the loop's tail-set instead and the answer changes.
    val prog = Iteration(lit(p("h", "t1"), p("h", "t2")), PathRef("y"), SpaceMention("rest"),
                         Union(M("outer"), M("rest")))
    // substitute `outer := Mention("rest")` where the OUTER `rest` is an input, then close both
    val substituted = Subst.mention(prog, SpaceMention("outer"), M("rest"))
    val env = SpaceContextMap(Map(SpaceMention("rest") -> SpaceValue(Set(p("z")))))
    // the CORRECT reading: `outer` becomes the environment's `rest`, so `z` is in the answer
    given SpaceContext = env
    val got = eval(substituted)
    assert(got.paths.contains(p("z")),
      s"`z` is absent, so the substituted `rest` was captured by the Iteration binder: ${got.show}")
    // and the three executors agree
    assertEquals(evalI(substituted)(using summon[PathContext],
      Map(SpaceMention("rest") -> ITrie.fromSpaceValue(SpaceValue(Set(p("z"))))),
      PartialFunction.empty).toSpaceValue, got, "evalI disagrees after capture avoidance")
  }

  // ================================================================================================
  // B. SHADOWING — the mirror image: an inner binder REBINDS the substituted name.
  // ================================================================================================

  test("B1. substitution does NOT descend into a scope that rebinds the name (Iteration)") {
    // `rest` is rebound by the inner Iteration, so the inner `Mention(rest)` is the INNER one.
    val body = Union(M("rest"), Iteration(lit(p("a")), PathRef("y"), SpaceMention("rest"), M("rest")))
    val out = Subst.mention(body, SpaceMention("rest"), lit(p("REPLACED")))
    out match
      case Union(l, Iteration(_, _, rest2, inner)) =>
        assertEquals(l, lit(p("REPLACED")), "the FREE occurrence was not substituted")
        assertEquals(rest2.s, "rest", "the binder was renamed although nothing needed avoiding")
        assertEquals(inner, M("rest"),
          "the SHADOWED occurrence was substituted — it belongs to the inner binder, and rewriting " +
          "it changes what the inner loop computes")
      case other => fail(s"unexpected shape: $other")
  }

  test("B2. the same for Fixpoint's `rec` and Fold's three binders") {
    val fx = Union(M("rec"), Fixpoint(lit(p("a")), SpaceMention("rec"), M("rec")))
    Subst.mention(fx, SpaceMention("rec"), lit(p("R"))) match
      case Union(l, Fixpoint(_, _, inner)) =>
        assertEquals(l, lit(p("R")), "Fixpoint: the free occurrence was not substituted")
        assertEquals(inner, M("rec"), "Fixpoint: the shadowed occurrence WAS substituted")
      case other => fail(s"unexpected shape: $other")
    val fd = Union(M("rest"), Fold(lit(p("a")), K, PathRef("acc"), PathRef("sym"),
                                    SpaceMention("rest"), M("rest"), K))
    Subst.mention(fd, SpaceMention("rest"), lit(p("R"))) match
      case Union(l, Fold(_, _, _, _, _, inner, _)) =>
        assertEquals(l, lit(p("R")), "Fold: the free occurrence was not substituted")
        assertEquals(inner, M("rest"), "Fold: the shadowed occurrence WAS substituted")
      case other => fail(s"unexpected shape: $other")
    // and the ref side: `acc`/`sym` shadow a path-ref substitution over `templates` and `update`
    val fr = Union(Singleton(D("acc")), Fold(lit(p("a")), D("acc"), PathRef("acc"), PathRef("sym"),
                                              SpaceMention("r"), Singleton(D("acc")), D("acc")))
    Subst.pathRef(fr, PathRef("acc"), K) match
      case Union(Singleton(l), Fold(_, ini, _, _, _, tmpl, upd)) =>
        assertEquals(l, K, "the free ref occurrence was not substituted")
        assertEquals(ini, K, "Fold's `initial` is OUTSIDE the acc binder and must be substituted")
        assertEquals(tmpl, Singleton(D("acc")), "Fold's `templates` is inside the binder — shadowed")
        assertEquals(upd, D("acc"), "Fold's `update` is inside the binder — shadowed")
      case other => fail(s"unexpected shape: $other")
  }

  test("B3. the source of a binding form is OUTSIDE its scope and IS substituted") {
    // The binder rules, as behaviour: `Iteration.src`, `Fixpoint.init` and `Fold.src`/`initial` are
    // evaluated outside the binder, so a shadowing binder must not stop them being substituted.
    // `substMention`'s own header states these rules; this is the check that it still obeys them.
    val it = Iteration(M("rest"), PathRef("y"), SpaceMention("rest"), M("rest"))
    Subst.mention(it, SpaceMention("rest"), lit(p("R"))) match
      case Iteration(src, _, _, body) =>
        assertEquals(src, lit(p("R")), "Iteration's SOURCE was not substituted (it is outside the binder)")
        assertEquals(body, M("rest"), "Iteration's body was substituted despite the shadow")
      case other => fail(s"unexpected shape: $other")
    val fx = Fixpoint(M("rec"), SpaceMention("rec"), M("rec"))
    Subst.mention(fx, SpaceMention("rec"), lit(p("R"))) match
      case Fixpoint(init, _, body) =>
        assertEquals(init, lit(p("R")), "Fixpoint's INIT was not substituted")
        assertEquals(body, M("rec"), "Fixpoint's body was substituted despite the shadow")
      case other => fail(s"unexpected shape: $other")
  }

  // ================================================================================================
  // C. SIMULTANEITY — the `g(y,x)` case, which sequential substitution gets wrong.
  // ================================================================================================

  test("C1. `g(y,x)`: simultaneous substitution is NOT sequential composition") {
    // A routine `g(a, b)` whose body uses both formals, called with the formals SWAPPED.
    val a = SpaceMention("a"); val b = SpaceMention("b")
    val body = Union(Mention(a), Wrap(Mention(b), K))
    val simultaneous = Subst(body, Map(a -> Mention(b), b -> Mention(a)))
    // sequential, the way `Lower.inline` used to do it
    var seq = body
    for (mn, arg) <- Vector(a -> Mention(b), b -> Mention(a)) do seq = Subst.mention(seq, mn, arg)
    assertEquals(simultaneous, Union(Mention(b), Wrap(Mention(a), K)),
      "simultaneous substitution did not swap the two arguments")
    assertNotEquals(seq, simultaneous,
      "sequential and simultaneous agreed on `g(b,a)`, so this test is not exercising the case it " +
      "exists for — the whole point is that they differ here")
    assertEquals(seq, Union(Mention(a), Wrap(Mention(a), K)),
      "the sequential result is not the expected WRONG one; the regression's shape has changed")
  }

  test("C2. the same hazard ACROSS the two sorts") {
    // A path argument naming a mention formal's binder, and a mention argument naming a ref formal.
    // Two separate loops (one per sort) resolve these in whichever order they happen to run.
    val m = SpaceMention("m"); val r = PathRef("r")
    val body = Union(Mention(m), Singleton(Path.Deref(r)))
    val out = Subst(body, Map(m -> Singleton(Path.Deref(r))), Map(r -> Path.Constant(p("c"))))
    assertEquals(out, Union(Singleton(Path.Deref(r)), Singleton(Path.Constant(p("c")))),
      "the mention's replacement had its free ref rewritten by the path map — the two sorts were " +
      "not applied simultaneously, so a replacement was substituted INTO")
  }

  test("C3. `Lower.inline` itself is simultaneous — the regression, end to end") {
    // The actual pass, not a re-implementation: a routine called with its own formals swapped.
    val g = RoutinePtr("g")
    val a = SpaceMention("a"); val b = SpaceMention("b")
    val routine = Routine(g, Vector.empty, Vector(a, b), Union(Mention(a), Wrap(Mention(b), K)))
    val rc: PartialFunction[RoutinePtr, Routine] = { case `g` => routine }
    // call g(X, Y) with two DISTINGUISHABLE arguments named after the formals
    val call = Call(g, Vector.empty, Vector(Mention(b), Mention(a)))
    val inlined = AgnosticPipeline.unrollControl(call, 2)(using rc)
    assertEquals(inlined, Union(Mention(b), Wrap(Mention(a), K)),
      "`unrollControl` collapsed the two swapped arguments into one variable — the sequential " +
      "one-parameter-at-a-time inline is back")
  }

  test("C4. inlining agrees with calling, on the swapped-argument routine, in all three executors") {
    val g = RoutinePtr("g")
    val a = SpaceMention("a"); val b = SpaceMention("b")
    val routine = Routine(g, Vector.empty, Vector(a, b), Union(Mention(a), Wrap(Mention(b), K)))
    val rc: PartialFunction[RoutinePtr, Routine] = { case `g` => routine }
    val call = Call(g, Vector.empty, Vector(lit(p("X")), lit(p("Y"))))
    given PartialFunction[RoutinePtr, Routine] = rc
    given SpaceContext = SpaceContextMap(Map.empty)
    val direct = eval(call)
    val inlined = eval(AgnosticPipeline.unrollControl(call, 2)(using rc))
    assertEquals(inlined, direct, "inlining and calling disagree on the swapped-argument routine")
    // `Union(X, Wrap(Y, k))` = {X} ∪ {k.Y}
    assertEquals(direct, SpaceValue(Set(p("X"), p("k", "Y"))),
      s"the call's own denotation is not what the routine says: ${direct.show}")
  }
end SubstCapture
