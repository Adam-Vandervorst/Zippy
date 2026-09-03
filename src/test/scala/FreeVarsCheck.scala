package morkl

import munit.FunSuite

/** FREE VARIABLES, AND THE MONOTONICITY GATE THAT DEPENDS ON THEM.
 *
 *  `AgnosticPipeline.usesMention` and `usesPathRef` answer "is this name free in this term". They
 *  are not bookkeeping: [[AgnosticPipeline.monotoneInMention]] decides variance with
 *
 *      case other => !free(other)          // Range / Call / Fold / grounded: unknown variance
 *
 *  i.e. it is CONSERVATIVE by asking whether the recursion variable occurs in a node whose variance
 *  it cannot reason about. A `free` that answers `false` for a name that IS there inverts that: the
 *  node comes out MONOTONE, and monotonicity is the side condition under which an emitter may give
 *  a `Space.Fixpoint` a first-class least-post-fixpoint denotation at all
 *  (`terminating/fixpoint_is_lfp.smt2`, O1; `AgSmt.fixSym`, `renderZ`, `formalOf` all gate on it).
 *
 *  BOTH FUNCTIONS HAD THAT HOLE. Each ended in `case _ => false`, and `Fold`, `Call`, `GroundedPS`
 *  and `GroundedSS` fell into it — so `monotoneInMention(Fold(src = Mention(m), …), m)` returned
 *  `true`. Found while making `expandKeepBinders` evaluate only closed subterms: it asked `free`
 *  which nodes read an enclosing binder, was told "none", evaluated a `Fold` that did, and n-queens
 *  died with `key not found: PathRef(q)` inside `eval`.
 *
 *  This file pins both directions for every constructor: the name IS found where it occurs free,
 *  and is NOT found where a binder shadows it.
 */
class FreeVarsCheck extends FunSuite:
  import Space.*
  import AgnosticPipeline.{monotoneInMention, usesMention, usesPathRef}

  private val m = SpaceMention("m")
  private val mm: Space = Mention(m)
  private val other: Space = Mention(SpaceMention("other"))
  private val q = PathRef("q").known(1)
  private val dq: Path = Path.Deref(q)
  private val k = Path.Constant(PathValue(List("k")))
  private val lit: Space = Literal(SpaceValue(Set(PathValue(List("a")))))
  private def fold(src: Space, rest: SpaceMention, body: Space, sym: PathRef = PathRef("h").known(1),
                   acc: PathRef = PathRef("acc"), initial: Path = k, upd: Path = k) =
    Fold(src, initial, acc, sym, rest, body, upd)

  // ------------------------------------------------------------------------------------------
  test("usesMention finds the name in EVERY constructor that can carry it") {
    val cases: Vector[(String, Space)] = Vector(
      "Mention" -> mm,
      "Union" -> Union(lit, mm),
      "Intersection" -> Intersection(lit, mm),
      "Subtraction" -> Subtraction(lit, mm),
      "Restriction" -> Restriction(lit, mm),
      "Raffination" -> Raffination(lit, mm),
      "Composition" -> Composition(lit, mm),
      "Wrap" -> Wrap(mm, k),
      "Unwrap" -> Unwrap(mm, k),
      "TailsUnion" -> TailsUnion(mm),
      "TailsIntersection" -> TailsIntersection(mm),
      "Iteration (source)" -> Iteration(mm, PathRef("h").known(1), SpaceMention("t"), lit),
      "Iteration (body)" -> Iteration(lit, PathRef("h").known(1), SpaceMention("t"), mm),
      "Fixpoint (init)" -> Fixpoint(mm, SpaceMention("r"), lit),
      "Fixpoint (body)" -> Fixpoint(lit, SpaceMention("r"), mm),
      "Fold (source)" -> fold(mm, SpaceMention("t"), lit),
      "Fold (body)" -> fold(lit, SpaceMention("t"), mm),
      "Call (argument)" -> Call(RoutinePtr("r"), Vector.empty, Vector(mm)),
      "GroundedSS" -> GroundedSS(mm, identity),
      "Range" -> Range(mm, 0, 1),
    )
    val missed = cases.filterNot((_, s) => usesMention(s, "m")).map(_._1)
    assertEquals(missed, Vector.empty[String],
      s"usesMention says `m` is not free in: ${missed.mkString(", ")} — every one of these is a " +
      "node monotoneInMention would then call MONOTONE")
  }

  test("usesMention respects the binders — a shadowed name is NOT free") {
    val h = PathRef("h").known(1)
    assert(!usesMention(Iteration(lit, h, m, mm), "m"), "Iteration's `rest` must shadow")
    assert(!usesMention(Fixpoint(lit, m, mm), "m"), "Fixpoint's `rec` must shadow")
    assert(!usesMention(fold(lit, m, mm), "m"), "Fold's `rest` must shadow")
    // ...but only in the body: the source is outside the binder
    assert(usesMention(Iteration(mm, h, m, lit), "m"), "Iteration's SOURCE is outside the binder")
    assert(usesMention(Fixpoint(mm, m, lit), "m"), "Fixpoint's INIT is outside the binder")
    assert(usesMention(fold(mm, m, lit), "m"), "Fold's SOURCE is outside the binder")
  }

  test("usesPathRef finds the ref in EVERY constructor that can carry it") {
    val cases: Vector[(String, Space)] = Vector(
      "Singleton" -> Singleton(dq),
      "Singleton (inside a Concat)" -> Singleton(Path.Concat(k, dq)),
      "Wrap (path)" -> Wrap(lit, dq),
      "Unwrap (path)" -> Unwrap(lit, dq),
      "Union" -> Union(lit, Singleton(dq)),
      "TailsUnion" -> TailsUnion(Singleton(dq)),
      "Iteration (source)" -> Iteration(Singleton(dq), PathRef("h").known(1), SpaceMention("t"), lit),
      "Iteration (body)" -> Iteration(lit, PathRef("h").known(1), SpaceMention("t"), Singleton(dq)),
      "Fixpoint (init)" -> Fixpoint(Singleton(dq), SpaceMention("r"), lit),
      "Fixpoint (body)" -> Fixpoint(lit, SpaceMention("r"), Singleton(dq)),
      "Fold (source)" -> fold(Singleton(dq), SpaceMention("t"), lit),
      "Fold (body)" -> fold(lit, SpaceMention("t"), Singleton(dq)),
      "Fold (initial)" -> fold(lit, SpaceMention("t"), lit, initial = dq),
      "Fold (update)" -> fold(lit, SpaceMention("t"), lit, upd = dq),
      "Call (path argument)" -> Call(RoutinePtr("r"), Vector(dq), Vector.empty),
      "Call (space argument)" -> Call(RoutinePtr("r"), Vector.empty, Vector(Singleton(dq))),
      "GroundedPS" -> GroundedPS(dq, _ => SpaceValue(Set.empty)),
      "GroundedSS" -> GroundedSS(Singleton(dq), identity),
      "Range" -> Range(Singleton(dq), 0, 1),
    )
    val missed = cases.filterNot((_, s) => usesPathRef(s, "q")).map(_._1)
    assertEquals(missed, Vector.empty[String],
      s"usesPathRef says `q` is not free in: ${missed.mkString(", ")}")
  }

  test("usesPathRef respects the binders — Fold binds BOTH acc and symbol, Fixpoint binds neither") {
    // `Fold` binds `acc` and `symbol` over `templates` AND `update`
    assert(!usesPathRef(fold(lit, SpaceMention("t"), Singleton(dq), acc = q), "q"), "Fold's `acc` must shadow the body")
    assert(!usesPathRef(fold(lit, SpaceMention("t"), Singleton(dq), sym = q), "q"), "Fold's `symbol` must shadow the body")
    assert(!usesPathRef(fold(lit, SpaceMention("t"), lit, acc = q, upd = dq), "q"), "…and the update")
    // `initial` is evaluated OUTSIDE them
    assert(usesPathRef(fold(lit, SpaceMention("t"), lit, acc = q, initial = dq), "q"),
           "Fold's `initial` is outside the binders")
    // `Iteration` binds only `symbol`; `Fixpoint`'s binder is a space mention and shadows no ref
    assert(!usesPathRef(Iteration(lit, q, SpaceMention("t"), Singleton(dq)), "q"), "Iteration's `symbol` must shadow")
    assert(usesPathRef(Fixpoint(lit, SpaceMention("q"), Singleton(dq)), "q"),
           "a Fixpoint binds a SPACE mention and must not shadow a path ref of the same name")
  }

  // ------------------------------------------------------------------------------------------
  test("THE CONSEQUENCE: monotoneInMention is CONSERVATIVE on Fold, Call, Range and grounded") {
    // each of these reads `m` in a node whose variance the gate cannot reason about, so the honest
    // answer is "not known monotone".  With the pre-fix `case _ => false` in `usesMention`, every
    // one of them answered `true`.
    val unknown: Vector[(String, Space)] = Vector(
      "Fold over m" -> fold(mm, SpaceMention("t"), lit),
      "Fold whose body reads m" -> fold(lit, SpaceMention("t"), mm),
      "Call passing m" -> Call(RoutinePtr("r"), Vector.empty, Vector(mm)),
      "grounded over m" -> GroundedSS(mm, identity),
      "Range over m" -> Range(mm, 0, 1),
    )
    val wrong = unknown.filter((_, s) => monotoneInMention(s, m)).map(_._1)
    assertEquals(wrong, Vector.empty[String],
      s"monotoneInMention calls these MONOTONE: ${wrong.mkString(", ")} — each would then be given " +
      "a first-class least-post-fixpoint denotation whose axioms need not hold of the executor")
    // and it stays PERMISSIVE where it should be: the same nodes over a DIFFERENT mention are fine
    for (why, s) <- unknown do
      assert(monotoneInMention(s, SpaceMention("unrelated")),
             s"$why: the gate must not reject a term that does not mention the recursion variable")
    // the genuinely monotone algebra is still accepted
    assert(monotoneInMention(Union(mm, TailsUnion(mm)), m), "union/tails-union is monotone in m")
    assert(!monotoneInMention(Subtraction(lit, mm), m), "m under a subtrahend is ANTITONE")
    assert(!monotoneInMention(TailsIntersection(mm), m), "m under TailsIntersection is not monotone")
  }
end FreeVarsCheck
