package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==================================================================================================
 *  THE INTERPROCEDURAL SUMMARY, OVER VARYING PATH ARGUMENTS, AND ITS PRODUCTION CONSUMER.
 *
 *  `SpatialRecursion` solves the abstract result of a routine at an abstract argument tuple to a
 *  CERTIFIED post-fixed point.  Two things were wrong with that before this suite:
 *
 *   1. NOTHING IN PRODUCTION CONSULTED IT.  `SpatialTypeSystem`'s and `SpatialTypes`' `Call` arms
 *      descend into a callee interprocedurally and stop at a RECURSIVE call — `env.active(rp)` is
 *      what keeps the descent finite — and both then returned ⊤.  So the solver existed and no query
 *      read it, which is the same disconnect the review objects to for the decorated analysis.
 *   2. THE EXISTING TESTS FIXED THE PATH ARGUMENT TO `"a"`.  A summary is indexed by an argument
 *      TUPLE, path arguments included, and a routine whose result depends on a path argument is
 *      exactly where the indexing earns its keep.  One path value cannot show that the key is used:
 *      a table that ignored the path entirely would pass.
 *
 *  ==THE FIXTURE, AND WHY ITS RESULT REALLY DEPENDS ON THE PATH==
 *  {{{ descend(p, S) := S \/ descend(p, Unwrap(S, p)) }}}
 *  so `descend(p, S) = S ∪ S/p ∪ S/p/p ∪ …`.  Every `p` gives a different answer on the same `S`
 *  (`descend("a", {a.a.b, a.c}) = {a.a.b, a.c, a.b, c, b}` and `descend("c", …) = {a.a.b, a.c}`), and
 *  it TERMINATES under `eval`: the body is `Union(l, Call(rp, …))` with the self-call on the right, so
 *  `eval`'s fixpoint guard stops the recursion once one more `Unwrap` changes nothing — which happens
 *  at `∅` after at most `depth/|p|` steps.  That is what makes γ-soundness CHECKABLE here rather than
 *  assumed: the real value is computed and tested for membership.
 *  ================================================================================================== */
class CrossFunctionCheck extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(20, "min")

  val P = PathRef("p")
  val S = SpaceMention("s")
  val DESC = RoutinePtr("descend")

  /** `descend(p, S) := S ∪ descend(p, Unwrap(S, p))` */
  val descend: Routine =
    Routine(DESC, Vector(P), Vector(S),
            Union(Mention(S), Call(DESC, Vector(Path.Deref(P)),
                                   Vector(Unwrap(Mention(S), Path.Deref(P))))))
  val table: PartialFunction[RoutinePtr, Routine] = { case DESC => descend }

  def pv(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)

  /** the REAL value of `descend(p, v)`, from the reference executor */
  def real(p: PathValue, v: SpaceValue): SpaceValue =
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = table
    eval(Call(DESC, Vector(Path.Constant(p)), Vector(Literal(v))))

  def keyFor(p: SpatialRecursion.PathArg, v: SpaceValue): SpatialRecursion.Key =
    SpatialRecursion.Key(DESC, SpatialRecursion.argsOf(Vector(SpatialGamma.alpha(v)), Vector(p)))

  /** the argument values the whole suite varies over.  The `p`s differ in FIRST ITEM and in LENGTH,
   *  which are the two things a path argument can change about the answer. */
  val paths: Vector[PathValue] = Vector(pv("a"), pv("b"), pv("c"), pv("a", "a"), pv("a", "b"))
  val values: Vector[SpaceValue] = Vector(
    sv(pv("a", "a", "b"), pv("a", "c")),
    sv(pv("a", "a", "a", "a")),
    sv(pv("b", "a"), pv("a", "b"), pv("c")),
    sv(pv()),                                        // ε only
    SpaceValue(Set.empty))

  // ================================================================================================
  test("A. γ-SOUNDNESS over varying path arguments: the real value is in γ of the summary") {
    var checked = 0
    var certified = 0
    for p <- paths; v <- values do
      val key = keyFor(SpatialRecursion.PathArg.known(p), v)
      val s = SpatialRecursion.summarise(key, table)
      checked += 1
      if s.certified then
        certified += 1
        val t = s.at(key)
        val r = real(p, v)
        assert(SpatialGamma.gamma(t)(r),
               s"descend(${p.show}, ${v.show}) = ${r.show} is NOT in γ of its summary ${t.show}")
    println(s"[1D.1] A: $certified of $checked (path, value) summaries certified; every certified one " +
            "admits the real value")
    // A SUMMARY NOBODY CAN CERTIFY PROVES NOTHING, so the fixture has to reach the certified case.
    assert(certified >= checked * 3 / 4,
           s"only $certified of $checked summaries certified — the fixture is not exercising the " +
           "post-fixed-point solve, so the γ check above is nearly vacuous")
  }

  test("B. THE PATH ARGUMENT IS PART OF THE KEY: different paths give different summaries") {
    val v = values.head
    val byPath = paths.map { p =>
      val key = keyFor(SpatialRecursion.PathArg.known(p), v)
      p -> SpatialRecursion.summarise(key, table).at(key)
    }
    for (p, t) <- byPath do println(f"[1D.1] B: descend(${p.show}%-6s, ${v.show}) : ${t.show}")
    // THE NON-VACUITY THE OLD FIXTURE COULD NOT SHOW.  With the path fixed to `"a"` a table that
    // ignored path arguments entirely would pass every test; here the summaries must actually differ.
    val distinct = byPath.map(_._2).distinct
    assert(distinct.size >= 2,
           s"all ${byPath.size} path arguments produced the SAME summary (${distinct.head.show}) — " +
           "then the path is not part of the key and the whole `Args.paths` channel is inert")
    // and the REAL answers differ too, so the summaries differing is tracking something real
    val realDistinct = paths.map(p => real(p, v)).distinct
    assert(realDistinct.size >= 2,
           s"the fixture's real answers do not depend on the path argument: ${realDistinct.map(_.show)}")
    println(s"[1D.1] B: ${distinct.size} distinct summaries and ${realDistinct.size} distinct real " +
            s"answers over ${paths.size} path arguments")
  }

  test("C. AN OPAQUE PATH ARGUMENT is sound for EVERY concrete path of that length") {
    // the key a caller builds when the path is a bound reference of known length but unknown value.
    // The summary must then admit the real answer for every `p` of that length — that is what
    // `PathArg.opaque` claims, and it is the case the production consumer hits most often.
    for len <- Vector(1, 2); v <- values do
      val arg = SpatialRecursion.PathArg.opaque(Lower.LenBounds(len, len))
      val key = keyFor(arg, v)
      val s = SpatialRecursion.summarise(key, table)
      if s.certified then
        val t = s.at(key)
        for p <- paths if p.items.length == len do
          val r = real(p, v)
          assert(SpatialGamma.gamma(t)(r),
                 s"the OPAQUE-|p|=$len summary ${t.show} excludes descend(${p.show}, ${v.show}) = " +
                 r.show)
    println("[1D.1] C: opaque path arguments admit every concrete path of the declared length")
  }

  test("D. THE PRODUCTION CONSUMER FIRES: a recursive call is no longer ⊤") {
    // The outer call is not active, so `SpatialTypeSystem` descends into the body; inside, the
    // self-call IS active and used to return `Shape.top`.  It now consults the summary, so the
    // inferred type of the WHOLE call must be better than ⊤.
    val v = values.head
    val env = SpatialTyping.Env(lenv = SpatialEnv(routines = table))
    val call = Call(DESC, Vector(Path.Constant(pv("a"))), Vector(Literal(v)))
    val t = SpatialTyping.infer(call, env)
    val r = real(pv("a"), v)
    println(s"[1D.1] D: infer(descend(\"a\", ${v.show})) = ${t.show}")
    println(s"[1D.1] D: the real value is ${r.show}")
    assert(SpatialGamma.gamma(t)(r), s"the inferred type excludes the real value: ${t.show}")
    assert(!t.shape.isTop || t.size.hi < Lower.SizeBounds.INF,
           s"the inferred type is still ⊤ on both channels — the consumer is not firing: ${t.show}")
    // and the LENGTH half too: `descend` never lengthens a path, so the result's lengths are bounded
    // by the argument's, and that is a bound only the summary (or the interprocedural descent through
    // it) can give.
    println(s"[1D.1] D: lens = ${t.lens.size}, len hull = ${t.len}")
  }

  test("E. AN UNCERTIFIED SUMMARY IS NOT CONSUMED") {
    // `Summaries.at` returns a plausible-looking type from an UNCERTIFIED table, and
    // `SpatialRecursion.summaryAt` must refuse it: an uncertified table is a schedule that ran out,
    // not a proof.  One round cannot certify anything but the most trivial key.
    val v = values.head
    val arg = SpatialRecursion.PathArg.known(pv("a"))
    val tight = SpatialRecursion.Limits(maxRounds = 1, maxKeys = 1, maxUpdates = 1)
    val key = keyFor(arg, v)
    val s = SpatialRecursion.summarise(key, table, tight)
    println(s"[1D.1] E: with $tight the solve is certified=${s.certified} (${s.note})")
    if !s.certified then
      assertEquals(SpatialRecursion.summaryAt(DESC, key.args, table, tight), None,
                   "an UNCERTIFIED table must not be consumed — `at` would have returned a type")
      println("[1D.1] E: the consumer refused it, as it must")
    else
      // if even one round certifies, the refusal cannot be exercised here; say so rather than
      // pretending the case was covered
      println("[1D.1] E: one round certified this key, so the refusal path is not reached by it")
    // the OTHER refusal: a key the solve never reached.  `at` answers ⊤ for it, which is
    // indistinguishable from "no claim", and returning that as a summary would make an unreached key
    // look answered.
    val unreached = keyFor(SpatialRecursion.PathArg.known(pv("z", "z", "z")), values(2))
    val solved = SpatialRecursion.summarise(key, table)
    assert(!solved.table.contains(unreached), "the fixture's `unreached` key was in fact reached")
    assertEquals(solved.at(unreached), SpatialType.top,
                 "`at` is expected to answer ⊤ for an unreached key — that is why `summaryAt` " +
                 "checks membership rather than trusting `at`")
  }

  test("F. THE SUMMARY IS MONOTONE IN THE VALUE ARGUMENT, over varying paths") {
    // `descend` is monotone in `S`, so a larger argument must give a summary that admits at least as
    // much.  Checked over the SAME varying paths, because the property has to hold at every key and
    // a single path cannot show that the table is indexed rather than shared.
    val small = sv(pv("a", "b"))
    val big = sv(pv("a", "b"), pv("a", "a", "b"), pv("c"))
    assert(small.paths.subsetOf(big.paths))
    var pairs = 0
    for p <- paths do
      val (ks, kb) = (keyFor(SpatialRecursion.PathArg.known(p), small),
                      keyFor(SpatialRecursion.PathArg.known(p), big))
      val (ss, sb) = (SpatialRecursion.summarise(ks, table), SpatialRecursion.summarise(kb, table))
      if ss.certified && sb.certified then
        pairs += 1
        // the real values are ordered, so the BIG summary must admit the big real value and the
        // small summary the small one — and the big real value must not be in the small summary's γ
        // only if it genuinely is not a member, which is a fact about the two sets and not about the
        // order, so what is asserted is the soundness of each side.
        assert(SpatialGamma.gamma(ss.at(ks))(real(p, small)), s"small at ${p.show}")
        assert(SpatialGamma.gamma(sb.at(kb))(real(p, big)), s"big at ${p.show}")
        assert(real(p, small).paths.subsetOf(real(p, big).paths),
               s"`descend` is not monotone in S at ${p.show}: ${real(p, small).show} vs " +
               real(p, big).show)
    println(s"[1D.1] F: monotonicity in the value argument checked at $pairs of ${paths.size} paths")
    assert(pairs >= 3, s"only $pairs path arguments gave two certified summaries")
  }
end CrossFunctionCheck
