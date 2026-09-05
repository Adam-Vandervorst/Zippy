package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** SPILL / WIDENING SOUNDNESS (from the stop-ship finding).
 *
 *  The representation keeps per-length classes plus ONE spill bucket for "all other lengths".  The
 *  invariant that makes `at(l)` meaningful is that the spill's length range never covers a tracked
 *  length; before `SpatialTypes.disjoin` nothing enforced it, so a transfer that routes part of a
 *  length's paths into the spill (composition puts every rest-involving product there) left the
 *  tracked class counting only the rest — an UNSOUND per-length upper bound, not lost precision.
 *
 *  These tests deliberately exceed `MaxClasses`/`MaxLen` and then push the widened type through
 *  every operator, checking the per-length bounds and both projections against `eval`. */
class SpillSoundness extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def lit(ps: Iterable[PathValue]): Space = Space.Literal(SpaceValue(ps.toSet))
  /** a literal with `n` distinct path lengths — n > MaxClasses forces a spill */
  def manyLengths(n: Int, tag: String = "p"): Space =
    lit((0 until n).map(k => PathValue(List.fill(k)(s"$tag$k"))))
  def histogram(v: SpaceValue): Map[Long, Long] =
    v.paths.groupBy(_.items.length.toLong).view.mapValues(_.size.toLong).toMap

  /** every per-length class AND both projections must bracket the truth */
  def check(name: String, s: Space): Unit =
    val t = SpatialTypes.infer(s)
    val v = eval(s)
    val h = histogram(v)
    for (l, n) <- h do
      val c = t.at(l)
      assert(c.lo <= n && n <= c.hi,
             s"$name: $n paths of length $l outside ${c.show}\n  type = ${t.show}")
    for l <- t.byLen.keys do
      assert(t.at(l).lo <= h.getOrElse(l, 0L),
             s"$name: claimed ≥${t.at(l).lo} at length $l, found ${h.getOrElse(l, 0L)}\n  type = ${t.show}")
    val sz = t.size; val n = v.paths.size.toLong
    assert(sz.lo <= n && n <= sz.hi, s"$name: size ${sz} excludes $n\n  type = ${t.show}")
    val lb = t.len
    for l <- h.keys do assert(lb.lo <= l && l <= lb.hi, s"$name: len [${lb.lo}, ${lb.hi}] excludes $l")
    // the representation invariant itself: the spill must not cover a tracked length
    if t.rest.hi > 0 && !t.restLens.isEmpty then
      for l <- t.byLen.keys do
        assert(!(t.restLens.lo <= l && l <= t.restLens.hi),
               s"$name: INVARIANT BROKEN — spill [${t.restLens.lo}, ${t.restLens.hi}] covers tracked length $l")

  test("the review's reproducer: composition after spilling") {
    val a = manyLengths(25)
    val q = Space.Composition(a, a)                       // 49 output lengths ⇒ widening spills
    val b = lit(Set(PathValue(Nil), PathValue(List.fill(12)("c"))))
    val result = Space.Composition(q, b)
    check("reproducer", result)
    // the specific class the review names
    val t = SpatialTypes.infer(result)
    val actual = eval(result).paths.count(_.items.length == 24).toLong
    assert(t.at(24).lo <= actual && actual <= t.at(24).hi, s"len 24: $actual outside ${t.at(24).show}")
  }

  test("widened types stay sound through every operator") {
    val wide = Space.Composition(manyLengths(25), manyLengths(25))   // spilled
    val small = lit(Set(PathValue(Nil), PathValue(List("c")), PathValue(List.fill(12)("c"))))
    val tag = Path.Constant(PathValue(List("t1", "t2")))
    val cases = List(
      "comp-left"    -> Space.Composition(wide, small),
      "comp-right"   -> Space.Composition(small, wide),
      "comp-self"    -> Space.Composition(wide, wide),
      "union"        -> Space.Union(wide, small),
      "inter"        -> Space.Intersection(wide, small),
      "inter-self"   -> Space.Intersection(wide, wide),
      "sub"          -> Space.Subtraction(wide, small),
      "sub-rev"      -> Space.Subtraction(small, wide),
      "wrap"         -> Space.Wrap(wide, tag),
      "unwrap"       -> Space.Unwrap(Space.Wrap(wide, tag), tag),
      "tailsU"       -> Space.TailsUnion(wide),
      "tailsI"       -> Space.TailsIntersection(wide),
      "restrict"     -> Space.Restriction(wide, small),
      "raffinate"    -> Space.Raffination(wide, small),
      "range"        -> Space.Range(wide, 0, 5),
      "iter"         -> wide.iter(P"h", S"t", Space.Composition(Space.Singleton(P"h"), S"t")),
      "iter-nested"  -> wide.iter(P"h", S"t", S"t".iter(P"h2", S"t2", Space.Singleton(P"h2"))),
      "wrap-of-comp" -> Space.Wrap(Space.Composition(wide, small), tag),
      "deep"         -> Space.Union(Space.Composition(wide, small), Space.TailsUnion(Space.Wrap(wide, tag))),
    )
    for (name, s) <- cases do check(name, s)
    println(s"SPILL: ${cases.size} widened-operator cases sound (per-length, size, length, invariant)")
  }

  test("very long paths exceed MaxLen and stay sound") {
    val long = lit(Set(PathValue(List.fill(3)("a")), PathValue(List.fill(9000)("b"))))
    check("maxlen", long)
    check("maxlen-comp", Space.Composition(long, long))
    check("maxlen-tails", Space.TailsUnion(long))
    val t = SpatialTypes.infer(long)
    assert(t.byLen.keys.forall(_ <= SpatialTypes.MaxLen), s"a length over the cap stayed tracked: ${t.show}")
  }

  test("the class cap actually holds (constructors route through the widening)") {
    val t = SpaceType.of(eval(manyLengths(60)))
    assert(t.byLen.size <= SpatialTypes.MaxClasses, s"${t.byLen.size} classes > ${SpatialTypes.MaxClasses}")
    check("literal-60-lengths", manyLengths(60))
    // and a declared input type with too many classes is widened, not silently oversized
    val declared = SpaceType.closed((0L until 60L).map(l => l -> Ivl(1, 1))*)
    assert(declared.byLen.size <= SpatialTypes.MaxClasses, s"declared: ${declared.byLen.size} classes")
  }

  test("randomised spill/track collisions across operators") {
    val rng = new java.util.Random(77)
    val items = Vector("a", "b", "c")
    def randLit(maxLen: Int, k: Int): Space =
      lit((0 until k).map(_ => PathValue(List.fill(rng.nextInt(maxLen))(items(rng.nextInt(3))))))
    var checked = 0
    for i <- 0 until 60 do
      val x = randLit(30, 12)                     // wide length spread ⇒ spills after composition
      val y = randLit(6, 4)
      val base = if i % 2 == 0 then Space.Composition(x, y) else Space.Composition(x, x)
      val s = (i % 5) match
        case 0 => Space.Composition(base, y)
        case 1 => Space.Union(base, Space.TailsUnion(base))
        case 2 => Space.Intersection(base, Space.Composition(y, base))
        case 3 => Space.Wrap(Space.Subtraction(base, y), Path.Constant(PathValue(List("w"))))
        case _ => base.iter(P"h", S"t", Space.Composition(Space.Singleton(P"h"), S"t"))
      check(s"rand#$i", s); checked += 1
    println(s"SPILL-RANDOM: $checked randomised spill/track collision cases sound")
  }
end SpillSoundness

/** The remaining the review that are precision (not soundness) bugs. */
class ReviewFindings extends FunSuite:
  import Space.*
  import Lower.{LenBounds, SizeBounds}

  test("loops use the DECLARED input type, not just the syntactic baseline") {
    // the requirement: "With an environment stating that xs has exactly two length-one paths, iterating
    // {h} over xs evaluates to exactly two paths; this analysis returns { len 1: [0, inf] }"
    val prog = S"xs".iter(P"h", S"t", Space.Singleton(P"h"))
    val env = SpatialEnv(spaces = Map(SpaceMention("xs") -> SpaceType.closed(1L -> Ivl(2, 2))))
    val t = SpatialTypes.infer(prog, env)
    assertEquals(t.at(1).hi, 2L, s"upper must use the declared type: ${t.show}")
    assertEquals(t.len, LenBounds(1, 1))
    // sound against a matching instantiation
    given SpaceContext = SpaceContextMap(Map(SpaceMention("xs") ->
      SpaceValue(Set(PathValue(List("a")), PathValue(List("b"))))))
    val v = eval(prog)
    assert(t.size.lo <= v.paths.size && v.paths.size <= t.size.hi, s"${t.size} excludes ${v.paths.size}")
  }

  test("sizeOf/lenOf/bestSize pass the caller's env and routines through") {
    val r = Routine(RoutinePtr("dbl"), Vector.empty, Vector(SpaceMention("z")),
                    Space.Union(S"z", Space.Singleton(Path.Constant(PathValue(List("q"))))))
    val prog = Space.Call(RoutinePtr("dbl"), Vector.empty, Vector(Space.Mention(SpaceMention("in"))))
    val env = SpatialEnv(spaces = Map(SpaceMention("in") -> SpaceType.closed(1L -> Ivl(3, 3))),
                         routines = Syntax.mod(r))
    // with the routine table AND the input type, the call is analysed interprocedurally
    val sz = SpatialTypes.sizeOf(prog, env)
    assert(sz.hi <= 4L, s"expected ≤ 4 (3 + the singleton), got $sz")
    val ln = SpatialTypes.lenOf(prog, env)
    assertEquals((ln.lo, ln.hi), (1L, 1L))
    // and the plumbing must not be worse than tier-1 given the same information
    val b = Lower.sizeBounds(prog, env.routines)
    assert(sz.hi <= b.hi, s"sizeOf $sz looser than tier-1 $b")
  }

  test("fixpoint counts are widened before the union post-fixpoint check is accepted") {
    // a fixpoint whose body genuinely grows must not come back with a finite per-class count
    val init = Space.Literal(SpaceValue(Set(PathValue(List("a")))))
    val fx = Space.Fixpoint(init, SpaceMention("r"),
                            Space.Union(S"r", Space.Composition(S"r", init)))
    val t = SpatialTypes.infer(fx)
    assertEquals(t.size.hi, Ivl.INF, s"growing fixpoint must have an unbounded count: ${t.show}")
    assert(t.size.lo >= 1L, "and still at least the initial set")
  }
