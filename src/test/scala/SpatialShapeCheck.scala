package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** THE SPATIAL TYPE SYSTEM — the shape component (a bounded abstract trie) reduced against the
 *  length/count histogram.  These tests are the review's own probes, the corpus soundness gate, and
 *  a randomized per-operator differential matrix.
 *
 *  The gates assert γ-MEMBERSHIP (`SpatialTyping.gammaMember`), not the weaker dispatcher check:
 *  the concrete value produced by `eval` must satisfy every one of the shape's four channels (ε,
 *  each tracked head, the untracked-head count, the other-tail summary) and the histogram's
 *  representation invariant.  `eval` appears ONLY here, as ground truth — never inside the
 *  analysis (docs/design_spatial_lattice.md §0). */
class SpatialShapeCheck extends FunSuite:
  import Space.*
  import Lower.{LenBounds, SizeBounds}
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
  def p(items: String*): PathValue = PathValue(items.toList)
  /** iterate and return the group head — the classic head-count observation */
  def headsOf(s: Space): Space =
    Space.Iteration(s, PathRef("h").known(1), SpaceMention("_"),
                    Space.Singleton(Path.Deref(PathRef("h").known(1))))

  test("review probe 1: shape distinguishes spaces a length histogram cannot") {
    val a = lit(p("a", "0"), p("a", "1"), p("a", "2"), p("a", "3"))   // ONE head
    val b = lit(p("a", "0"), p("b", "0"), p("c", "0"), p("d", "0"))   // FOUR heads
    // the histogram alone: identical
    assertEquals(SpatialTypes.infer(a).show, SpatialTypes.infer(b).show)
    // the spatial type: different, in BOTH directions now that the must channels are back
    assertEquals(SpatialTyping.infer(a).headCount, Ivl(1, 1))
    assertEquals(SpatialTyping.infer(b).headCount, Ivl(4, 4))
    val (ta, tb) = (SpatialTyping.infer(headsOf(a)), SpatialTyping.infer(headsOf(b)))
    assertEquals(ta.size.hi, 1L, s"A heads: ${ta.show}")
    assertEquals(tb.size.hi, 4L, s"B heads: ${tb.show}")
    assert(ta.size.hi < tb.size.hi, "the two must be distinguishable")
    assertEquals(eval(headsOf(a)).paths.size, 1)
    assertEquals(eval(headsOf(b)).paths.size, 4)
    // and the MUST direction is exact too
    assertEquals(ta.size.lo, 1L); assertEquals(tb.size.lo, 4L)
  }

  test("review probe 2: an absent prefix is PROVED absent") {
    // Unwrap(Literal({b}), "a") is empty — the histogram says {len 0: [0,1]} and cannot see it
    val x = Space.Unwrap(lit(p("b")), Path.Constant(p("a")))
    assert(!SpatialTypes.infer(x).isProvablyEmpty, "precondition: the histogram cannot prove this")
    assert(SpatialTyping.infer(x).isProvablyEmpty, s"shape must prove it empty: ${SpatialTyping.infer(x).show}")
    assertEquals(eval(x), SpaceValue(Set.empty))
    assert(Fact.from(SpatialTyping.infer(x)).contains(Fact.DefinitelyEmpty))
    // and a prefix that IS present is not falsely proved absent
    val y = Space.Unwrap(lit(p("a", "z")), Path.Constant(p("a")))
    assert(!SpatialTyping.infer(y).isProvablyEmpty)
    assertEquals(eval(y), SpaceValue(Set(p("z"))))
  }

  test("intersection of disjoint head sets is provably empty") {
    val l = lit(p("a", "x"), p("b", "y"))
    val r = lit(p("c", "x"), p("d", "y"))
    assert(SpatialTyping.infer(Space.Intersection(l, r)).isProvablyEmpty)
    assertEquals(eval(Space.Intersection(l, r)), SpaceValue(Set.empty))
    // overlapping heads are NOT proved empty
    assert(!SpatialTyping.infer(Space.Intersection(l, lit(p("a", "x")))).isProvablyEmpty)
  }

  test("validated facts, not raw numbers (the empty-space len.lo trap)") {
    val e = SpatialTyping.infer(Space.Empty)
    // the raw marker would read INF >= 3 and "prove" three items in an empty space
    assert(e.len.lo >= 3, "precondition: the raw length marker is misleading")
    assertEquals(Fact.from(e), Vector(Fact.DefinitelyEmpty), "facts must not license a length claim")
    val ne = SpatialTyping.infer(lit(p("a", "b", "c"), p("a", "b", "d")))
    val fs = Fact.from(ne)
    assert(fs.contains(Fact.DefinitelyNonEmpty))
    assert(fs.contains(Fact.AllPathsHaveAtLeast(3)))
    assert(fs.contains(Fact.MaximumPathLength(3)))
    assert(fs.contains(Fact.ExactHeadSet(Set("a"))))
    assert(fs.contains(Fact.MaximumHeadCount(1)))
    assert(fs.contains(Fact.MinimumHeadCount(1)))
  }

  test("declared input SHAPES flow through, and specialisation keeps its precondition") {
    // xs : heads exactly {a, b}; so iterating heads yields at most 2 paths
    val xsShape = Shape.of(SpaceValue(Set(p("a", "1"), p("b", "1"))))
    val env = SpatialTyping.Env(spaces = Map(SpaceMention("xs") -> SpatialType(xsShape, SpaceType.unknown)))
    val t = SpatialTyping.infer(headsOf(S"xs"), env)
    assertEquals(t.size.hi, 2L, s"declared shape must bound the group count: ${t.show}")
    // the precondition is DATA, and decides actual inputs
    val r = Routine(RoutinePtr("f"), Vector.empty, Vector(SpaceMention("xs")), headsOf(S"xs"))
    val spec = SpatialTyping.SpecializedRoutine(
      Map(SpaceMention("xs") -> SpatialType(xsShape, SpaceType.of(SpaceValue(Set(p("a", "1"), p("b", "1")))))), r, Fact.from(t))
    assert(spec.applicableTo(Map(SpaceMention("xs") -> SpaceValue(Set(p("a", "1"), p("b", "1"))))))
    assert(!spec.applicableTo(Map(SpaceMention("xs") -> SpaceValue(Set(p("z", "1"))))),
           "an input outside the precondition must be rejected, not silently accepted")
  }

  // ---------------------------------------------------------------------------------------------
  // the transfers the review asked for, each with the observation that shows it is not ⊤
  // ---------------------------------------------------------------------------------------------
  test("COMPOSITION grafts at the leaves (was ⊤)") {
    val x = lit(p("a"), p("b", "c"))
    val y = lit(p("z"), p("w"))
    val t = SpatialTyping.infer(Space.Composition(x, y))
    val v = eval(Space.Composition(x, y))
    assert(SpatialTyping.gammaMember(v, t), s"${v.pretty} not in ${t.show}")
    assertEquals(t.headCount, Ivl(2, 2), s"heads a and b, exactly: ${t.show}")
    assert(t.shape.headsClosed && t.shape.heads.keySet == Set("a", "b"))
    // the grafted tails are there: a.z and a.w, not a.a
    assert(t.shape.mayHavePrefix(List("a", "z")))
    assert(!t.shape.mayHavePrefix(List("a", "a")), s"a.a is impossible: ${t.shape.show}")
    assertEquals(t.size, SizeBounds(4, 4, 4), s"exact: ${t.show}")
  }

  test("COMPOSITION with an epsilon-carrying left factor keeps the right factor whole") {
    val x = lit(PathValue(Nil), p("a"))
    val y = lit(p("z"))
    val term = Space.Composition(x, y)
    val t = SpatialTyping.infer(term)
    assert(SpatialTyping.gammaMember(eval(term), t))
    assertEquals(eval(term), SpaceValue(Set(p("z"), p("a", "z"))))
    assertEquals(t.headCount, Ivl(2, 2), t.show)
  }

  test("RANGE is a may-only slice, and the identity window is exact") {
    val x = lit(p("a"), p("b"), p("c"))
    val whole = Space.Range(x, 0, 0)
    assertEquals(SpatialTyping.infer(whole).headCount, Ivl(3, 3), "the identity window keeps MUST")
    val one = Space.Range(x, 1, 2)
    val t = SpatialTyping.infer(one)
    assert(SpatialTyping.gammaMember(eval(one), t), s"${eval(one).pretty} not in ${t.show}")
    assertEquals(t.headCount.hi, 1L, s"a 1-wide window has at most one head: ${t.show}")
    assertEquals(t.headCount.lo, 0L, "and no lower bound: the window may be empty")
    assertEquals(t.size.hi, 1L, t.show)
  }

  test("FIXPOINT reaches a verified post-fixpoint instead of ⊤") {
    // the accumulator shrinks: init ∪ tails(init) ∪ tails(tails(init)) ...
    val term = Space.Fixpoint(lit(p("a", "b", "c")), SpaceMention("r"),
                              Space.TailsUnion(Space.Mention(SpaceMention("r"))))
    val t = SpatialTyping.infer(term)
    val v = eval(term)
    assert(SpatialTyping.gammaMember(v, t), s"${v.pretty} not in ${t.show}")
    assert(!t.shape.isTop, s"the shape must not degrade to ⊤: ${t.shape.show}")
    assert(t.shape.definitelyNonEmpty, s"init is contained, so the result is non-empty: ${t.shape.show}")
    assert(t.shape.mayHavePrefix(List("a", "b", "c")))
  }

  test("CALL is analysed interprocedurally (was ⊤)") {
    val m = SpaceMention("m$0")
    val f = Routine(RoutinePtr("f"), Vector.empty, Vector(m), Space.TailsUnion(Space.Mention(m)))
    val table: PartialFunction[RoutinePtr, Routine] = { case RoutinePtr("f") => f }
    val term = Space.Call(RoutinePtr("f"), Vector.empty, Vector(lit(p("a", "x"), p("a", "y"))))
    val env = SpatialTyping.Env(lenv = SpatialEnv(routines = table))
    val t = SpatialTyping.infer(term, env)
    val v = eval(term)(using rc = table)
    assert(SpatialTyping.gammaMember(v, t), s"${v.pretty} not in ${t.show}")
    assert(!t.shape.isTop, s"must not degrade to ⊤: ${t.shape.show}")
    assertEquals(t.shape.heads.keySet, Set("x", "y"), t.shape.show)
    assertEquals(t.headCount, Ivl(2, 2), t.show)
    // a recursive routine still degrades, and says so
    val g = Routine(RoutinePtr("g"), Vector.empty, Vector(m),
                    Space.Union(Space.Mention(m), Space.Call(RoutinePtr("g"), Vector.empty, Vector(Space.TailsUnion(Space.Mention(m))))))
    val t2 = SpatialTyping.shapeOf(Space.Call(RoutinePtr("g"), Vector.empty, Vector(lit(p("a")))),
                                   SpatialTyping.Env(lenv = SpatialEnv(routines = { case RoutinePtr("g") => g })))
    assert(!t2.definitelyEmpty, "a recursive call must widen, not vanish")
  }

  test("an UNKNOWN path of ANNOTATED length still carries shape information (was ⊤)") {
    val src = lit(p("a", "x"), p("a", "y"), p("b", "z"))
    val pr = PathRef("q").known(1)
    // Unwrap by an unknown ONE-item path: a subset of the level-1 tails union, closed head set
    val u = Space.Unwrap(src, Path.Deref(pr))
    val t = SpatialTyping.shapeOf(u)
    assert(!t.isTop, s"must not be ⊤: ${t.show}")
    assert(t.headsClosed, s"the head set is still closed: ${t.show}")
    assertEquals(t.heads.keySet, Set("x", "y", "z"), t.show)
    for it <- Vector("a", "b", "c") do
      val v = eval(u)(using pc = PathContextMap(Map(pr -> PathValue(List(it)))))
      assert(Shape.contains(t, v), s"ref=$it: ${v.pretty} not in ${t.show}")
    // Wrap by an unknown TWO-item path: exactly one head, and the depth structure survives
    val w = SpatialTyping.shapeOf(Space.Wrap(src, Path.Deref(PathRef("q2").known(2))))
    assertEquals(w.headCount, Ivl(1, 1), w.show)
    assertEquals(w.lens, LenBounds(4, 4), w.show)
  }

  test("TAILS-INTERSECTION does not intersect the children of MAY-present heads") {
    // {b.x, b.y} satisfies a shape that tracks heads a and b (a only MAY be present).  Intersecting
    // both children would claim the result is {x} and MISS y — the bug this arm exists to prevent.
    val sh = Shape.of(SpaceValue(Set(p("a", "x"), p("b", "x"), p("b", "y"))))
    val declared = SpatialType(Shape.weaken(sh), SpaceType.unknown)
    val env = SpatialTyping.Env(spaces = Map(SpaceMention("xs") -> declared))
    val term = Space.TailsIntersection(S"xs")
    val t = SpatialTyping.infer(term, env)
    val real = SpaceValue(Set(p("b", "x"), p("b", "y")))
    assert(Shape.contains(Shape.weaken(sh), real), "precondition: the value satisfies the declared shape")
    assert(Shape.contains(t.shape, SpaceValue(Set(p("x"), p("y")))),
           s"the true tails-intersection {x,y} must be admitted: ${t.shape.show}")
  }

  // ---------------------------------------------------------------------------------------------
  // GATE 1 — the corpus
  // ---------------------------------------------------------------------------------------------
  test("soundness: the concrete value satisfies the inferred type, on the corpus") {
    val recs = ShapeShrink.corpus
    assume(recs.nonEmpty, "corpus not found")
    var checked = 0; var headExact = 0; var shapeTighter = 0; var proved = 0
    val bad = Vector.newBuilder[(Space, String)]
    for (closed, i) <- ShapeShrink.instances(recs, 31337).zipWithIndex do
      val t = SpatialTyping.infer(closed)
      val v = eval(closed)
      ShapeShrink.violation(closed) match
        case Some(why) => bad += (closed -> why)
        case None => ()
      val realHeads = v.paths.collect { case PathValue(h :: _) => h }.toSet.size.toLong
      val hc = t.headCount
      if hc.lo == hc.hi then headExact += 1
      if t.size.hi < SpatialTypes.infer(closed).size.hi then shapeTighter += 1
      if t.isProvablyEmpty then proved += 1
      checked += 1
    val bs = bad.result()
    for (b, why) <- bs.take(3) do
      val m = ShapeShrink.shrink(b)
      println(s"SHAPE FAILURE: $why\n  shrunk to: ${ShapeShrink.safeShow(m)}\n  " +
        s"value ${eval(m).pretty}  type ${SpatialTyping.infer(m).show}")
    println(s"SHAPE CORPUS: $checked closed instances — γ-membership holds on ${checked - bs.size}; " +
      s"head count exact on $headExact; size strictly tighter than the histogram alone on $shapeTighter; " +
      s"provably empty on $proved")
    assertEquals(bs.size, 0, s"${bs.size} corpus instances escape their inferred type")
  }

  test("soundness: a second corpus sample, different seed") {
    val recs = ShapeShrink.corpus
    assume(recs.nonEmpty, "corpus not found")
    var checked = 0
    val bad = Vector.newBuilder[String]
    for closed <- ShapeShrink.instances(recs, 8675309) do
      ShapeShrink.violation(closed).foreach(w => bad += w)
      checked += 1
    val bs = bad.result()
    for w <- bs.take(3) do println("SHAPE FAILURE (seed 2): " + w)
    println(s"SHAPE CORPUS seed 2: $checked closed instances — γ-membership holds on ${checked - bs.size}")
    assertEquals(bs.size, 0, bs.take(3).mkString("; "))
  }

  /** the review measured `infer(...).size = [0,256]` against `sizeOf(...) = [0,4]` for a four-deep
   *  rest-chained iteration over four length-four paths — a public entry point 64x looser than
   *  another one on the same term.  The shape component closes that by construction: the group count
   *  is the DISTINCT-HEAD count, so a rest chain does not exponentiate. */
  test("PRECISION: the nested rest-chained iteration") {
    val src = lit(p("a", "b", "c", "d"), p("a", "b", "c", "e"), p("a", "b", "f", "g"), p("h", "i", "j", "k"))
    def chain(x: Space, d: Int): Space =
      if d == 0 then x
      else Space.Iteration(x, PathRef("h" + d).known(1), SpaceMention("r" + d),
                           Space.Wrap(chain(Space.Mention(SpaceMention("r" + d)), d - 1), Path.Deref(PathRef("h" + d).known(1))))
    val term = chain(src, 4)
    val real = eval(term)
    val hist = SpatialTypes.infer(term).size
    val t = SpatialTyping.infer(term)
    println(s"PRECISION nested-iteration: actual ${real.paths.size}; histogram alone [${hist.lo}, ${hist.hi}]; " +
      s"reduced product [${t.size.lo}, ${t.size.hi}]; SpatialTypes.sizeOf ${SpatialTypes.sizeOf(term)}")
    assert(SpatialTyping.gammaMember(real, t), s"${real.pretty} not in ${t.show}")
    assertEquals(real, src match { case Space.Literal(v) => v; case _ => real }, "the chain rebuilds its source")
    assert(t.size.hi <= hist.hi, "the product must never be looser than the histogram alone")
  }

  // ---------------------------------------------------------------------------------------------
  // GATE 2 — the randomized per-operator differential matrix
  // ---------------------------------------------------------------------------------------------
  test("the operator matrix: every operator, γ-membership of the real result") {
    val rng = new java.util.Random(4242)
    var total = 0
    val fails = collection.mutable.Map.empty[String, Int].withDefaultValue(0)
    val runs = collection.mutable.Map.empty[String, Int].withDefaultValue(0)
    val topped = collection.mutable.Map.empty[String, Int].withDefaultValue(0)
    val skipped = collection.mutable.Map.empty[String, Int].withDefaultValue(0)
    val examples = collection.mutable.Map.empty[String, String]
    for row <- OpMatrix.rows; mode <- 0 until 4; _ <- 0 until 400 do
      OpMatrix.trial(row, mode, rng, OpMatrix.randSV) match
        case None => skipped(row.name) += 1
        case Some((term, v, t)) =>
          total += 1; runs(row.name) += 1
          if t.shape.isTop then topped(row.name) += 1
          val ok = SpatialTyping.gammaMember(v, t)
          val realHeads = v.paths.collect { case PathValue(h :: _) => h }.toSet.size.toLong
          val hc = t.headCount
          val headOk = hc.lo <= realHeads && realHeads <= hc.hi
          if !ok || !headOk then
            fails(row.name) += 1
            if !examples.contains(row.name) then
              examples(row.name) = s"mode $mode  ${ShapeShrink.safeShow(term)}\n      value ${v.pretty}" +
                s"\n      type  ${t.show}\n      heads $realHeads vs ${hc.show}  (γ=$ok head=$headOk)"
    println(f"OPERATOR MATRIX: $total%d checks over ${OpMatrix.rows.size}%d operators x 4 modes")
    for row <- OpMatrix.rows do
      println(f"  ${row.name}%-18s runs=${runs(row.name)}%4d  top=${topped(row.name)}%4d  " +
        f"skipped=${skipped(row.name)}%4d  VIOLATIONS=${fails(row.name)}%d")
      examples.get(row.name).foreach(e => println("      " + e))
    assertEquals(fails.values.sum, 0, s"operator-matrix violations: ${fails.filter(_._2 > 0)}")
  }

  /** the two CAP boundaries the small alphabet never reaches: more than `Shape.MaxHeads` distinct
   *  heads (which forces the width spill into `others`/`otherTail`) and paths longer than
   *  `Shape.MaxDepth` (which forces `capDepth`).  Both are pure loosening in theory; this is the
   *  differential evidence. */
  test("the operator matrix on WIDE (head spill) and DEEP (past MaxDepth) operands") {
    val rng = new java.util.Random(777001)
    var total = 0; var bad = 0; var spilled = 0; var deep = 0
    var first: Option[String] = None
    for row <- OpMatrix.rows; mode <- 0 until 4; _ <- 0 until 120 do
      OpMatrix.trial(row, mode, rng, OpMatrix.randSVBig) match
        case None => ()
        case Some((term, v, t)) =>
          total += 1
          if !t.shape.headsClosed then spilled += 1
          if v.paths.exists(_.items.length > Shape.MaxDepth) then deep += 1
          val realHeads = v.paths.collect { case PathValue(h :: _) => h }.toSet.size.toLong
          val hc = t.headCount
          if !SpatialTyping.gammaMember(v, t) || realHeads < hc.lo || realHeads > hc.hi then
            bad += 1
            if first.isEmpty then first = Some(s"${row.name} mode $mode ${ShapeShrink.safeShow(term)}" +
              s"\n    value ${v.pretty}\n    type ${t.show}\n    heads $realHeads vs ${hc.show}")
    println(s"WIDE/DEEP MATRIX: $total checks, open head set on $spilled, over-MaxDepth paths on $deep, violations $bad")
    first.foreach(f => println("  witness: " + f))
    assertEquals(bad, 0, first.getOrElse(""))
  }

  test("the operator matrix over NESTED terms (depth 4)") {
    val rng = new java.util.Random(90210)
    var total = 0; var bad = 0; var tops = 0
    var first: Option[String] = None
    for _ <- 0 until 8000 do
      OpMatrix.nestedTrial(rng, 4) match
        case None => ()
        case Some((term, v, t)) =>
          total += 1
          if t.shape.isTop then tops += 1
          val realHeads = v.paths.collect { case PathValue(h :: _) => h }.toSet.size.toLong
          val hc = t.headCount
          if !SpatialTyping.gammaMember(v, t) || realHeads < hc.lo || realHeads > hc.hi then
            bad += 1
            if first.isEmpty then
              first = Some(s"${ShapeShrink.safeShow(ShapeShrink.shrink(term))}\n    value ${eval(term).pretty}" +
                s"\n    type ${t.show}")
    println(s"NESTED MATRIX: $total terms, ⊤ shape on $tops, violations $bad")
    first.foreach(f => println("  witness: " + f))
    assertEquals(bad, 0, first.getOrElse(""))
  }
end SpatialShapeCheck

/** The randomized operator matrix: one row per `Space` constructor, three environment modes, and a
 *  differential check of `eval` against `SpatialTyping.infer`.
 *
 *  mode 0 — operands are `Literal`s and paths are constants (a fully closed term);
 *  mode 1 — operands are mentions with declared types `α(v)` and paths are refs the abstract env
 *           knows the value of;
 *  mode 2 — the same, but the abstract env does NOT know the ref values, which exercises the
 *           unknown-path arms (`Singleton`/`Wrap` of an unknown path, `Unwrap` → ⊤). */
object OpMatrix:
  enum BK:
    case Plain, Iter, Fold, Fix

  final case class Row(name: String, ar: Int, par: Int, bk: BK,
                       mk: (Vector[Space], Vector[Path], Space) => Space)

  val sym: PathRef = PathRef("h$")
  val rest: SpaceMention = SpaceMention("r$")
  val acc: PathRef = PathRef("acc$")
  val recm: SpaceMention = SpaceMention("rec$")
  val opSpaces: Vector[SpaceMention] = Vector("s$0", "s$1").map(SpaceMention.apply)
  val opPaths: Vector[PathRef] = Vector("p$0", "p$1").map(PathRef.apply)

  val callee: RoutinePtr = RoutinePtr("shape$callee")
  private val cRefs = Vector(PathRef("q$0"))
  private val cMentions = Vector(SpaceMention("m$0"), SpaceMention("m$1"))
  val calleeRoutine: Routine = Routine(callee, cRefs, cMentions,
    Space.Union(Space.Wrap(Space.Mention(cMentions(0)), Path.Deref(cRefs(0))),
                Space.TailsUnion(Space.Mention(cMentions(1)))))
  val routines: PartialFunction[RoutinePtr, Routine] = { case `callee` => calleeRoutine }

  val gPS: PathValue => SpaceValue = pv => SpaceValue(pv.items.indices.map(i => PathValue(pv.items.take(i + 1))).toSet)
  val gSS: SpaceValue => SpaceValue = sv => SpaceValue(sv.paths.map(x => PathValue(x.items.reverse)))

  val rows: Vector[Row] = Vector(
    Row("Literal", 1, 0, BK.Plain, (xs, _, _) => xs(0)),
    Row("Singleton", 0, 1, BK.Plain, (_, ps, _) => Space.Singleton(ps(0))),
    Row("Union", 2, 0, BK.Plain, (xs, _, _) => Space.Union(xs(0), xs(1))),
    Row("Intersection", 2, 0, BK.Plain, (xs, _, _) => Space.Intersection(xs(0), xs(1))),
    Row("Subtraction", 2, 0, BK.Plain, (xs, _, _) => Space.Subtraction(xs(0), xs(1))),
    Row("Restriction", 2, 0, BK.Plain, (xs, _, _) => Space.Restriction(xs(0), xs(1))),
    Row("Raffination", 2, 0, BK.Plain, (xs, _, _) => Space.Raffination(xs(0), xs(1))),
    Row("Composition", 2, 0, BK.Plain, (xs, _, _) => Space.Composition(xs(0), xs(1))),
    Row("Wrap", 1, 1, BK.Plain, (xs, ps, _) => Space.Wrap(xs(0), ps(0))),
    Row("Unwrap", 1, 1, BK.Plain, (xs, ps, _) => Space.Unwrap(xs(0), ps(0))),
    Row("TailsUnion", 1, 0, BK.Plain, (xs, _, _) => Space.TailsUnion(xs(0))),
    Row("TailsIntersection", 1, 0, BK.Plain, (xs, _, _) => Space.TailsIntersection(xs(0))),
    Row("Range(0,2)", 1, 0, BK.Plain, (xs, _, _) => Space.Range(xs(0), 0, 2)),
    Row("Range(2,3)", 1, 0, BK.Plain, (xs, _, _) => Space.Range(xs(0), 2, 3)),
    Row("Range(-2,0)", 1, 0, BK.Plain, (xs, _, _) => Space.Range(xs(0), -2, 0)),
    Row("Range(0,0)", 1, 0, BK.Plain, (xs, _, _) => Space.Range(xs(0), 0, 0)),
    Row("Iteration", 1, 0, BK.Iter, (xs, _, b) => Space.Iteration(xs(0), sym, rest, b)),
    Row("Fold", 1, 1, BK.Fold, (xs, ps, b) =>
      Space.Fold(xs(0), ps(0), acc, sym, rest, b, Path.Concat(Path.Deref(acc), Path.Deref(sym)))),
    Row("Fixpoint", 1, 0, BK.Fix, (xs, _, b) => Space.Fixpoint(xs(0), recm, b)),
    Row("Call", 2, 1, BK.Plain, (xs, ps, _) => Space.Call(callee, Vector(ps(0)), xs)),
    Row("GroundedPS", 0, 1, BK.Plain, (_, ps, _) => Space.GroundedPS(ps(0), gPS)),
    Row("GroundedSS", 1, 0, BK.Plain, (xs, _, _) => Space.GroundedSS(xs(0), gSS)))

  private val A = Vector("a", "b", "c")
  /** 18 items > `Shape.MaxHeads`, so the width spill actually fires */
  private val Big = (0 until 18).map(i => ('a' + i).toChar.toString).toVector

  def randPath(rng: java.util.Random, maxLen: Int): PathValue =
    PathValue(List.fill(rng.nextInt(maxLen + 1))(A(rng.nextInt(A.length))))
  def randSV(rng: java.util.Random): SpaceValue =
    SpaceValue((0 until rng.nextInt(5)).map(_ => randPath(rng, 3)).toSet)
  /** WIDE and DEEP: up to 24 paths over 18 items with up to 7 items each, so both `Shape.MaxHeads`
   *  and `Shape.MaxDepth` are exceeded */
  def randSVBig(rng: java.util.Random): SpaceValue =
    SpaceValue((0 until rng.nextInt(25)).map(_ =>
      PathValue(List.fill(rng.nextInt(8))(Big(rng.nextInt(Big.length))))).toSet)

  /** bodies for the binder rows.  Every `Fixpoint` body must be concretely convergent (the
   *  reference `eval` loops until the argument stabilises), so they only ever shrink or saturate. */
  private def iterBodies: Vector[Space] = Vector(
    Space.Singleton(Path.Deref(sym)),
    Space.Mention(rest),
    Space.Wrap(Space.Mention(rest), Path.Deref(sym)),
    Space.Union(Space.Singleton(Path.Deref(sym)), Space.Mention(rest)),
    Space.TailsUnion(Space.Mention(rest)),
    Space.Composition(Space.Singleton(Path.Deref(sym)), Space.Mention(rest)))
  private def foldBodies: Vector[Space] = iterBodies ++ Vector(
    Space.Singleton(Path.Deref(acc)),
    Space.Union(Space.Singleton(Path.Deref(acc)), Space.Mention(rest)),
    Space.Wrap(Space.Mention(rest), Path.Deref(acc)))
  private def fixBodies(lit: Space): Vector[Space] = Vector(
    Space.Mention(recm),
    Space.TailsUnion(Space.Mention(recm)),
    Space.Union(Space.Mention(recm), lit),
    Space.Subtraction(Space.Mention(recm), lit),
    Space.Restriction(Space.Mention(recm), lit),
    Space.Intersection(Space.Mention(recm), lit))

  /** one trial; `None` when the term is not evaluable (a free ref the mode does not bind, etc.) */
  def trial(row: Row, mode: Int, rng: java.util.Random, gen: java.util.Random => SpaceValue)
      : Option[(Space, SpaceValue, SpatialType)] =
    val svs = Vector.fill(row.ar max 1)(gen(rng))
    val pvs = Vector.fill(row.par max 1)(randPath(rng, 2))
    val litOperands = svs.map(v => Space.Literal(v))
    val operands = if mode == 0 then litOperands else svs.indices.toVector.map(i => Space.Mention(opSpaces(i)))
    val paths: Vector[Path] =
      if mode == 0 then pvs.map(Path.Constant.apply)
      // mode 3: the ref's LENGTH is annotated but its content is not known — the case the
      // `wrapUnknown`/`unwrapUnknown`/`oneUnknownPath` arms exist for
      else if mode == 3 then pvs.indices.toVector.map(j => Path.Deref(opPaths(j).known(pvs(j).items.length)))
      else pvs.indices.toVector.map(j => Path.Deref(opPaths(j)))
    val body = row.bk match
      case BK.Plain => Space.Empty
      case BK.Iter => iterBodies(rng.nextInt(iterBodies.size))
      case BK.Fold => foldBodies(rng.nextInt(foldBodies.size))
      case BK.Fix => fixBodies(Space.Literal(randSV(rng)))(rng.nextInt(fixBodies(Space.Empty).size))
    val term = row.mk(operands, paths, body)
    val lenv = SpatialEnv(routines = routines)
    val env =
      if mode == 0 then SpatialTyping.Env(lenv = lenv)
      else if mode == 1 then
        SpatialTyping.Env(spaces = svs.indices.map(i => opSpaces(i) -> SpatialType.of(svs(i))).toMap,
                          paths = pvs.indices.map(j => opPaths(j) -> pvs(j)).toMap, lenv = lenv)
      else
        SpatialTyping.Env(spaces = svs.indices.map(i => opSpaces(i) -> SpatialType.of(svs(i))).toMap,
                          lenv = lenv)
    val pc = PathContextMap(pvs.indices.map(j => opPaths(j) -> pvs(j)).toMap)
    val sc = SpaceContextMap(svs.indices.map(i => opSpaces(i) -> svs(i)).toMap)
    try
      val v = eval(term)(using pc, sc, routines)
      Some((term, v, SpatialTyping.infer(term, env)))
    catch case _: Throwable => None

  /** a NESTED closed term of the given depth, built from the same rows — this is what catches a
   *  transfer that is sound in isolation but wrong when its operand is itself an approximation. */
  def nestedTrial(rng: java.util.Random, depth: Int): Option[(Space, SpaceValue, SpatialType)] =
    def build(d: Int): Space =
      if d <= 0 then Space.Literal(randSV(rng))
      else
        val row = rows(rng.nextInt(rows.size))
        val operands = Vector.fill(row.ar max 1)(build(d - 1))
        val paths = Vector.fill(row.par max 1)(Path.Constant(randPath(rng, 2)))
        val body = row.bk match
          case BK.Plain => Space.Empty
          case BK.Iter => iterBodies(rng.nextInt(iterBodies.size))
          case BK.Fold => foldBodies(rng.nextInt(foldBodies.size))
          case BK.Fix => fixBodies(Space.Literal(randSV(rng)))(rng.nextInt(fixBodies(Space.Empty).size))
        row.mk(operands, paths, body)
    val term = build(depth)
    try
      val v = eval(term)(using PathContextMap(Map.empty), SpaceContextMap(Map.empty), routines)
      Some((term, v, SpatialTyping.infer(term, SpatialTyping.Env(lenv = SpatialEnv(routines = routines)))))
    catch case _: Throwable => None
end OpMatrix

/** A greedy delta-debugger over `Space`: given a term whose concrete value escapes its inferred
 *  type, repeatedly replace a node by something strictly smaller while the escape survives.  This is
 *  how the restriction bug below was found rather than guessed at.
 *
 *  MINIMAL WITNESS (found on 25 of 1000 corpus instances before the fix):
 *
 *      Restriction(Composition(Literal({d}), Literal({d})), Literal({b, d}))
 *      eval = {d.d}          inferred shape = ∅
 *
 *  ROOT CAUSE: `Composition` degraded to ⊤ — an OPEN head set — and `Shape.restrict` then computed
 *  its result key set as `x.heads.keys ∩ prefixes.heads.keys` (empty, because ⊤ tracks no heads)
 *  while marking the result CLOSED because the prefix side was closed.  An untracked head of `x`
 *  that equals a prefix head was therefore dropped, and a non-empty restriction was inferred ∅.
 *  Fixed by keying the result on the CLOSED side (`prefixes.heads.keys` when only `prefixes` is
 *  closed) and descending through `x.under(h)`, which is the weakened `otherTail`. */
object ShapeShrink:
  /** the fuzz corpus, or empty when the file is absent */
  lazy val corpus: Vector[FuzzRec] =
    if !Corpus.file.exists then Vector.empty else Corpus.load()

  /** each corpus program instantiated CLOSED: the free mentions s0..s2 replaced by random literals
   *  and the free refs p0..p2 by random constant paths */
  def instances(recs: Vector[FuzzRec], seed: Long): Vector[Space] =
    val rng = new java.util.Random(seed)
    val A = SpaceFuzzer.alphabet
    def randPath(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def randSV(): SpaceValue = SpaceValue((0 until rng.nextInt(6)).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector
    recs.map { r =>
      val svs = Vector.fill(3)(randSV()); val pvs = Vector.fill(3)(randPath())
      subs(r.prog)(
        spre = { case Space.Mention(m) if sNames.contains(m) => Space.Literal(svs(sNames.indexOf(m))) },
        ppre = { case Path.Deref(pr) if pNames.contains(pr) => Path.Constant(pvs(pNames.indexOf(pr))) })
    }

  /** `Space.show` is not total (`Fold` has no arm), so never let a diagnostic crash the gate */
  def safeShow(s: Space): String =
    try s.show.replace('\n', ' ').take(220) catch case _: Throwable => s.toString.take(220)

  /** why `s` is a soundness witness, if it is one.  A term whose evaluation throws is not a witness. */
  def violation(s: Space): Option[String] =
    val v = try Some(eval(s)) catch case _: Throwable => None
    v.flatMap { value =>
      val t = SpatialTyping.infer(s)
      if !SpatialTyping.gammaMember(value, t) then Some(s"value ${value.pretty} not in ${t.show} :: ${safeShow(s)}")
      else
        val real = value.paths.collect { case PathValue(h :: _) => h }.toSet.size.toLong
        val hc = t.headCount
        if real < hc.lo || real > hc.hi then Some(s"head count $real outside ${hc.show} :: ${safeShow(s)}")
        else None
    }

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
    case Space.Call(_, _, ms) => ms
    case Space.GroundedSS(a, _) => Vector(a)
    case _ => Vector.empty

  def withKids(s: Space, k: Vector[Space]): Space = s match
    case Space.Union(_, _) => Space.Union(k(0), k(1))
    case Space.Intersection(_, _) => Space.Intersection(k(0), k(1))
    case Space.Subtraction(_, _) => Space.Subtraction(k(0), k(1))
    case Space.Restriction(_, _) => Space.Restriction(k(0), k(1))
    case Space.Raffination(_, _) => Space.Raffination(k(0), k(1))
    case Space.Composition(_, _) => Space.Composition(k(0), k(1))
    case Space.Wrap(_, p) => Space.Wrap(k(0), p)
    case Space.Unwrap(_, p) => Space.Unwrap(k(0), p)
    case Space.TailsUnion(_) => Space.TailsUnion(k(0))
    case Space.TailsIntersection(_) => Space.TailsIntersection(k(0))
    case Space.Range(_, a, b) => Space.Range(k(0), a, b)
    case Space.Iteration(_, y, r, _) => Space.Iteration(k(0), y, r, k(1))
    case Space.Fixpoint(_, r, _) => Space.Fixpoint(k(0), r, k(1))
    case Space.Fold(_, i, a, y, r, _, u) => Space.Fold(k(0), i, a, y, r, k(1), u)
    case Space.Call(r, rs, _) => Space.Call(r, rs, k)
    case Space.GroundedSS(_, f) => Space.GroundedSS(k(0), f)
    case _ => s

  def size(s: Space): Int = 1 + kids(s).map(size).sum

  private def variants(s: Space): Vector[Space] =
    val here: Vector[Space] = kids(s) ++ Vector(Space.Empty) ++ (s match
      case Space.Literal(v) if v.paths.size > 1 => v.paths.toVector.map(x => Space.Literal(SpaceValue(Set(x))))
      case Space.Literal(v) if v.paths.exists(_.items.length > 1) =>
        v.paths.toVector.map(x => Space.Literal(SpaceValue(Set(PathValue(x.items.take(1))))))
      case _ => Vector.empty)
    val ks = kids(s)
    here ++ ks.indices.toVector.flatMap(i => variants(ks(i)).map(k2 => withKids(s, ks.updated(i, k2))))

  def shrink(s0: Space): Space =
    var cur = s0
    var going = true
    var steps = 0
    while going && steps < 200 do
      going = false; steps += 1
      variants(cur).filter(c => size(c) < size(cur)).sortBy(size).find(c => violation(c).isDefined) match
        case Some(c) => cur = c; going = true
        case None => ()
    cur
end ShapeShrink
