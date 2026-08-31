package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** INTERMEDIATE-SPACE ELIMINATION driven by abstract interpretation over FUNCTIONS with ABSTRACT
 *  ANNOTATED INPUTS — the only sanctioned route to removing work (nothing here evaluates a subterm).
 *
 *  The contract: `eliminate(body, env)` agrees with the original on every input satisfying `env`.
 *  These tests check three things separately, because they fail differently:
 *    1. it FIRES on facts the syntactic `Lower.SizeEmpty` law cannot see;
 *    2. it is SOUND — with no annotations, unconditionally; with annotations, on every input that
 *       satisfies them (and the annotation is what makes the specialisation legitimate);
 *    3. it does NOT fire when the fact is not derivable. */
class SpatialElimination extends FunSuite:
  import Space.*
  import Lower.{LenBounds, SizeBounds}

  def pathOf(n: Int, item: String = "a"): PathValue = PathValue(List.fill(n)(item))
  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))
  def nodes(s: Space): Int = 1 + SizeZ3.children(s).map(nodes).sum

  test("fires where the syntactic emptiness law cannot: length-disjoint meet") {
    // the meet of a length-10 and a length-15 class is empty; `sizeBounds` only sees [0, min] = [0,1]
    val meet = Space.Intersection(lit(pathOf(10)), lit(pathOf(15, "b")))
    assert(Lower.sizeBounds(meet).hi > 0, "precondition: the syntactic law cannot prove this empty")
    assertEquals(Lower.SizeEmpty(meet), meet, "precondition: SizeEmpty leaves it alone")
    // a big intermediate computation built ON that meet is all dead work
    val intermediate = Space.Composition(Space.Wrap(meet, Path.Constant(pathOf(3, "t"))), lit(pathOf(2, "z")))
    val prog = Space.Union(lit(pathOf(1, "keep")), intermediate)
    val e = SpatialTypes.eliminate(prog, SpatialEnv())
    assert(e.removed.nonEmpty, "nothing was removed")
    println(s"  disjoint-meet: removed ${e.nodesRemoved} nodes — ${e.removed.map(_.fact).distinct.mkString(",")}")
    assert(nodes(e.residual) < nodes(prog), s"residual not smaller: ${e.residual.show}")
    assertEquals(eval(e.residual), eval(prog), "residual must agree (no annotations ⇒ unconditional)")
  }

  test("fires on restriction annihilation") {
    // every path of `xs` is shorter than the shortest prefix, so the restriction is empty
    val xs = lit(pathOf(1, "s"), pathOf(2, "s"))
    val prefixes = lit(pathOf(5, "p"))
    val prog = Space.Wrap(Space.Restriction(xs, prefixes), Path.Constant(pathOf(1, "w")))
    val e = SpatialTypes.eliminate(prog, SpatialEnv())
    assertEquals(e.residual, Space.Empty)
    assertEquals(eval(e.residual), eval(prog))
    println(s"  restriction-annihilation: removed ${e.nodesRemoved} nodes")
  }

  test("fires ONLY because of the input annotation (a specialisation)") {
    // `xs` is a free mention: without an annotation nothing is derivable
    val prog = Space.Restriction(S"xs", lit(pathOf(4, "k")))
    val bare = SpatialTypes.eliminate(prog, SpatialEnv())
    assertEquals(bare.removed, Vector.empty, "no annotation ⇒ no fact ⇒ no rewrite")
    // annotate: xs only ever holds length-2 paths ⇒ it cannot start with a length-4 prefix
    val env = SpatialEnv(spaces = Map(SpaceMention("xs") -> SpaceType.closed(2L -> Ivl(0, 9))))
    val spec = SpatialTypes.eliminate(prog, env)
    assertEquals(spec.residual, Space.Empty, s"annotated ⇒ provably empty, got ${spec.residual.show}")
    // sound on every input SATISFYING the annotation
    val rng = new java.util.Random(5)
    for _ <- 0 until 40 do
      val v = SpaceValue((0 until rng.nextInt(9)).map(_ => pathOf(2, s"x${rng.nextInt(4)}")).toSet)
      given SpaceContext = SpaceContextMap(Map(SpaceMention("xs") -> v))
      assertEquals(eval(spec.residual), eval(prog), s"specialisation wrong for xs = ${v.show}")
    // and the annotation is what carries it: an input VIOLATING it need not agree, which is exactly
    // why the residual is a specialisation and not an unconditional rewrite
    locally {
      given SpaceContext = SpaceContextMap(Map(SpaceMention("xs") ->
        SpaceValue(Set(PathValue(List("k", "k", "k", "k", "tail"))))))
      assertNotEquals(eval(prog), eval(spec.residual),
                      "the annotation must be load-bearing (else the test proves nothing)")
    }
  }

  test("on a FUNCTION: annotated parameters specialise the body and delete dead work") {
    // f(xs, ys) = (xs <| {len-4 prefix}) ∪ (ys ∩ {len 7})   — with xs : len 2 and ys : len 3,
    // BOTH branches are provably empty, so the whole body collapses
    val body = Space.Union(Space.Restriction(S"xs", lit(pathOf(4, "k"))),
                           Space.Intersection(S"ys", lit(pathOf(7, "q"))))
    val f = Routine(RoutinePtr("f"), Vector.empty, Vector(SpaceMention("xs"), SpaceMention("ys")), body)
    val env = SpatialEnv(spaces = Map(SpaceMention("xs") -> SpaceType.closed(2L -> Ivl(0, 9)),
                                      SpaceMention("ys") -> SpaceType.closed(3L -> Ivl(0, 9))))
    val (spec, removed) = SpatialTypes.eliminateIn(f, env)
    println(s"  function: removed ${removed.map(_.nodes).sum} nodes; residual = ${spec.body.show}")
    assert(removed.nonEmpty)
    // after the ordinary laws propagate Empty the body is gone entirely
    assertEquals(SC.reduce(spec.body), Space.Empty, s"expected total collapse, got ${SC.reduce(spec.body).show}")
    val rng = new java.util.Random(11)
    for _ <- 0 until 40 do
      val xv = SpaceValue((0 until rng.nextInt(6)).map(_ => pathOf(2, s"a${rng.nextInt(3)}")).toSet)
      val yv = SpaceValue((0 until rng.nextInt(6)).map(_ => pathOf(3, s"b${rng.nextInt(3)}")).toSet)
      given SpaceContext = SpaceContextMap(Map(SpaceMention("xs") -> xv, SpaceMention("ys") -> yv))
      assertEquals(eval(spec.body), eval(body), "specialised routine disagrees on a conforming input")
  }

  test("does NOT fire without a derivable fact, and never inside a Call") {
    val live = Space.Union(S"xs", Space.Intersection(S"xs", S"ys"))
    assertEquals(SpatialTypes.eliminate(live, SpatialEnv()).removed, Vector.empty)
    val call = Space.Call(RoutinePtr("g"), Vector.empty, Vector(Space.Mention(SpaceMention("xs"))))
    assertEquals(SpatialTypes.eliminate(call, SpatialEnv()).residual, call, "a Call must be left intact")
    // a genuinely non-empty intersection of overlapping length classes stays
    val overlap = Space.Intersection(lit(pathOf(3, "x")), lit(pathOf(3, "x")))
    assertEquals(SpatialTypes.eliminate(overlap, SpatialEnv()).removed, Vector.empty)
  }

  test("corpus: unconditional elimination never changes meaning") {
    val recs = Corpus.load()
    val rng = new java.util.Random(909)
    val A = SpaceFuzzer.alphabet
    def randPath(): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
    def randSV(): SpaceValue = SpaceValue((0 until rng.nextInt(6)).map(_ => randPath()).toSet)
    val sNames = (0 until 3).map(i => SpaceMention("s" + i)).toVector
    val pNames = (0 until 3).map(j => PathRef("p" + j)).toVector
    var fired = 0; var removedNodes = 0; var checked = 0
    for r <- recs do
      // NO annotations ⇒ the rewrite must be unconditionally meaning-preserving
      val e = SpatialTypes.eliminate(r.prog, SpatialEnv())
      if e.removed.nonEmpty then { fired += 1; removedNodes += e.nodesRemoved }
      for _ <- 0 until 2 do
        val pc = PathContextMap(pNames.map(_ -> randPath()).toMap)
        val sc = SpaceContextMap(sNames.map(_ -> randSV()).toMap)
        assertEquals(eval(e.residual)(using pc, sc), eval(r.prog)(using pc, sc),
                     s"unconditional elimination changed meaning on ${r.prog.show.take(120)}")
        checked += 1
    println(s"ELIMINATION: fired on $fired/${recs.size} corpus programs, $removedNodes AST nodes removed; " +
      s"$checked differential checks clean")
  }
end SpatialElimination
