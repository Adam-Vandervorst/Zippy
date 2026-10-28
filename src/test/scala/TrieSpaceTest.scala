package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions
import scala.util.Random

class TrieSpaceTest extends FunSuite:
  import Space.*

  private def roundTrip(sv: SpaceValue): Unit =
    assertEquals(TrieSpace.fromSpaceValue(sv).toSpaceValue, sv)

  private def assertTrieEqualsReference(s: Space)(using
    pc: PathContext = PathContext.emptyMap,
    sc: SpaceContext = SpaceContextMap(Map.empty),
    tc: TrieSpaceContext = TrieSpaceContext.emptyMap,
    rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  ): Unit =
    assertEquals(evalTrieValue(s)(using pc, tc, rc), eval(s)(using pc, sc, rc))

  private def assertZipperEqualsReference(s: Space)(using
    pc: PathContext = PathContext.emptyMap,
    sc: SpaceContext = SpaceContextMap(Map.empty),
    zc: ZipperSpaceContext = ZipperSpaceContext.emptyMap,
    rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
  ): Unit =
    assertEquals(evalZValue(s)(using pc, zc, rc), eval(s)(using pc, sc, rc))

  private def graphIndex(graphs: Map[String, RecursiveOpGraph]): PartialFunction[String, RecursiveOpGraph] =
    graphs.lift.unlift

  private def execTValue(g: RecursiveOpGraph, mentions: Vector[SpaceMention], ctx: TrieSpaceContextMap, index: Map[String, RecursiveOpGraph] = Map.empty): SpaceValue =
    val stack = collection.mutable.Stack(new Array[List[Int] | TrieSpace | Null](g.nodes.length))
    for (sm, i) <- mentions.zipWithIndex do stack.top(i) = ctx.resolve(sm)
    execT(g, stack, graphIndex(index))
    stack.top.last.asInstanceOf[TrieSpace].toSpaceValue

  private def execValue(g: RecursiveOpGraph, mentions: Vector[SpaceMention], ctx: SpaceContextMap, index: Map[String, RecursiveOpGraph] = Map.empty): SpaceValue =
    val stack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](g.nodes.length))
    for (sm, i) <- mentions.zipWithIndex do stack.top(i) = ctx.resolve(sm)
    exec(g, stack, graphIndex(index))
    stack.top.last.asInstanceOf[SpaceValue]

  private def graphVariants(r: Routine): Vector[(String, RecursiveOpGraph)] =
    Vector(
      "raw" -> transpile(r),
      "push_out" -> push_out(transpile(r)),
      "sharing" -> optimize_sharing(transpile(r)),
      "optimized" -> optimize(transpile(r))
    )

  private def assertGraphWellScoped(g: RecursiveOpGraph, clue: String): Unit =
    val bad = graphReferenceErrors(g)
    assert(bad.isEmpty, s"$clue has invalid graph references:\n${bad.mkString("\n")}")

  private def graphOps(g: RecursiveOpGraph): Vector[String] =
    g.root.operation +: g.nodes.toVector.flatMap {
      case Left(n) => Vector(n.operation)
      case Right(sg) => graphOps(sg)
    }

  private def firstSubgraph(g: RecursiveOpGraph, op: String): RecursiveOpGraph =
    g.nodes.collectFirst { case Right(sg) if sg.root.operation == op => sg }
      .getOrElse(throw AssertionError(s"missing $op subgraph"))

  private def subgraphCount(g: RecursiveOpGraph, op: String): Int =
    g.nodes.collect { case Right(sg) =>
      (if sg.root.operation == op then 1 else 0) + subgraphCount(sg, op)
    }.sum

  private def maxIterationNesting(s: Space): Int =
    def recp(p: Path, depth: Int): Int = p match
      case Path.Deref(_) | Path.Constant(_) => depth
      case Path.Concat(a, b) => recp(a, depth).max(recp(b, depth))
      case Path.GroundedPP(p, _) => recp(p, depth)
      case Path.GroundedSP(s, _) => recs(s, depth)
    def recs(s: Space, depth: Int): Int = s match
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => depth
      case Space.Call(_, refs, mentions) =>
        refs.map(recp(_, depth)).maxOption.getOrElse(depth)
          .max(mentions.map(recs(_, depth)).maxOption.getOrElse(depth))
      case Space.Singleton(p) => recp(p, depth)
      case Space.Union(a, b) => recs(a, depth).max(recs(b, depth))
      case Space.Intersection(a, b) => recs(a, depth).max(recs(b, depth))
      case Space.Subtraction(a, b) => recs(a, depth).max(recs(b, depth))
      case Space.Restriction(a, b) => recs(a, depth).max(recs(b, depth))
      case Space.Raffination(a, b) => recs(a, depth).max(recs(b, depth))
      case Space.Composition(a, b) => recs(a, depth).max(recs(b, depth))
      case Space.Iteration(src, _, _, body) =>
        recs(src, depth).max(recs(body, depth + 1))
      case Space.Fold(src, initial, _, _, _, body, update) =>
        recs(src, depth).max(recp(initial, depth)).max(recs(body, depth + 1)).max(recp(update, depth + 1))
      case Space.Fixpoint(initial, _, step) => recs(initial, depth).max(recs(step, depth + 1))
      case Space.Wrap(src, p) => recs(src, depth).max(recp(p, depth))
      case Space.Unwrap(src, p) => recs(src, depth).max(recp(p, depth))
      case Space.TailsUnion(src) => recs(src, depth)
      case Space.TailsIntersection(src) => recs(src, depth)
      case Space.PrefixClosure(src) => recs(src, depth)
      case Space.SuffixClosure(src) => recs(src, depth)
      case Space.TailsClosure(src) => recs(src, depth)
      case Space.Range(src, _, _) => recs(src, depth)
      case Space.GroundedPS(p, _) => recp(p, depth)
      case Space.GroundedSS(src, _) => recs(src, depth)
    recs(s, 0)

  private val randomSymbols = Vector("a", "b", "c", "d", "e", "0", "1")

  private def randomPathValue(rng: Random, maxLen: Int = 3): PathValue =
    val len = rng.nextInt(maxLen + 1)
    PathValue((0 until len).map(_ => PathItem(randomSymbols(rng.nextInt(randomSymbols.length)))).toList)

  private def randomSpaceValue(rng: Random, maxPaths: Int = 6): SpaceValue =
    val count = 1 + rng.nextInt(maxPaths)
    SpaceValue((0 until count).map(_ => randomPathValue(rng)).toSet)

  private def randomPath(rng: Random, bound: Vector[PathRef], depth: Int): Path =
    if depth <= 0 then
      if bound.nonEmpty && rng.nextBoolean() then Path.Deref(bound(rng.nextInt(bound.length)))
      else Path.Constant(randomPathValue(rng, maxLen = 2))
    else rng.nextInt(if bound.nonEmpty then 4 else 3) match
      case 0 => Path.Constant(randomPathValue(rng, maxLen = 2))
      case 1 if bound.nonEmpty => Path.Deref(bound(rng.nextInt(bound.length)))
      case _ => Path.Concat(randomPath(rng, bound, depth - 1), randomPath(rng, bound, depth - 1))

  private def randomSpace(rng: Random, boundS: Vector[SpaceMention], boundP: Vector[PathRef], depth: Int): Space =
    def leaf: Space =
      rng.nextInt(if boundS.nonEmpty then 4 else 3) match
        case 0 => Space.Empty
        case 1 => Space.Literal(randomSpaceValue(rng))
        case 2 => Space.Singleton(randomPath(rng, boundP, 1))
        case _ => Space.Mention(boundS(rng.nextInt(boundS.length)))
    if depth <= 0 then leaf
    else rng.nextInt(18) match
      case 0 => leaf
      case 1 => randomSpace(rng, boundS, boundP, depth - 1) \/ randomSpace(rng, boundS, boundP, depth - 1)
      case 2 => randomSpace(rng, boundS, boundP, depth - 1) /\ randomSpace(rng, boundS, boundP, depth - 1)
      case 3 => randomSpace(rng, boundS, boundP, depth - 1) \ randomSpace(rng, boundS, boundP, depth - 1)
      case 4 => randomSpace(rng, boundS, boundP, depth - 1) <| randomSpace(rng, boundS, boundP, depth - 1)
      case 5 => randomSpace(rng, boundS, boundP, depth - 1) \| randomSpace(rng, boundS, boundP, depth - 1)
      case 6 => randomSpace(rng, boundS, boundP, depth - 1) x randomSpace(rng, boundS, boundP, depth - 1)
      case 7 => Space.Wrap(randomSpace(rng, boundS, boundP, depth - 1), randomPath(rng, boundP, 1))
      case 8 => Space.Unwrap(randomSpace(rng, boundS, boundP, depth - 1), randomPath(rng, boundP, 1))
      case 9 => \/(randomSpace(rng, boundS, boundP, depth - 1))
      case 10 => /\(randomSpace(rng, boundS, boundP, depth - 1))
      case 11 => Space.Range(randomSpace(rng, boundS, boundP, depth - 1), 0, rng.nextInt(5))
      case 12 => Space.Range(randomSpace(rng, boundS, boundP, depth - 1), -rng.nextInt(5), 0)
      case 13 => Space.PrefixClosure(randomSpace(rng, boundS, boundP, depth - 1))
      case 14 => Space.SuffixClosure(randomSpace(rng, boundS, boundP, depth - 1))
      case 15 => Space.TailsClosure(randomSpace(rng, boundS, boundP, depth - 1))
      case _ =>
        val h = PathRef(s"h_${depth}_${rng.nextInt(100000)}")
        val t = SpaceMention(s"t_${depth}_${rng.nextInt(100000)}")
        Space.Iteration(
          randomSpace(rng, boundS, boundP, depth - 1),
          h,
          t,
          randomSpace(rng, t +: boundS, h +: boundP, depth - 1)
        )

  test("roundtrip preserves reference SpaceValue including epsilon") {
    roundTrip(SpaceValue(Set(
      PathValue(Nil),
      Syntax.parse("a.b"),
      Syntax.parse("a.c"),
      Syntax.parse("b"),
      Syntax.parse("$x.[2]")
    )))
  }

  test("native set and prefix operations match reference semantics") {
    val x = s("a.x", "a.y", "a.z", "b.y", "b.z", "c.y")
    val y = s("a.y", "b.y", "d")
    val prefixes = s("a", "b.y")
    val cases = Vector[Space](
      x \/ y,
      x /\ y,
      x \ y,
      x <| prefixes,
      x \| prefixes,
      x x y,
      "root" x x,
      x("a"),
      \/(x),
      /\(s("a.x", "a.y", "b.y", "b.z", "c.y")),
      Space.Range(x, 0, 3),
      Space.Range(x, -2, 0)
    )
    cases.foreach(assertTrieEqualsReference(_))
  }

  test("native closure operations match reference epsilon semantics") {
    val trie = TrieSpace.fromSpaceValue(SpaceValue(PathValue(Nil), Syntax.parse("a.b"), Syntax.parse("a.c"), Syntax.parse("d")))

    assertEquals(trie.prefixClosure.toSpaceValue, SpaceValue("a", "a.b", "a.c", "d"))
    assertEquals(trie.suffixClosure.toSpaceValue, SpaceValue("a.b", "b", "a.c", "c", "d"))
    assertEquals(trie.tailsClosure.toSpaceValue, SpaceValue(PathValue(Nil), Syntax.parse("a.b"), Syntax.parse("b"), Syntax.parse("a.c"), Syntax.parse("c"), Syntax.parse("d")))
    assertTrieEqualsReference(Space.PrefixClosure(Space.Literal(trie.toSpaceValue)))
    assertTrieEqualsReference(Space.SuffixClosure(Space.Literal(trie.toSpaceValue)))
    assertTrieEqualsReference(Space.TailsClosure(Space.Literal(trie.toSpaceValue)))
  }

  test("range filters tries in native path order without rebuilding included subtries") {
    val sv = SpaceValue(Set(
      PathValue(Nil),
      Syntax.parse("a"),
      Syntax.parse("a.a"),
      Syntax.parse("a.a.0"),
      Syntax.parse("a.b"),
      Syntax.parse("b.z"),
      Syntax.parse("c")
    ))
    val trie = TrieSpace.fromSpaceValue(sv)
    val firstFive = trie.range(0, 5)
    val lastTwo = trie.range(-2, 0)
    val second = trie.range(2, 3)
    val a = TrieSpace.intern(Syntax.parse("a")).head

    assertEquals(firstFive.toSpaceValue, eval(Space.Range(Space.Literal(sv), 0, 5)))
    assertEquals(lastTwo.toSpaceValue, eval(Space.Range(Space.Literal(sv), -2, 0)))
    assertEquals(second.toSpaceValue, eval(Space.Range(Space.Literal(sv), 2, 3)))
    assert(firstFive.children(a).eq(trie.children(a)), "range should reuse a whole included subtree")
  }

  test("range preserves epsilon and child border semantics") {
    val sv = SpaceValue(Set(
      PathValue(Nil),
      Syntax.parse("a.1"),
      Syntax.parse("a.2"),
      Syntax.parse("b.1"),
      Syntax.parse("c.1")
    ))
    val trie = TrieSpace.fromSpaceValue(sv)
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head

    val firstOnly = trie.range(0, 1)
    val firstTwo = trie.range(0, 2)
    val firstThree = trie.range(0, 3)

    assertEquals(firstOnly.toSpaceValue, SpaceValue(PathValue(Nil)))
    assert(firstOnly.children.isEmpty, "epsilon-only range must not retain children")
    assertEquals(firstTwo.children(a).toSpaceValue, SpaceValue("1"))
    assertEquals(firstThree.children(a).toSpaceValue, SpaceValue("1", "2"))
    assert(firstThree.children.get(b).forall(_.isEmpty), "range should prune children after the upper border")
  }

  test("native trie exposes head and non-empty path projections for iteration") {
    val sv = SpaceValue(PathValue(Nil), Syntax.parse("a.1"), Syntax.parse("a.2"), Syntax.parse("b.3"))
    val trie = TrieSpace.fromSpaceValue(sv)
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head
    val head = trie.head

    assertEquals(head.toSpaceValue, SpaceValue("a", "b"))
    assertEquals(head.childCount, 2)
    assertEquals(head.pathCount, 2)
    assert(head.children(a).eq(TrieSpace.epsilon), "head projection should share the native epsilon subtree for a")
    assert(head.children(b).eq(TrieSpace.epsilon), "head projection should share the native epsilon subtree for b")
    assertEquals(trie.nonEmptyPaths.toSpaceValue, SpaceValue("a.1", "a.2", "b.3"))
    assert(trie.nonEmptyPaths.children(a).eq(trie.children(a)))
  }

  test("trie evaluator expands canonical and distributed iteration bodies") {
    val src = Space.Literal(SpaceValue(PathValue(Nil), Syntax.parse("a.1"), Syntax.parse("a.2"), Syntax.parse("b.3")))
    val h = PathRef("h").known(1)
    val rest = SpaceMention("tail")
    val headOnly = Space.Iteration(src, h, rest, Space.Singleton(Path.Deref(h)))
    val reconstruct = Space.Iteration(src, h, rest, Space.Singleton(Path.Deref(h)) x S"tail")
    val distributed = Space.Iteration(src, h, rest, (Space.Singleton(Path.Deref(h)) x S"tail") \/ Space.Singleton(Path.Deref(h)))
    val invariant = Space.Iteration(src, h, rest, s("static"))
    val invariantOnEpsilonOnly = Space.Iteration(Space.Literal(SpaceValue(PathValue(Nil))), h, rest, s("static"))
    val prefixedTail = Space.Iteration(src, h, rest, Space.Wrap(S"tail", Path.Constant(Syntax.parse("tag"))))
    val prefixedHead = Space.Iteration(src, h, rest, Space.Singleton(Path.Constant(Syntax.parse("tag")) x Path.Deref(h)))
    val filteredTail = Space.Iteration(src, h, rest, Space.Restriction(S"tail", s("1", "missing")))
    val multiTail = Space.Literal(SpaceValue("a.1", "a.2", "b.3", "c.4"))
    val rangeTail = Space.Iteration(multiTail, h, rest, Space.Range(S"tail", 0, 1))
    val rangeHead = Space.Iteration(multiTail, h, rest, Space.Range(Space.Singleton(Path.Deref(h)), 0, 1))
    val rangeReconstruct = Space.Iteration(multiTail, h, rest, Space.Singleton(Path.Deref(h)) x Space.Range(S"tail", 0, 1))

    assertTrieEqualsReference(headOnly)
    assertTrieEqualsReference(reconstruct)
    assertTrieEqualsReference(distributed)
    assertTrieEqualsReference(invariant)
    assertTrieEqualsReference(invariantOnEpsilonOnly)
    assertTrieEqualsReference(prefixedTail)
    assertTrieEqualsReference(prefixedHead)
    assertTrieEqualsReference(filteredTail)
    assertTrieEqualsReference(rangeTail)
    assertTrieEqualsReference(rangeHead)
    assertTrieEqualsReference(rangeReconstruct)
    assertEquals(evalTrieValue(headOnly), SpaceValue("a", "b"))
    assertEquals(evalTrieValue(reconstruct), SpaceValue("a.1", "a.2", "b.3"))
    assertEquals(evalTrieValue(distributed), SpaceValue("a", "a.1", "a.2", "b", "b.3"))
    assertEquals(evalTrieValue(invariant), SpaceValue("static"))
    assertEquals(evalTrieValue(invariantOnEpsilonOnly), SpaceValue(Set.empty))
    assertEquals(evalTrieValue(prefixedTail), SpaceValue("tag.1", "tag.2", "tag.3"))
    assertEquals(evalTrieValue(prefixedHead), SpaceValue("tag.a", "tag.b"))
    assertEquals(evalTrieValue(filteredTail), SpaceValue("1"))
    assertEquals(evalTrieValue(rangeTail), SpaceValue("1", "3", "4"))
    assertEquals(evalTrieValue(rangeHead), SpaceValue("a", "b", "c"))
    assertEquals(evalTrieValue(rangeReconstruct), SpaceValue("a.1", "b.3", "c.4"))
  }

  test("iteration union invariant rewrite does not leak over empty sources") {
    val expr = Space.Iteration(
      Space.Empty,
      PathRef("h").known(1),
      SpaceMention("tail"),
      s("leak") \/ S"tail"
    )
    val rewritten = all_forever(expr, List(Lower.IterUnion_Indep))

    assertEquals(eval(expr), SpaceValue(Set.empty))
    assertEquals(eval(rewritten), eval(expr))

    val headed = Space.Iteration(
      s("head.rest"),
      PathRef("h").known(1),
      SpaceMention("tail"),
      s("constant") \/ S"tail"
    )
    assertEquals(eval(all_forever(headed, List(Lower.IterUnion_Indep))), eval(headed))
  }

  test("singleton iteration exposes epsilon as the empty tail") {
    val expr = Space.Iteration(
      Space.Singleton(Path.Constant(Syntax.parse("a"))),
      PathRef("h").known(1),
      SpaceMention("tail"),
      S"tail"
    )
    val rewritten = all_forever(expr, List(Lower.IterateSingleton_Deref))
    assertEquals(eval(expr), SpaceValue(Set(PathValue(Nil))))
    assertEquals(eval(rewritten), eval(expr))
  }

  test("iteration identity rewrite removes epsilon-only source paths") {
    val src = Space.Literal(SpaceValue(PathValue(Nil), Syntax.parse("a.b")))
    val h = PathRef("h").known(1)
    val expr = Space.Iteration(
      src,
      h,
      SpaceMention("tail"),
      Path.Deref(h) x S"tail"
    )
    val rewritten = all_forever(expr, List(Lower.Iter_Ident, Lower.AlgebraicIdentities))

    assertEquals(eval(expr), SpaceValue(Syntax.parse("a.b")))
    assertEquals(eval(rewritten), eval(expr))
  }

  test("fold graph round-trips through untranspile") {
    val routine = R"fold_roundtrip"(S"xs") :=
      S"xs".fold("z", "acc", "h", "tail", P"acc" x P"h" x S"tail", P"acc" x P"h")
    val graph = transpile(routine)
    val stack = collection.mutable.Stack(new Array[Path | Space | Null](graph.nodes.length))
    untranspile(graph, stack)
    val reconstructed = stack.top.last.asInstanceOf[Space]
    assert(
      Matching.alphaEqual(reconstructed, routine.body),
      s"fold round-trip changed body:\nexpected: ${routine.body.show}\nactual:   ${reconstructed.show}"
    )
  }

  test("Track B Dist generator examples agree across trie and graph backends") {
    given java.util.Random = new java.util.Random(20260708L)
    val examples = Vector.fill(12)(SpaceFuzzer.example(maxDepth = 4, maxResult = 220).sample)
    examples.zipWithIndex.foreach { (ex, i) =>
      val ctx = SpaceContextMap(Map(SpaceFuzzer.argM -> ex.arg))
      val tctx = TrieSpaceContext.fromReference(ctx)
      val routine = Routine(RoutinePtr(s"dist_fuzz_$i"), Vector.empty, Vector(SpaceFuzzer.argM), ex.program)
      val graph = optimize(transpile(routine))

      assertEquals(eval(ex.program)(using PathContext.emptyMap, ctx), ex.result, s"reference mismatch for Dist sample $i")
      assertEquals(evalTrieValue(ex.program)(using PathContext.emptyMap, tctx), ex.result, s"evalTrie mismatch for Dist sample $i")
      assertGraphWellScoped(graph, s"Dist sample $i")
      assertEquals(execValue(graph, routine.mentions, ctx), ex.result, s"exec mismatch for Dist sample $i")
      assertEquals(execTValue(graph, routine.mentions, tctx), ex.result, s"execT mismatch for Dist sample $i")
    }
  }

  test("fixpoint accumulates step output instead of replacing state") {
    val expr = Space.Fixpoint(s("seed"), SpaceMention("seen"), s("later") \ S"seen")
    val expected = SpaceValue("seed", "later")
    val routine = R"accumulating_fixpoint"() := expr
    val graph = transpile(routine)

    assertEquals(eval(expr), expected)
    assertEquals(evalTrieValue(expr), expected)
    assertEquals(execValue(graph, Vector.empty, SpaceContextMap(Map.empty)), expected)
    assertEquals(execTValue(graph, Vector.empty, TrieSpaceContext.emptyMap), expected)
  }

  test("nested fixpoint preserves outer iteration rest bindings") {
    val expr = s("left.a", "right.b").iter(P"h", S"rest",
      Space.Fixpoint(Space.Empty, SpaceMention("seen"), S"rest")
    )
    val expected = SpaceValue("a", "b")
    val routine = R"nested_fixpoint_rest"() := expr

    assertEquals(eval(expr), expected)
    assertEquals(evalTrieValue(expr), expected)
    for (name, graph) <- graphVariants(routine) do
      assertGraphWellScoped(graph, name)
      assertEquals(execValue(graph, Vector.empty, SpaceContextMap(Map.empty)), expected, s"$name exec mismatch")
      assertEquals(execTValue(graph, Vector.empty, TrieSpaceContext.emptyMap), expected, s"$name execT mismatch")
  }

  test("meet-all tails intersection keeps only tails under every head") {
    val rows = s("a.x", "a.y", "a.z", "b.y", "b.z", "c.y")
    assertEquals(evalTrieValue(/\(rows)), SpaceValue("y"))
    assertTrieEqualsReference(/\(rows))
  }

  test("zipper cursor descends to subtries without materializing paths") {
    val trie = TrieSpace.fromSpaceValue(SpaceValue("a.x", "a.y", "b.z"))
    val cursor = TrieSpace.Cursor(trie).descend(Syntax.parse("a")).get
    assertEquals(cursor.subtree.toSpaceValue, SpaceValue("x", "y"))
    assertEquals(cursor.up.get.subtree.toSpaceValue, trie.toSpaceValue)
  }

  test("space zipper cursor keeps edits when moving across siblings") {
    val parent = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("a.old", "b.peer", "c.peer")))
    val root = SpaceZipper.Cursor(parent)
    val atA = root.down(PathItem("a")).get
    val replacement = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("fresh")))
    val editedA = atA.graft(replacement)

    assertEquals(editedA.pathValue, Syntax.parse("a"))
    assertEquals(editedA.whole.toSpaceValue, SpaceValue("a.fresh", "b.peer", "c.peer"))

    val atB = editedA.nextSibling.get
    assertEquals(atB.pathValue, Syntax.parse("b"))
    assertEquals(atB.focus.toSpaceValue, SpaceValue("peer"))
    assertEquals(atB.whole.toSpaceValue, SpaceValue("a.fresh", "b.peer", "c.peer"))

    val backToA = atB.previousSibling.get
    assertEquals(backToA.pathValue, Syntax.parse("a"))
    assertEquals(backToA.focus.toSpaceValue, SpaceValue("fresh"))
    assertEquals(backToA.whole.toSpaceValue, SpaceValue("a.fresh", "b.peer", "c.peer"))

    val removedA = atA.removeFocus
    val bAfterRemoval = removedA.nextSibling.get
    assertEquals(bAfterRemoval.pathValue, Syntax.parse("b"))
    assertEquals(bAfterRemoval.whole.toSpaceValue, SpaceValue("b.peer", "c.peer"))
    assert(removedA.previousSibling.isEmpty)
  }

  test("zipper native operations short-circuit referentially identical trie nodes") {
    val shared = TrieSpace.fromSpaceValue(SpaceValue("a.b", "a.c", "d"))
    val left = SpaceZipper.traversal(shared)
    val right = SpaceZipper.traversal(shared)

    assert(SpaceZipper.union(left, right).materialize.asInstanceOf[AnyRef] eq shared.asInstanceOf[AnyRef])
    assert(SpaceZipper.intersection(left, right).materialize.asInstanceOf[AnyRef] eq shared.asInstanceOf[AnyRef])
    assertEquals(SpaceZipper.subtraction(left, right).materialize, TrieSpace.empty)

    val nestedMeet = SpaceZipper.intersection(SpaceZipper.intersection(left, right), SpaceZipper.traversal(shared))
    assert(nestedMeet.materialize.asInstanceOf[AnyRef] eq shared.asInstanceOf[AnyRef])
    assert(TrieSpace.meetAll(Vector(shared, shared, shared)).asInstanceOf[AnyRef] eq shared.asInstanceOf[AnyRef])
  }

  test("trie algebra reports exhaustive identities, bespoke values, and empty causes") {
    val left = TrieSpace.fromSpaceValue(SpaceValue("a", "b"))
    val equal = TrieSpace.fromSpaceValue(SpaceValue("a", "b"))
    val a = TrieSpace.fromSpaceValue(SpaceValue("a"))
    val b = TrieSpace.fromSpaceValue(SpaceValue("b"))
    val bc = TrieSpace.fromSpaceValue(SpaceValue("b", "c"))

    assertEquals(left.unionResult(equal), AlgebraicResult.Identity(AlgebraicResult.Both))
    assert(left.union(equal).asInstanceOf[AnyRef] eq left.asInstanceOf[AnyRef])
    assertEquals(left.unionResult(a), AlgebraicResult.Identity(AlgebraicResult.Left))
    assert(left.union(a).asInstanceOf[AnyRef] eq left.asInstanceOf[AnyRef])
    assertEquals(
      TrieSpace.empty.unionResult(TrieSpace.empty),
      AlgebraicResult.Empty(AlgebraicEmptyReason.AllArguments)
    )
    left.unionResult(bc) match
      case AlgebraicResult.Bespoke(value) => assertEquals(value.toSpaceValue, SpaceValue("a", "b", "c"))
      case other => fail(s"expected bespoke union, got $other")

    assertEquals(left.intersectionResult(a), AlgebraicResult.Identity(AlgebraicResult.Right))
    assert(left.intersect(a).asInstanceOf[AnyRef] eq a.asInstanceOf[AnyRef])
    left.intersectionResult(bc) match
      case AlgebraicResult.Bespoke(value) => assertEquals(value.toSpaceValue, SpaceValue("b"))
      case other => fail(s"expected bespoke intersection, got $other")
    assertEquals(
      a.intersectionResult(b),
      AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
    )
    assertEquals(
      a.intersectionResult(TrieSpace.empty),
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Right))
    )

    // A non-empty but disjoint right side is also a left identity for subtraction.
    assertEquals(a.subtractionResult(b), AlgebraicResult.Identity(AlgebraicResult.Left))
    assert(a.diff(b).asInstanceOf[AnyRef] eq a.asInstanceOf[AnyRef])
    left.subtractionResult(a) match
      case AlgebraicResult.Bespoke(value) => assertEquals(value.toSpaceValue, SpaceValue("b"))
      case other => fail(s"expected bespoke subtraction, got $other")
    assertEquals(
      a.subtractionResult(left),
      AlgebraicResult.Empty(AlgebraicEmptyReason.LeftCovered)
    )
    assertEquals(
      TrieSpace.empty.subtractionResult(a),
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Left))
    )
  }

  test("restriction reports left/right identity, prefix coverage, and all empty causes") {
    val equalLeft = TrieSpace.fromSpaceValue(SpaceValue("a.b"))
    val equalLeftPrefixes = TrieSpace.fromSpaceValue(SpaceValue("a", "z"))
    val leftOutcome = equalLeft.restrictionResult(equalLeftPrefixes)
    assertEquals(leftOutcome.result, AlgebraicResult.Identity(AlgebraicResult.Left))
    assert(!leftOutcome.allPrefixesMatched)
    assert(equalLeft.restrictBy(equalLeftPrefixes).asInstanceOf[AnyRef] eq equalLeft.asInstanceOf[AnyRef])

    val exactSource = TrieSpace.fromSpaceValue(SpaceValue("a", "drop"))
    val exactPrefixes = TrieSpace.fromSpaceValue(SpaceValue("a"))
    val exactOutcome = exactSource.restrictionResult(exactPrefixes)
    assertEquals(exactOutcome.result, AlgebraicResult.Identity(AlgebraicResult.Right))
    assert(exactOutcome.sourcePathsDropped)
    assert(exactOutcome.allPrefixesMatched)
    assert(exactSource.restrictBy(exactPrefixes).asInstanceOf[AnyRef] eq exactPrefixes.asInstanceOf[AnyRef])

    val coveringSource = TrieSpace.fromSpaceValue(SpaceValue("a.b", "drop"))
    val coveringPrefixes = TrieSpace.fromSpaceValue(SpaceValue("a"))
    val coveringOutcome = coveringSource.restrictionResult(coveringPrefixes)
    coveringOutcome.result match
      case AlgebraicResult.Bespoke(value) => assertEquals(value.toSpaceValue, SpaceValue("a.b"))
      case other => fail(s"expected prefix-covering bespoke restriction, got $other")
    assert(coveringOutcome.sourcePathsDropped)
    assert(coveringOutcome.allPrefixesMatched)

    val unmatchedPrefixes = TrieSpace.fromSpaceValue(SpaceValue("a", "z"))
    val bespokeOutcome = coveringSource.restrictionResult(unmatchedPrefixes)
    assert(bespokeOutcome.result.isInstanceOf[AlgebraicResult.Bespoke[?]])
    assert(!bespokeOutcome.allPrefixesMatched)

    val equalCopy = TrieSpace.fromSpaceValue(SpaceValue("a.b", "drop"))
    assertEquals(
      coveringSource.restrictionResult(equalCopy),
      RestrictionResult(AlgebraicResult.Identity(AlgebraicResult.Both), allPrefixesMatched = true)
    )

    assertEquals(
      TrieSpace.empty.restrictionResult(TrieSpace.empty).result,
      AlgebraicResult.Empty(AlgebraicEmptyReason.AllArguments)
    )
    assertEquals(
      TrieSpace.empty.restrictionResult(coveringPrefixes).result,
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Left))
    )
    assertEquals(
      coveringSource.restrictionResult(TrieSpace.empty).result,
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Right))
    )
    assertEquals(
      TrieSpace.fromSpaceValue(SpaceValue("x")).restrictionResult(coveringPrefixes).result,
      AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch)
    )

    // Exercise both Patricia Bin-containment orientations, not only Tip lookup.
    val wideSource = TrieSpace.fromEncodedPaths(Vector(List(0), List(1), List(1 << 20)))
    val narrowPrefixes = TrieSpace.fromEncodedPaths(Vector(List(0), List(1)))
    assertEquals(
      wideSource.restrictionResult(narrowPrefixes),
      RestrictionResult(AlgebraicResult.Identity(AlgebraicResult.Right), allPrefixesMatched = true)
    )
    assertEquals(
      narrowPrefixes.restrictionResult(wideSource),
      RestrictionResult(AlgebraicResult.Identity(AlgebraicResult.Left), allPrefixesMatched = false)
    )
  }

  test("algebraic result metadata agrees with exhaustive finite path sets") {
    val universe = Vector(
      PathValue(Nil),
      Syntax.parse("a"), Syntax.parse("b"), Syntax.parse("c"),
      Syntax.parse("a.a"), Syntax.parse("a.b"), Syntax.parse("b.a"), Syntax.parse("b.b"),
      Syntax.parse("a.a.a"), Syntax.parse("a.b.a"), Syntax.parse("b.a.b")
    )
    val rng = Random(0x51a7cafeL)

    def randomTrie(): TrieSpace =
      TrieSpace.fromSpaceValue(SpaceValue(universe.filter(_ => rng.nextBoolean()).toSet))

    def valueOf(result: AlgebraicResult[TrieSpace], left: TrieSpace, right: TrieSpace): TrieSpace = result match
      case AlgebraicResult.Empty(_) => TrieSpace.empty
      case AlgebraicResult.Identity(arguments) =>
        if (arguments & AlgebraicResult.Left) != 0 then left else right
      case AlgebraicResult.Bespoke(value) => value

    def assertComplete(
      result: AlgebraicResult[TrieSpace],
      left: TrieSpace,
      right: TrieSpace,
      expected: Set[PathValue],
      rightIdentityIsSpecial: Boolean = true
    ): Unit =
      val value = valueOf(result, left, right)
      assertEquals(value.toSpaceValue.paths, expected)
      result match
        case AlgebraicResult.Empty(_) => assert(expected.isEmpty)
        case AlgebraicResult.Identity(arguments) =>
          assert(expected.nonEmpty)
          assertEquals((arguments & AlgebraicResult.Left) != 0, expected == left.toSpaceValue.paths)
          if rightIdentityIsSpecial then
            assertEquals((arguments & AlgebraicResult.Right) != 0, expected == right.toSpaceValue.paths)
          else assertEquals(arguments, AlgebraicResult.Left)
        case AlgebraicResult.Bespoke(_) =>
          assert(expected.nonEmpty)
          assertNotEquals(expected, left.toSpaceValue.paths)
          if rightIdentityIsSpecial then assertNotEquals(expected, right.toSpaceValue.paths)

    for _ <- 0 until 300 do
      val left = randomTrie()
      val right = randomTrie()
      val leftPaths = left.toSpaceValue.paths
      val rightPaths = right.toSpaceValue.paths

      assertComplete(left.unionResult(right), left, right, leftPaths union rightPaths)
      assertComplete(left.intersectionResult(right), left, right, leftPaths intersect rightPaths)
      assertComplete(
        left.subtractionResult(right),
        left,
        right,
        leftPaths diff rightPaths,
        rightIdentityIsSpecial = false
      )

      val expectedRestriction = leftPaths.filter(path =>
        rightPaths.exists(prefix => path.items.startsWith(prefix.items))
      )
      val restriction = left.restrictionResult(right)
      assertComplete(restriction.result, left, right, expectedRestriction)
      val expectedCoverage = rightPaths.forall(prefix =>
        expectedRestriction.exists(path => path.items.startsWith(prefix.items))
      )
      assertEquals(
        restriction.allPrefixesMatched,
        expectedCoverage,
        s"left=$leftPaths right=$rightPaths kept=$expectedRestriction result=${restriction.result}"
      )
  }

  test("zipper restriction pushes through union and subtraction before materialization") {
    val x = SpaceValue("keep.a", "keep.b", "drop.a", "drop.b", "other.z")
    val y = SpaceValue("keep.b", "drop.b")
    val prefixes = SpaceValue("keep", "other")
    val zx = SpaceZipper.traversal(TrieSpace.fromSpaceValue(x))
    val zy = SpaceZipper.traversal(TrieSpace.fromSpaceValue(y))
    val zp = SpaceZipper.traversal(TrieSpace.fromSpaceValue(prefixes))

    val diffRestricted = SpaceZipper.restriction(SpaceZipper.subtraction(zx, zy), zp)
    assertEquals(diffRestricted.toSpaceValue, eval((Space.Literal(x) \ Space.Literal(y)) <| Space.Literal(prefixes)))
    assert(diffRestricted match
      case SpaceZipper.Memo(SpaceZipper.Subtraction(SpaceZipper.Memo(SpaceZipper.Restriction(_, _)), _)) => true
      case _ => false
    )

    val unionRestricted = SpaceZipper.restriction(SpaceZipper.union(zx, zy), zp)
    assertEquals(unionRestricted.toSpaceValue, eval((Space.Literal(x) \/ Space.Literal(y)) <| Space.Literal(prefixes)))
    assert(unionRestricted match
      case SpaceZipper.Memo(SpaceZipper.Union(
            SpaceZipper.Memo(SpaceZipper.Restriction(_, _)),
            SpaceZipper.Memo(SpaceZipper.Restriction(_, _)))) => true
      case _ => false
    )
  }

  test("direct trie evaluator reuses interned PathItems during native iteration") {
    val ctx = SpaceContextMap(Map(SpaceMention("xs") -> SpaceValue("a.b", "c.d")))
    given TrieSpaceContext = TrieSpaceContext.fromReference(ctx)
    val before = TrieSpace.interner.size
    val expr = S"xs".iter(P"h", S"tail", P"h" x S"tail")
    assertEquals(evalTrieValue(expr), ctx.resolve(SpaceMention("xs")))
    assertEquals(TrieSpace.interner.size, before)
  }

  test("temperature interval covers arbitrary ranges without runaway recursion") {
    val covered = TemperatureExample.interval(3, 28, 7)
    val values = (0 until 128).filter { i =>
      val path = PathValue(TemperatureExample.bits(i, 7).map(PathItem.apply).toList)
      covered.paths.exists(prefix => path.items.startsWith(prefix.items))
    }.toSet
    assertEquals(values, (3 to 28).toSet)
  }

  test("direct trie evaluator agrees on Aunt query") {
    given SpaceContext = AuntQuery.context
    given TrieSpaceContext = TrieSpaceContext.fromReference(AuntQuery.context)
    assertTrieEqualsReference(Routines.aunt_query_routine.body)
  }

  test("direct trie evaluator agrees on recursive semi-naive Datalog") {
    val edges = SpaceValue("edge.a.b", "edge.b.c", "edge.c.d")
    val semiNaive = DatalogExample.semiNaiveTransitive
    val call = semiNaive.name(DatalogExample.semiNaiveInitial(Literal(edges)))("complete.path")
    val defs: PartialFunction[RoutinePtr, Routine] = { case semiNaive.name => semiNaive }
    assertTrieEqualsReference(call)(using rc = defs)
  }

  test("direct trie evaluator agrees on pure Game of Life") {
    val field = GoalExampleData.randomLife(7, 7, 14, 2026)
    val call = R"nextStep"(Literal(field))
    assertTrieEqualsReference(call)(using rc = mod(LifeExample.neigh, LifeExample.nextStep))
  }

  test("direct trie evaluator agrees on process-SC residual programs") {
    val edges = SpaceValue("edge.a.b", "edge.b.c", "edge.c.d")
    val semiNaive = DatalogExample.semiNaiveTransitive
    val defs: PartialFunction[RoutinePtr, Routine] = { case semiNaive.name => semiNaive }
    val call = semiNaive.name(DatalogExample.semiNaiveInitial(Literal(edges)))("complete.path")
    val residual = SC.supercompile(call, defs, SC.Config(maxNodes = 100, maxDepth = 80))
    assert(residual.report.elapsedMs >= 0.0)
    assertEquals(residual.report.maxMillis, CompileBudget.Default.maxMillis)
    assertEquals(evalTrieValue(residual.top)(using rc = residual.env), eval(residual.top)(using rc = residual.env))
  }

  test("compile reports source and graph optimization timings") {
    val compiled = Supercompiler.compile(Routines.aunt_query_routine)
    assert(compiled.report.compileMs >= 0.0)
    assert(compiled.report.sourceTimings.nonEmpty)
    assert(compiled.report.graphTimings.exists(_.pass == "hoist_loop_invariant_subgraphs"))
    assert(compiled.report.graphTimings.exists(_.pass == "push_out"))
    assert(compiled.report.graphTimings.exists(_.pass == "optimize_sharing"))
    assertEquals(compiled.report.maxCompileMillis, CompileBudget.Default.maxMillis)
  }

  test("source optimizer respects compile deadline") {
    val expired = CompileDeadline(System.nanoTime() - 2_000_000L, System.nanoTime() - 1_000_000L, 1L)
    val ex = intercept[RuntimeException] {
      Supercompiler.normalize(Space.Empty, deadline = expired)
    }
    assert(ex.getMessage.contains("compile time cap 1 ms exceeded"))
  }

  test("source optimizer applies path-set algebraic laws") {
    def norm(s: Space): Space = Supercompiler.normalize(s).space

    val xs = S"xs"
    val state = SpaceMention("state")
    val emptyLiteral = Space.Literal(SpaceValue(Set.empty))
    val firstTwo = Space.Range(xs, 0, 2)
    val ys = S"ys"
    val prefixes = s("a")
    val otherPrefixes = s("b", "a.c")
    val restricted = Space.Restriction(xs, prefixes)
    val raffinated = Space.Raffination(xs, prefixes)
    val withoutPrefixes = Space.Subtraction(xs, prefixes)
    val withoutYs = Space.Subtraction(xs, ys)
    val withoutEpsilon = Space.Subtraction(xs, Space.Singleton(Path.ZERO))
    val overlapYs = Space.Intersection(xs, ys)
    val static = s("new")
    val h = PathRef("h").known(1)
    val rest = SpaceMention("tail")
    val prefixedReconstruct = Space.Iteration(
      xs,
      h,
      rest,
      Space.Composition(Space.Singleton(Path.Constant(Syntax.parse("tag")) x Path.Deref(h)), Space.Mention(rest))
    )
    val prefixedReconstructExpected =
      Space.Wrap(Space.Subtraction(xs, Space.Singleton(Path.ZERO)), Path.Constant(Syntax.parse("tag")))

    assertEquals(norm(emptyLiteral), Space.Empty)
    assertEquals(norm(xs \/ firstTwo), norm(xs))
    assertEquals(norm(xs /\ firstTwo), norm(firstTwo))
    assertEquals(norm(Space.Subtraction(firstTwo, xs)), Space.Empty)
    assertEquals(norm(xs \/ (xs /\ ys)), norm(xs))
    assertEquals(norm(xs \/ restricted), norm(xs))
    assertEquals(norm(xs \/ raffinated), norm(xs))
    assertEquals(norm(xs \/ withoutPrefixes), norm(xs))
    assertEquals(norm(withoutYs \/ overlapYs), norm(xs))
    assertEquals(norm(overlapYs \/ withoutYs), norm(xs))
    assertEquals(norm(withoutYs \/ ys), norm(xs \/ ys))
    assertEquals(norm(restricted \/ raffinated), norm(xs))
    assertEquals(norm(xs /\ (xs \/ ys)), norm(xs))
    assertEquals(norm(xs /\ restricted), norm(restricted))
    assertEquals(norm(xs /\ withoutPrefixes), norm(withoutPrefixes))
    assertEquals(norm(firstTwo \ xs), Space.Empty)
    assertEquals(norm((xs /\ ys) \ xs), Space.Empty)
    assertEquals(norm(restricted \ xs), Space.Empty)
    assertEquals(norm(raffinated \ xs), Space.Empty)
    assertEquals(norm(restricted /\ raffinated), Space.Empty)
    assertEquals(norm(xs \ restricted), norm(raffinated))
    assertEquals(norm(xs \ raffinated), norm(restricted))
    assertEquals(norm(xs \ (xs /\ ys)), norm(xs \ ys))
    assertEquals(norm(xs \ withoutYs), norm(xs /\ ys))
    assertEquals(norm(xs \ (ys \ xs)), norm(xs))
    assertEquals(norm((xs \/ ys) \ withoutYs), norm(ys))
    assertEquals(norm((xs \/ ys) \ xs), norm(ys \ xs))
    assertEquals(norm(xs \ (ys \/ prefixes)), norm((xs \ prefixes) \ ys))
    assertEquals(norm((xs \ prefixes) \ prefixes), norm(xs \ prefixes))
    assertEquals(norm((xs /\ ys) \/ (xs /\ prefixes)), norm(xs /\ (ys \/ prefixes)))
    assertEquals(norm((xs \/ ys) /\ (xs \/ prefixes)), norm(xs \/ (ys /\ prefixes)))
    assertEquals(
      norm(Space.Composition(xs, prefixes) \/ Space.Composition(ys, prefixes)),
      norm(Space.Composition(xs \/ ys, prefixes))
    )
    assertEquals(
      norm(Space.Unwrap(xs, Path.Constant(Syntax.parse("a"))) \/
        Space.Unwrap(ys, Path.Constant(Syntax.parse("a")))),
      norm(Space.Unwrap(xs \/ ys, Path.Constant(Syntax.parse("a"))))
    )
    assertEquals(norm((xs \ ys) \/ (xs \ prefixes)), norm(xs \ (ys /\ prefixes)))
    assertEquals(norm((xs \ ys) /\ (xs \ prefixes)), norm(xs \ (ys \/ prefixes)))
    assertEquals(
      norm(Space.Restriction(xs, prefixes) \/ Space.Restriction(xs, otherPrefixes)),
      norm(Space.Restriction(xs, prefixes \/ otherPrefixes))
    )
    assertEquals(
      norm(Space.Raffination(xs, prefixes) /\ Space.Raffination(xs, otherPrefixes)),
      norm(Space.Raffination(xs, prefixes \/ otherPrefixes))
    )
    assertEquals(norm(withoutEpsilon \/ Space.PrefixClosure(xs)), Space.PrefixClosure(xs))
    assertEquals(norm(withoutEpsilon /\ Space.PrefixClosure(xs)), norm(withoutEpsilon))
    assertEquals(norm(withoutEpsilon \ Space.PrefixClosure(xs)), Space.Empty)
    assertEquals(norm(withoutEpsilon \/ Space.SuffixClosure(xs)), Space.SuffixClosure(xs))
    assertEquals(norm(withoutEpsilon /\ Space.SuffixClosure(xs)), norm(withoutEpsilon))
    assertEquals(norm(withoutEpsilon \ Space.SuffixClosure(xs)), Space.Empty)
    assertEquals(norm(Space.TailsUnion(xs) \/ Space.TailsClosure(xs)), Space.TailsClosure(xs))
    assertEquals(norm(Space.SuffixClosure(xs) /\ Space.TailsClosure(xs)), Space.SuffixClosure(xs))
    assertEquals(norm(Space.Range(Space.Range(xs, 0, 2), 0, 1)), Space.Range(xs, 0, 1))
    assertEquals(norm(Space.Range(Space.Range(xs, 0, 1), 0, 2)), Space.Range(xs, 0, 1))
    assertEquals(norm(Space.Range(Space.Range(xs, 0, 4), 2, 3)), Space.Range(xs, 2, 3))
    assertEquals(norm(Space.Range(Space.Range(xs, 0, 2), 2, 2)), Space.Empty)
    assertEquals(norm(Space.Range(xs, 2, 2)), Space.Empty)
    assertEquals(norm(Space.Range(xs, 3, 2)), Space.Empty)
    assertEquals(norm(Space.Range(xs, -2, -2)), Space.Empty)
    assertEquals(norm(Space.Range(xs, -2, -3)), Space.Empty)
    assertEquals(norm(Space.Range(Space.Range(xs, 2, 0), 0, 2)), Space.Range(xs, 2, 4))
    assertEquals(norm(Space.Range(Space.Range(xs, 2, 0), 2, 0)), Space.Range(xs, 3, 0))
    assertEquals(norm(Space.Range(Space.Range(xs, -5, 0), -2, 0)), Space.Range(xs, -2, 0))

    assertEquals(norm(Space.PrefixClosure(Space.Empty)), Space.Empty)
    assertEquals(norm(Space.SuffixClosure(Space.Empty)), Space.Empty)
    assertEquals(norm(Space.TailsClosure(Space.Empty)), Space.Empty)
    assertEquals(norm(Space.PrefixClosure(Space.PrefixClosure(xs))), Space.PrefixClosure(xs))
    assertEquals(norm(Space.SuffixClosure(Space.SuffixClosure(xs))), Space.SuffixClosure(xs))
    assertEquals(norm(Space.TailsClosure(Space.TailsClosure(xs))), Space.TailsClosure(xs))
    assertEquals(norm(Space.Fixpoint(xs, state, Space.Mention(state))), xs)
    assertEquals(norm(Space.Fixpoint(xs, state, static)), norm(xs \/ static))
    assertEquals(norm(Space.Fixpoint(xs, state, Space.Mention(state) \/ static)), norm(xs \/ static))
    assertEquals(norm(Space.Fixpoint(xs, state, static \/ Space.Mention(state))), norm(xs \/ static))
    assertEquals(norm(Space.Fixpoint(xs, state, \/(Space.Mention(state)))), Space.TailsClosure(xs))
    assertEquals(norm(Space.Fixpoint(xs, state, \/(Space.Mention(state)) \/ static)), norm(Space.TailsClosure(xs \/ static)))
    assertEquals(norm(Space.Fixpoint(xs, state, static \/ \/(Space.Mention(state)))), norm(Space.TailsClosure(xs \/ static)))
    assertEquals(norm(prefixedReconstruct), norm(prefixedReconstructExpected))
  }

  test("unit-only optimizer laws preserve random literal path sets") {
    def lit(sv: SpaceValue): Space = Space.Literal(sv)
    def norm(s: Space): Space = Supercompiler.normalize(s).space

    val rng = Random(0x51a7e5)
    for i <- 0 until 80 do
      val a = lit(randomSpaceValue(rng, maxPaths = 8))
      val b = lit(randomSpaceValue(rng, maxPaths = 8))
      val c = lit(randomSpaceValue(rng, maxPaths = 8))
      val nonEmptyA = a \ Space.Singleton(Path.ZERO)
      val cases = Vector(
        ((a /\ b) \/ (a /\ c), a /\ (b \/ c)),
        ((a \/ b) /\ (a \/ c), a \/ (b /\ c)),
        ((a \ b) \/ (a \ c), a \ (b /\ c)),
        ((a \ b) /\ (a \ c), a \ (b \/ c)),
        (nonEmptyA \/ Space.PrefixClosure(a), Space.PrefixClosure(a)),
        (nonEmptyA /\ Space.PrefixClosure(a), nonEmptyA),
        (nonEmptyA \ Space.PrefixClosure(a), Space.Empty),
        (nonEmptyA \/ Space.SuffixClosure(a), Space.SuffixClosure(a)),
        (nonEmptyA /\ Space.SuffixClosure(a), nonEmptyA),
        (nonEmptyA \ Space.SuffixClosure(a), Space.Empty),
        (Space.TailsUnion(a) \/ Space.TailsClosure(a), Space.TailsClosure(a)),
        (Space.SuffixClosure(a) /\ Space.TailsClosure(a), Space.SuffixClosure(a)),
        (Space.Restriction(a, b) \/ Space.Restriction(a, c), Space.Restriction(a, b \/ c)),
        (Space.Raffination(a, b) /\ Space.Raffination(a, c), Space.Raffination(a, b \/ c)),
        (Space.Composition(a, c) \/ Space.Composition(b, c), Space.Composition(a \/ b, c)),
        (Space.Composition(c, a) \/ Space.Composition(c, b), Space.Composition(c, a \/ b)),
        (
          Space.Unwrap(a, Path.Constant(Syntax.parse("a"))) \/ Space.Unwrap(b, Path.Constant(Syntax.parse("a"))),
          Space.Unwrap(a \/ b, Path.Constant(Syntax.parse("a")))
        )
      )
      cases.zipWithIndex.foreach { case ((lhs, rhs), j) =>
        assertEquals(eval(lhs), eval(rhs), s"raw law $j failed on iteration $i")
        assertEquals(eval(norm(lhs)), eval(rhs), s"normalized lhs $j failed on iteration $i")
        assertEquals(eval(norm(rhs)), eval(rhs), s"normalized rhs $j failed on iteration $i")
      }
      val rangeBounds = Vector((0, 0), (0, 1), (0, 2), (1, 2), (2, 0), (2, 3), (3, 4))
      for
        (start1, end1) <- rangeBounds
        (start2, end2) <- rangeBounds
      do
        val nested = Space.Range(Space.Range(a, start1, end1), start2, end2)
        assertEquals(
          eval(norm(nested)),
          eval(nested),
          s"nested range normalization failed on iteration $i for ($start1,$end1) then ($start2,$end2)"
        )
  }

  test("operation graph executes directly over TrieSpace") {
    val compiled = Supercompiler.compile(Routines.aunt_query_routine)
    val graph = compiled.graph.get
    val stack = collection.mutable.Stack(new Array[PathValue | TrieSpace | Null](graph.nodes.length))
    stack.top(0) = TrieSpace.fromSpaceValue(AuntQuery.context.resolve(SpaceMention("family")))
    stack.top(1) = TrieSpace.fromSpaceValue(AuntQuery.context.resolve(SpaceMention("people")))
    execTrie(graph, stack)
    assertEquals(stack.top.last.asInstanceOf[TrieSpace].toSpaceValue,
      eval(compiled.routine.body)(using sc = AuntQuery.context))
  }

  test("operation graph trie backend covers pure pair swap and closure nodes") {
    val swapPairs = R"swap_pairs"(S"pairs") :=
      S"pairs".iter((P"x", P"y"), S"_", ss"pair" x sP"y" x sP"x")
    val closures = R"closures"(S"x") :=
      Space.PrefixClosure(S"x") \/
      ("suffix" x Space.SuffixClosure(S"x")) \/
      ("tails" x Space.TailsClosure(S"x"))

    val pairs = SpaceValue("a.b", "c.d")
    val x = SpaceValue("root.a.1", "root.a.2", "root.b.1")

    val tg = Supercompiler.compile(swapPairs).graph.get
    val ts = collection.mutable.Stack(new Array[PathValue | TrieSpace | Null](tg.nodes.length))
    ts.top(0) = TrieSpace.fromSpaceValue(pairs)
    execTrie(tg, ts)
    assertEquals(ts.top.last.asInstanceOf[TrieSpace].toSpaceValue, SpaceValue("pair.b.a", "pair.d.c"))

    val cg = Supercompiler.compile(closures).graph.get
    val cs = collection.mutable.Stack(new Array[PathValue | TrieSpace | Null](cg.nodes.length))
    cs.top(0) = TrieSpace.fromSpaceValue(x)
    execTrie(cg, cs)
    assertEquals(cs.top.last.asInstanceOf[TrieSpace].toSpaceValue,
      eval(closures.body)(using sc = SpaceContextMap(Map(SpaceMention("x") -> x))))
  }

  test("operation graph trie backend covers native closure nodes") {
    val routine = R"closures"(S"xs") :=
      Space.PrefixClosure(S"xs") \/
      ("suffix" x Space.SuffixClosure(S"xs")) \/
      ("tails" x Space.TailsClosure(S"xs"))
    val xs = SpaceValue("a.b.c", "a.d", "e")
    val ctx = SpaceContextMap(Map(SpaceMention("xs") -> xs))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(routine.body)(using sc = ctx)

    assertEquals(evalTrieValue(routine.body)(using sc = tctx), expected)
    for (name, graph) <- graphVariants(routine) do
      assertGraphWellScoped(graph, s"$name closures")
      assertEquals(execValue(graph, routine.mentions, ctx), expected, s"$name exec mismatch")
      assertEquals(execTValue(graph, routine.mentions, tctx), expected, s"$name execT mismatch")
  }

  test("graph optimizers preserve nested iteration semantics under execT") {
    val routine = R"graph_opt_nested"(S"xs", S"ys") :=
      S"xs".iter(P"h", S"tail",
        ("iter" x P"h" x S"tail") \/
        ("outside" x S"ys"("key")) \/
        ("meet" x (S"tail" /\ S"ys"("tail"))) \/
        ("const" x (s("one", "two") /\ s("two", "three")))
      )
    val ctx = SpaceContextMap(Map(
      SpaceMention("xs") -> SpaceValue("a.left", "b.right", "c.left"),
      SpaceMention("ys") -> SpaceValue("key.v1", "key.v2", "tail.left", "tail.other")
    ))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(routine.body)(using sc = ctx)

    for (name, graph) <- graphVariants(routine) do
      assertGraphWellScoped(graph, name)
      assertEquals(execTValue(graph, routine.mentions, tctx), expected, s"$name execT mismatch")
      assertEquals(execValue(graph, routine.mentions, ctx), expected, s"$name exec mismatch")
  }

  test("nonEmpty is an epsilon-valued constant-border emptiness indicator") {
    val fixtures = Vector(
      SpaceValue(),
      SpaceValue(PathValue(Nil)),
      SpaceValue("a"),
      SpaceValue(PathValue(Nil), "a", "b.tail")
    )
    fixtures.foreach { value =>
      val expression = Syntax.nonEmpty(Space.Literal(value))
      val expected = if value.paths.isEmpty then SpaceValue() else SpaceValue(PathValue(Nil))
      assertEquals(eval(expression), expected, s"reference nonEmpty(${value.pretty})")
      assertEquals(evalTrieValue(expression), expected, s"trie nonEmpty(${value.pretty})")
      assertEquals(evalZValue(expression), expected, s"zipper nonEmpty(${value.pretty})")
    }
  }

  test("independent nested product union pushes out with headed guards and common prefix factoring") {
    val foo = S"s"("foo")
    val bar = S"s"("bar")
    val input = foo.iter(P"x", S"x_",
      bar.iter(P"y", S"y_",
        Space.Singleton("cux" x P"x") \/ Space.Singleton("cux" x P"y")
      )
    )
    val epsilon = Space.Singleton(Path.ZERO)
    val expected = "cux" x (
      (Syntax.nonEmpty(bar \ epsilon) x head(foo)) \/
        (Syntax.nonEmpty(foo \ epsilon) x head(bar))
    )
    val normalized = Supercompiler.normalize(input)
    val normalizedExpected = Supercompiler.normalize(expected)

    assert(Matching.alphaEqual(normalized.space, normalizedExpected.space),
      s"unexpected independent-product normal form:\n${normalized.space.show}\nexpected:\n${normalizedExpected.space.show}")
    assert(normalized.steps.exists(_.pass == "independent-product-push-out"))
    assert(normalized.steps.exists(_.pass == "concat-singleton-iteration"))
    assert(normalized.steps.exists(_.pass == "epsilon-guard-wrap"))
    assertEquals(maxIterationNesting(normalized.space), 1,
      s"nested product loop survived:\n${normalized.space.show}")

    val routine = Routine(RoutinePtr("independent_product_union"), Vector.empty, Vector(S"s".variable), input)
    val optimizedRoutine = routine.copy(body = normalized.space)
    val fixtures = Vector(
      SpaceValue(),
      SpaceValue("foo", "bar.z"),
      SpaceValue("foo.x", "bar"),
      SpaceValue("foo.a", "foo.b", "bar.c", "bar.d"),
      SpaceValue(PathValue(Nil), "foo.a.tail", "bar.b.tail", "other.q")
    )
    fixtures.foreach { value =>
      val ctx = SpaceContextMap(Map(S"s".variable -> value))
      val tctx = TrieSpaceContext.fromReference(ctx)
      val reference = eval(input)(using sc = ctx)
      assertEquals(eval(normalized.space)(using sc = ctx), reference, s"normalized ${value.pretty}")
      assertEquals(eval(expected)(using sc = ctx), reference, s"guarded target ${value.pretty}")
      assertEquals(evalTrieValue(normalized.space)(using sc = tctx), reference, s"trie ${value.pretty}")
      val graph = optimize(transpile(optimizedRoutine))
      assertEquals(execTValue(graph, optimizedRoutine.mentions, tctx), reference, s"execT ${value.pretty}")
      assertEquals(execValue(graph, optimizedRoutine.mentions, ctx), reference, s"exec ${value.pretty}")
    }

    val universe = Vector(PathValue(Nil), Syntax.parse("foo"), Syntax.parse("foo.a"), Syntax.parse("foo.b.tail"),
      Syntax.parse("bar"), Syntax.parse("bar.c"), Syntax.parse("other.q"))
    for mask <- 0 until (1 << universe.size) do
      val value = SpaceValue(universe.indices.collect { case i if (mask & (1 << i)) != 0 => universe(i) }.toSet)
      val ctx = SpaceContextMap(Map(S"s".variable -> value))
      assertEquals(eval(normalized.space)(using sc = ctx), eval(input)(using sc = ctx), s"exhaustive mask=$mask")
  }

  test("optimal sharing merges structurally identical iteration subgraphs") {
    val branch = S"xs".iter(P"h", S"tail", Space.Singleton("tag" x P"h"))
    val routine = R"share_identical_iterations"(S"xs") := (branch \/ branch)
    val raw = transpile(routine)
    val shared = optimize_sharing(raw)
    val ctx = SpaceContextMap(Map(SpaceMention("xs") -> SpaceValue("a.left", "b.right")))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(routine.body)(using sc = ctx)

    assertEquals(subgraphCount(raw, "Iteration"), 2)
    assertEquals(subgraphCount(shared, "Iteration"), 1, shared.show)
    assertGraphWellScoped(shared, "identical subgraph sharing")
    assertEquals(execValue(shared, routine.mentions, ctx), expected)
    assertEquals(execTValue(shared, routine.mentions, tctx), expected)
  }

  test("optimal sharing treats renamed iteration binders as alpha-equivalent") {
    val first = S"xs".iter(P"left_head", S"left_tail", Space.Singleton("tag" x P"left_head"))
    val second = S"xs".iter(P"right_head", S"right_tail", Space.Singleton("tag" x P"right_head"))
    val routine = R"share_alpha_iterations"(S"xs") := (first \/ second)
    val raw = transpile(routine)
    val shared = optimize_sharing(raw)
    val ctx = SpaceContextMap(Map(SpaceMention("xs") -> SpaceValue("a.left", "b.right")))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(routine.body)(using sc = ctx)

    assertEquals(subgraphCount(raw, "Iteration"), 2)
    assertEquals(subgraphCount(shared, "Iteration"), 1, shared.show)
    assertGraphWellScoped(shared, "alpha-equivalent subgraph sharing")
    assertEquals(execValue(shared, routine.mentions, ctx), expected)
    assertEquals(execTValue(shared, routine.mentions, tctx), expected)
  }

  test("optimal sharing alpha-converts nested iteration binders") {
    def nested(outer: PathRef, tails: SpaceMention, inner: PathRef, rest: SpaceMention): Space =
      Space.Iteration(S"xs", outer, tails,
        Space.Iteration(Space.Mention(tails), inner, rest,
          Space.Singleton(Path.Concat(Path.Deref(outer), Path.Deref(inner)))))
    val first = nested(PathRef("left_outer"), SpaceMention("left_tails"),
      PathRef("left_inner"), SpaceMention("left_rest"))
    val second = nested(PathRef("right_outer"), SpaceMention("right_tails"),
      PathRef("right_inner"), SpaceMention("right_rest"))
    val routine = R"share_nested_alpha"(S"xs") := (first \/ second)
    val raw = transpile(routine)
    val shared = optimize_sharing(raw)
    val ctx = SpaceContextMap(Map(SpaceMention("xs") -> SpaceValue("a.1.x", "a.2.y", "b.3.z")))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(routine.body)(using sc = ctx)

    assertEquals(subgraphCount(raw, "Iteration"), 4)
    assertEquals(subgraphCount(shared, "Iteration"), 2, shared.show)
    assertGraphWellScoped(shared, "nested alpha-equivalent sharing")
    assertEquals(execValue(shared, routine.mentions, ctx), expected)
    assertEquals(execTValue(shared, routine.mentions, tctx), expected)
  }

  test("optimal sharing keeps non-alpha-equivalent nested binder uses separate") {
    def nested(useOuter: Boolean, suffix: String): Space =
      val outer = PathRef(s"${suffix}_outer")
      val tails = SpaceMention(s"${suffix}_tails")
      val inner = PathRef(s"${suffix}_inner")
      val rest = SpaceMention(s"${suffix}_rest")
      Space.Iteration(S"xs", outer, tails,
        Space.Iteration(Space.Mention(tails), inner, rest,
          Space.Singleton(Path.Deref(if useOuter then outer else inner))))
    val routine = R"reject_false_alpha"(S"xs") := (nested(useOuter = true, "left") \/ nested(useOuter = false, "right"))
    val raw = transpile(routine)
    val shared = optimize_sharing(raw)
    val ctx = SpaceContextMap(Map(SpaceMention("xs") -> SpaceValue("a.1.x", "a.2.y", "b.3.z")))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(routine.body)(using sc = ctx)

    assertEquals(subgraphCount(raw, "Iteration"), 4)
    assertEquals(subgraphCount(shared, "Iteration"), 4,
      s"outer and inner de Bruijn coordinates must remain distinct:\n${shared.show}")
    assertGraphWellScoped(shared, "non-alpha nested sharing")
    assertEquals(execValue(shared, routine.mentions, ctx), expected)
    assertEquals(execTValue(shared, routine.mentions, tctx), expected)
  }

  test("optimal sharing alpha-converts fixpoint and fold binders") {
    def closure(name: String): Space =
      val state = SpaceMention(s"${name}_state")
      Space.Fixpoint(S"xs", state, Space.Mention(state) \/ Space.TailsUnion(Space.Mention(state)))
    def folded(name: String): Space =
      val acc = PathRef(s"${name}_acc")
      val head = PathRef(s"${name}_head")
      val rest = SpaceMention(s"${name}_rest")
      Space.Fold(S"xs", Path.Constant(Syntax.parse("seed")), acc, head, rest,
        Space.Singleton(Path.Concat(Path.Deref(acc), Path.Deref(head))), Path.Deref(acc))
    val routine = R"share_alpha_loops"(S"xs") :=
      (closure("left") \/ closure("right")) \/ (folded("left") \/ folded("right"))
    val raw = transpile(routine)
    val shared = optimize_sharing(raw)
    val ctx = SpaceContextMap(Map(SpaceMention("xs") -> SpaceValue("a.1", "b.2")))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(routine.body)(using sc = ctx)

    assertEquals(subgraphCount(raw, "Fixpoint"), 2)
    assertEquals(subgraphCount(shared, "Fixpoint"), 1, shared.show)
    assertEquals(subgraphCount(raw, "Fold"), 2)
    assertEquals(subgraphCount(shared, "Fold"), 1, shared.show)
    assertGraphWellScoped(shared, "fixpoint/fold alpha sharing")
    assertEquals(execValue(shared, routine.mentions, ctx), expected)
    assertEquals(execTValue(shared, routine.mentions, tctx), expected)
  }

  test("loop invariant hoist lifts transitive invariant DAG out of iteration") {
    val routine = R"loop_hoist"(S"xs", S"ys") :=
      S"xs".iter(P"h", S"tail",
        ("dyn" x P"h" x S"tail") \/
        ("inv" x ((S"ys"("keep") /\ s("a", "b", "keep.v")) x (s("k") \/ s("m"))))
      )
    val ctx = SpaceContextMap(Map(
      SpaceMention("xs") -> SpaceValue("p.left", "q.right", "r.left"),
      SpaceMention("ys") -> SpaceValue("keep.v", "keep.w", "other.z")
    ))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val raw = transpile(routine)
    val hoisted = hoist_loop_invariant_subgraphs(raw)
    val rawLoop = firstSubgraph(raw, "Iteration")
    val hoistedLoop = firstSubgraph(hoisted, "Iteration")
    val expected = eval(routine.body)(using sc = ctx)

    assertGraphWellScoped(hoisted, "loop invariant hoist")
    assert(Supercompiler.graphStats(hoistedLoop).nodes < Supercompiler.graphStats(rawLoop).nodes,
      s"expected hoisted loop to shrink\nraw:\n${raw.show}\nhoisted:\n${hoisted.show}")
    assertEquals(execValue(hoisted, routine.mentions, ctx), expected)
    assertEquals(execTValue(hoisted, routine.mentions, tctx), expected)
  }

  test("graph compile pipeline inlines helper calls before execT") {
    val helper = R"graph_helper"(S"x") := ("H" x S"x") \/ ("K" x S"x"("k"))
    val top = R"graph_caller"(S"x") := R"graph_helper"(S"x") \/ ("T" x S"x")
    val ctx = SpaceContextMap(Map(SpaceMention("x") -> SpaceValue("k.1", "k.2", "z.3")))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(top.body)(using sc = ctx, rc = mod(helper))
    val compiled = Supercompiler.compile(top, ctx = mod(helper))
    val graph = compiled.graph.get

    assert(!graphOps(graph).contains("Call"), "compiled graph should inline helper calls before execution")
    assertGraphWellScoped(graph, "compiled helper call graph")
    assertEquals(execTValue(graph, top.mentions, tctx), expected)
  }

  test("graph execT fallback calls optimized callee graphs") {
    val helper = R"fallback_helper"(S"x") := ("H" x S"x") \/ ("K" x S"x"("k"))
    val top = R"fallback_caller"(S"x") := R"fallback_helper"(S"x") \/ ("T" x S"x")
    val ctx = SpaceContextMap(Map(SpaceMention("x") -> SpaceValue("k.1", "k.2", "z.3")))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val expected = eval(top.body)(using sc = ctx, rc = mod(helper))
    val topGraph = optimize(transpile(top))
    val helperGraph = optimize(transpile(helper))

    assert(graphOps(topGraph).contains("Call"), "fallback test should retain a Call node")
    assertGraphWellScoped(topGraph, "optimized caller graph")
    assertGraphWellScoped(helperGraph, "optimized callee graph")
    assertEquals(execValue(topGraph, top.mentions, ctx, Map(helper.name.s -> helperGraph)), expected)
    assertEquals(execTValue(topGraph, top.mentions, tctx, Map(helper.name.s -> helperGraph)), expected)
  }

  test("benchmark fallback notes include retained calls inside optimized callees") {
    val leaf = R"fallback_leaf"(S"x") := "L" x S"x"
    val mid = R"fallback_mid"(S"x") := R"fallback_leaf"(S"x") \/ ("M" x S"x")
    val top = R"fallback_top"(S"x") := R"fallback_mid"(S"x") \/ ("T" x S"x")

    val topGraph = optimize(transpile(top))
    val midGraph = optimize(transpile(mid))
    val leafGraph = optimize(transpile(leaf))
    val note = TrieBenchmarks.fallbackCallNoteForTest(
      topGraph,
      Map(mid.name.s -> midGraph, leaf.name.s -> leafGraph)
    ).getOrElse("")

    assert(graphOps(topGraph).contains("Call"), "top graph should retain a fallback call")
    assert(graphOps(midGraph).contains("Call"), "callee graph should retain a nested fallback call")
    assert(note.contains("fallback_mid"), note)
    assert(note.contains("fallback_leaf"), note)
  }

  test("zipper transpile lowers union-saturating recursive helper calls itself") {
    val recursive = R"zipper_self_union"(S"x") := S"x" \/ R"zipper_self_union"(S"x")
    val call = recursive.name(s("seed"))
    val (zipper, construction) = ExecutorCostMeter.measure(
      transpileZ(call)(using PathContext.emptyMap, ZipperSpaceContext.emptyMap, mod(recursive)))

    assertEquals(construction.rounds, 0L)
    assertEquals(zipper.toSpaceValue,
      eval(call)(using PathContext.emptyMap, SpaceContextMap(Map.empty), mod(recursive)))
  }

  test("zipper transpile rejects non-lowered recursive calls outside top-level self-union") {
    val recursive = R"zipper_nested_self"(S"x") := "p" x R"zipper_nested_self"(S"x")
    val failure = intercept[UnsupportedOperationException] {
      evalZValue(recursive.name(s("seed")))(using rc = mod(recursive))
    }

    assert(failure.getMessage.contains("recursive routine call"), failure.getMessage)
    assert(failure.getMessage.contains("outside the union-saturating fixpoint fragment"), failure.getMessage)
  }

  test("graph optimizer handles generated pure sliding puzzle graph") {
    val expr = SlidingPuzzleExample.step(2, Literal(SlidingPuzzleExample.solved(2)))
    val routine = R"slide_graph"() := expr
    val optimizedRaw = optimize(transpile(routine))
    assertGraphWellScoped(optimizedRaw, "optimized raw sliding puzzle")
    assertEquals(optimize(optimizedRaw).show, optimizedRaw.show)

    val graph = Supercompiler.compile(routine, ctx = SlidingPuzzleExample.context(2)).graph.get
    val expected = eval(expr)(using rc = SlidingPuzzleExample.context(2))

    assertGraphWellScoped(graph, "optimized sliding puzzle")
    assert(!graphOps(graph).contains("Call"), "compiled sliding puzzle graph should inline helper calls before execution")
    assertEquals(execTValue(graph, Vector.empty, TrieSpaceContext.emptyMap), expected)
  }

  test("compile pipeline lowers union-saturating recursion before graph exec") {
    val semiNaive = DatalogExample.semiNaiveTransitive
    val expr = semiNaive.name(DatalogExample.semiNaiveInitial(S"edges"))("complete.path")
    val routine = R"datalog_fix_graph"(S"edges") := expr
    val ctx = SpaceContextMap(Map(SpaceMention("edges") ->
      SpaceValue("edge.a.b", "edge.b.c", "edge.c.d")))
    val tctx = TrieSpaceContext.fromReference(ctx)
    val compiled = Supercompiler.compile(routine, ctx = mod(semiNaive))
    val graph = compiled.graph.get
    val expected = eval(expr)(using sc = ctx, rc = mod(semiNaive))

    assert(graphOps(graph).contains("Fixpoint"), "compiled graph should contain lowered fixpoint loop")
    assert(!graphOps(graph).contains("Call"), "compiled graph should not retain recursive Call nodes")
    assertGraphWellScoped(graph, "compiled datalog fixpoint graph")
    assertEquals(execValue(graph, routine.mentions, ctx), expected)
    assertEquals(execTValue(graph, routine.mentions, tctx), expected)
  }

  test("mutual union-saturating recursion lowers to one tagged fixpoint") {
    val toB = s("a.b")
    val toA = s("b.c")
    def image(rel: Space, xs: Space): Space =
      xs.iterh(P"h", rel(P"h"))
    val a = R"mutual_a"(S"x") := S"x" \/ R"mutual_b"(image(toB, S"x"))
    val b = R"mutual_b"(S"x") := S"x" \/ R"mutual_a"(image(toA, S"x"))
    val lowered = Supercompiler.lowerFixpointCalls(R"mutual_a"(s("a")), mod(a, b))
    val expected = SpaceValue("a", "c")
    val routine = R"mutual_fix_graph"() := lowered
    val graph = optimize(transpile(routine))

    assert(graphOps(graph).contains("Fixpoint"), lowered.show)
    assert(!graphOps(graph).contains("Call"), lowered.show)
    assertGraphWellScoped(graph, "lowered mutual fixpoint graph")
    assertEquals(eval(lowered), expected)
    assertEquals(evalTrieValue(lowered), expected)
    assertEquals(evalZValue(R"mutual_a"(s("a")))(using rc = mod(a, b)), expected)
    assertEquals(execValue(graph, Vector.empty, SpaceContextMap(Map.empty)), expected)
    assertEquals(execTValue(graph, Vector.empty, TrieSpaceContext.emptyMap), expected)
  }

  test("unproved multi-argument recursion remains an explicit call") {
    val explore = R"unproved_explore"(S"frontier", S"states") :=
      S"states" \/ R"unproved_explore"(S"frontier" \ S"states", S"frontier" \/ S"states")
    val lowered = Supercompiler.lowerFixpointCalls(R"unproved_explore"(s("a"), Space.Empty), mod(explore))
    val routine = R"unproved_explore_graph"() := lowered
    val graph = transpile(routine)

    assert(graphOps(graph).contains("Call"), lowered.show)
    assert(!graphOps(graph).contains("Fixpoint"), lowered.show)
    assertGraphWellScoped(graph, "unproved recursion fallback graph")
  }

  test("zipper traversal and virtual native operations match reference trie operations") {
    val rng = Random(0x7170706572L)

    def zip(sv: SpaceValue): SpaceZipper =
      SpaceZipper.traversal(TrieSpace.fromSpaceValue(sv))

    for i <- 0 until 120 do
      val x = randomSpaceValue(rng, maxPaths = 8)
      val y = randomSpaceValue(rng, maxPaths = 8)
      val px = randomPathValue(rng, maxLen = 2)
      val zx = zip(x)
      val zy = zip(y)
      val prefix = TrieSpace.intern(px)

      val cases = Vector[(String, Space, SpaceZipper)](
        ("union", Space.Literal(x) \/ Space.Literal(y), SpaceZipper.union(zx, zy)),
        ("intersection", Space.Literal(x) /\ Space.Literal(y), SpaceZipper.intersection(zx, zy)),
        ("subtraction", Space.Literal(x) \ Space.Literal(y), SpaceZipper.subtraction(zx, zy)),
        ("restriction", Space.Literal(x) <| Space.Literal(y), SpaceZipper.restriction(zx, zy)),
        ("raffination", Space.Literal(x) \| Space.Literal(y), SpaceZipper.subtraction(zx, SpaceZipper.restriction(zx, zy))),
        ("composition", Space.Literal(x) x Space.Literal(y), SpaceZipper.concat(zx, zy)),
        ("wrap", Space.Wrap(Space.Literal(x), Path.Constant(px)), SpaceZipper.wrap(zx, prefix)),
        ("unwrap", Space.Unwrap(Space.Literal(x), Path.Constant(px)), SpaceZipper.unwrap(zx, prefix)),
        ("tailsUnion", Space.TailsUnion(Space.Literal(x)), SpaceZipper.TailsUnion(zx)),
        ("tailsIntersection", Space.TailsIntersection(Space.Literal(x)), SpaceZipper.TailsIntersection(zx)),
        ("prefixClosure", Space.PrefixClosure(Space.Literal(x)), SpaceZipper.PrefixClosure(zx)),
        ("suffixClosure", Space.SuffixClosure(Space.Literal(x)), SpaceZipper.SuffixClosure(zx)),
        ("tailsClosure", Space.TailsClosure(Space.Literal(x)), SpaceZipper.TailsClosure(zx)),
        ("rangeFirst", Space.Range(Space.Literal(x), 0, 3), SpaceZipper.range(zx, 0, 3)),
        ("rangeLast", Space.Range(Space.Literal(x), -3, 0), SpaceZipper.range(zx, -3, 0))
      )

      cases.foreach { (name, expr, zipper) =>
        assertEquals(zipper.toSpaceValue, eval(expr), s"$name mismatch on iteration $i")
      }

      assertEquals(SpaceZipper.union(zx, zy).toSpaceValue, SpaceZipper.union(zy, zx).toSpaceValue, s"union commutative $i")
      val z = zip(randomSpaceValue(rng, maxPaths = 8))
      assertEquals(
        SpaceZipper.union(SpaceZipper.union(zx, zy), z).toSpaceValue,
        SpaceZipper.union(zx, SpaceZipper.union(zy, z)).toSpaceValue,
        s"union associative $i"
      )
      assertEquals(SpaceZipper.intersection(zx, zy).toSpaceValue, SpaceZipper.intersection(zy, zx).toSpaceValue, s"intersection commutative $i")
    end for
  }

  test("zipper composition stays virtual under selective consumers") {
    val left = SpaceValue("a.1", "b.2", "c.3")
    val right = SpaceValue("x", "y")
    val selector = SpaceValue("b.2.y")
    val zl = SpaceZipper.traversal(TrieSpace.fromSpaceValue(left))
    val zr = SpaceZipper.traversal(TrieSpace.fromSpaceValue(right))
    val zs = SpaceZipper.traversal(TrieSpace.fromSpaceValue(selector))

    val product = SpaceZipper.concat(zl, zr)
    val selected = SpaceZipper.intersection(product, zs)

    assert(product.concrete.isEmpty, "composition zipper must not expose a materialized product")
    assert(selected.concrete.isEmpty, "selective consumers must traverse composition virtually")
    assertEquals(selected.toSpaceValue, selector)
  }

  test("virtual tails meet and prefix-closure nullability drive product descent") {
    def zip(paths: String*): SpaceZipper =
      SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue(paths.map(Syntax.parse).toSet)))

    val a = TrieSpace.intern(Syntax.parse("a")).head
    val d = TrieSpace.intern(Syntax.parse("d")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head

    val virtualSource = SpaceZipper.union(
      SpaceZipper.wrap(SpaceZipper.NonEmpty(zip("b", "c")), List(a)),
      SpaceZipper.wrap(SpaceZipper.NonEmpty(zip("b", "q")), List(d))
    )
    val tailsMeet = SpaceZipper.TailsIntersection(virtualSource)
    assert(tailsMeet.concrete.isEmpty, "tails intersection over a virtual union must stay virtual")
    assert(tailsMeet.child(b).terminal, "the common b tail must be accepted")
    assertEquals(tailsMeet.toSpaceValue, SpaceValue("b"))

    val closure = SpaceZipper.PrefixClosure(zip("a.b"))
    assert(closure.child(a).terminal, "an interior prefix-closure focus must accept epsilon")

    val product = SpaceZipper.concat(SpaceZipper.PrefixClosure(zip("a")), zip("b"))
    assert(product.concrete.isEmpty, "closure-left composition must stay virtual")
    assert(product.child(a).child(b).terminal, "nullable closure focus must expose the right product child")
    assertEquals(product.toSpaceValue, SpaceValue("a.b"))
  }

  test("zipper generic iteration keeps child observations virtual") {
    val source = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("a.1", "b.2", "c.3")))
    val outKey = TrieSpace.intern(Syntax.parse("out")).head
    val raw = SpaceZipper.Iteration(
      source,
      (head, tail) => SpaceZipper.wrap(tail, outKey :: head :: Nil)
    )

    val first = raw.child(outKey)
    val second = raw.child(outKey)
    val iterated = raw.childrenIterator.find(_._1 == outKey).get._2

    assert(first match
      case SpaceZipper.Memo(SpaceZipper.IterationChild(_, _)) => true
      case SpaceZipper.IterationChild(_, _) => true
      case _ => false
    , s"direct child lookup should stay as a virtual IterationChild, saw $first")
    assert(first.asInstanceOf[AnyRef] eq second.asInstanceOf[AnyRef], "direct child lookup should reuse the per-key virtual child")
    assert(first.asInstanceOf[AnyRef] eq iterated.asInstanceOf[AnyRef], "childrenIterator should share the cached per-key virtual child")
    assertEquals(first.toSpaceValue, SpaceValue("a.1", "b.2", "c.3"))
  }

  test("zipper iteration materializes each branch without rebuilding its virtual cursor tree") {
    val width = 128
    val sourceHeads = Vector.tabulate(width)(i => TrieSpace.intern(Syntax.parse(s"source_$i")).head)
    val sourceTail = TrieSpace.intern(Syntax.parse("tail")).head
    val resultPrefix = TrieSpace.intern(Syntax.parse("result")).head
    val outputPrefix = TrieSpace.intern(Syntax.parse("out")).head
    val outputLeaf = TrieSpace.intern(Syntax.parse("leaf")).head
    val source = SpaceZipper.traversal(
      TrieSpace.fromEncodedPaths(sourceHeads.map(head => head :: sourceTail :: Nil))
    )

    var cursorObservations = 0
    var branchMaterializations = 0
    def countedBranch(value: TrieSpace): SpaceZipper = new SpaceZipper:
      override def terminal: Boolean =
        cursorObservations += 1
        value.terminal
      override def child(item: Int): SpaceZipper =
        cursorObservations += 1
        countedBranch(value.children.getOrElse(item, TrieSpace.empty))
      override def childKeys: IterableOnce[Int] =
        cursorObservations += 1
        value.children.keysIterator
      override def materialize: TrieSpace =
        branchMaterializations += 1
        value

    val iteration = SpaceZipper.Iteration(
      source,
      (head, _tail) => countedBranch(TrieSpace.empty.insertItems(outputPrefix :: head :: outputLeaf :: Nil))
    )
    val expected = TrieSpace.joinAll(
      sourceHeads.iterator.map(head => TrieSpace.empty.insertItems(outputPrefix :: head :: outputLeaf :: Nil))
    )

    assertEquals(SpaceZipper.wrap(iteration, resultPrefix :: Nil).materialize, expected.wrapItems(resultPrefix :: Nil))
    assertEquals(branchMaterializations, width)
    assertEquals(cursorObservations, 0,
      "final materialization should use native trie union instead of rescanning every branch at every output prefix")

    cursorObservations = 0
    branchMaterializations = 0
    val focusedIteration = SpaceZipper.Iteration(
      source,
      (head, _tail) => countedBranch(TrieSpace.empty.insertItems(outputPrefix :: head :: outputLeaf :: Nil))
    ).child(outputPrefix)
    assertEquals(focusedIteration.materialize, expected.unwrapItems(outputPrefix :: Nil))
    assertEquals(branchMaterializations, width)
    assertEquals(cursorObservations, width,
      "a focused iteration should inspect each branch once, not rebuild its cursor tree below the focus")
  }

  test("zipper iteration keeps canonical and general iteration virtual") {
    val source = SpaceValue("a.1", "b.2", "c.3")
    val h = PathRef("h").known(1)
    val rest = SpaceMention("tail")
    val sourceExpr = Space.Literal(source)
    def containsIteration(z: SpaceZipper): Boolean = z match
      case SpaceZipper.Memo(src) => containsIteration(src)
      case SpaceZipper.Union(left, right) => containsIteration(left) || containsIteration(right)
      case SpaceZipper.JoinAll(children) => children.exists(containsIteration)
      case SpaceZipper.Intersection(left, right) => containsIteration(left) || containsIteration(right)
      case SpaceZipper.MeetAll(children) => children.exists(containsIteration)
      case SpaceZipper.Subtraction(left, right) => containsIteration(left) || containsIteration(right)
      case SpaceZipper.Restriction(src, prefixes) => containsIteration(src) || containsIteration(prefixes)
      case SpaceZipper.Concat(left, right) => containsIteration(left) || containsIteration(right)
      case SpaceZipper.Prefix(_, src) => containsIteration(src)
      case SpaceZipper.NonEmpty(src) => containsIteration(src)
      case SpaceZipper.TailsUnion(src) => containsIteration(src)
      case SpaceZipper.TailsIntersection(src) => containsIteration(src)
      case SpaceZipper.PrefixClosure(src, _) => containsIteration(src)
      case SpaceZipper.SuffixClosure(src) => containsIteration(src)
      case SpaceZipper.TailsClosure(src) => containsIteration(src)
      case SpaceZipper.Head(src) => containsIteration(src)
      case SpaceZipper.Fixpoint(src, _) => containsIteration(src)
      case SpaceZipper.PatchChild(parent, _, replacement) => containsIteration(parent) || containsIteration(replacement)
      case SpaceZipper.Range(src, _, _) => containsIteration(src)
      case SpaceZipper.LastRange(src, _) => containsIteration(src)
      case SpaceZipper.DropLastRange(src, _) => containsIteration(src)
      case SpaceZipper.Iteration(_, _, _) => true
      case SpaceZipper.Trie(_) => false

    def hasFixpointTag(z: SpaceZipper, tag: SpaceZipper.IterTemplateTag): Boolean = z match
      case SpaceZipper.Fixpoint(_, found) if found == tag => true
      case SpaceZipper.Memo(SpaceZipper.Fixpoint(_, found)) if found == tag => true
      case _ => false

    val tails = transpileZ(Space.Iteration(sourceExpr, h, rest, Space.Mention(rest)))
    val heads = transpileZ(Space.Iteration(sourceExpr, h, rest, Space.Singleton(Path.Deref(h))))
    val reconstruct = transpileZ(Space.Iteration(sourceExpr, h, rest, Space.Wrap(Space.Mention(rest), Path.Deref(h))))
    val prefixedTailExpr = Space.Iteration(sourceExpr, h, rest, Space.Wrap(Space.Mention(rest), Path.Constant(Syntax.parse("tag"))))
    val prefixedHeadExpr = Space.Iteration(sourceExpr, h, rest, Space.Singleton(Path.Constant(Syntax.parse("tag")) x Path.Deref(h)))
    val prefixedReconstructExpr =
      Space.Iteration(sourceExpr, h, rest, Space.Wrap(Space.Mention(rest), Path.Constant(Syntax.parse("tag")) x Path.Deref(h)))
    val filteredTailExpr = Space.Iteration(sourceExpr, h, rest, Space.Restriction(Space.Mention(rest), s("1", "missing")))
    val subtractedTailExpr = Space.Iteration(sourceExpr, h, rest, Space.Subtraction(Space.Mention(rest), s("2")))
    val composedTailExpr = Space.Iteration(sourceExpr, h, rest, Space.Composition(s("tag"), Space.Mention(rest)))
    val tailClosureExpr = Space.Iteration(sourceExpr, h, rest, Space.TailsUnion("tag" x Path.Deref(h) x Space.Mention(rest)))
    val taggedExpr =
      Space.Iteration(sourceExpr, h, rest,
        Space.Composition(Space.Singleton(Path.Constant(Syntax.parse("out")) x Path.Deref(h)), S"tail" \/ s("extra")))
    val multiTailSource = Space.Literal(SpaceValue("a.1", "a.2", "b.3", "c.4"))
    val state = SpaceMention("state")
    val fixpointTailExpr = Space.Fixpoint(sourceExpr, state, Space.TailsUnion(S"state"))
    val fixpointIterTailExpr = Space.Fixpoint(sourceExpr, state, Space.Iteration(S"state", h, rest, S"tail"))
    val fixpointIterHeadExpr = Space.Fixpoint(sourceExpr, state, Space.Iteration(S"state", h, rest, Space.Singleton(Path.Deref(h))))
    val fixpointIterRangeTailExpr = Space.Fixpoint(multiTailSource, state, Space.Iteration(S"state", h, rest, Space.Range(S"tail", 0, 1)))
    val fixpointIterRangeReconstructExpr = Space.Fixpoint(
      multiTailSource,
      state,
      Space.Iteration(S"state", h, rest, Space.Singleton(Path.Deref(h)) x Space.Range(S"tail", 0, 1))
    )
    val rangeTailExpr = Space.Iteration(multiTailSource, h, rest, Space.Range(S"tail", 0, 1))
    val rangeHeadExpr = Space.Iteration(multiTailSource, h, rest, Space.Range(Space.Singleton(Path.Deref(h)), 0, 1))
    val rangeReconstructExpr = Space.Iteration(multiTailSource, h, rest, Space.Singleton(Path.Deref(h)) x Space.Range(S"tail", 0, 1))
    val prefixedRangeReconstructExpr =
      Space.Iteration(multiTailSource, h, rest, Space.Singleton(Path.Constant(Syntax.parse("tag")) x Path.Deref(h)) x Space.Range(S"tail", 0, 1))
    val tagged = transpileZ(taggedExpr)
    val prefixedReconstruct = transpileZ(prefixedReconstructExpr)
    val rangeTail = transpileZ(rangeTailExpr)
    val rangeHead = transpileZ(rangeHeadExpr)
    val rangeReconstruct = transpileZ(rangeReconstructExpr)
    val prefixedRangeReconstruct = transpileZ(prefixedRangeReconstructExpr)
    val fixpointTail = transpileZ(fixpointTailExpr)
    val fixpointIterTail = transpileZ(fixpointIterTailExpr)
    val fixpointIterHead = transpileZ(fixpointIterHeadExpr)
    val fixpointIterRangeTail = transpileZ(fixpointIterRangeTailExpr)
    val fixpointIterRangeReconstruct = transpileZ(fixpointIterRangeReconstructExpr)
    val pushed = Vector(prefixedTailExpr, prefixedHeadExpr, filteredTailExpr, subtractedTailExpr, composedTailExpr, tailClosureExpr).map(transpileZ(_))

    assert(tails.isInstanceOf[SpaceZipper.TailsUnion], "tail template should lower to TailsUnion")
    assert(heads match
      case SpaceZipper.Head(_) | SpaceZipper.Memo(SpaceZipper.Head(_)) => true
      case _ => false
    , "head template should lower to Head")
    assert(reconstruct.isInstanceOf[SpaceZipper.NonEmpty], "reconstruct template should lower to NonEmpty")
    assert(pushed.forall(!containsIteration(_)), "pushable iteration templates should stay algebraic instead of falling back to Iteration")
    val tagPrefix = TrieSpace.intern(Syntax.parse("tag"))
    assert(prefixedReconstruct match
      case SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.PrefixedReconstruct(`tagPrefix`))) |
          SpaceZipper.Memo(SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.PrefixedReconstruct(`tagPrefix`)))) => true
      case _ => false
    , s"tag.head.tail should lower to a reifiable PrefixedReconstruct iteration, saw $prefixedReconstruct")
    assert(tagged match
      case SpaceZipper.Iteration(_, _, None) | SpaceZipper.Memo(SpaceZipper.Iteration(_, _, None)) => true
      case _ => false
    , "general iteration should lower to lazy Iteration")
    assert(tagged.concrete.isEmpty, "general iteration zipper must not expose a materialized concrete result")
    val outKey = TrieSpace.intern(Syntax.parse("out")).head
    assertEquals(tagged.child(outKey).toSpaceValue, SpaceValue("a.1", "a.extra", "b.2", "b.extra", "c.3", "c.extra"))
    assert(rangeTail match
      case SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.RangeTail(0, 1))) |
          SpaceZipper.Memo(SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.RangeTail(0, 1)))) => true
      case _ => false
    , s"dependent Range(tail, ...) should lower to a reifiable lazy Iteration, saw $rangeTail")
    assert(rangeReconstruct match
      case SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.RangeReconstruct(0, 1))) |
          SpaceZipper.Memo(SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.RangeReconstruct(0, 1)))) => true
      case _ => false
    , s"head x Range(tail, ...) should lower to a reifiable lazy Iteration, saw $rangeReconstruct")
    assert(prefixedRangeReconstruct match
      case SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(`tagPrefix`, 0, 1))) |
          SpaceZipper.Memo(SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(`tagPrefix`, 0, 1)))) => true
      case _ => false
    , s"tag.head x Range(tail, ...) should lower to a reifiable lazy Iteration, saw $prefixedRangeReconstruct")
    assert(hasFixpointTag(fixpointTail, SpaceZipper.IterTemplateTag.Tail),
      s"Fixpoint(_, state, TailsUnion(state)) should stay as a reifiable zipper Fixpoint, saw $fixpointTail")
    assert(hasFixpointTag(fixpointIterTail, SpaceZipper.IterTemplateTag.Tail),
      s"Fixpoint(_, state, state.iter(... tail ...)) should lower to zipper Fixpoint(Tail), saw $fixpointIterTail")
    assert(hasFixpointTag(fixpointIterHead, SpaceZipper.IterTemplateTag.Head),
      s"Fixpoint(_, state, state.iter(... head ...)) should lower to zipper Fixpoint(Head), saw $fixpointIterHead")
    assert(hasFixpointTag(fixpointIterRangeTail, SpaceZipper.IterTemplateTag.RangeTail(0, 1)),
      s"Fixpoint(_, state, state.iter(... Range(tail) ...)) should lower to zipper Fixpoint(RangeTail), saw $fixpointIterRangeTail")
    assert(hasFixpointTag(fixpointIterRangeReconstruct, SpaceZipper.IterTemplateTag.RangeReconstruct(0, 1)),
      s"Fixpoint(_, state, state.iter(... head x Range(tail) ...)) should lower to zipper Fixpoint(RangeReconstruct), saw $fixpointIterRangeReconstruct")

    val generalExpr = taggedExpr
    assertEquals(tails.toSpaceValue, eval(Space.TailsUnion(sourceExpr)))
    assertEquals(heads.toSpaceValue, SpaceValue("a", "b", "c"))
    assertEquals(reconstruct.toSpaceValue, eval(sourceExpr))
    Vector(prefixedTailExpr, prefixedHeadExpr, filteredTailExpr, subtractedTailExpr, composedTailExpr, tailClosureExpr).zip(pushed).foreach { (expr, z) =>
      assertEquals(z.toSpaceValue, eval(expr), s"pushed iteration mismatch for ${expr.show}")
    }
    assertEquals(prefixedReconstruct.toSpaceValue, eval(prefixedReconstructExpr))
    assertEquals(tagged.toSpaceValue, eval(generalExpr))
      assertEquals(rangeTail.toSpaceValue, SpaceValue("1", "3", "4"))
      assertEquals(rangeHead.toSpaceValue, SpaceValue("a", "b", "c"))
      assertEquals(rangeReconstruct.toSpaceValue, SpaceValue("a.1", "b.3", "c.4"))
      assertEquals(prefixedRangeReconstruct.toSpaceValue, SpaceValue("tag.a.1", "tag.b.3", "tag.c.4"))
      assertEquals(fixpointTail.toSpaceValue, eval(fixpointTailExpr))
      assertEquals(fixpointIterTail.toSpaceValue, eval(fixpointIterTailExpr))
      assertEquals(fixpointIterHead.toSpaceValue, eval(fixpointIterHeadExpr))
      assertEquals(fixpointIterRangeTail.toSpaceValue, eval(fixpointIterRangeTailExpr))
      assertEquals(fixpointIterRangeReconstruct.toSpaceValue, eval(fixpointIterRangeReconstructExpr))

    val exactHead = SpaceZipper.head(
      SpaceZipper.subtraction(
        SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("a.1", "b.2"))),
        SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("a.1")))
      )
    )
    assertEquals(exactHead.toSpaceValue, SpaceValue("b"))
  }

  test("zipper transpilation executes nonrecursive helpers with path and space arguments") {
    val helper = R"zipper_helper"(P"prefix", S"input") :=
      (P"prefix" x S"input") \/ ("tails" x \/(S"input"))
    val call = R"zipper_helper"("tag", Space.Literal(SpaceValue("a.1", "a.2", "b.3")))
    val routines = mod(helper)
    assertEquals(evalZ(call)(using PathContext.emptyMap, ZipperSpaceContext.emptyMap, routines).toSpaceValue,
      eval(call)(using PathContext.emptyMap, SpaceContextMap(Map.empty), routines))
  }

  test("semi-naive helper recursion auto-lowers to a lazy exact zipper fixpoint") {
    val edges = Space.Literal(SpaceValue("edge.a.b", "edge.b.c", "edge.c.d"))
    val routine = DatalogExample.semiNaiveTransitive
    val call = routine.name(DatalogExample.semiNaiveInitial(edges))("complete.path")
    val routines = mod(routine)
    val (zipper, construction) = ExecutorCostMeter.measure(
      transpileZ(call)(using PathContext.emptyMap, ZipperSpaceContext.emptyMap, routines))
    assertEquals(construction.rounds, 0L, s"recursive helper construction must stay lazy: $construction")
    assertEquals(zipper.toSpaceValue,
      eval(call)(using PathContext.emptyMap, SpaceContextMap(Map.empty), routines))
  }

  test("synchronous evalZ rounds execute in native trie algebra and scale with the closure") {
    def measured(size: Int): (TrieSpace, ExecutorCostCounts) =
      val edges = Space.Literal(SpaceValue((0 until size).map { index =>
        Syntax.parse(s"edge.n$index.n${index + 1}")
      }.toSet))
      val routine = DatalogExample.semiNaiveTransitive
      val call = routine.name(DatalogExample.semiNaiveInitial(edges))("complete.path")
      ExecutorCostMeter.measure(evalZ(call)(using rc = mod(routine)))

    val (small, smallCost) = measured(20)
    val (large, largeCost) = measured(40)
    assertEquals(small.pathCount, 210)
    assertEquals(large.pathCount, 820)
    assert(largeCost.nodeVisits <= smallCost.nodeVisits * 6,
      s"native synchronous work regressed beyond closure growth: small=$smallCost large=$largeCost")
    assert(largeCost.allocations <= smallCost.allocations * 5,
      s"native synchronous allocation regressed beyond closure growth: small=$smallCost large=$largeCost")
  }

  test("divide-and-conquer SCC stays construction-lazy and agrees after full traversal") {
    val (zipper, construction) = ExecutorCostMeter.measure(
      transpileZ(SccCornerstone.body)(using PathContext.emptyMap, ZipperSpaceContext.emptyMap, SccCornerstone.rc)
    )
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head
    val (reachable, focusedCost) = ExecutorCostMeter.measure(zipper.child(a).child(b).terminal)

    assertEquals(construction.rounds, 0L, s"fixpoint construction performed eager rounds: $construction")
    assert(reachable, s"a.b should be emitted by the SCC representative partition; cost=$focusedCost")
    assertEquals(zipper.toSpaceValue, SccCornerstone.expected)
  }

  test("generic iteration fixpoint uses exact rounds across head propagation") {
    val state = SpaceMention("multi_round_state")
    def enables(prefix: String, output: String, suffix: String): Space =
      val head = PathRef(s"${prefix}_head")
      val rest = SpaceMention(s"${prefix}_rest")
      Space.Iteration(
        Space.Unwrap(Space.Mention(state), Path.Constant(Syntax.parse(prefix))),
        head,
        rest,
        Space.Singleton(Path.Constant(Syntax.parse(s"$output.$suffix"))),
      )
    val expression = Space.Fixpoint(
      Space.Literal(SpaceValue("a.seed")),
      state,
      enables("a", "b", "seed") \/ enables("b", "c", "seed") \/ enables("c", "d", "seed"),
    )
    val (zipper, construction) = ExecutorCostMeter.measure(transpileZ(expression))
    val d = TrieSpace.intern(Syntax.parse("d.seed"))
    val (found, demandCost) = ExecutorCostMeter.measure(d.foldLeft(zipper)((z, item) => z.child(item)).terminal)

    assertEquals(construction.rounds, 0L)
    assert(found, s"new heads must feed later exact rounds: $demandCost")
    assert(demandCost.rounds >= 3L, s"expected multi-round propagation, saw $demandCost")
    assertEquals(zipper.toSpaceValue, SpaceValue("a.seed", "b.seed", "c.seed", "d.seed"))
  }

  test("causal wrapped fixpoint remains prefix-demanded across propagation rounds") {
    val state = SpaceMention("wrapped_demand_state")
    val a = Path.Constant(Syntax.parse("a"))
    val limit = Space.Literal(SpaceValue("a", "a.a", "a.a.a"))
    val expression = Space.Fixpoint(
      Space.Literal(SpaceValue(PathValue(Nil))),
      state,
      Space.Intersection(Space.Wrap(Space.Mention(state), a), limit),
    )
    val expected = SpaceValue(
      PathValue(Nil),
      Syntax.parse("a"),
      Syntax.parse("a.a"),
      Syntax.parse("a.a.a"),
    )
    val (zipper, construction) = ExecutorCostMeter.measure(transpileZ(expression))
    val deepest = TrieSpace.intern(Syntax.parse("a.a.a"))
    val (found, demandCost) = ExecutorCostMeter.measure(
      deepest.foldLeft(zipper)((focus, item) => focus.child(item)).terminal,
    )

    assertEquals(construction.rounds, 0L)
    assert(found, s"causal prefix dependencies must propagate to the bounded depth: $demandCost")
    assert(demandCost.rounds >= 3L, s"expected several demanded prefix rounds: $demandCost")
    assertEquals(zipper.toSpaceValue, expected)
    assertEquals(zipper.toSpaceValue, eval(expression))
  }

  test("tail-emitting generic iteration uses the exact fixpoint fallback") {
    val state = SpaceMention("iteration_productivity_state")
    val head = PathRef("iteration_productivity_head")
    val rest = SpaceMention("iteration_productivity_rest")
    val expression = Space.Fixpoint(
      Space.Literal(SpaceValue("a")),
      state,
      Space.Iteration(
        Space.Mention(state),
        head,
        rest,
        Space.Mention(rest) \/ Space.Literal(SpaceValue("x")),
      ),
    )
    val expected = SpaceValue(PathValue(Nil), Syntax.parse("a"), Syntax.parse("x"))
    val (zipper, construction) = ExecutorCostMeter.measure(transpileZ(expression))
    val (nullable, observation) = ExecutorCostMeter.measure(zipper.terminal)

    assertEquals(construction.rounds, 0L)
    assert(nullable, s"the first exact iteration round emits epsilon: $observation")
    assert(observation.rounds > 0L,
      s"generic tail binding must not enter the non-productive prefix solver: $observation")
    assertEquals(zipper.toSpaceValue, expected)
    assertEquals(zipper.toSpaceValue, eval(expression))
  }

  test("state-dependent tails intersection uses the lazy exact fixpoint fallback") {
    val state = SpaceMention("tails_intersection_state")
    val expression = Space.Fixpoint(
      Space.Literal(SpaceValue("a", "b")),
      state,
      Space.Literal(SpaceValue("x.z")) \/
        Space.TailsIntersection(Space.Mention(state)),
    )
    val expected = SpaceValue(
      PathValue(Nil),
      Syntax.parse("a"),
      Syntax.parse("b"),
      Syntax.parse("x.z"),
    )
    val (zipper, construction) = ExecutorCostMeter.measure(transpileZ(expression))
    val focusedPath = TrieSpace.intern(Syntax.parse("x.z"))
    val (found, focusedCost) = ExecutorCostMeter.measure(
      focusedPath.foldLeft(zipper)((focus, item) => focus.child(item)).terminal,
    )

    assertEquals(construction.rounds, 0L,
      s"even an exact fallback must remain lazy until observation: $construction")
    assert(found, s"the focused literal branch must terminate without expanding a cyclic MeetAll: $focusedCost")
    assert(focusedCost.rounds > 0L,
      s"an unproved order-sensitive step must run synchronous rounds, not prefix cells: $focusedCost")
    assertEquals(zipper.toSpaceValue, expected)
    assertEquals(zipper.toSpaceValue, eval(expression))
  }

  test("state-dependent unwrap uses the productive exact fixpoint fallback") {
    val state = SpaceMention("unwrap_fixpoint_state")
    val expression = Space.Fixpoint(
      Space.Literal(SpaceValue("a")),
      state,
      Space.Unwrap(Space.Mention(state), Path.Constant(Syntax.parse("a"))),
    )
    val expected = SpaceValue(PathValue(Nil), Syntax.parse("a"))
    val (zipper, construction) = ExecutorCostMeter.measure(transpileZ(expression))
    val (nullable, observation) = ExecutorCostMeter.measure(zipper.terminal)

    assertEquals(construction.rounds, 0L)
    assert(nullable, s"the exact first round exposes epsilon: $observation")
    assert(observation.rounds > 0L,
      s"state-dependent Unwrap must not enter the non-productive prefix solver: $observation")
    assertEquals(zipper.toSpaceValue, expected)
    assertEquals(zipper.toSpaceValue, eval(expression))
  }

  test("union-wrapped recursive tails union uses the exact fixpoint fallback") {
    val state = SpaceMention("nested_tails_union_state")
    val expression = Space.Fixpoint(
      Space.Literal(SpaceValue("a")),
      state,
      Space.TailsUnion(Space.Mention(state)) \/ Space.Literal(SpaceValue("x")),
    )
    val expected = SpaceValue(PathValue(Nil), Syntax.parse("a"), Syntax.parse("x"))
    val (zipper, construction) = ExecutorCostMeter.measure(transpileZ(expression))
    val (materialized, observation) = ExecutorCostMeter.measure(zipper.toSpaceValue)

    assertEquals(construction.rounds, 0L)
    assert(observation.rounds > 0L,
      s"a nested tail projection must not grow an unbounded prefix dependency cone: $observation")
    assertEquals(materialized, expected)
    assertEquals(materialized, eval(expression))
  }

  test("intersection enumerates a hinted frontier without sizing an unknown operand") {
    val delegate = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("keep.hit", "other.value")))
    var unknownKeysEnumerated = false
    val noHint = new SpaceZipper:
      override def terminal: Boolean = delegate.terminal
      override def child(item: Int): SpaceZipper = delegate.child(item)
      override def childKeys: IterableOnce[Int] =
        unknownKeysEnumerated = true
        delegate.childKeys
    val demand = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("keep.hit")))
    val result = SpaceZipper.intersection(noHint, demand)

    assertEquals(result.toSpaceValue, SpaceValue("keep.hit"))
    assert(!unknownKeysEnumerated, "the no-hint operand should receive membership probes, not frontier enumeration")
  }

  test("memoized union emptiness does not enumerate descendant key frontiers") {
    var enumerated = false
    def nonEmptyTrap(label: String): SpaceZipper = new SpaceZipper:
      override def terminal: Boolean = false
      override def isEmpty: Boolean = false
      override def child(item: Int): SpaceZipper = SpaceZipper.empty
      override def childKeys: IterableOnce[Int] =
        enumerated = true
        fail(s"$label descendant keys were enumerated by an emptiness probe")

    val joined = SpaceZipper.union(nonEmptyTrap("left"), nonEmptyTrap("right"))
    val (_, cost) = ExecutorCostMeter.measure(assert(!joined.isEmpty))

    assert(!enumerated)
    assertEquals(cost.nodeVisits, 0L,
      s"propagated exact emptiness should not perform a child-membership traversal: $cost")
  }

  test("size-only zipper merges use native aggregate counts without width scans") {
    def measured(width: Int): Vector[(Int, ExecutorCostCounts)] =
      val left = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue(
        (0 until width).map(i => Syntax.parse(s"left.$i")).toSet)))
      val right = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue(
        (0 until width).map(i => Syntax.parse(s"right.$i")).toSet)))
      Vector(
        ExecutorCostMeter.measure(SpaceZipper.union(left, right).pathCount),
        ExecutorCostMeter.measure(SpaceZipper.intersection(left, right).pathCount),
        ExecutorCostMeter.measure(SpaceZipper.subtraction(left, right).pathCount),
      )
    val small = measured(64)
    val large = measured(4096)

    assertEquals(small.map(_._1), Vector(128, 0, 64))
    assertEquals(large.map(_._1), Vector(8192, 0, 4096))
    assertEquals(large.map(_._2.patriciaVisits), small.map(_._2.patriciaVisits),
      s"disjoint size-only merges should not scale with an untouched width: small=$small large=$large")
  }

  test("tail fixpoint answers a focused child without eager Kleene rounds") {
    val source = Space.Literal(SpaceValue(
      (0 until 256).map(i => Syntax.parse(s"root.$i.leaf")).toSet,
    ))
    val state = SpaceMention("focused_fixpoint_state")
    val zipper = transpileZ(Space.Fixpoint(source, state, Space.TailsUnion(Space.Mention(state))))
    val root = TrieSpace.intern(Syntax.parse("root")).head
    val (focused, cost) = ExecutorCostMeter.measure(zipper.child(root).toSpaceValue)
    assertEquals(focused.paths.size, 256)
    assertEquals(cost.rounds, 0L, s"tail closure should use its demand-driven frontier, saw $cost")
  }

  test("zipper range over virtual operands stays a border traversal") {
    val left = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("a.1", "b.1", "d.1")))
    val right = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("a.2", "c.1", "e.1")))
    val union = SpaceZipper.union(left, right)
    val firstTwo = SpaceZipper.range(union, 0, 2)
    val nested = SpaceZipper.range(SpaceZipper.range(union, 0, 4), 2, 3)
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head

    assert(union.concrete.nonEmpty, "the union can report a concrete value when asked")
    assert(firstTwo.concrete.isEmpty, "Range over a virtual union should not pre-materialize the union")
    assert(nested.concrete.isEmpty, "nested Range over a virtual union should remain a virtual slice")
    assertEquals(firstTwo.child(a).toSpaceValue, SpaceValue("1", "2"))
    assert(firstTwo.child(b).isEmpty, "virtual Range child lookup should prune siblings outside the slice")
    assertEquals(firstTwo.toSpaceValue, eval(Space.Range(Space.Literal(left.materialize.toSpaceValue) \/ Space.Literal(right.materialize.toSpaceValue), 0, 2)))
    assertEquals(nested.toSpaceValue, eval(Space.Range(Space.Range(Space.Literal(left.materialize.toSpaceValue) \/ Space.Literal(right.materialize.toSpaceValue), 0, 4), 2, 3)))

    val tag = TrieSpace.intern(Syntax.parse("tag"))
    val wrapped = SpaceZipper.wrap(union, tag)
    val firstWrapped = SpaceZipper.range(wrapped, 0, 2)
    assert(firstWrapped.concrete.isEmpty, "Range over a prefixed virtual union should not materialize the union")
    assert(firstWrapped match
      case SpaceZipper.Memo(SpaceZipper.Prefix(`tag`, SpaceZipper.Range(_, _, _))) => true
      case _ => false
    , s"expected prefixed Range to stay as Prefix(Range(...)), saw $firstWrapped")
    assertEquals(firstWrapped.child(tag.head).toSpaceValue, firstTwo.toSpaceValue)
    assertEquals(firstWrapped.toSpaceValue,
      eval(Space.Range(Space.Wrap(Space.Literal(left.materialize.toSpaceValue) \/ Space.Literal(right.materialize.toSpaceValue), Path.Constant(Syntax.parse("tag"))), 0, 2)))
  }

  test("zipper range supports to-end and negative border slices virtually") {
    val left = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue(PathValue(Nil), "a.1", "b.1", "d.1")))
    val right = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("a.2", "c.1", "e.1")))
    val union = SpaceZipper.union(left, right)
    val sourceExpr = Space.Literal(left.materialize.toSpaceValue) \/ Space.Literal(right.materialize.toSpaceValue)

    val toEnd = SpaceZipper.range(union, 2, 0)
    val dropLast = SpaceZipper.range(union, 0, -2)
    val lastTwo = SpaceZipper.range(union, -2, 0)
    val negativeWindow = SpaceZipper.range(union, -4, -1)

    assert(toEnd.concrete.isEmpty, "Range(start, 0) over a virtual union should stay virtual")
    assert(dropLast.concrete.isEmpty, "Range(0, -n) over a virtual union should stay virtual")
    assert(lastTwo.concrete.isEmpty, "Range(-n, 0) over a virtual union should stay virtual")
    assert(negativeWindow.concrete.isEmpty, "Range(-n, -m) over a virtual union should stay virtual")

    assertEquals(toEnd.toSpaceValue, eval(Space.Range(sourceExpr, 2, 0)))
    assertEquals(dropLast.toSpaceValue, eval(Space.Range(sourceExpr, 0, -2)))
    assertEquals(lastTwo.toSpaceValue, eval(Space.Range(sourceExpr, -2, 0)))
    assertEquals(negativeWindow.toSpaceValue, eval(Space.Range(sourceExpr, -4, -1)))
  }

  test("zipper range-reconstruct iteration descends directly to the matching branch") {
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head
    val tag = TrieSpace.intern(Syntax.parse("tag"))
    val included = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("1", "2")))
    val forbidden = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("9")))
    var forbiddenChildTouched = false
    val source = new SpaceZipper:
      override def terminal: Boolean = false
      override def child(item: Int): SpaceZipper =
        if item == a then included
        else if item == b then
          forbiddenChildTouched = true
          forbidden
        else SpaceZipper.empty
      override def hasChild(item: Int): Boolean =
        item == a || item == b
      override def childKeys: IterableOnce[Int] =
        Iterator(a, b)
      override def childrenIterator: Iterator[(Int, SpaceZipper)] =
        Iterator(a -> included, b -> forbidden)

    val rangeReconstruct = SpaceZipper.iteration(
      source,
      (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, 0, 1), List(head)),
      Some(SpaceZipper.IterTemplateTag.RangeReconstruct(0, 1))
    )
    assertEquals(rangeReconstruct.child(a).toSpaceValue, SpaceValue("1"))
    assert(!forbiddenChildTouched, "RangeReconstruct.child(a) should not build or inspect the b branch")

    val prefixedRangeReconstruct = SpaceZipper.iteration(
      source,
      (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, 0, 1), tag :+ head),
      Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(tag, 0, 1))
    )
    val afterTag = prefixedRangeReconstruct.child(tag.head)
    assert(!forbiddenChildTouched, "PrefixedRangeReconstruct.child(tag) should only peel the static prefix")
    assertEquals(afterTag.child(a).toSpaceValue, SpaceValue("1"))
    assert(!forbiddenChildTouched, "PrefixedRangeReconstruct.child(tag).child(a) should not inspect the b branch")
  }

  test("zipper range stops before asking the first excluded border child for size") {
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head
    val included = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("1", "2")))
    var excludedPathCountTouched = false
    val excluded = new SpaceZipper:
      override def terminal: Boolean = true
      override def child(item: Int): SpaceZipper = SpaceZipper.empty
      override def childKeys: IterableOnce[Int] = Iterator.empty
      override lazy val pathCount: Int =
        excludedPathCountTouched = true
        1
    val parent = new SpaceZipper:
      override def terminal: Boolean = false
      override def child(item: Int): SpaceZipper =
        if item == a then included else if item == b then excluded else SpaceZipper.empty
      override def hasChild(item: Int): Boolean = item == a || item == b
      override def childKeys: IterableOnce[Int] = Iterator(a, b)
      override def childrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> included, b -> excluded)
      override def orderedChildrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> included, b -> excluded)
      override lazy val pathCount: Int = 3

    val firstTwo = SpaceZipper.range(parent, 0, 2)
    assert(firstTwo.child(b).isEmpty)
    assert(!excludedPathCountTouched, "Range.child should prune at hi before touching the excluded child size")
    assertEquals(firstTwo.childrenIterator.toVector.map(_._1), Vector(a))
    assert(!excludedPathCountTouched, "Range.childrenIterator should not size the first excluded child")
  }

  test("zipper range child lookup does not size unrelated in-slice siblings") {
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head
    val included = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("1", "2")))
    var siblingPathCountTouched = false
    val sibling = new SpaceZipper:
      override def terminal: Boolean = true
      override def child(item: Int): SpaceZipper = SpaceZipper.empty
      override def childKeys: IterableOnce[Int] = Iterator.empty
      override lazy val pathCount: Int =
        siblingPathCountTouched = true
        1
    val parent = new SpaceZipper:
      override def terminal: Boolean = false
      override def child(item: Int): SpaceZipper =
        if item == a then included else if item == b then sibling else SpaceZipper.empty
      override def hasChild(item: Int): Boolean = item == a || item == b
      override def childKeys: IterableOnce[Int] = Iterator(a, b)
      override def childrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> included, b -> sibling)
      override def orderedChildrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> included, b -> sibling)
      override lazy val pathCount: Int = 3

    val firstThree = SpaceZipper.range(parent, 0, 3)
    assertEquals(firstThree.child(a).toSpaceValue, SpaceValue("1", "2"))
    assert(!siblingPathCountTouched, "Range.child(a) should not size an unrelated b sibling inside the slice")
  }

  test("zipper range direct child movement does not size the matching border child") {
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head
    var firstPathCountTouched = false
    var lastPathCountTouched = false
    var dropPathCountTouched = false

    def counted(paths: SpaceValue, mark: () => Unit): SpaceZipper =
      val trie = TrieSpace.fromSpaceValue(paths)
      new SpaceZipper:
        override def terminal: Boolean = trie.terminal
        override def child(item: Int): SpaceZipper =
          trie.children.get(item).fold(SpaceZipper.empty)(SpaceZipper.traversal)
        override def hasChild(item: Int): Boolean =
          trie.children.contains(item)
        override def childKeys: IterableOnce[Int] =
          trie.children.keysIterator
        override def childrenIterator: Iterator[(Int, SpaceZipper)] =
          trie.children.iterator.map((item, child) => item -> SpaceZipper.traversal(child))
        override def orderedChildrenIterator: Iterator[(Int, SpaceZipper)] =
          trie.orderedChildren.iterator.map((item, child) => item -> SpaceZipper.traversal(child))
        override lazy val orderedChildren: Array[(Int, SpaceZipper)] =
          trie.orderedChildren.map((item, child) => item -> SpaceZipper.traversal(child))
        override lazy val pathCount: Int =
          mark()
          trie.pathCount

    val firstChild = counted(SpaceValue("1", "2"), () => firstPathCountTouched = true)
    val lastChild = counted(SpaceValue("3", "4"), () => lastPathCountTouched = true)
    val dropChild = counted(SpaceValue("3", "4"), () => dropPathCountTouched = true)

    val firstParent = new SpaceZipper:
      override def terminal: Boolean = false
      override def child(item: Int): SpaceZipper =
        if item == a then firstChild else if item == b then lastChild else SpaceZipper.empty
      override def hasChild(item: Int): Boolean = item == a || item == b
      override def childKeys: IterableOnce[Int] = Iterator(a, b)
      override def childrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> firstChild, b -> lastChild)
      override def orderedChildrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> firstChild, b -> lastChild)

    val lastParent = new SpaceZipper:
      override def terminal: Boolean = false
      override def child(item: Int): SpaceZipper =
        if item == a then firstChild else if item == b then lastChild else SpaceZipper.empty
      override def hasChild(item: Int): Boolean = item == a || item == b
      override def childKeys: IterableOnce[Int] = Iterator(a, b)
      override def childrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> firstChild, b -> lastChild)
      override lazy val orderedChildren: Array[(Int, SpaceZipper)] = Array(a -> firstChild, b -> lastChild)

    val dropParent = new SpaceZipper:
      override def terminal: Boolean = false
      override def child(item: Int): SpaceZipper =
        if item == a then firstChild else if item == b then dropChild else SpaceZipper.empty
      override def hasChild(item: Int): Boolean = item == a || item == b
      override def childKeys: IterableOnce[Int] = Iterator(a, b)
      override def childrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> firstChild, b -> dropChild)
      override lazy val orderedChildren: Array[(Int, SpaceZipper)] = Array(a -> firstChild, b -> dropChild)

    val firstFocus = SpaceZipper.range(firstParent, 0, 1).child(a)
    assert(!firstPathCountTouched, "Range(0, 1).child(a) should return a lazy child slice without sizing a")
    assertEquals(firstFocus.toSpaceValue, SpaceValue("1"))

    val lastFocus = SpaceZipper.range(lastParent, -1, 0).child(b)
    assert(!lastPathCountTouched, "Range(-1, 0).child(b) should return a lazy right-border slice without sizing b")
    assertEquals(lastFocus.toSpaceValue, SpaceValue("4"))

    val dropFocus = SpaceZipper.range(dropParent, 0, -1).child(b)
    assert(!dropPathCountTouched, "Range(0, -1).child(b) should return a lazy drop-last slice without sizing b")
    assertEquals(dropFocus.toSpaceValue, SpaceValue("3"))
  }

  test("zipper negative range projections do not ask the parent for total path count") {
    val a = TrieSpace.intern(Syntax.parse("a")).head
    val b = TrieSpace.intern(Syntax.parse("b")).head
    val first = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("1", "2")))
    val second = SpaceZipper.traversal(TrieSpace.fromSpaceValue(SpaceValue("3", "4")))
    var parentPathCountTouched = false
    val parent = new SpaceZipper:
      override def terminal: Boolean = false
      override def child(item: Int): SpaceZipper =
        if item == a then first else if item == b then second else SpaceZipper.empty
      override def hasChild(item: Int): Boolean = item == a || item == b
      override def childKeys: IterableOnce[Int] = Iterator(a, b)
      override def childrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> first, b -> second)
      override def orderedChildrenIterator: Iterator[(Int, SpaceZipper)] = Iterator(a -> first, b -> second)
      override lazy val orderedChildren: Array[(Int, SpaceZipper)] = Array(a -> first, b -> second)
      override lazy val pathCount: Int =
        parentPathCountTouched = true
        4

    assertEquals(SpaceZipper.range(parent, -1, 0).toSpaceValue, SpaceValue("b.4"))
    assert(!parentPathCountTouched, "Range(-n, 0) should walk the right border instead of normalizing from parent pathCount")
    assertEquals(SpaceZipper.range(parent, 0, -1).toSpaceValue, SpaceValue("a.1", "a.2", "b.3"))
    assert(!parentPathCountTouched, "Range(0, -n) should drop the right border instead of normalizing from parent pathCount")
  }

  test("space-to-zipper evaluator agrees with reference and trie evaluation on random programs") {
    val rng = Random(0x51a55a5eedL)
    val mentions = Vector(SpaceMention("x"), SpaceMention("y"), SpaceMention("z"))
    val emptyDefs = PartialFunction.empty[RoutinePtr, Routine]

    for i <- 0 until 80 do
      val ctx = SpaceContextMap(mentions.map(sm => sm -> randomSpaceValue(rng, maxPaths = 5)).toMap)
      val tctx = TrieSpaceContext.fromReference(ctx)
      val zctx = ZipperSpaceContext.fromTrie(tctx)
      val expr = randomSpace(rng, mentions, Vector.empty, depth = 4)
      val expected = eval(expr)(using PathContext.emptyMap, ctx, emptyDefs)

      if expected.paths.size <= 220 then
        assertEquals(evalTrieValue(expr)(using PathContext.emptyMap, tctx, emptyDefs), expected, s"evalTrie mismatch for ${expr.show}")
        assertEquals(evalZValue(expr)(using PathContext.emptyMap, zctx, emptyDefs), expected, s"evalZ mismatch for ${expr.show}")
    end for
  }

  test("random trie-native programs agree across eval, evalTrie, exec, and execT") {
    val rng = Random(0x5eed5eedL)
    val mentions = Vector(SpaceMention("x"), SpaceMention("y"), SpaceMention("z"))
    val emptyDefs = PartialFunction.empty[RoutinePtr, Routine]
    var accepted = 0
    var attempts = 0

    while accepted < 40 && attempts < 400 do
      attempts += 1
      val ctx = SpaceContextMap(mentions.map(sm => sm -> randomSpaceValue(rng, maxPaths = 5)).toMap)
      val tctx = TrieSpaceContext.fromReference(ctx)
      val zctx = ZipperSpaceContext.fromTrie(tctx)
      val expr = randomSpace(rng, mentions, Vector.empty, depth = 4)
      val expected = eval(expr)(using PathContext.emptyMap, ctx, emptyDefs)

      if expected.paths.size <= 180 then
        val routine = Routine(RoutinePtr(s"random_eval_exec_$accepted"), Vector.empty, mentions, expr)
        val graph = optimize(transpile(routine))
        assertGraphWellScoped(graph, s"random program $accepted")
        assertEquals(evalTrieValue(expr)(using PathContext.emptyMap, tctx, emptyDefs), expected, s"evalTrie mismatch for ${expr.show}")
        assertEquals(evalZValue(expr)(using PathContext.emptyMap, zctx, emptyDefs), expected, s"evalZ mismatch for ${expr.show}")
        assertEquals(execValue(graph, mentions, ctx), expected, s"exec mismatch for ${expr.show}")
        assertEquals(execTValue(graph, mentions, tctx), expected, s"execT mismatch for ${expr.show}")
        accepted += 1

    assertEquals(accepted, 40)
  }
