package morkl

import munit.FunSuite

class ZipperDenotationOracleTest extends FunSuite:
  private val alphabet: Vector[Int] =
    Vector("a", "b").map(s => TrieSpace.interner.intern(PathItem(s)))

  private def pathsUpTo(maxLen: Int): Vector[List[Int]] =
    def exact(n: Int): Vector[List[Int]] =
      if n == 0 then Vector(Nil)
      else
        for
          prefix <- exact(n - 1)
          item <- alphabet
        yield prefix :+ item
    (0 to maxLen).iterator.flatMap(exact).toVector

  private def allSpaces(maxLen: Int): Vector[TrieSpace] =
    val paths = pathsUpTo(maxLen)
    require(paths.length <= 30, s"too many paths for bit-subset enumeration: ${paths.length}")
    Vector.tabulate(1 << paths.length) { mask =>
      val kept = paths.indices.iterator.collect {
        case i if (mask & (1 << i)) != 0 => paths(i)
      }
      TrieSpace.fromEncodedPaths(kept.toVector)
    }

  private def z(space: TrieSpace): SpaceZipper =
    SpaceZipper.traversal(space)

  private def checkObservation(name: String, zipper: SpaceZipper, expected: TrieSpace): Unit =
    assertEquals(zipper.observation, SpaceZipper.Observation.fromTrie(expected), s"$name observation mismatch")

  private def checkUnary(name: String, spaces: Vector[TrieSpace])
                        (zipperOp: SpaceZipper => SpaceZipper)
                        (trieOp: TrieSpace => TrieSpace): Unit =
    spaces.zipWithIndex.foreach { (space, i) =>
      val actualZipper = zipperOp(z(space))
      val expectedTrie = trieOp(space)
      assertEquals(
        actualZipper.materialize,
        expectedTrie,
        s"$name mismatch for bounded space #$i"
      )
      checkObservation(s"$name bounded space #$i", actualZipper, expectedTrie)
    }

  private def checkBinary(name: String, spaces: Vector[TrieSpace])
                         (zipperOp: (SpaceZipper, SpaceZipper) => SpaceZipper)
                         (trieOp: (TrieSpace, TrieSpace) => TrieSpace): Unit =
    for
      (left, i) <- spaces.zipWithIndex
      (right, j) <- spaces.zipWithIndex
    do
      val actualZipper = zipperOp(z(left), z(right))
      val expectedTrie = trieOp(left, right)
      assertEquals(
        actualZipper.materialize,
        expectedTrie,
        s"$name mismatch for bounded spaces #$i and #$j"
      )
      checkObservation(s"$name bounded spaces #$i and #$j", actualZipper, expectedTrie)

  private def allFoci(root: TrieSpace): Vector[TrieSpace.Zipper] =
    def rec(cursor: TrieSpace.Zipper): Vector[TrieSpace.Zipper] =
      cursor +: cursor.focus.orderedChildren.iterator.flatMap((item, _) => cursor.down(item).toVector.flatMap(rec)).toVector
    rec(TrieSpace.Zipper(root))

  private def allVirtualFoci(root: SpaceZipper): Vector[SpaceZipper.Cursor] =
    def rec(cursor: SpaceZipper.Cursor): Vector[SpaceZipper.Cursor] =
      cursor +: cursor.focus.orderedChildren.iterator.flatMap((item, _) => cursor.down(item).toVector.flatMap(rec)).toVector
    rec(SpaceZipper.Cursor(root))

  test("zipper algebra agrees with trie denotation on exhaustive small path sets") {
    val spaces = allSpaces(maxLen = 2)

    checkUnary("nonEmpty", spaces)(SpaceZipper.NonEmpty.apply)(_.diff(TrieSpace.epsilon))
    checkUnary("tailsUnion", spaces)(SpaceZipper.TailsUnion.apply)(_.tailsUnion)
    checkUnary("tailsIntersection", spaces)(SpaceZipper.TailsIntersection.apply)(_.tailsIntersection)
    checkUnary("prefixClosure", spaces)(s => SpaceZipper.PrefixClosure(s))(_.prefixClosure)
    checkUnary("suffixClosure", spaces)(SpaceZipper.SuffixClosure.apply)(_.suffixClosure)
    checkUnary("tailsClosure", spaces)(SpaceZipper.TailsClosure.apply)(_.tailsClosure)
    checkUnary("range-all", spaces)(s => SpaceZipper.range(s, 0, 0))(_.range(0, 0))
    checkUnary("range-first", spaces)(s => SpaceZipper.range(s, 0, 1))(_.range(0, 1))
    checkUnary("range-last", spaces)(s => SpaceZipper.range(s, -1, 0))(_.range(-1, 0))

    checkBinary("union", spaces)(SpaceZipper.union)(_.union(_))
    checkBinary("intersection", spaces)(SpaceZipper.intersection)(_.intersect(_))
    checkBinary("subtraction", spaces)(SpaceZipper.subtraction)(_.diff(_))
    checkBinary("restriction", spaces)(SpaceZipper.restriction)(_.restrictBy(_))
    checkBinary("raffination", spaces)((a, b) => SpaceZipper.subtraction(a, SpaceZipper.restriction(a, b)))(_.raffinate(_))
    checkBinary("concat", spaces)(SpaceZipper.concat)(_.concat(_))
  }

  test("child movement is the Brzozowski derivative on exhaustive length-three sets") {
    val spaces = allSpaces(maxLen = 3)
    for
      (space, i) <- spaces.zipWithIndex
      item <- alphabet
    do
      assertEquals(
        z(space).child(item).materialize,
        space.unwrapItems(item :: Nil),
        s"child derivative mismatch for bounded length-three space #$i and item ${TrieSpace.item(item).show}"
      )
  }

  test("suffix and tails closure descend through frontier states") {
    val a = alphabet(0)
    val b = alphabet(1)
    val root = TrieSpace.fromEncodedPaths(Vector(a :: b :: Nil, b :: a :: Nil, a :: Nil))

    val suffix = SpaceZipper.SuffixClosure(z(root))
    val suffixA = suffix.child(a)
    assert(
      suffixA.isInstanceOf[SpaceZipper.FrontierState],
      "SuffixClosure.child should stay in the Antimirov frontier-state representation"
    )
    suffixA match
      case SpaceZipper.FrontierState(SpaceZipper.FrontierTailUnion(_: SpaceZipper.SuffixClosure, `a`)) =>
      case other => fail(s"SuffixClosure.child used unexpected frontier state: $other")
    assertEquals(suffixA.materialize, root.suffixClosure.unwrapItems(a :: Nil))
    assertEquals(suffixA.child(b).materialize, root.suffixClosure.unwrapItems(a :: b :: Nil))

    val tails = SpaceZipper.TailsClosure(z(root))
    val tailsB = tails.child(b)
    assert(
      tailsB.isInstanceOf[SpaceZipper.FrontierState],
      "TailsClosure.child should stay in the Antimirov frontier-state representation"
    )
    tailsB match
      case SpaceZipper.FrontierState(SpaceZipper.FrontierTailUnion(_: SpaceZipper.TailsClosure, `b`)) =>
      case other => fail(s"TailsClosure.child used unexpected frontier state: $other")
    assertEquals(tails.materialize, root.tailsClosure)
    assertEquals(tailsB.materialize, root.tailsClosure.unwrapItems(b :: Nil))
  }

  test("iteration range templates agree with trie denotation on exhaustive small path sets") {
    val spaces = allSpaces(maxLen = 2)
    val prefix = alphabet.head :: Nil

    def iterateTrie(space: TrieSpace)(branch: (Int, TrieSpace) => TrieSpace): TrieSpace =
      TrieSpace.joinAll(space.children.iterator.map((item, child) => branch(item, child)))

    val cases = Vector[(String, SpaceZipper => SpaceZipper, TrieSpace => TrieSpace)](
      (
        "iter-tail",
        (src: SpaceZipper) => SpaceZipper.iteration(src, (_head, tail) => tail, Some(SpaceZipper.IterTemplateTag.Tail)),
        (space: TrieSpace) => space.tailsUnion
      ),
      (
        "iter-head",
        (src: SpaceZipper) => SpaceZipper.iteration(src, (head, _tail) => SpaceZipper.singleton(head :: Nil), Some(SpaceZipper.IterTemplateTag.Head)),
        (space: TrieSpace) => space.head
      ),
      (
        "iter-reconstruct",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (head, tail) => SpaceZipper.concat(SpaceZipper.singleton(head :: Nil), tail),
          Some(SpaceZipper.IterTemplateTag.Reconstruct)
        ),
        (space: TrieSpace) => space.nonEmptyPaths
      ),
      (
        "iter-range-tail-first",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (_head, tail) => SpaceZipper.range(tail, 0, 1),
          Some(SpaceZipper.IterTemplateTag.RangeTail(0, 1))
        ),
        (space: TrieSpace) => iterateTrie(space)((_, child) => child.range(0, 1))
      ),
      (
        "iter-range-tail-full-sentinel",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (_head, tail) => SpaceZipper.range(tail, 0, 0),
          Some(SpaceZipper.IterTemplateTag.RangeTail(0, 0))
        ),
        (space: TrieSpace) => iterateTrie(space)((_, child) => child.range(0, 0))
      ),
      (
        "iter-range-tail-drop-last",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (_head, tail) => SpaceZipper.range(tail, 0, -1),
          Some(SpaceZipper.IterTemplateTag.RangeTail(0, -1))
        ),
        (space: TrieSpace) => iterateTrie(space)((_, child) => child.range(0, -1))
      ),
      (
        "iter-range-reconstruct-first",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, 0, 1), head :: Nil),
          Some(SpaceZipper.IterTemplateTag.RangeReconstruct(0, 1))
        ),
        (space: TrieSpace) => iterateTrie(space)((item, child) => child.range(0, 1).wrapItems(item :: Nil))
      ),
      (
        "iter-range-reconstruct-full-sentinel",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, 0, 0), head :: Nil),
          Some(SpaceZipper.IterTemplateTag.RangeReconstruct(0, 0))
        ),
        (space: TrieSpace) => iterateTrie(space)((item, child) => child.range(0, 0).wrapItems(item :: Nil))
      ),
      (
        "iter-prefixed-range-reconstruct-first",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, 0, 1), prefix :+ head),
          Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(prefix, 0, 1))
        ),
        (space: TrieSpace) => iterateTrie(space)((item, child) => child.range(0, 1).wrapItems(prefix :+ item))
      ),
      (
        "iter-prefixed-range-reconstruct-drop-last",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, 0, -1), prefix :+ head),
          Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(prefix, 0, -1))
        ),
        (space: TrieSpace) => iterateTrie(space)((item, child) => child.range(0, -1).wrapItems(prefix :+ item))
      ),
      (
        "iter-prefixed-range-reconstruct-empty-slice",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, 1, 1), prefix :+ head),
          Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(prefix, 1, 1))
        ),
        (_: TrieSpace) => TrieSpace.empty
      ),
      (
        "iter-range-tail-empty-slice",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (_head, tail) => SpaceZipper.range(tail, 1, 1),
          Some(SpaceZipper.IterTemplateTag.RangeTail(1, 1))
        ),
        (_: TrieSpace) => TrieSpace.empty
      ),
      (
        "iter-range-reconstruct-drop-last",
        (src: SpaceZipper) => SpaceZipper.iteration(
          src,
          (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, 0, -1), head :: Nil),
          Some(SpaceZipper.IterTemplateTag.RangeReconstruct(0, -1))
        ),
        (space: TrieSpace) => iterateTrie(space)((item, child) => child.range(0, -1).wrapItems(item :: Nil))
      )
    )

    for
      (space, i) <- spaces.zipWithIndex
      (name, zipperOp, trieOp) <- cases
    do
      val actual = zipperOp(z(space)).materialize
      val expected = trieOp(space)
      assertEquals(actual, expected, s"$name mismatch for bounded space #$i")
  }

  test("finite fixpoint templates agree with trie denotation on exhaustive small path sets") {
    val spaces = allSpaces(maxLen = 2)
    def kleeneTrie(initial: TrieSpace)(step: TrieSpace => TrieSpace): TrieSpace =
      var current = initial
      var changed = true
      while changed do
        val next = current.union(step(current))
        changed = next != current
        current = next
      current

    val cases = Vector[(String, SpaceZipper.IterTemplateTag, TrieSpace => TrieSpace)](
      (
        "fixpoint-tail",
        SpaceZipper.IterTemplateTag.Tail,
        (space: TrieSpace) => space.tailsClosure
      ),
      (
        "fixpoint-head",
        SpaceZipper.IterTemplateTag.Head,
        (space: TrieSpace) => space.union(space.head)
      ),
      (
        "fixpoint-reconstruct",
        SpaceZipper.IterTemplateTag.Reconstruct,
        (space: TrieSpace) => space
      ),
      (
        "fixpoint-range-tail-first",
        SpaceZipper.IterTemplateTag.RangeTail(0, 1),
        (space: TrieSpace) =>
          kleeneTrie(space) { state =>
            TrieSpace.joinAll(state.children.valuesIterator.map(_.range(0, 1)))
          }
      ),
      (
        "fixpoint-range-tail-empty-slice",
        SpaceZipper.IterTemplateTag.RangeTail(1, 1),
        (space: TrieSpace) => space
      )
    )

    for
      (space, i) <- spaces.zipWithIndex
      (name, template, trieOp) <- cases
    do
      val actual = SpaceZipper.fixpoint(z(space), template).materialize
      val expected = trieOp(space)
      assertEquals(actual, expected, s"$name mismatch for bounded space #$i")
      checkObservation(s"$name bounded space #$i", SpaceZipper.fixpoint(z(space), template), expected)

    val unsupported = intercept[UnsupportedOperationException] {
      SpaceZipper.fixpoint(z(TrieSpace.fromEncodedPaths(Vector(alphabet.head :: Nil))), SpaceZipper.IterTemplateTag.PrefixedReconstruct(alphabet.head :: Nil)).materialize
    }
    assert(unsupported.getMessage.startsWith("unsupported potentially length-growing zipper fixpoint template"))
  }

  test("range fixpoint preserves synchronous transient outputs across sibling demand order") {
    val a = alphabet(0)
    val b = alphabet(1)
    val initial = TrieSpace.fromEncodedPaths(Vector(a :: b :: Nil, b :: a :: Nil))
    val expected = TrieSpace.fromEncodedPaths(Vector(Nil, a :: Nil, b :: Nil, a :: b :: Nil, b :: a :: Nil))

    def closure: SpaceZipper =
      SpaceZipper.fixpoint(z(initial), SpaceZipper.IterTemplateTag.RangeTail(0, 1))

    val (leftFirst, construction) = ExecutorCostMeter.measure(closure)
    assertEquals(construction.rounds, 0L, s"fixpoint construction must not start a Kleene traversal: $construction")
    val (leftFound, leftCost) = ExecutorCostMeter.measure(leftFirst.child(a).terminal)
    assert(leftFound, s"the first sibling is a transient output of the initial synchronous round: $leftCost")
    assert(leftCost.rounds > 0L, s"order-sensitive Range fixpoints must use the synchronous fallback: $leftCost")
    val (rightFound, rightCost) = ExecutorCostMeter.measure(leftFirst.child(b).terminal)
    assert(rightFound,
      s"the second sibling must observe the same prior approximation as the first sibling in each solver round: $rightCost")
    assertEquals(leftFirst.materialize, expected)

    val rightFirst = closure
    assert(rightFirst.child(b).terminal)
    assert(rightFirst.child(a).terminal)
    assertEquals(rightFirst.materialize, expected)
  }

  test("transpileZ lowers prefixed ranged iteration reconstruct templates") {
    val a = alphabet(0)
    val b = alphabet(1)
    val c = TrieSpace.interner.intern(PathItem("c"))
    val tag = TrieSpace.interner.intern(PathItem("tag"))
    val source = TrieSpace.fromEncodedPaths(Vector(
      a :: b :: Nil,
      a :: c :: Nil,
      b :: a :: Nil,
      b :: c :: Nil
    ))
    val sourceSpace = Space.Literal(source.toSpaceValue)
    val head = PathRef("h").known(1)
    val rest = SpaceMention("tail")
    val staticPrefix = Path.Constant(TrieSpace.decode(tag :: Nil))
    val prefixedHead = Path.Concat(staticPrefix, Path.Deref(head))

    def hasPrefixedRangeReconstruct(z: SpaceZipper, start: Int, end: Int): Boolean = z match
      case SpaceZipper.Memo(src) => hasPrefixedRangeReconstruct(src, start, end)
      case SpaceZipper.Iteration(_, _, Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(prefix, `start`, `end`))) =>
        prefix == (tag :: Nil)
      case SpaceZipper.Prefix(_, src) => hasPrefixedRangeReconstruct(src, start, end)
      case _ => false

    val cases = Vector[(String, Space, Int, Int)](
      (
        "range-wrap-prefixed-head",
        Space.Range(
          Space.Wrap(Space.Mention(rest), prefixedHead),
          0,
          1
        ),
        0,
        1
      ),
      (
        "range-composition-prefixed-head",
        Space.Range(
          Space.Composition(Space.Singleton(prefixedHead), Space.Mention(rest)),
          0,
          -1
        ),
        0,
        -1
      ),
      (
        "wrap-range-prefixed-head",
        Space.Wrap(
          Space.Range(Space.Mention(rest), 0, 1),
          prefixedHead
        ),
        0,
        1
      )
    )

    cases.foreach { (name, template, start, end) =>
      val expr = Space.Iteration(sourceSpace, head, rest, template)
      val actual = transpileZ(expr)
      assertEquals(actual.materialize, evalTrie(expr), s"$name materialization mismatch")
      assert(
        hasPrefixedRangeReconstruct(actual, start, end),
        s"$name should lower to PrefixedRangeReconstruct instead of generic iteration"
      )
    }
  }

  test("range composition and border laws agree in executable zippers") {
    val spaces = allSpaces(maxLen = 2)

    val cases = Vector[(String, SpaceZipper => SpaceZipper, SpaceZipper => SpaceZipper)](
      (
        "first-idempotent",
        (src: SpaceZipper) => SpaceZipper.range(SpaceZipper.range(src, 0, 1), 0, 1),
        (src: SpaceZipper) => SpaceZipper.range(src, 0, 1)
      ),
      (
        "last-idempotent",
        (src: SpaceZipper) => SpaceZipper.range(SpaceZipper.range(src, -1, 0), -1, 0),
        (src: SpaceZipper) => SpaceZipper.range(src, -1, 0)
      ),
      (
        "first-of-last",
        (src: SpaceZipper) => SpaceZipper.range(SpaceZipper.range(src, -1, 0), 0, 1),
        (src: SpaceZipper) => SpaceZipper.range(src, -1, 0)
      ),
      (
        "drop-last-of-first-empty",
        (src: SpaceZipper) => SpaceZipper.range(SpaceZipper.range(src, 0, 1), 0, -1),
        (_: SpaceZipper) => SpaceZipper.empty
      )
    )

    for
      (space, i) <- spaces.zipWithIndex
      (name, left, right) <- cases
    do
      assertEquals(left(z(space)).materialize, right(z(space)).materialize, s"$name mismatch for bounded space #$i")
  }

  test("exact negative and key observations agree with bounded trie denotation") {
    val epsMinusHead = SpaceZipper.subtraction(
      SpaceZipper.traversal(TrieSpace.epsilon),
      SpaceZipper.singleton(alphabet.head :: Nil)
    )
    assert(epsMinusHead.observation.nullable, "epsilon minus a headed singleton should still be nullable")
    assert(!epsMinusHead.observation.nonterminal, "nullable and nonterminal must be exact complements")
    assertEquals(epsMinusHead.observation.childKeys, Set.empty[Int])

    val headedMinusEps = SpaceZipper.subtraction(
      SpaceZipper.singleton(alphabet.head :: Nil),
      SpaceZipper.traversal(TrieSpace.epsilon)
    )
    assert(!headedMinusEps.observation.nullable, "headed singleton minus epsilon should not be nullable")
    assert(headedMinusEps.observation.nonterminal)
    assertEquals(headedMinusEps.observation.childKeys, Set(alphabet.head))
  }

  test("concrete trie zipper plug reconstructs the whole at every focus") {
    val spaces = allSpaces(maxLen = 3)
    spaces.zipWithIndex.foreach { (space, i) =>
      allFoci(space).foreach { cursor =>
        assertEquals(cursor.whole, space, s"plug failed for bounded space #$i at ${cursor.pathValue.show}")
        assertEquals(space.subtreeItems(cursor.path.toList).getOrElse(TrieSpace.empty), cursor.focus)
        cursor.up.foreach { parent =>
          assertEquals(parent.whole, space, s"up changed the reconstructed whole at ${cursor.pathValue.show}")
          assertEquals(parent.down(cursor.path.last).map(_.focus), Some(cursor.focus))
        }
        assertEquals(cursor.toRoot.focus, space, s"toRoot focus mismatch for bounded space #$i")
      }
    }
  }

  test("concrete trie zipper supports focus edits and ordered sibling movement") {
    val a = alphabet(0)
    val b = alphabet(1)
    val c = TrieSpace.interner.intern(PathItem("c"))
    val x = TrieSpace.interner.intern(PathItem("x"))
    val root = TrieSpace.fromEncodedPaths(Vector(
      a :: b :: Nil,
      a :: c :: Nil,
      b :: Nil,
      c :: Nil
    ))

    val atA = TrieSpace.Zipper(root).down(a).getOrElse(fail("missing child a"))
    val replacement = TrieSpace.fromEncodedPaths(Vector(Nil, x :: Nil))
    val grafted = atA.graft(replacement).whole
    assertEquals(grafted.unwrapItems(a :: Nil), replacement)
    assertEquals(grafted.unwrapItems(b :: Nil), root.unwrapItems(b :: Nil))

    val removed = atA.removeFocus.whole
    assert(!removed.children.contains(a), "removing the focused child should remove its parent edge")
    assertEquals(removed.unwrapItems(b :: Nil), root.unwrapItems(b :: Nil))

    val inserted = atA.insertItemsAtFocus(x :: Nil).whole
    assert(inserted.containsItems(a :: x :: Nil))
    assertEquals(inserted.unwrapItems(b :: Nil), root.unwrapItems(b :: Nil))

    val atB = TrieSpace.Zipper(root).down(b).getOrElse(fail("missing child b"))
    val next = atB.nextSibling.getOrElse(fail("missing next sibling"))
    assertEquals(next.path, Vector(c))
    assertEquals(next.previousSibling.map(_.path), Some(Vector(b)))

    val removedA = atA.removeFocus
    val nextAfterRemovedA = removedA.nextSibling.getOrElse(fail("missing next sibling after removed a"))
    assertEquals(nextAfterRemovedA.path, Vector(b))
    assertEquals(nextAfterRemovedA.pathValue, TrieSpace.decode(b :: Nil))
    assertEquals(nextAfterRemovedA.whole, removed)
    assertEquals(nextAfterRemovedA.previousSibling, None)

    val removedC = TrieSpace.Zipper(root).down(c).getOrElse(fail("missing child c")).removeFocus
    val previousAfterRemovedC = removedC.previousSibling.getOrElse(fail("missing previous sibling after removed c"))
    assertEquals(previousAfterRemovedC.path, Vector(b))
    assertEquals(previousAfterRemovedC.pathValue, TrieSpace.decode(b :: Nil))
    assertEquals(previousAfterRemovedC.whole, removedC.whole)
  }

  test("virtual zipper context movement plugs every operation-shaped focus") {
    val a = alphabet(0)
    val b = alphabet(1)
    val c = TrieSpace.interner.intern(PathItem("c"))
    val d = TrieSpace.interner.intern(PathItem("d"))
    val x = TrieSpace.fromEncodedPaths(Vector(Nil, a :: b :: Nil, a :: c :: Nil, b :: Nil, d :: a :: Nil))
    val y = TrieSpace.fromEncodedPaths(Vector(Nil, a :: b :: Nil, c :: Nil, d :: Nil))
    val prefixes = TrieSpace.fromEncodedPaths(Vector(a :: Nil, d :: Nil))
    val zx = SpaceZipper.traversal(x)
    val zy = SpaceZipper.traversal(y)
    val zp = SpaceZipper.traversal(prefixes)

    val cases = Vector[(String, SpaceZipper)](
      "memo" -> SpaceZipper.Memo(SpaceZipper.Union(zx, zy)),
      "union" -> SpaceZipper.Union(zx, zy),
      "joinAll" -> SpaceZipper.JoinAll(Vector(zx, zy, SpaceZipper.wrap(zx, d :: Nil))),
      "intersection" -> SpaceZipper.Intersection(zx, zy),
      "meetAll" -> SpaceZipper.MeetAll(Vector(zx, zy, SpaceZipper.wrap(zy, d :: Nil))),
      "subtraction" -> SpaceZipper.Subtraction(zx, zy),
      "restriction" -> SpaceZipper.Restriction(zx, zp),
      "raffination" -> SpaceZipper.subtraction(zx, SpaceZipper.restriction(zx, zp)),
      "concat" -> SpaceZipper.Concat(SpaceZipper.NonEmpty(zx), SpaceZipper.NonEmpty(zy)),
      "wrap" -> SpaceZipper.Prefix(a :: Nil, zy),
      "nonEmpty" -> SpaceZipper.NonEmpty(zx),
      "tailsUnion" -> SpaceZipper.TailsUnion(zx),
      "tailsIntersection" -> SpaceZipper.TailsIntersection(zx),
      "prefixClosure" -> SpaceZipper.PrefixClosure(zx),
      "suffixClosure" -> SpaceZipper.SuffixClosure(zx),
      "tailsClosure" -> SpaceZipper.TailsClosure(zx),
      "range" -> SpaceZipper.Range(zx, 1, x.pathCount.min(4)),
      "lastRange" -> SpaceZipper.range(SpaceZipper.Union(zx, zy), -2, 0),
      "dropLastRange" -> SpaceZipper.range(SpaceZipper.Union(zx, zy), 0, -2),
      "patchChild" -> SpaceZipper.PatchChild(SpaceZipper.Union(zx, zy), a, SpaceZipper.singleton(c :: Nil))
    )

    cases.foreach { (name, root) =>
      val expected = root.materialize
      allVirtualFoci(root).foreach { cursor =>
        assertEquals(cursor.whole.materialize, expected, s"$name plug mismatch at ${cursor.pathValue.show}")
        cursor.up.foreach { parent =>
          assertEquals(parent.whole.materialize, expected, s"$name up changed whole at ${cursor.pathValue.show}")
          assertEquals(parent.down(cursor.path.last).map(_.focus.materialize), Some(cursor.focus.materialize), s"$name down/up focus mismatch at ${cursor.pathValue.show}")
        }
        assertEquals(cursor.toRoot.whole.materialize, expected, s"$name toRoot whole mismatch at ${cursor.pathValue.show}")
      }
    }
  }

  test("virtual zipper context graft edits focus through lazy patch frames") {
    val a = alphabet(0)
    val b = alphabet(1)
    val c = TrieSpace.interner.intern(PathItem("c"))
    val x = TrieSpace.fromEncodedPaths(Vector(a :: b :: Nil, a :: c :: Nil, b :: Nil))
    val y = TrieSpace.fromEncodedPaths(Vector(a :: b :: Nil, c :: Nil))
    val root = SpaceZipper.Union(SpaceZipper.traversal(x), SpaceZipper.Prefix(c :: Nil, SpaceZipper.traversal(y)))
    val cursor = SpaceZipper.Cursor(root).down(a).getOrElse(fail("missing a focus"))
    val replacement = SpaceZipper.singleton(c :: b :: Nil)
    val edited = cursor.graft(replacement).whole
    val expected = TrieSpace.Zipper(root.materialize)
      .descendItems(cursor.path)
      .getOrElse(fail("missing concrete focus"))
      .graft(replacement.materialize)
      .whole

    assertEquals(edited.materialize, expected)
    assert(edited.concrete.isEmpty, "virtual graft should remain a lazy zipper patch")
    assertEquals(cursor.nextSibling.map(_.previousSibling.map(_.path)), Some(Some(cursor.path)))

    val removed = cursor.removeFocus
    val next = removed.nextSibling.getOrElse(fail("missing virtual next sibling after removed focus"))
    assertEquals(next.path, Vector(b))
    assertEquals(next.pathValue, TrieSpace.decode(b :: Nil))
    assertEquals(next.whole.materialize, removed.whole.materialize)
    assertEquals(next.previousSibling, None)

    val atC = SpaceZipper.Cursor(root).down(c).getOrElse(fail("missing c focus"))
    val removedC = atC.removeFocus
    val previous = removedC.previousSibling.getOrElse(fail("missing virtual previous sibling after removed focus"))
    assertEquals(previous.path, Vector(b))
    assertEquals(previous.pathValue, TrieSpace.decode(b :: Nil))
    assertEquals(previous.whole.materialize, removedC.whole.materialize)
  }
