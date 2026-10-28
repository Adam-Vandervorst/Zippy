package morkl

import munit.FunSuite

object TrieAlgebraDistributionData:
  enum Regime:
    case Identity, RootDisjoint, MixedQuarter, Interwoven

  case class Row(
    size: Int,
    regime: Regime,
    nodeVisits: Long,
    patriciaVisits: Long,
    allocations: Long,
    nanos: Double,
  )

  private def trie(keys: IndexedSeq[Int]): TrieSpace =
    TrieSpace.fromEncodedPaths(keys.map(key => key :: 0 :: Nil))

  private def operands(size: Int, regime: Regime): (TrieSpace, TrieSpace) = regime match
    case Regime.Identity =>
      val value = trie(0 until size)
      value -> value
    case Regime.RootDisjoint =>
      trie(0 until size) -> trie((0 until size).map(_ + (1 << 28)))
    case Regime.MixedQuarter =>
      val shared = size / 4
      val left = (0 until shared).map(_ * 2) ++
        (0 until size - shared).map(_ + (1 << 27))
      val right = (0 until shared).map(index => index * 2 + 1) ++
        (0 until size - shared).map(_ + (1 << 29))
      trie(left) -> trie(right)
    case Regime.Interwoven =>
      trie((0 until size).map(_ * 2)) -> trie((0 until size).map(index => index * 2 + 1))

  private var sink = 0

  def row(size: Int, regime: Regime): Row =
    val (left, right) = operands(size, regime)
    val (_, counts) = ExecutorCostMeter.measure(left.union(right))
    val repetitions = (262144 / size).max(16)
    var warmup = 0
    while warmup < 3 do
      var index = 0
      while index < repetitions do
        sink ^= left.union(right).pathCount
        index += 1
      warmup += 1
    val samples = Vector.fill(5) {
      val started = System.nanoTime()
      var index = 0
      while index < repetitions do
        sink ^= left.union(right).pathCount
        index += 1
      (System.nanoTime() - started).toDouble / repetitions
    }
    Row(size, regime, counts.nodeVisits, counts.patriciaVisits, counts.allocations, samples.sorted.apply(2))

  def rows: Vector[Row] =
    for
      size <- Vector(256, 1024, 4096, 16384)
      regime <- Regime.values.toVector
    yield row(size, regime)

@main def trieAlgebraDistributionReport(): Unit =
  println("size,regime,node_visits,patricia_visits,allocations,ns_per_union")
  TrieAlgebraDistributionData.rows.foreach { row =>
    println(f"${row.size},${row.regime},${row.nodeVisits},${row.patriciaVisits},${row.allocations},${row.nanos}%.1f")
  }

class TrieLayerAsymptoticTest extends FunSuite:
  private def path(items: String*): PathValue = PathValue(items.map(PathItem(_)).toList)

  test("wide disjoint algebra preserves Patricia aggregates without output-width scans") {
    val width = 8192
    // Use controlled encoded keys so this test measures the intended
    // root-disjoint Patricia regime independently of process-global PathItem
    // interning order. Sequentially interning l*/r* can straddle a Patricia
    // prefix boundary after another suite has already allocated labels.
    val left = TrieSpace.fromEncodedPaths((0 until width).map(index => index :: Nil))
    val right = TrieSpace.fromEncodedPaths((0 until width).map(index => (index + (1 << 28)) :: Nil))
    val (union, cost) = ExecutorCostMeter.measure(left.union(right))
    assertEquals(union.pathCount, width * 2)
    assertEquals(cost.nodeVisits, 1L)
    assertEquals(cost.patriciaVisits, 1L)
    assertEquals(cost.allocations, 1L)

    val (intersection, intersectionCost) = ExecutorCostMeter.measure(left.intersect(right))
    assert(intersection.isEmpty)
    assertEquals(intersectionCost.nodeVisits, 1L)
    assertEquals(intersectionCost.patriciaVisits, 1L)
  }

  test("union retains distinct Patricia distribution regimes") {
    val sizes = Vector(256, 1024, 4096)
    val identity = sizes.map(TrieAlgebraDistributionData.row(_, TrieAlgebraDistributionData.Regime.Identity))
    val disjoint = sizes.map(TrieAlgebraDistributionData.row(_, TrieAlgebraDistributionData.Regime.RootDisjoint))
    val mixed = sizes.map(TrieAlgebraDistributionData.row(_, TrieAlgebraDistributionData.Regime.MixedQuarter))
    val interwoven = sizes.map(TrieAlgebraDistributionData.row(_, TrieAlgebraDistributionData.Regime.Interwoven))

    assert(identity.forall(row => row.nodeVisits == 1 && row.patriciaVisits == 0 && row.allocations == 0))
    assert(disjoint.forall(row => row.nodeVisits == 1 && row.patriciaVisits == 1 && row.allocations == 1))
    assert(interwoven.forall(row => row.nodeVisits == 1 &&
      row.patriciaVisits == row.size.toLong * 2L - 1L && row.allocations == 1),
      s"interwoven union did not visit each Patricia node pair exactly once: $interwoven")
    assert(mixed.forall(row => row.nodeVisits == 1 &&
      row.patriciaVisits == row.size.toLong / 2L + 1L && row.allocations == 1),
      s"quarter-interwoven union did not retain its exact touched-branch cost: $mixed")
  }

  test("single-path suffix and tails closures are linear for repeated and periodic labels") {
    Vector(256, 1024, 4096).foreach { depth =>
      val a = TrieSpace.interner.intern(PathItem("same-a"))
      val b = TrieSpace.interner.intern(PathItem("same-b"))
      Vector(List.fill(depth)(a), List.tabulate(depth)(index => if index % 2 == 0 then a else b)).foreach { path =>
        val source = TrieSpace.fromEncodedPaths(Vector(path))
        val (suffixes, cost) = ExecutorCostMeter.measure(source.suffixClosure)
        assertEquals(suffixes.pathCount, depth)
        assert(cost.allocations <= depth.toLong * 4L,
          s"depth=$depth closure allocations were ${cost.allocations}")
        assertEquals(cost.nodeVisits, 0L)
      }
    }
  }

  test("single-path suffix automaton denotes exactly the proper suffix language") {
    Vector(
      List("a", "b", "a", "b", "a"),
      List("a", "b", "c", "d", "e"),
      List("a", "a", "b", "a", "a", "b"),
    ).foreach { labels =>
      val source = TrieSpace.fromPaths(Vector(path(labels*)))
      val expected = SpaceValue(labels.indices.map(index => path(labels.drop(index)*)).toSet)
      assertEquals(source.suffixClosure.toSpaceValue, expected)
      assertEquals(source.tailsClosure.toSpaceValue, SpaceValue(expected.paths + PathValue(Nil)))
    }
  }

  test("read cursor descent and focused zipper rebuild are depth-linear") {
    val depth = 256
    val width = 16
    val main = Vector.tabulate(depth)(index => PathItem(s"d$index"))
    val paths = Vector.newBuilder[PathValue]
    paths += PathValue(main.toList)
    (0 until depth).foreach { level =>
      (0 until width).foreach { sibling =>
        paths += PathValue((main.take(level) :+ PathItem(s"s$level-$sibling")).toList)
      }
    }
    val source = TrieSpace.fromPaths(paths.result())
    val mainPath = PathValue(main.toList)

    val (readCursor, readCost) = ExecutorCostMeter.measure(TrieSpace.Cursor(source).descend(mainPath))
    assert(readCursor.nonEmpty)
    assertEquals(readCost.nodeVisits, 1L)

    val focused = TrieSpace.Zipper(source).descend(mainPath).getOrElse(fail("missing deep focus"))
    val replacement = focused.insertAtFocus(path("new"))
    val (whole, rebuildCost) = ExecutorCostMeter.measure(replacement.whole)
    assertEquals(whole.pathCount, source.pathCount + 1)
    assertEquals(rebuildCost.nodeVisits, 0L)
    assertEquals(rebuildCost.allocations, depth.toLong)
  }

  test("walking ordered siblings sorts once for trie and virtual cursors") {
    val width = 4096
    val source = TrieSpace.fromPaths((0 until width).map(index => path(f"k$index%05d")))

    def walkTrie(): Int =
      var count = 0
      var cursor = TrieSpace.Zipper(source).firstChild
      while cursor.nonEmpty do
        count += 1
        cursor = cursor.get.nextSibling
      count

    def walkVirtual(): Int =
      var count = 0
      var cursor = SpaceZipper.Cursor(SpaceZipper.traversal(source)).firstChild
      while cursor.nonEmpty do
        count += 1
        cursor = cursor.get.nextSibling
      count

    val (trieCount, trieCost) = ExecutorCostMeter.measure(walkTrie())
    val (virtualCount, virtualCost) = ExecutorCostMeter.measure(walkVirtual())
    assertEquals(trieCount, width)
    assertEquals(virtualCount, width)
    val comparisonCeiling = width.toLong * 64L
    assert(trieCost.pathComparisons <= comparisonCeiling,
      s"trie sibling walk comparisons=${trieCost.pathComparisons}")
    assert(virtualCost.pathComparisons <= comparisonCeiling,
      s"virtual sibling walk comparisons=${virtualCost.pathComparisons}")
  }

  test("left-associated path concatenation is evaluated with one linear flatten") {
    val depth = 12000
    val factors = Vector.tabulate(depth)(index => Path.Constant(path(s"p$index")))
    val expression = Space.Singleton(Path.fromFactors(factors))
    val trie = evalTrie(expression)
    assertEquals(trie.pathCount, 1)
    assertEquals(trie.nodeCount, depth + 1)
    val zipper = evalZ(expression)
    assertEquals(zipper.pathCount, 1)
    assertEquals(zipper.nodeCount, depth + 1)
  }

  test("specialized iteration factors a static prefix outside the head union") {
    val heads = 512
    val prefixLength = 64
    val sourceMention = SpaceMention("prefix_source")
    val rest = SpaceMention("prefix_rest")
    val symbol = PathRef("prefix_head")
    val source = TrieSpace.fromPaths((0 until heads).map(index => path(s"h$index", "tail")))
    val staticPrefix = Path.Constant(PathValue(List.fill(prefixLength)(PathItem("static"))))
    val template = Space.Range(
      Space.Wrap(Space.Mention(rest), Path.Concat(staticPrefix, Path.Deref(symbol))),
      0,
      1,
    )
    val expression = Space.Iteration(Space.Mention(sourceMention), symbol, rest, template)
    val context = TrieSpaceContextMap(Map(sourceMention -> source))
    val (result, cost) = ExecutorCostMeter.measure(evalTrie(expression)(using
      PathContext.emptyMap, context, PartialFunction.empty))
    assertEquals(result.pathCount, heads)
    assert(cost.allocations <= heads.toLong * 4L + prefixLength * 2L,
      s"factored iteration allocated ${cost.allocations}")
  }

  test("left-associated intersections flatten without recursive Vector concatenation") {
    val mention = SpaceMention("intersection_source")
    val depth = 4096
    val expression = Vector.fill(depth)(Space.Mention(mention): Space).reduceLeft(Space.Intersection(_, _))
    given ZipperSpaceContext = ZipperSpaceContextMap(Map(
      mention -> SpaceZipper.traversal(TrieSpace.fromPaths(Vector(path("value")))),
    ))
    assertEquals(evalZ(expression).toSpaceValue, SpaceValue(Set(path("value"))))
  }
