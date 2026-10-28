package morkl

import munit.FunSuite

object TrieConstructionAsymptoticData:
  case class Row(size: Int, wideMs: Double, deepMs: Double)

  def wide(size: Int): Vector[List[Int]] =
    Vector.tabulate(size)(index => List(index + 2, 0))

  def deep(size: Int): Vector[List[Int]] =
    val width = Integer.numberOfTrailingZeros(Integer.highestOneBit(size))
    Vector.tabulate(size) { index =>
      (0 until width).reverseIterator.map(bit => (index >>> bit) & 1).toList
    }

  private def medianMillis(paths: Vector[List[Int]]): Double =
    def run(): Double =
      val started = System.nanoTime()
      val result = TrieSpace.fromEncodedPaths(paths)
      val elapsed = (System.nanoTime() - started).toDouble / 1_000_000.0
      require(result.pathCount == paths.size)
      elapsed
    Vector.fill(3)(run())
    Vector.fill(7)(run()).sorted.apply(3)

  def rows: Vector[Row] = Vector(256, 1024, 4096, 16384).map { size =>
    Row(size, medianMillis(wide(size)), medianMillis(deep(size)))
  }

@main def trieConstructionAsymptoticBenchmark(): Unit =
  println("size,wide_ms,deep_ms")
  TrieConstructionAsymptoticData.rows.foreach { row =>
    println(f"${row.size},${row.wideMs}%.3f,${row.deepMs}%.3f")
  }

object TrieIncrementalUnionAsymptoticData:
  case class Row(size: Int, nodeVisits: Long, patriciaVisits: Long, allocations: Long, millis: Double)

  private def operands(size: Int): Vector[TrieSpace] =
    Vector.tabulate(size)(index => TrieSpace.fromEncodedPaths(Vector(List(index + 2, 0))))

  def fold(size: Int): TrieSpace =
    operands(size).foldLeft(TrieSpace.empty)(_.union(_))

  private def medianMillis(values: Vector[TrieSpace], size: Int): Double =
    def run(): Double =
      val started = System.nanoTime()
      val result = values.foldLeft(TrieSpace.empty)(_.union(_))
      val elapsed = (System.nanoTime() - started).toDouble / 1_000_000.0
      require(result.pathCount == size)
      elapsed
    Vector.fill(2)(run())
    Vector.fill(5)(run()).sorted.apply(2)

  def rows: Vector[Row] = Vector(512, 2048, 8192, 32768).map { size =>
    val values = operands(size)
    val (result, cost) = ExecutorCostMeter.measure(values.foldLeft(TrieSpace.empty)(_.union(_)))
    require(result.pathCount == size)
    Row(size, cost.nodeVisits, cost.patriciaVisits, cost.allocations, medianMillis(values, size))
  }

@main def trieIncrementalUnionAsymptoticBenchmark(): Unit =
  println("size,node_visits,patricia_visits,allocations,incremental_union_ms")
  TrieIncrementalUnionAsymptoticData.rows.foreach { row =>
    println(f"${row.size},${row.nodeVisits},${row.patriciaVisits},${row.allocations},${row.millis}%.3f")
  }

class TrieConstructionAsymptoticTest extends FunSuite:
  test("persistent insertion derives aggregates without rescanning wide parents") {
    Vector(256, 1024, 4096, 16384).foreach { size =>
      val (wide, wideCost) = ExecutorCostMeter.measure(
        TrieSpace.fromEncodedPaths(TrieConstructionAsymptoticData.wide(size)))
      assertEquals(wide.pathCount, size)
      assertEquals(wideCost.nodeVisits, 0L)
      assertEquals(wideCost.allocations, size.toLong + 1L)

      val deepPaths = TrieConstructionAsymptoticData.deep(size)
      val (deep, deepCost) = ExecutorCostMeter.measure(TrieSpace.fromEncodedPaths(deepPaths))
      assertEquals(deep.pathCount, size)
      assertEquals(deepCost.nodeVisits, 0L)
      assertEquals(deepCost.allocations, size.toLong - 1L)
    }
  }

  test("bulk join scans once and zipper insertion inherits delta construction") {
    val size = 4096
    val paths = TrieConstructionAsymptoticData.wide(size)
    val singletons = paths.map(path => TrieSpace.fromEncodedPaths(Vector(path)))
    val (joined, joinCost) = ExecutorCostMeter.measure(TrieSpace.joinAll(singletons))
    assertEquals(joined.pathCount, size)
    assertEquals(joinCost.nodeVisits, size.toLong - 1L)
    assertEquals(joinCost.allocations, size.toLong - 1L)

    val repeated = TrieSpace.fromEncodedPaths(Vector(List(1, 2, 3)))
    val (deduplicated, duplicateCost) = ExecutorCostMeter.measure(
      TrieSpace.joinAll(Vector.fill(size)(repeated)))
    assert(deduplicated.asInstanceOf[AnyRef] eq repeated.asInstanceOf[AnyRef])
    assertEquals(duplicateCost.nodeVisits, 0L)
    assertEquals(duplicateCost.allocations, 0L)

    val (zipper, zipperCost) = ExecutorCostMeter.measure {
      paths.foldLeft(TrieSpace.Zipper(TrieSpace.empty))((cursor, path) => cursor.insertItemsAtFocus(path))
    }
    assertEquals(zipper.whole.pathCount, size)
    assertEquals(zipperCost.nodeVisits, 0L)
    assertEquals(zipperCost.allocations, size.toLong * 3L)
  }

  test("incremental singleton union follows touched Patricia spines, not accumulator width") {
    Vector(256, 1024, 4096).foreach { size =>
      val operands = Vector.tabulate(size)(index =>
        TrieSpace.fromEncodedPaths(Vector(List(index + 2, 0))))
      val (result, cost) = ExecutorCostMeter.measure(
        operands.foldLeft(TrieSpace.empty)(_.union(_)))
      assertEquals(result.pathCount, size)
      assertEquals(cost.nodeVisits, size.toLong)
      assertEquals(cost.allocations, size.toLong - 1L)
      // IntMap keys are fixed-width integers, so every inserted singleton can
      // touch at most one bounded Patricia spine. This rejects a result-width
      // scan at every fold step without assuming a balanced key distribution.
      assert(cost.patriciaVisits <= size.toLong * 64L,
        s"size=$size incremental union visited ${cost.patriciaVisits} Patricia nodes")
    }
  }

  test("fixpoint union of a wide accumulator and one delta stays within fixed key-depth ceilings") {
    val seed = SpaceMention("fixpoint_union_seed")
    val current = SpaceMention("fixpoint_union_current")
    val delta = PathValue(List(PathItem("new-head"), PathItem("value")))
    val expression = Space.Fixpoint(
      Space.Mention(seed),
      current,
      Space.Union(Space.Mention(current), Space.Singleton(Path.Constant(delta))),
    )
    val widths = Vector(256, 1024, 4096, 16384)
    val costs = widths.map { size =>
      val initial = TrieSpace.fromPaths((0 until size).map(index =>
        PathValue(List(PathItem(s"h$index"), PathItem("value")))))
      val context = TrieSpaceContextMap(Map(seed -> initial))
      val (result, cost) = ExecutorCostMeter.measure(evalTrie(expression)(using
        PathContext.emptyMap, context, PartialFunction.empty))
      assertEquals(result.pathCount, size + 1)
      cost
    }
    // PathItem ids are assigned process-globally, so earlier suites can change
    // the numeric Patricia layout. Exact visit counts are not invariant under
    // that relabeling: the lasting claim is a constant number of semantic
    // checks and a constant number of fixed-32-bit Patricia spines, independent
    // of accumulator width.
    assert(costs.forall(_.nodeVisits <= 8L),
      s"fixpoint trie visits exceeded the constant semantic ceiling: ${widths.zip(costs)}")
    assert(costs.forall(_.patriciaVisits <= 8L * Integer.SIZE),
      s"fixpoint Patricia visits exceeded the fixed-key-depth ceiling: ${widths.zip(costs)}")
    assertEquals(costs.map(_.allocations).distinct.size, 1,
      s"fixpoint allocation count changed with accumulator width: ${widths.zip(costs)}")
    assertEquals(costs.map(_.rounds), Vector.fill(widths.size)(2L))
  }
