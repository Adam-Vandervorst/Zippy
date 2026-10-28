package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

class ReferenceExamplesTest extends FunSuite:
  import Space.*
  import Unification.MQT

  private def item(p: PathItem): String = p.show

  private def pairSet(sv: SpaceValue): Set[(String, String)] =
    sv.paths.collect { case PathValue(a :: b :: Nil) => item(a) -> item(b) }

  private def transitiveClosure(edges: Set[(String, String)]): Set[(String, String)] =
    var known = edges
    var changed = true
    while changed do
      val next = known ++ (for (a, b) <- known; (c, d) <- known if b == c yield a -> d)
      changed = next.size != known.size
      known = next
    known

  test("semi-naive Datalog over carac-style facts matches independent closure") {
    val (facts, _) = GoalExampleData.caracFacts
    val edges = GoalExampleData.transitiveEdgesFrom(facts)
    val initial = DatalogExample.semiNaiveInitial(Literal(edges))
    val semiNaive = DatalogExample.semiNaiveTransitive
    val got = eval(semiNaive.name(initial)("complete.path"))(using rc = { case semiNaive.name => semiNaive })
    assertEquals(pairSet(got), transitiveClosure(pairSet(eval(Literal(edges)("edge")))))
  }

  private def lifeCells(field: SpaceValue): Set[(Int, Int)] =
    field.paths.collect {
      case PathValue(PathItem("Cell") :: PathItem(x) :: PathItem(y) :: Nil) => x.toInt -> y.toInt
    }

  private def lifeField(cells: Set[(Int, Int)]): SpaceValue =
    SpaceValue(cells.map((x, y) => Syntax.parse(s"Cell.$x.$y")))

  private def lifeStep(cells: Set[(Int, Int)]): Set[(Int, Int)] =
    val counts = collection.mutable.Map.empty[(Int, Int), Int].withDefaultValue(0)
    for (x, y) <- cells; dx <- -1 to 1; dy <- -1 to 1 if dx != 0 || dy != 0 do
      val k = (x + dx, y + dy)
      counts.update(k, counts(k) + 1)
    counts.iterator.collect { case (cell, n) if n == 3 || (n == 2 && cells(cell)) => cell }.toSet

  test("Game of Life examples match independent B3/S23 reference") {
    val fields = Vector(
      GoalExampleData.randomLife(7, 7, 14, 2026),
      GoalExampleData.fredOrGlider._1
    )
    for field <- fields do
      val got = eval(R"nextStep"(Literal(field)))(using rc = mod(LifeExample.neigh, LifeExample.nextStep))
      assertEquals(lifeCells(got), lifeStep(lifeCells(field)))
  }

  private def puzzleNeighbors(n: Int, state: Vector[Int]): Set[Vector[Int]] =
    val blank = state.indexOf(0)
    val row = blank / n
    val col = blank % n
    Vector(row - 1 -> col, row + 1 -> col, row -> (col - 1), row -> (col + 1))
      .filter((r, c) => r >= 0 && c >= 0 && r < n && c < n)
      .map((r, c) =>
        val j = r * n + c
        state.updated(blank, state(j)).updated(j, 0)
      ).toSet

  private def puzzleReachable(n: Int, start: Vector[Int], maxDepth: Int = Int.MaxValue): Set[Vector[Int]] =
    var seen = Set(start)
    var frontier = Set(start)
    var depth = 0
    while frontier.nonEmpty && depth < maxDepth do
      val next = frontier.flatMap(puzzleNeighbors(n, _)) -- seen
      seen ++= next
      frontier = next
      depth += 1
    seen

  private def puzzlePath(n: Int, state: Vector[Int]): PathValue =
    SlidingPuzzleExample.pathState(n, state)

  test("pure sliding puzzle 2x2 and 3x3 one-step expansions match independent neighbor generator") {
    for n <- Vector(2, 3) do
      val start = (0 until n * n).toVector
      val got = eval(SlidingPuzzleExample.step(n, Literal(SpaceValue(puzzlePath(n, start)))))(using rc = SlidingPuzzleExample.context(n))
      assertEquals(got.paths, puzzleNeighbors(n, start).map(puzzlePath(n, _)))
  }

  test("pure sliding puzzle 2x2 explore reaches the complete state space") {
    val n = 2
    val start = (0 until n * n).toVector
    val got = eval(SlidingPuzzleExample.reachable(n, Literal(SpaceValue(puzzlePath(n, start)))))(using rc = SlidingPuzzleExample.context(n))
    assertEquals(got.paths, puzzleReachable(n, start).map(puzzlePath(n, _)))
    assertEquals(got.paths.size, 12)
  }

  test("sliding puzzle 3x3 full reachable state space has the parity count") {
    assertEquals(puzzleReachable(3, (0 until 9).toVector).size, 181440)
  }

  test("pure sliding puzzle 3x3 bounded expansion matches independent BFS") {
    val n = 3
    val start = (0 until n * n).toVector
    var frontier: Space = Literal(SpaceValue(puzzlePath(n, start)))
    var acc: Space = frontier
    for _ <- 0 until 4 do
      frontier = SlidingPuzzleExample.step(n, frontier) \ acc
      acc = acc \/ frontier
    assertEquals(eval(acc)(using rc = SlidingPuzzleExample.context(n)).paths, puzzleReachable(n, start, maxDepth = 4).map(puzzlePath(n, _)))
  }

  test("NOAA spatial prefix query matches manual prefix filter") {
    val data = GoalExampleData.noaaTemperatureData
    val world = data.world
    val prefixes = eval("cell" x Literal(TemperatureExample.interval(4, 11, data.latBits)) x Literal(TemperatureExample.interval(3, 12, data.lonBits)))
    val query = Literal(world) <| Literal(prefixes)
    val got = eval(query)
    val manual = world.paths.filter(p => prefixes.paths.exists(prefix => p.items.startsWith(prefix.items)))
    assertEquals(got.paths, manual)
  }

  test("NOAA temperature-first query matches manual label filter") {
    val data = GoalExampleData.noaaTemperatureData
    val query = Literal(data.byTemperature) <| ss"temp.H"
    val got = eval(query)
    val manual = data.byTemperature.paths.filter(_.items.take(2) == List(PathItem("temp"), PathItem("H")))
    assertEquals(got.paths, manual)
  }

  test("n-queens reference count matches known 8x8 count") {
    val (place, ctx) = NQueensExample.program(8)
    val graph = optimize_sharing(transpile(Supercompiler.compile(place, ctx = ctx).routine))
    val stack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](graph.nodes.length))
    exec(graph, stack)
    assertEquals(stack.top.last.asInstanceOf[SpaceValue].paths.size, 92)
  }

  private def nQueensCount(n: Int): Int =
    def loop(row: Int, cols: Int, diagA: Int, diagB: Int): Int =
      if row == n then 1
      else
        val all = (1 << n) - 1
        var free = all & ~(cols | diagA | diagB)
        var total = 0
        while free != 0 do
          val bit = free & -free
          free -= bit
          total += loop(row + 1, cols | bit, ((diagA | bit) << 1) & all, (diagB | bit) >> 1)
        total
    loop(0, 0, 0, 0)

  test("n-queens independent reference scaling matches known counts through 12x12") {
    val expected = Vector(
      1 -> 1,
      2 -> 0,
      3 -> 0,
      4 -> 2,
      5 -> 10,
      6 -> 4,
      7 -> 40,
      8 -> 92,
      9 -> 352,
      10 -> 724,
      11 -> 2680,
      12 -> 14200
    )
    assertEquals(expected.map((n, _) => n -> nQueensCount(n)), expected)
  }

  test("pure n-queens programs are generated for 8x8 through 12x12 without grounded operations") {
    for n <- 8 to 12 do
      val (place, ctx) = NQueensExample.program(n)
      assertEquals(Supercompiler.backendUnsupported(place.body), Vector.empty)
      assert(ctx.isDefinedAt(RoutinePtr("aoe")))

    val (place8, ctx8) = NQueensExample.program(8)
    val compiled8 = Supercompiler.compile(place8, ctx = ctx8, buildGraph = false)
    assertEquals(Supercompiler.backendUnsupported(compiled8.routine.body), Vector.empty)
    assert(compiled8.report.converged)
  }
