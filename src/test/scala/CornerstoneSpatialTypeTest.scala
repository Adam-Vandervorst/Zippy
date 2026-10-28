package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path as JPath, Paths}
import scala.concurrent.duration.*

object CornerstoneAbstractInterpretations:
  private def exactLength(length: Int): PathLengthEstimate =
    PathLengthEstimate.exact(PathLengthExpr.const(length))

  def pattern(count: SizeExpr, items: SpatialItem*): SpatialType =
    val shape = SpatialPattern(items.toVector)
    SpatialType.fromStrata(Vector(SpatialStratum(
      exactLength(shape.length),
      ResultSizeEstimate.exact(count),
      Some(shape),
    )))

  def union(types: SpatialType*): SpatialType =
    SpatialType.fromStrata(types.toVector.flatMap(_.strata))

  private def c(value: String): SpatialItem = SpatialItem.Constant(PathItem(value))
  private def u(name: String): SpatialItem = SpatialItem.Unknown(name)
  private def a(name: String, minimum: Int, maximum: Int): SpatialItem =
    SpatialItem.Affine(name, 0, minimum, maximum)

  val auntFamily: SpatialType = union(
    pattern(SizeExpr.symbol("parentEdges"), c("parent"), u("parent"), u("child")),
    pattern(SizeExpr.symbol("childEdges"), c("child"), u("child"), u("parent")),
    pattern(SizeExpr.symbol("femalePeople"), c("female"), u("female")),
    pattern(SizeExpr.symbol("malePeople"), c("male"), u("male")),
    pattern(SizeExpr.symbol("peopleTags"), c("person"), u("personTag")),
  )
  val auntPeople: SpatialType = pattern(SizeExpr.symbol("people"), u("person"))

  lazy val aunt: SpatialType = SpatialTypeAnalysis.outputRoutineAbstract(
    Routines.aunt_query_routine,
    SpatialRoutineAnnotations(
      spaces = Map(
        SpaceMention("family") -> auntFamily,
        SpaceMention("people") -> auntPeople,
      ),
      resultLaws = Vector(SpatialBoundLaw.ProvedUpperBound(SizeExpr.multiply(
        SizeExpr.symbol("people"),
        SizeExpr.minimum(
          SizeExpr.symbol("parentEdges"),
          SizeExpr.symbol("childEdges"),
          SizeExpr.symbol("femalePeople"),
        ),
      ))),
    ),
    PartialFunction.empty,
  )

  private val datalogEdgesMention = SpaceMention("edges")
  private val datalogCall = DatalogExample.semiNaiveTransitive.name(
    DatalogExample.semiNaiveInitial(Space.Mention(datalogEdgesMention))
  )("complete.path")
  val datalogFixpoint: Space = Supercompiler.lowerFixpointCalls(
    datalogCall,
    mod(DatalogExample.semiNaiveTransitive),
  )
  val datalogEdges: SpatialType =
    pattern(SizeExpr.symbol("edges"), c("edge"), u("source"), u("target"))
  lazy val datalog: SpatialType = SpatialTypeAnalysis.outputRoutineAbstract(
    Routine(RoutinePtr("semi_naive_datalog_abstract"), Vector.empty, Vector(datalogEdgesMention), datalogFixpoint),
    SpatialRoutineAnnotations(
      spaces = Map(datalogEdgesMention -> datalogEdges),
      resultLaws = Vector(SpatialBoundLaw.DirectedTransitiveClosure(datalogEdgesMention)),
    ),
    PartialFunction.empty,
  )

  private val lifeFieldMention = LifeExample.nextStep.mentions.head
  val lifeField: SpatialType = pattern(
    SizeExpr.symbol("liveCells"),
    c("Cell"), a("cell.x", -63, 63), a("cell.y", -63, 63),
  )
  lazy val life: SpatialType = SpatialTypeAnalysis.outputRoutineAbstract(
    LifeExample.nextStep,
    SpatialRoutineAnnotations(
      spaces = Map(lifeFieldMention -> lifeField),
      resultLaws = Vector(SpatialBoundLaw.SubsetOfImage(lifeFieldMention, SizeExpr.const(9))),
      config = SpatialAnalysisConfig(patternLimit = 16),
    ),
    routines = mod(LifeExample.neigh),
  )

  private val puzzleStartMention = SpaceMention("start")
  private val puzzleContext = SlidingPuzzleExample.context(3)
  private val puzzleReachableMention = SpaceMention("reachable")
  val puzzleFixpoint: Space = Space.Fixpoint(
    Space.Mention(puzzleStartMention),
    puzzleReachableMention,
    Space.Union(
      Space.Mention(puzzleReachableMention),
      SlidingPuzzleExample.step(3, Space.Mention(puzzleReachableMention)),
    ),
  )
  val puzzleStart: SpatialType = pattern(
    SizeExpr.One,
    u("blank"), u("tile1"), u("tile2"), u("tile3"), u("tile4"),
    u("tile5"), u("tile6"), u("tile7"), u("tile8"),
  )
  def slidingPuzzleStateCount(width: Int): BigInt =
    FiniteStateCardinality.slidingPuzzleReachableStates(width)
  lazy val puzzle: SpatialType = SpatialTypeAnalysis.outputRoutineAbstract(
    Routine(RoutinePtr("eight_puzzle_reachable_abstract"), Vector.empty, Vector(puzzleStartMention), puzzleFixpoint),
    SpatialRoutineAnnotations(
      spaces = Map(puzzleStartMention -> puzzleStart),
      resultLaws = Vector(SpatialBoundLaw.SlidingPuzzleReachability(puzzleStartMention, width = 3)),
    ),
    routines = puzzleContext,
  )

  private val temperatureWorldMention = SpaceMention("world")
  private val temperaturePrefixes =
    "cell" x
      Space.Literal(TemperatureExample.interval(0, 1, height = 2)) x
      Space.Literal(TemperatureExample.interval(0, 1, height = 2))
  val temperatureWorld: SpatialType = pattern(
    SizeExpr.symbol("worldCells"), c("cell"), u("latitude"), u("longitude"), u("bucket"),
  )
  lazy val temperature: SpatialType = SpatialTypeAnalysis.outputRoutineAbstract(
    Routine(RoutinePtr("temperature_abstract"), Vector.empty, Vector(temperatureWorldMention),
      Space.Mention(temperatureWorldMention) <| temperaturePrefixes),
    SpatialRoutineAnnotations(spaces = Map(temperatureWorldMention -> temperatureWorld)),
    PartialFunction.empty,
  )

  def nqueensConstraintProblem(size: Int): FiniteIntConstraintProblem =
    FiniteIntConstraintProblem.nQueens(size)
  private val (queensRoutine, queensContext) = NQueensExample.program(4)
  val nqueensConstraints: FiniteIntConstraintProblem = nqueensConstraintProblem(4)
  lazy val nqueens: SpatialType = SpatialTypeAnalysis.outputRoutineAbstract(
    queensRoutine,
    SpatialRoutineAnnotations(resultLaws = Vector(SpatialBoundLaw.NQueensSolutions(size = 4))),
    routines = queensContext,
  )

  private val sccEdgesMention = SpaceMention("scc_edges")
  lazy val scc: SpatialType = SpatialTypeAnalysis.outputRoutineAbstract(
    Routine(RoutinePtr("scc_abstract"), Vector.empty, Vector(sccEdgesMention),
      SccCornerstone.expression(Space.Mention(sccEdgesMention))),
    SpatialRoutineAnnotations(
      spaces = Map(sccEdgesMention -> pattern(SizeExpr.symbol("sccEdges"), u("source"), u("target"))),
      resultLaws = Vector(SpatialBoundLaw.RepresentativeScc(sccEdgesMention)),
    ),
    SccCornerstone.rc,
  )

  lazy val all: Vector[(String, SpatialType)] = Vector(
    "aunt" -> aunt,
    "semi-naive-datalog-fixpoint" -> datalog,
    "game-of-life" -> life,
    "eight-puzzle-all-states" -> puzzle,
    "temperature" -> temperature,
    "nqueens" -> nqueens,
    "scc-representative-pairs" -> scc,
  )

object CornerstoneSpatialReport:
  val DefaultOutput: JPath = Paths.get("docs/CORNERSTONE_ABSTRACT_INTERPRETATIONS_GENERATED.md")

  private def tableCell(value: String): String = value.replace("|", "\\|").replace("\n", " ")

  def render(results: Vector[(String, SpatialType)] = CornerstoneAbstractInterpretations.all): String =
    val rows = results.map { (name, result) =>
      s"| `$name` | `${tableCell(result.size.show)}` | `${tableCell(result.pathLength.show)}` | ${result.strata.size} |"
    }
    (Vector(
      "# Generated Cornerstone Spatial Summary",
      "",
      "This deterministic table is generated from the production `SpatialTypeAnalysis` entry point. The analysis does not execute or materialize any concrete cornerstone output.",
      "",
      "Regenerate it with `scala-cli run src/main/scala src/test/scala --test --server=false --scala 3.8.1 --source 3.3 --dependency org.scalameta::munit:1.2.1 --dependency org.scala-lang.modules::scala-collection-contrib:0.3.0 --main-class morkl.cornerstoneSpatialTypeReport --`.",
      "",
      "| Program | Cardinality interval | Path-length interval | Strata |",
      "| --- | --- | --- | ---: |",
    ) ++ rows).mkString("\n") + "\n"

  def write(output: JPath = DefaultOutput): JPath =
    Option(output.getParent).foreach(parent => Files.createDirectories(parent))
    Files.writeString(output, render(), StandardCharsets.UTF_8)
    output

@main def cornerstoneSpatialTypeReport(args: String*): Unit =
  require(args.length <= 1, "usage: cornerstoneSpatialTypeReport [output-file]")
  val output = CornerstoneSpatialReport.write(args.headOption.map(Paths.get(_)).getOrElse(CornerstoneSpatialReport.DefaultOutput))
  println(s"wrote ${CornerstoneAbstractInterpretations.all.length} cornerstone spatial analyses to $output")

class CornerstoneSpatialTypeTest extends FunSuite:
  override val munitTimeout: Duration = 1.minute

  private def transitiveClosure(edges: Set[(Int, Int)]): Set[(Int, Int)] =
    var known = edges
    var changed = true
    while changed do
      val next = known ++ (for (a, b) <- known; (c, d) <- known if b == c yield a -> d)
      changed = next.size != known.size
      known = next
    known

  private def lifeStep(cells: Set[(Int, Int)]): Set[(Int, Int)] =
    val counts = collection.mutable.Map.empty[(Int, Int), Int].withDefaultValue(0)
    for (x, y) <- cells; dx <- -1 to 1; dy <- -1 to 1 if dx != 0 || dy != 0 do
      val point = (x + dx, y + dy)
      counts.update(point, counts(point) + 1)
    counts.iterator.collect {
      case (cell, neighbors) if neighbors == 3 || (neighbors == 2 && cells(cell)) => cell
    }.toSet

  test("spatial routine analysis does not execute a zero-argument generator") {
    val routine = Routine(
      RoutinePtr("must_not_execute"),
      Vector.empty,
      Vector.empty,
      Space.GroundedSS(Space.Singleton(Path.ZERO), _ => throw RuntimeException("concrete evaluation occurred")),
    )
    val result = SpatialTypeAnalysis.outputRoutine(routine, Map.empty, Map.empty)
    assert(!result.exactValue.isDefined)
  }

  test("strict range transfer propagates its literal annotation without concrete evaluation") {
    val source = Space.Literal(SpaceValue("a", "b", "c"))
    val routine = Routine(RoutinePtr("abstract_range"), Vector.empty, Vector.empty, Space.Range(source, 1, 2))
    val result = SpatialTypeAnalysis.outputRoutineAbstract(routine, SpatialRoutineAnnotations(), PartialFunction.empty)
    assertEquals(result.size, ResultSizeEstimate.exact(SizeExpr.One))
    assertEquals(result.pathLength, PathLengthEstimate.exact(PathLengthExpr.One))
    assertEquals(result.exactValue, None)
  }

  test("annotation-only bound resolution never executes opaque atoms") {
    val opaque = Space.GroundedSS(Space.Empty, _ => throw RuntimeException("bound resolution evaluated output"))
    assertEquals(SizeExpr.sizeOf(opaque).annotatedValue, None)
    assertEquals(PathLengthExpr.MinimumLengthOf(opaque).annotatedValue, None)
    assertEquals(PathLengthExpr.MaximumLengthOf(opaque).annotatedValue, None)
    assertEquals(SizeExpr.sizeOf(opaque).annotatedBound(Z3BoundDirection.Lower), Some(BigInt(0)))
    assertEquals(SizeExpr.sizeOf(opaque).annotatedBound(Z3BoundDirection.Upper), None)
    assertEquals(PathLengthExpr.MinimumLengthOf(opaque).annotatedBound(Z3BoundDirection.Lower), Some(BigInt(0)))
    assertEquals(PathLengthExpr.MaximumLengthOf(opaque).annotatedBound(Z3BoundDirection.Upper), None)
  }

  test("cornerstone abstract interpretations use annotated variables and retain output shapes") {
    import CornerstoneAbstractInterpretations.*

    datalogFixpoint match
      case Space.Unwrap(Space.Fixpoint(_, _, _), _) => ()
      case other => fail(s"semi-naive Datalog was not lowered to Fixpoint: ${other.show}")
    puzzleFixpoint match
      case Space.Fixpoint(_, _, _) => ()
      case other => fail(s"8-puzzle reachability was not lowered to Fixpoint: ${other.show}")

    assertEquals(aunt.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(3)))
    assertEquals(datalog.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(2)))
    assertEquals(life.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(3)))
    assertEquals(puzzle.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(9)))
    assertEquals(temperature.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(4)))
    assertEquals(nqueens.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(4)))
    assertEquals(scc.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(2)))

    assert(all.forall((_, result) => result.exactValue.isEmpty))
    assertEquals(aunt.size.lower, SizeExpr.Zero)
    assert(aunt.size.upper.show.contains("childEdges"))
    assertEquals(life.strata.flatMap(_.pattern).map(_.show).toSet.size, 8)
    val lifeCap = SizeExpr.multiply(SizeExpr.symbol("liveCells"), SizeExpr.const(9))
    assertEquals(life.size.upper, lifeCap)
    assert(life.size.upper.nodeCount(32) <= 8, life.size.show)
    assert(life.strata.forall(stratum =>
      SizeExpr.provablyNoGreater(stratum.cardinality.upper, lifeCap)), life.show)
    assert(datalog.size.lower.show.contains("edges"))
    assert(datalog.size.upper.show.contains("edges"))
    assertEquals(puzzle.size, ResultSizeEstimate.exact(SizeExpr.const(181440)))
    assertEquals(temperature.size.lower, SizeExpr.Zero)
    assertEquals(temperature.size.upper, SizeExpr.symbol("worldCells"))
    assertEquals(nqueensConstraints.count, BigInt(2))
    assertEquals(nqueens.size, ResultSizeEstimate.exact(SizeExpr.const(2)))
    assert(nqueens.strata.forall(_.cardinality.upper.evaluate.exists(_ <= 2)))
    assert(puzzle.strata.forall(_.cardinality.upper.evaluate.exists(_ <= 181440)))
    assertEquals(
      Files.readString(CornerstoneSpatialReport.DefaultOutput, StandardCharsets.UTF_8),
      CornerstoneSpatialReport.render(all),
      "regenerate the checked cornerstone spatial summary with morkl.cornerstoneSpatialTypeReport",
    )
  }

  test("SCC cornerstone retains pair shape and the representative certificate") {
    import CornerstoneAbstractInterpretations.scc
    assertEquals(scc.pathLength, PathLengthEstimate.exact(PathLengthExpr.const(2)))
    assertEquals(scc.size.lower, SizeExpr.Zero)
    val cap = SizeExpr.multiply(SizeExpr.const(2), SizeExpr.symbol("sccEdges"))
    assert(SizeExpr.provablyNoGreater(scc.size.upper, cap), scc.size.show)
    assert(scc.size.upper.nodeCount(64) <= 32, scc.size.show)
  }

  test("directed closure cardinality contract is exhaustive on all three-node graphs") {
    val possible = (for left <- 0 until 3; right <- 0 until 3 yield left -> right).toVector
    for mask <- 0 until (1 << possible.size) do
      val edges = possible.indices.collect { case index if (mask & (1 << index)) != 0 => possible(index) }.toSet
      val closure = transitiveClosure(edges)
      assert(closure.size >= edges.size, s"closure dropped an edge for mask $mask")
      assert(closure.size <= edges.size * edges.size,
        s"closure exceeded E^2 for mask $mask: E=${edges.size}, closure=${closure.size}")
  }

  test("divide-and-conquer SCC representative envelope is exhaustive on all three-node graphs") {
    val possible = (for left <- 0 until 3; right <- 0 until 3 yield left -> right).toVector
    for mask <- 0 until (1 << possible.size) do
      val edges = possible.indices.collect { case index if (mask & (1 << index)) != 0 => possible(index) }.toSet
      val closure = transitiveClosure(edges)
      val nodes = edges.flatMap((from, to) => Set(from, to))
      val components = nodes.groupBy { node =>
        nodes.filter(other => other == node || (closure(node -> other) && closure(other -> node)))
      }.values.toSet
      val representatives = components.iterator.filter(_.size > 1).flatMap { component =>
        val representative = component.min
        component.iterator.filterNot(_ == representative).map(representative -> _)
      }.toSet
      assert(representatives.size <= 2 * edges.size,
        s"representative SCC output exceeded 2E for mask $mask: E=${edges.size}, output=${representatives.size}")
      assert(representatives.forall((representative, member) =>
        closure(representative -> member) && closure(member -> representative)))
  }

  test("Game of Life output is contained in the nine-cell image of every live cell") {
    val possible = (for x <- 0 until 3; y <- 0 until 3 yield x -> y).toVector
    for mask <- 0 until (1 << possible.size) do
      val field = possible.indices.collect { case index if (mask & (1 << index)) != 0 => possible(index) }.toSet
      val next = lifeStep(field)
      val image = field.flatMap { (x, y) =>
        for dx <- -1 to 1; dy <- -1 to 1 yield (x + dx, y + dy)
      }
      assert(next.subsetOf(image), s"Life produced a cell outside the radius-one image for mask $mask")
      assert(next.size <= 9 * field.size, s"Life exceeded the 9L cardinality bound for mask $mask")
  }

  test("finite relational domain counts n-queens without evaluating MORKL") {
    import CornerstoneAbstractInterpretations.nqueensConstraintProblem
    val known = Vector[BigInt](1, 0, 0, 2, 10, 4)
    assertEquals((1 to 6).map(size => nqueensConstraintProblem(size).count).toVector, known)
  }

  test("sliding-puzzle component bounds are parameterized by board width") {
    import CornerstoneAbstractInterpretations.slidingPuzzleStateCount
    assertEquals((1 to 3).map(slidingPuzzleStateCount).toVector,
      Vector[BigInt](1, 12, 181440))
  }
