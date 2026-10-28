package morkl

import munit.FunSuite
import scala.collection.mutable

object SpatialCostCounterCorpus:
  private val leftMention = SpaceMention("cost_left")
  private val rightMention = SpaceMention("cost_right")

  case class CounterCase(name: String, expression: Space, left: SpaceValue, right: SpaceValue)
  case class CounterRow(
    name: String,
    backend: SpatialBackend,
    predicted: SpatialCostComponents,
    actual: ExecutorCostCounts,
  )

  private def under(head: String, count: Int): SpaceValue = SpaceValue(
    (0 until count).map(index => PathValue(List(PathItem(head), PathItem(index.toString)))).toSet,
  )

  private def wide(prefix: String, count: Int): SpaceValue = SpaceValue(
    (0 until count).map(index => PathValue(List(PathItem(s"$prefix$index")))).toSet,
  )

  private def headedWide(prefix: String, count: Int): SpaceValue = SpaceValue(
    (0 until count).map(index => PathValue(List(PathItem(s"$prefix$index"), PathItem("value")))).toSet,
  )

  private val maxRightPrefixes = 4096
  private val prefixSource = headedWide("p", maxRightPrefixes)

  def cases: Vector[CounterCase] =
    val selective = Vector(64, 512, 4096).flatMap { count =>
      val left = under("a", count / 2).paths ++ under("b", count - count / 2).paths
      Vector(
        CounterCase(
          s"restriction-left-$count",
          Space.Restriction(Space.Mention(leftMention), Space.Mention(rightMention)),
          SpaceValue(left),
          SpaceValue(Set(PathValue(List(PathItem("a"))), PathValue(List(PathItem("b"))))),
        ),
        CounterCase(
          s"intersection-left-$count",
          Space.Intersection(Space.Mention(leftMention), Space.Mention(rightMention)),
          under("a", count),
          under("b", 8),
        ),
        CounterCase(
          s"subtraction-left-$count",
          Space.Subtraction(Space.Mention(leftMention), Space.Mention(rightMention)),
          under("a", count),
          under("b", 8),
        ),
        CounterCase(
          s"raffination-left-$count",
          Space.Raffination(Space.Mention(leftMention), Space.Mention(rightMention)),
          SpaceValue(left),
          SpaceValue(Set(PathValue(List(PathItem("a"))), PathValue(List(PathItem("b"))))),
        ),
      )
    }
    val growingRight = Vector(64, 512, 4096).map { count =>
      CounterCase(
        s"restriction-right-$count",
        Space.Restriction(Space.Mention(leftMention), Space.Mention(rightMention)),
        prefixSource,
        SpaceValue((0 until count).map(index => PathValue(List(PathItem(s"p$index")))).toSet),
      )
    }
    val products = Vector(64, 256, 1024).flatMap { count =>
      Vector(
        CounterCase(
          s"composition-left-$count",
          Space.Composition(Space.Mention(leftMention), Space.Mention(rightMention)),
          wide("l", count),
          wide("r", 4),
        ),
        CounterCase(
          s"composition-right-$count",
          Space.Composition(Space.Mention(leftMention), Space.Mention(rightMention)),
          wide("l", 4),
          wide("r", count),
        ),
      )
    }
    selective ++ growingRight ++ products

  private def optimized(value: CounterCase): Space =
    Supercompiler.normalize(value.expression).space

  private def predicted(value: CounterCase, backend: SpatialBackend): SpatialCostComponents =
    val annotations = SpatialRoutineAnnotations(spaces = Map(
      leftMention -> SpatialType.exact(value.left),
      rightMention -> SpatialType.exact(value.right),
    ))
    val routine = Routine(RoutinePtr(s"abstract_${value.name}"), Vector.empty,
      Vector(leftMention, rightMention), value.expression)
    Supercompiler.optimizedSpatialType(routine, annotations, PartialFunction.empty)
      .cost.forBackend(backend).componentsUpper

  private def actualTrie(value: CounterCase, program: Space): (TrieSpace, ExecutorCostCounts) =
    val context = TrieSpaceContextMap(Map(
      leftMention -> TrieSpace.fromSpaceValue(value.left),
      rightMention -> TrieSpace.fromSpaceValue(value.right),
    ))
    ExecutorCostMeter.measure(evalTrie(program)(using PathContext.emptyMap, context, PartialFunction.empty))

  private def actualZipper(value: CounterCase, program: Space): (TrieSpace, ExecutorCostCounts) =
    val trieContext = TrieSpaceContextMap(Map(
      leftMention -> TrieSpace.fromSpaceValue(value.left),
      rightMention -> TrieSpace.fromSpaceValue(value.right),
    ))
    given ZipperSpaceContext = ZipperSpaceContext.fromTrie(trieContext)
    ExecutorCostMeter.measure(evalZ(program))

  private def actualGraph(value: CounterCase, program: Space): (TrieSpace, ExecutorCostCounts) =
    val routine = Routine(RoutinePtr(s"counter_${value.name}"), Vector.empty,
      Vector(leftMention, rightMention), program)
    val graph = transpile(routine)
    val arguments = Vector(TrieSpace.fromSpaceValue(value.left), TrieSpace.fromSpaceValue(value.right))
    def execute(): TrieSpace =
      val frame = new Array[List[Int] | TrieSpace | Null](graph.nodes.length)
      arguments.indices.foreach(index => frame(index) = arguments(index))
      val stack = mutable.Stack(frame)
      execT(graph, stack)
      frame.last.asInstanceOf[TrieSpace]
    execute() // populate graph literal/path caches outside the measured region
    ExecutorCostMeter.measure(execute())

  def rows: Vector[CounterRow] = cases.flatMap { value =>
    val program = optimized(value)
    val trie = actualTrie(value, program)
    val zipper = actualZipper(value, program)
    val graph = actualGraph(value, program)
    require(trie._1 == zipper._1 && trie._1 == graph._1, s"${value.name}: executor disagreement")
    Vector(
      CounterRow(value.name, SpatialBackend.Trie, predicted(value, SpatialBackend.Trie), trie._2),
      CounterRow(value.name, SpatialBackend.Zipper, predicted(value, SpatialBackend.Zipper), zipper._2),
      CounterRow(value.name, SpatialBackend.Graph, predicted(value, SpatialBackend.Graph), graph._2),
    )
  }

@main def spatialCostCounterReport(): Unit =
  SpatialCostCounterCorpus.rows.foreach { row =>
    println(s"${row.name},${row.backend},predicted=${row.predicted},actual=${row.actual}")
  }

class SpatialCostCounterTest extends FunSuite:
  private def constant(expr: SizeExpr, clue: String): Long =
    expr.annotatedBound(Z3BoundDirection.Upper).filter(_.isValidLong).map(_.toLong)
      .getOrElse(fail(s"$clue was not a finite concrete bound: ${expr.show}"))

  private def assertComponentBounds(
    name: String,
    predicted: SpatialCostComponents,
    actual: ExecutorCostCounts,
  ): Unit =
    def covered(upper: SizeExpr, measured: Long): Boolean =
      SizeExpr.provablyNoGreater(SizeExpr.const(measured), upper)
    assert(covered(predicted.nodeVisits, actual.nodeVisits),
      s"$name node visits under-predicted: predicted=$predicted actual=$actual")
    assert(covered(predicted.patriciaVisits, actual.patriciaVisits),
      s"$name Patricia visits under-predicted: predicted=$predicted actual=$actual")
    assert(covered(predicted.pathComparisons, actual.pathComparisons),
      s"$name path comparisons under-predicted: predicted=$predicted actual=$actual")
    assert(covered(predicted.allocations, actual.allocations),
      s"$name allocations under-predicted: predicted=$predicted actual=$actual")
    assert(covered(predicted.rounds, actual.rounds),
      s"$name rounds under-predicted: predicted=$predicted actual=$actual")

  private def bounded(
    name: String,
    predicted: Long,
    actual: Long,
    enforceTightness: Boolean = true,
  ): Unit =
    assert(predicted >= actual, s"$name under-predicted: predicted=$predicted actual=$actual")
    if enforceTightness && actual > 0 then
      assert(predicted <= actual * 8,
        s"$name was asymptotically or materially loose: predicted=$predicted actual=$actual")

  test("typed costs bound asymmetric optimized executor counters without fitted residuals") {
    val rows = SpatialCostCounterCorpus.rows
    rows.foreach { row =>
      bounded(s"${row.name}/${row.backend}/nodeVisits",
        constant(row.predicted.nodeVisits, s"${row.name} node visits"), row.actual.nodeVisits)
      // Path items receive process-global numeric ids. Prior tests can change
      // the resulting IntMap topology (and therefore the exact number of
      // Patricia nodes touched) without changing the operation or its
      // asymptotic class. Retain the sound upper-bound gate for every row and
      // the topology-independent stable/growth gates below; the focused report
      // records the <= 8x ratio for its canonical interning order only.
      bounded(s"${row.name}/${row.backend}/patriciaVisits",
        constant(row.predicted.patriciaVisits, s"${row.name} Patricia visits"),
        row.actual.patriciaVisits,
        enforceTightness = false)
      bounded(s"${row.name}/${row.backend}/pathComparisons",
        constant(row.predicted.pathComparisons, s"${row.name} path comparisons"), row.actual.pathComparisons)
      bounded(s"${row.name}/${row.backend}/allocations",
        constant(row.predicted.allocations, s"${row.name} allocations"), row.actual.allocations)
      bounded(s"${row.name}/${row.backend}/rounds",
        constant(row.predicted.rounds, s"${row.name} rounds"), row.actual.rounds)
    }

    def nodeCounts(prefix: String, backend: SpatialBackend): Vector[(Long, Long)] = rows
      .filter(row => row.name.startsWith(prefix) && row.backend == backend)
      .sortBy(_.name.split('-').last.toInt)
      .map(row => constant(row.predicted.nodeVisits, s"${row.name} node visits") -> row.actual.nodeVisits)

    def patriciaCounts(prefix: String, backend: SpatialBackend): Vector[(Long, Long)] = rows
      .filter(row => row.name.startsWith(prefix) && row.backend == backend)
      .sortBy(_.name.split('-').last.toInt)
      .map(row => constant(row.predicted.patriciaVisits, s"${row.name} Patricia visits") -> row.actual.patriciaVisits)

    def predictedStable(values: Vector[Long]): Boolean = values.max <= values.min * 8
    def strictlyIncreasing(values: Vector[Long]): Boolean = values.sliding(2).forall {
      case Vector(left, right) => right > left
      case _ => true
    }

    SpatialBackend.values.filterNot(_ == SpatialBackend.Reference).foreach { backend =>
      Vector("restriction-left-", "intersection-left-", "subtraction-left-",
        "raffination-left-", "composition-right-").foreach { prefix =>
        val counts = nodeCounts(prefix, backend)
        val predicted = counts.map(_._1)
        assert(predicted.max <= predicted.min * 8,
          s"$backend/$prefix predicted cost grew asymptotically with an irrelevant operand: $counts")
        assertEquals(counts.map(_._2).distinct.size, 1,
          s"$backend/$prefix actual cost changed while irrelevant operand grew: $counts")
      }
      Vector("restriction-right-", "composition-left-").foreach { prefix =>
        val counts = nodeCounts(prefix, backend)
        assert(counts.map(_._1).sliding(2).forall {
          case Vector(left, right) => right > left
          case _ => true
        }, s"$backend/$prefix predicted cost did not grow with the traversed operand: $counts")
        assert(counts.map(_._2).sliding(2).forall {
          case Vector(left, right) => right > left
          case _ => true
        }, s"$backend/$prefix actual cost did not grow with the traversed operand: $counts")
      }
      Vector("restriction-left-", "intersection-left-", "subtraction-left-",
        "raffination-left-", "composition-right-").foreach { prefix =>
        val counts = patriciaCounts(prefix, backend)
        assert(predictedStable(counts.map(_._1)),
          s"$backend/$prefix predicted Patricia cost grew with an irrelevant operand: $counts")
        assertEquals(counts.map(_._2).distinct.size, 1,
          s"$backend/$prefix actual Patricia cost changed while irrelevant operand grew: $counts")
      }
      Vector("restriction-right-", "composition-left-").foreach { prefix =>
        val counts = patriciaCounts(prefix, backend)
        assert(strictlyIncreasing(counts.map(_._1)),
          s"$backend/$prefix predicted Patricia cost did not grow with the traversed operand: $counts")
        assert(strictlyIncreasing(counts.map(_._2)),
          s"$backend/$prefix actual Patricia cost did not grow with the traversed operand: $counts")
      }
    }
  }

  test("unwrap cost is prefix-only for optimized backends") {
    val sourceMention = SpaceMention("unwrap_source")
    val prefix = PathValue(List(PathItem("a"), PathItem("b"), PathItem("c")))
    val expression = Space.Unwrap(Space.Mention(sourceMention), Path.Constant(prefix))
    val small = SpaceValue(Set(PathValue(prefix.items :+ PathItem("0"))))
    val large = SpaceValue((0 until 4096).map(index =>
      PathValue(prefix.items ++ List(PathItem(index.toString), PathItem("value")))).toSet)

    def predicted(value: SpaceValue, backend: SpatialBackend): Long =
      val result = Supercompiler.optimizedSpatialType(expression,
        SpatialAssumptions(spaces = Map(sourceMention -> SpatialType.exact(value))))
      constant(result.cost.forBackend(backend).componentsUpper.nodeVisits, s"$backend unwrap")

    def trieActual(value: SpaceValue): Long =
      val context = TrieSpaceContextMap(Map(sourceMention -> TrieSpace.fromSpaceValue(value)))
      ExecutorCostMeter.measure(evalTrie(expression)(using
        PathContext.emptyMap, context, PartialFunction.empty))._2.nodeVisits

    def zipperActual(value: SpaceValue): Long =
      given ZipperSpaceContext = ZipperSpaceContext.fromTrie(
        TrieSpaceContextMap(Map(sourceMention -> TrieSpace.fromSpaceValue(value))))
      ExecutorCostMeter.measure(evalZ(expression))._2.nodeVisits

    assertEquals(Vector(predicted(small, SpatialBackend.Trie), predicted(large, SpatialBackend.Trie)), Vector(4L, 4L))
    assertEquals(Vector(trieActual(small), trieActual(large)), Vector(4L, 4L))
    assertEquals(Vector(predicted(small, SpatialBackend.Zipper), predicted(large, SpatialBackend.Zipper)), Vector(4L, 4L))
    assertEquals(Vector(zipperActual(small), zipperActual(large)), Vector(3L, 3L))
  }

  test("lazy intersection cost follows the forced frontier and bounds measured zipper work") {
    val a = SpaceMention("lazy_union_a")
    val b = SpaceMention("lazy_union_b")
    val d = SpaceMention("lazy_union_d")
    val e = SpaceMention("lazy_union_e")
    val c = SpaceMention("lazy_union_c")
    val demand = SpaceValue(Set(Syntax.parse("shared.hit")))

    def values(count: Int): Map[SpaceMention, SpaceValue] = Map(
      a -> SpaceValue((0 until count).map(i => Syntax.parse(s"left.$i")).toSet + Syntax.parse("shared.hit")),
      b -> SpaceValue((0 until count).map(i => Syntax.parse(s"right.$i")).toSet),
      d -> SpaceValue((0 until count).map(i => Syntax.parse(s"down.$i")).toSet),
      e -> SpaceValue((0 until count).map(i => Syntax.parse(s"extra.$i")).toSet),
      c -> demand,
    )

    def samePrefixValues(count: Int): Map[SpaceMention, SpaceValue] = Map(
      a -> SpaceValue((0 until count).map(i => Syntax.parse(s"shared.left.$i")).toSet + Syntax.parse("shared.hit")),
      b -> SpaceValue((0 until count).map(i => Syntax.parse(s"shared.right.$i")).toSet),
      d -> SpaceValue((0 until count).map(i => Syntax.parse(s"shared.down.$i")).toSet),
      e -> SpaceValue((0 until count).map(i => Syntax.parse(s"shared.extra.$i")).toSet),
      c -> demand,
    )

    def analyzed(expression: Space, inputs: Map[SpaceMention, SpaceValue]): SpatialCostInterval =
      val assumptions = SpatialAssumptions(spaces = inputs.view.mapValues(value => SpatialType.exact(value)).toMap)
      SpatialTypeAnalysis.output(expression, assumptions).cost.forBackend(SpatialBackend.Zipper)

    def actual(expression: Space, inputs: Map[SpaceMention, SpaceValue]): ExecutorCostCounts =
      val tries = TrieSpaceContextMap(inputs.view.mapValues(value => TrieSpace.fromSpaceValue(value)).toMap)
      val context = ZipperSpaceContext.fromTrie(tries)
      ExecutorCostMeter.measure(evalZ(expression)(using
        PathContext.emptyMap, context, PartialFunction.empty))._2

    val binary = Space.Intersection(Space.Union(Space.Mention(a), Space.Mention(b)), Space.Mention(c))
    val nested = Space.Intersection(
      Space.Union(Space.Union(Space.Union(Space.Mention(a), Space.Mention(b)), Space.Mention(d)), Space.Mention(e)),
      Space.Mention(c),
    )

    def referencePredicted(count: Int): Long =
      val left = SpaceValue((0 until count).map(i => Syntax.parse(s"left.$i")).toSet + Syntax.parse("shared.hit"))
      val right = SpaceValue((0 until count).map(i => Syntax.parse(s"right.$i")).toSet)
      val assumptions = SpatialAssumptions(spaces = Map(
        a -> SpatialType.exact(left),
        b -> SpatialType.exact(right),
        c -> SpatialType.exact(demand),
      ))
      constant(SpatialTypeAnalysis.output(binary, assumptions).cost.forBackend(SpatialBackend.Reference).workUpper,
        s"reference lazy union $count")

    Vector(binary, nested).foreach { expression =>
      val intervals = Vector(32, 512, 4096).map(count => analyzed(expression, values(count)))
      val measured = Vector(32, 512, 4096).map(count => actual(expression, values(count)))
      val predicted = intervals.map(interval => constant(interval.workUpper, "lazy zipper work"))
      assertEquals(predicted.distinct.size, 1,
        s"zipper work should depend on the forced C frontier, not resident branch widths: $predicted")
      assertEquals(measured.map(_.nodeVisits).distinct.size, 1, s"measured node visits grew: $measured")
      assertEquals(measured.map(_.patriciaVisits).distinct.size, 1, s"measured Patricia visits grew: $measured")
      intervals.zip(measured).foreach { (interval, work) =>
        assert(SizeExpr.provablyNoGreater(interval.workLower, interval.workUpper), interval.show)
        assert(SizeExpr.provablyNoGreater(interval.allocationLower, interval.allocationUpper), interval.show)
        assert(constant(interval.workLower, "lazy work lower") <= work.nodeVisits,
          s"work lower exceeded measured node visits: interval=${interval.show}, measured=$work")
        assert(constant(interval.allocationLower, "lazy allocation lower") <= work.allocations,
          s"allocation lower exceeded measured allocations: interval=${interval.show}, measured=$work")
        assert(constant(interval.componentsUpper.nodeVisits, "lazy node bound") >= work.nodeVisits, interval.show)
        assert(constant(interval.componentsUpper.patriciaVisits, "lazy Patricia bound") >= work.patriciaVisits,
          interval.show)
      }
    }

    Vector(binary, nested).foreach { expression =>
      val widths = Vector(32, 512, 4096)
      val intervals = widths.map(count => analyzed(expression, samePrefixValues(count)))
      val measured = widths.map(count => actual(expression, samePrefixValues(count)))
      assert(measured.forall(_.nodeVisits > 0),
        s"same-prefix membership work must be visible to the cursor meter: $measured")
      assertEquals(measured.map(_.nodeVisits).distinct.size, 1,
        s"wide irrelevant branches below the demanded root key were traversed: $measured")
      assertEquals(measured.map(_.patriciaVisits).distinct.size, 1,
        s"same-prefix Patricia work grew with irrelevant virtual branches: $measured")
      assertEquals(intervals.map(interval => constant(interval.workUpper, "same-prefix zipper work")).distinct.size, 1)
      intervals.zip(measured).foreach { (interval, work) =>
        assert(constant(interval.componentsUpper.nodeVisits, "same-prefix node bound") >= work.nodeVisits,
          s"cursor membership probes exceeded the static cap: interval=${interval.show}, measured=$work")
        assert(constant(interval.componentsUpper.patriciaVisits, "same-prefix Patricia bound") >= work.patriciaVisits,
          s"Patricia membership work exceeded the static cap: interval=${interval.show}, measured=$work")
      }
    }

    val unwrapSource = SpaceMention("lazy_unwrap_source")
    val longPrefix = PathValue((0 until 20).map(i => PathItem(s"p$i")).toList)
    val unwrapDemand = SpaceMention("lazy_unwrap_demand")
    val unwrapExpression = Space.Intersection(
      Space.Unwrap(Space.Mention(unwrapSource), Path.Constant(longPrefix)),
      Space.Mention(unwrapDemand),
    )
    val unwrapInputs = Map(
      unwrapSource -> SpaceValue(Set(PathValue(longPrefix.items :+ PathItem("hit")))),
      unwrapDemand -> SpaceValue(Set(Syntax.parse("hit"))),
    )
    val unwrapInterval = analyzed(unwrapExpression, unwrapInputs)
    val unwrapMeasured = actual(unwrapExpression, unwrapInputs)
    assertEquals(unwrapMeasured.nodeVisits, 22L,
      s"twenty prefix moves plus the demanded frontier must remain metered: $unwrapMeasured")
    assertEquals(unwrapMeasured.pathComparisons, 20L,
      s"every eager Unwrap prefix move must remain visible: $unwrapMeasured")
    assert(constant(unwrapInterval.workUpper, "long-prefix unwrap work") >= unwrapMeasured.nodeVisits,
      s"long-prefix work was capped by the smaller outer frontier: interval=${unwrapInterval.show}, measured=$unwrapMeasured")
    assert(constant(unwrapInterval.componentsUpper.nodeVisits, "long-prefix unwrap nodes") >= unwrapMeasured.nodeVisits,
      s"long-prefix nodes exceeded the static bound: interval=${unwrapInterval.show}, measured=$unwrapMeasured")
    assert(constant(unwrapInterval.componentsUpper.pathComparisons, "long-prefix unwrap comparisons") >= unwrapMeasured.pathComparisons,
      s"long-prefix comparisons exceeded the static bound: interval=${unwrapInterval.show}, measured=$unwrapMeasured")

    val longPath = PathValue(longPrefix.items :+ PathItem("hit"))
    Vector[(String, Space, Long)](
      ("literal", Space.Literal(SpaceValue(Set(longPath))), 21L),
      ("singleton", Space.Singleton(Path.Constant(longPath)), 22L),
    ).foreach { (name, expression, expectedAllocations) =>
      val interval = analyzed(expression, Map.empty)
      val measured = actual(expression, Map.empty)
      assertEquals(measured.allocations, expectedAllocations, s"$name construction counter changed: $measured")
      assert(constant(interval.workUpper, s"$name construction work") >= measured.allocations,
        s"$name construction work omitted trie creation: interval=${interval.show}, measured=$measured")
      assert(constant(interval.allocationUpper, s"$name construction allocation") >= measured.allocations,
        s"$name construction allocation omitted trie nodes: interval=${interval.show}, measured=$measured")
      assert(constant(interval.componentsUpper.allocations, s"$name construction component") >= measured.allocations,
        s"$name component allocation omitted trie nodes: interval=${interval.show}, measured=$measured")
      assert(constant(interval.componentsUpper.patriciaVisits, s"$name construction Patricia") >= measured.patriciaVisits,
        s"$name Patricia construction exceeded its component bound: interval=${interval.show}, measured=$measured")
    }

    val residentOther = SpaceMention("lazy_singleton_other")
    val singletonDemand = SpaceMention("lazy_singleton_demand")
    val singletonExpression = Space.Intersection(
      Space.Union(Space.Singleton(Path.Constant(longPath)), Space.Mention(residentOther)),
      Space.Mention(singletonDemand),
    )
    val singletonInputs = Map(
      residentOther -> SpaceValue(Set(Syntax.parse("other"))),
      singletonDemand -> SpaceValue(Set(Syntax.parse("x"))),
    )
    val singletonInterval = analyzed(singletonExpression, singletonInputs)
    val singletonMeasured = actual(singletonExpression, singletonInputs)
    assertEquals(singletonMeasured.allocations, 22L,
      s"the rejected resident singleton still constructs exactly its path trie: $singletonMeasured")
    assert(constant(singletonInterval.allocationUpper, "resident singleton allocation") >= singletonMeasured.allocations,
      s"outer demand incorrectly capped eager singleton construction: interval=${singletonInterval.show}, measured=$singletonMeasured")
    assert(constant(singletonInterval.componentsUpper.allocations, "resident singleton component") >= singletonMeasured.allocations,
      s"resident singleton component bound omitted construction: interval=${singletonInterval.show}, measured=$singletonMeasured")

    val reference = Vector(32, 512, 4096).map(referencePredicted)
    assert(reference.sliding(2).forall(window => window(0) < window(1)),
      s"reference work should retain eager union construction: $reference")
  }

  test("demand caps reject resident operators with nonlocal emptiness or eager merge work") {
    val width = 4096

    def check(
      name: String,
      expression: Space,
      inputs: Map[SpaceMention, SpaceValue],
      expected: SpaceValue,
    ): (SpatialCostInterval, ExecutorCostCounts) =
      val assumptions = SpatialAssumptions(
        spaces = inputs.view.mapValues(value => SpatialType.exact(value)).toMap)
      val interval = SpatialTypeAnalysis.output(expression, assumptions)
        .cost.forBackend(SpatialBackend.Zipper)
      val trieContext = TrieSpaceContextMap(
        inputs.view.mapValues(value => TrieSpace.fromSpaceValue(value)).toMap)
      given ZipperSpaceContext = ZipperSpaceContext.fromTrie(trieContext)
      val (actualValue, actualCost) = ExecutorCostMeter.measure(evalZ(expression))
      assertEquals(actualValue.toSpaceValue, expected, name)
      assertComponentBounds(name, interval.componentsUpper, actualCost)
      interval -> actualCost

    val intersectionLeft = SpaceMention("demand_cap_intersection_left")
    val intersectionRight = SpaceMention("demand_cap_intersection_right")
    val intersectionConsumer = SpaceMention("demand_cap_intersection_consumer")
    val sharedHit = Syntax.parse("shared.hit")
    check(
      "stored nested intersection",
      Space.Intersection(
        Space.Intersection(Space.Mention(intersectionLeft), Space.Mention(intersectionRight)),
        Space.Mention(intersectionConsumer),
      ),
      Map(
        intersectionLeft -> SpaceValue(
          (0 until width).map(index => Syntax.parse(s"shared.left.$index")).toSet + sharedHit),
        intersectionRight -> SpaceValue(
          (0 until width).map(index => Syntax.parse(s"shared.right.$index")).toSet + sharedHit),
        intersectionConsumer -> SpaceValue(Set(sharedHit)),
      ),
      SpaceValue(Set(sharedHit)),
    )

    val subtractionLeft = SpaceMention("demand_cap_subtraction_left")
    val subtractionRight = SpaceMention("demand_cap_subtraction_right")
    val subtractionConsumer = SpaceMention("demand_cap_subtraction_consumer")
    val equalResident = SpaceValue(
      (0 until width).map(index => Syntax.parse(s"shared.k$index.value")).toSet)
    check(
      "subtraction descendant emptiness",
      Space.Intersection(
        Space.Subtraction(Space.Mention(subtractionLeft), Space.Mention(subtractionRight)),
        Space.Mention(subtractionConsumer),
      ),
      Map(
        subtractionLeft -> equalResident,
        subtractionRight -> equalResident,
        subtractionConsumer -> SpaceValue(Set(Syntax.parse("shared"))),
      ),
      SpaceValue(Set.empty),
    )

    val restrictionSource = SpaceMention("demand_cap_restriction_source")
    val restrictionPrefixes = SpaceMention("demand_cap_restriction_prefixes")
    val prefixConsumer = SpaceMention("demand_cap_prefix_consumer")
    check(
      "prefix closure descendant emptiness",
      Space.Intersection(
        Space.PrefixClosure(Space.Restriction(
          Space.Mention(restrictionSource), Space.Mention(restrictionPrefixes))),
        Space.Mention(prefixConsumer),
      ),
      Map(
        restrictionSource -> SpaceValue(
          (0 until width).map(index => Syntax.parse(s"shared.a$index.value")).toSet),
        restrictionPrefixes -> SpaceValue(
          (0 until width).map(index => Syntax.parse(s"shared.p$index")).toSet),
        prefixConsumer -> SpaceValue(Set(Syntax.parse("shared"))),
      ),
      SpaceValue(Set.empty),
    )

    val wrapLeft = SpaceMention("demand_cap_wrap_left")
    val wrapRight = SpaceMention("demand_cap_wrap_right")
    val wrapConsumer = SpaceMention("demand_cap_wrap_consumer")
    val wrapPrefix = PathValue(
      (0 until 128).map(index => PathItem(s"prefix$index")).toList)
    val prefixedHit = PathValue(wrapPrefix.items ++ sharedHit.items)
    val (_, wrapCost) = check(
      "fixed wrap around resident union",
      Space.Intersection(
        Space.Wrap(
          Space.Union(Space.Mention(wrapLeft), Space.Mention(wrapRight)),
          Path.Constant(wrapPrefix),
        ),
        Space.Mention(wrapConsumer),
      ),
      Map(
        wrapLeft -> SpaceValue(
          (0 until width).map(index => Syntax.parse(s"shared.left.$index")).toSet),
        wrapRight -> SpaceValue(
          (0 until width - 1).map(index => Syntax.parse(s"shared.right.$index")).toSet + sharedHit),
        wrapConsumer -> SpaceValue(Set(prefixedHit)),
      ),
      SpaceValue(Set(prefixedHit)),
    )
    val formerWrapCap = 5L * (prefixedHit.items.length + 1L)
    assert(wrapCost.nodeVisits > formerWrapCap,
      s"wrap regression no longer exercises the former demand cap: cap=$formerWrapCap actual=$wrapCost")
  }

  test("iteration round bounds match every executor") {
    val sourceMention = SpaceMention("round_source")
    val rest = SpaceMention("round_rest")
    val head = PathRef("round_head")
    val source = SpaceValue(Set(
      PathValue(List(PathItem("a"), PathItem("0"))),
      PathValue(List(PathItem("b"), PathItem("0"))),
      PathValue(List(PathItem("c"), PathItem("0"))),
    ))
    val expression = Space.Iteration(Space.Mention(sourceMention), head, rest,
      Space.Singleton(Path.Concat(Path.Deref(head),
        Path.Constant(PathValue(List(PathItem("tag")))))))
    val annotations = SpatialRoutineAnnotations(spaces = Map(sourceMention -> SpatialType.exact(source)))
    val routine = Routine(RoutinePtr("round_counter"), Vector.empty, Vector(sourceMention), expression)
    val spatial = Supercompiler.optimizedSpatialType(routine, annotations, PartialFunction.empty)
    SpatialBackend.values.foreach { backend =>
      assertEquals(constant(spatial.cost.forBackend(backend).componentsUpper.rounds,
        s"$backend iteration rounds"), 3L)
    }

    val referenceContext = SpaceContextMap(Map(sourceMention -> source))
    val reference = ExecutorCostMeter.measure(eval(expression)(using
      PathContext.emptyMap, referenceContext, PartialFunction.empty))._2
    val trieSource = TrieSpace.fromSpaceValue(source)
    val trieContext = TrieSpaceContextMap(Map(sourceMention -> trieSource))
    val trie = ExecutorCostMeter.measure(evalTrie(expression)(using
      PathContext.emptyMap, trieContext, PartialFunction.empty))._2
    val zipper = {
      given ZipperSpaceContext = ZipperSpaceContext.fromTrie(trieContext)
      ExecutorCostMeter.measure(evalZ(expression).toSpaceValue)._2
    }
    val graph = transpile(Routine(RoutinePtr("round_counter_graph"), Vector.empty,
      Vector(sourceMention), expression))
    def graphRun(): TrieSpace =
      val frame = new Array[List[Int] | TrieSpace | Null](graph.nodes.length)
      frame(0) = trieSource
      val stack = mutable.Stack(frame)
      execT(graph, stack)
      frame.last.asInstanceOf[TrieSpace]
    val graphCost = ExecutorCostMeter.measure(graphRun())._2

    assertEquals(Vector(reference.rounds, trie.rounds, zipper.rounds, graphCost.rounds),
      Vector(3L, 3L, 3L, 3L))
  }

  test("reference instrumentation counts comparisons and allocated product paths") {
    val restriction = SpatialCostCounterCorpus.cases.find(_.name == "restriction-left-512").get
    val restrictionContext = SpaceContextMap(Map(
      SpaceMention("cost_left") -> restriction.left,
      SpaceMention("cost_right") -> restriction.right,
    ))
    val (_, restrictionCost) = ExecutorCostMeter.measure(eval(restriction.expression)(using
      PathContext.emptyMap, restrictionContext, PartialFunction.empty))
    assert(restrictionCost.pathComparisons > 0)

    val composition = SpatialCostCounterCorpus.cases.find(_.name == "composition-left-256").get
    val compositionContext = SpaceContextMap(Map(
      SpaceMention("cost_left") -> composition.left,
      SpaceMention("cost_right") -> composition.right,
    ))
    val (_, compositionCost) = ExecutorCostMeter.measure(eval(composition.expression)(using
      PathContext.emptyMap, compositionContext, PartialFunction.empty))
    assertEquals(compositionCost.allocations, 256L * 4L)
  }
