package morkl

import munit.FunSuite
import scala.collection.mutable

object SpatialCostCorrelation:
  private val leftMention = SpaceMention("correlation_left")
  private val rightMention = SpaceMention("correlation_right")

  private case class Example(program: Space, spatial: SpatialType, left: SpaceValue, right: SpaceValue)

  private def value(prefix: String, count: Int, length: Int = 2): SpaceValue = SpaceValue(
    (0 until count).map { index =>
      PathValue((Vector(prefix + index) ++ (1 until length).map(i => s"t$i")).map(PathItem(_)).toList)
    }.toSet)

  /** Scaling correlation is measured within one executor operation family;
    * cross-operator discrimination is checked separately by the winner cases. */
  private def examples: Vector[Example] = Vector(32, 64, 128, 256).map { count =>
    val left = value("l", count)
    val right = value("r", count)
    val expression = Space.Composition(Space.Mention(leftMention), Space.Mention(rightMention))
    val routine = Routine(RoutinePtr(s"cost_correlation_$count"), Vector.empty,
      Vector(leftMention, rightMention), expression)
    val annotations = SpatialRoutineAnnotations(spaces = Map(
      leftMention -> SpatialType.exact(left),
      rightMention -> SpatialType.exact(right),
    ))
    Example(Supercompiler.normalize(expression).space,
      Supercompiler.optimizedSpatialType(routine, annotations, PartialFunction.empty), left, right)
  }

  private def graphValue(graph: RecursiveOpGraph, arguments: Vector[TrieSpace]): SpaceValue =
    val frame = new Array[List[Int] | TrieSpace | Null](graph.nodes.length)
    arguments.indices.foreach(index => frame(index) = arguments(index))
    val stack = mutable.Stack(frame)
    execT(graph, stack)
    stack.top.last.asInstanceOf[TrieSpace].toSpaceValue

  private def medianNanos(run: () => SpaceValue, repetitions: Int = 3, warmups: Int = 3): Double =
    Vector.fill(warmups)(run())
    Vector.fill(repetitions) {
      val started = System.nanoTime()
      run()
      (System.nanoTime() - started).toDouble
    }.sorted.apply(repetitions / 2)

  private def rank(values: Vector[Double]): Vector[Double] =
    values.map(value =>
      val below = values.count(_ < value)
      val equal = values.count(_ == value)
      below + (equal - 1) / 2.0)

  private def spearman(left: Vector[Double], right: Vector[Double]): Double =
    val x = rank(left)
    val y = rank(right)
    val xm = x.sum / x.size
    val ym = y.sum / y.size
    val numerator = x.zip(y).map((a, b) => (a - xm) * (b - ym)).sum
    val denominator = math.sqrt(x.map(a => (a - xm) * (a - xm)).sum * y.map(b => (b - ym) * (b - ym)).sum)
    if denominator == 0 then 0 else numerator / denominator

  def correlations: Map[SpatialBackend, Double] =
    val rows = examples.map { example =>
      val referenceContext = SpaceContextMap(Map(leftMention -> example.left, rightMention -> example.right))
      val trieArguments = Vector(TrieSpace.fromSpaceValue(example.left), TrieSpace.fromSpaceValue(example.right))
      val trieContext = TrieSpaceContextMap(Map(leftMention -> trieArguments(0), rightMention -> trieArguments(1)))
      val graph = transpile(Routine(RoutinePtr("cost_correlation"), Vector.empty,
        Vector(leftMention, rightMention), example.program))
      val runs: Map[SpatialBackend, () => SpaceValue] = Map(
        SpatialBackend.Reference -> (() => eval(example.program)(using
          PathContext.emptyMap, referenceContext, PartialFunction.empty)),
        SpatialBackend.Trie -> (() => evalTrie(example.program)(using
          PathContext.emptyMap, trieContext, PartialFunction.empty).toSpaceValue),
        SpatialBackend.Zipper -> (() => {
          given ZipperSpaceContext = ZipperSpaceContext.fromTrie(trieContext)
          evalZ(example.program).toSpaceValue
        }),
        SpatialBackend.Graph -> (() => graphValue(graph, trieArguments)),
      )
      SpatialBackend.values.map { backend =>
        val predicted = example.spatial.cost.forBackend(backend).workUpper.annotatedBound(Z3BoundDirection.Upper)
          .getOrElse(BigInt(Long.MaxValue)).toDouble
        backend -> (predicted -> medianNanos(runs(backend), repetitions = 5))
      }.toMap
    }
    SpatialBackend.values.map { backend =>
      val values = rows.map(_(backend))
      backend -> spearman(values.map(_._1), values.map(_._2))
    }.toMap

@main def spatialCostCorrelationReport(): Unit =
  SpatialCostCorrelation.correlations.toVector.sortBy(_._1.ordinal).foreach { (backend, correlation) =>
    println(f"spatial cost correlation: $backend%-9s Spearman=$correlation%.3f")
  }

class SpatialCostCorrelationTest extends FunSuite:
  test("optimized open-program predictions correlate with every executor") {
    val correlations = SpatialCostCorrelation.correlations
    correlations.foreach { (backend, correlation) =>
      assert(correlation >= 0.25, s"$backend Spearman correlation $correlation was too weak")
    }
  }
