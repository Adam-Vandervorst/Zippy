package morkl

import morkl.Syntax.{*, given}

object IndependentProductBenchmarkData:
  private val foo = S"s"("foo")
  private val bar = S"s"("bar")
  val input: Space = foo.iter(P"x", S"x_",
    bar.iter(P"y", S"y_",
      Space.Singleton("cux" x P"x") \/ Space.Singleton("cux" x P"y")
    )
  )
  val optimized: Space = Supercompiler.normalize(input).space
  private val routine = Routine(RoutinePtr("independent_product_benchmark"), Vector.empty, Vector(S"s".variable), optimized)
  private val graph = optimize(transpile(routine))

  private def medianMillis(repetitions: Int)(f: => Unit): Double =
    f
    f
    val samples = Vector.fill(repetitions) {
      val start = System.nanoTime()
      f
      (System.nanoTime() - start).toDouble / 1_000_000.0
    }.sorted
    samples(samples.size / 2)

  private def graphValue(ctx: TrieSpaceContextMap): TrieSpace =
    val frame = new Array[List[Int] | TrieSpace | Null](graph.nodes.length)
    frame(0) = ctx.resolve(S"s".variable)
    val stack = collection.mutable.Stack(frame)
    execT(graph, stack)
    frame.last.asInstanceOf[TrieSpace]

  def csv(): String =
    val rows = Vector.newBuilder[String]
    rows += "heads,paths,original_ms,optimized_ms,compiled_execT_ms,original/optimized"
    for size <- Vector(32, 64, 128, 256) do
      val paths = (0 until size).flatMap(i => Vector(
        Syntax.parse(s"foo.f$i.tail"),
        Syntax.parse(s"bar.b$i.tail")
      )).toSet
      val ctx = TrieSpaceContextMap(Map(S"s".variable -> TrieSpace.fromSpaceValue(SpaceValue(paths))))
      val expected = evalTrieValue(input)(using sc = ctx)
      val actual = evalTrieValue(optimized)(using sc = ctx)
      val compiled = graphValue(ctx).toSpaceValue
      require(actual == expected && compiled == expected, s"benchmark result mismatch at $size heads")
      val repetitions = if size <= 64 then 9 else 5
      val originalMs = medianMillis(repetitions) { evalTrieValue(input)(using sc = ctx); () }
      val optimizedMs = medianMillis(repetitions) { evalTrieValue(optimized)(using sc = ctx); () }
      val graphMs = medianMillis(repetitions) { graphValue(ctx); () }
      rows += f"$size,${expected.paths.size},$originalMs%.4f,$optimizedMs%.4f,$graphMs%.4f,${originalMs / optimizedMs}%.2f"
    rows.result().mkString("\n")

@main def independentProductBenchmark(): Unit =
  println(IndependentProductBenchmarkData.csv())
