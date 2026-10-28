package morkl

object TrieAlgebraAsymptoticBenchData:
  private var sink = 0

  private def wide(size: Int, offset: Int = 0): TrieSpace =
    TrieSpace.fromEncodedPaths((0 until size).map(i => List(offset + i, 0)))

  private def everyFourth(size: Int, prefixOnly: Boolean): TrieSpace =
    TrieSpace.fromEncodedPaths(
      (0 until size by 4).map(i => if prefixOnly then List(i) else List(i, 0))
    )

  private def medianNs(repetitions: Int)(operation: => TrieSpace): Double =
    def sample(): Double =
      val started = System.nanoTime()
      var i = 0
      while i < repetitions do
        sink ^= operation.pathCount
        i += 1
      (System.nanoTime() - started).toDouble / repetitions

    var warmup = 0
    while warmup < 4 do
      sample()
      warmup += 1
    Vector.fill(7)(sample()).sorted.apply(3)

  def csv(): String =
    val rows = Vector.newBuilder[String]
    rows += "operation,size,ns_per_operation"
    for size <- Vector(1024, 4096, 16384, 65536) do
      val large = wide(size)
      val subset = everyFourth(size, prefixOnly = false)
      val prefixes = everyFourth(size, prefixOnly = true)
      val disjoint = wide(size, 1 << 24)
      val linearRepetitions = (262144 / size).max(8)
      rows += f"union-subset,$size,${medianNs(linearRepetitions)(large.union(subset))}%.1f"
      rows += f"intersection-subset,$size,${medianNs(linearRepetitions)(large.intersect(subset))}%.1f"
      rows += f"restriction-quarter,$size,${medianNs(linearRepetitions)(large.restrictBy(prefixes))}%.1f"
      rows += f"subtraction-disjoint,$size,${medianNs(20000)(large.diff(disjoint))}%.1f"
    rows.result().mkString("\n")

@main def trieAlgebraAsymptoticBenchmark(): Unit =
  println(TrieAlgebraAsymptoticBenchData.csv())
