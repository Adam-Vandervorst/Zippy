package morkl

/** Concrete membership in a spatial abstract value.
  *
  * `satisfies` is the signature/envelope check: all populated shape classes
  * obey their bounds, while a lower bound on an unpopulated class is ignored.
  * `gammaMember` is full concretization membership and enforces every lower
  * bound, including classes containing no concrete path. Upper bounds govern
  * an existential cover of the value; overlapping classes may share a path as
  * a lower-bound witness. Identical classes are canonicalized by `SpatialType`
  * before membership.
  */
object SpatialMembership:
  private def within(value: BigInt, estimate: ResultSizeEstimate): Boolean =
    estimate.lower.annotatedBound(Z3BoundDirection.Lower).forall(_ <= value) &&
      estimate.upper.annotatedBound(Z3BoundDirection.Upper).forall(value <= _)

  private def withinLength(length: Int, estimate: PathLengthEstimate): Boolean =
    estimate.lower.annotatedBound(Z3BoundDirection.Lower).forall(_ <= length) &&
      estimate.upper.annotatedBound(Z3BoundDirection.Upper).forall(BigInt(length) <= _)

  private def matches(path: PathValue, stratum: SpatialStratum): Boolean =
    withinLength(path.items.length, stratum.length) && stratum.pattern.forall(_.matches(path))

  /** Can every concrete path be attributed to at least one matching stratum
    * without exceeding any stratum's upper capacity?  Attributions establish
    * coverage, not ownership: the same path may independently witness lower
    * facts in several overlapping strata.
    */
  private def coverable(paths: Vector[PathValue], strata: Vector[SpatialStratum]): Boolean =
    val pathCount = paths.size
    val stratumCount = strata.size
    if pathCount == 0 then true
    else
      val source = 0
      val pathBase = 1
      val stratumBase = pathBase + pathCount
      val sink = stratumBase + stratumCount
      final case class Edge(to: Int, reverse: Int, var capacity: Int)
      val graph = Array.fill(sink + 1)(collection.mutable.ArrayBuffer.empty[Edge])
      def edge(from: Int, to: Int, capacity: Int): Unit =
        val forward = Edge(to, graph(to).size, capacity)
        val reverse = Edge(from, graph(from).size, 0)
        graph(from) += forward
        graph(to) += reverse
      paths.indices.foreach { index =>
        edge(source, pathBase + index, 1)
        strata.indices.foreach { stratum =>
          if matches(paths(index), strata(stratum)) then edge(pathBase + index, stratumBase + stratum, 1)
        }
      }
      strata.indices.foreach { index =>
        val capacity = strata(index).cardinality.upper.annotatedBound(Z3BoundDirection.Upper)
          .fold(pathCount)(_.min(BigInt(pathCount)).toInt)
        edge(stratumBase + index, sink, capacity)
      }
      var flow = 0
      var searching = true
      while searching && flow < pathCount do
        val previousNode = Array.fill(sink + 1)(-1)
        val previousEdge = Array.fill(sink + 1)(-1)
        val queue = collection.mutable.Queue(source)
        previousNode(source) = source
        while queue.nonEmpty && previousNode(sink) < 0 do
          val node = queue.dequeue()
          graph(node).indices.foreach { index =>
            val next = graph(node)(index)
            if next.capacity > 0 && previousNode(next.to) < 0 then
              previousNode(next.to) = node
              previousEdge(next.to) = index
              queue.enqueue(next.to)
          }
        if previousNode(sink) < 0 then searching = false
        else
          var node = sink
          while node != source do
            val from = previousNode(node)
            val index = previousEdge(node)
            val forward = graph(from)(index)
            forward.capacity -= 1
            graph(node)(forward.reverse).capacity += 1
            node = from
          flow += 1
      flow == pathCount

  private def check(value: SpaceValue, spatialType: SpatialType, full: Boolean): Boolean =
    if spatialType.isBottom then false
    else
      val paths = value.paths.toVector
      within(paths.size, spatialType.size) &&
        (paths.isEmpty || paths.forall(path => withinLength(path.items.length, spatialType.pathLength))) &&
        coverable(paths, spatialType.strata) &&
        spatialType.strata.forall { stratum =>
          val count = paths.count(matches(_, stratum))
          val lowerOkay = (!full && count == 0) ||
            stratum.cardinality.lower.annotatedBound(Z3BoundDirection.Lower).forall(_ <= count)
          val nonEmptyInterval = (for
            lower <- stratum.cardinality.lower.annotatedBound(Z3BoundDirection.Lower)
            upper <- stratum.cardinality.upper.annotatedBound(Z3BoundDirection.Upper)
          yield lower <= upper).getOrElse(true)
          lowerOkay && nonEmptyInterval
        }

  def satisfies(value: SpaceValue, spatialType: SpatialType): Boolean = check(value, spatialType, full = false)
  def gammaMember(value: SpaceValue, spatialType: SpatialType): Boolean = check(value, spatialType, full = true)

extension (spatialType: SpatialType)
  def satisfies(value: SpaceValue): Boolean = SpatialMembership.satisfies(value, spatialType)
  def gammaContains(value: SpaceValue): Boolean = SpatialMembership.gammaMember(value, spatialType)
