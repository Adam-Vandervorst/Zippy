package morkl

import java.util.concurrent.atomic.AtomicInteger

/** Representation-level operations counted by executors under an explicit
  * test/benchmark scope. Production execution pays only one disabled flag
  * branch at each instrumented operation boundary. */
case class ExecutorCostCounts(
  nodeVisits: Long = 0L,
  patriciaVisits: Long = 0L,
  pathComparisons: Long = 0L,
  allocations: Long = 0L,
  rounds: Long = 0L,
):
  def +(that: ExecutorCostCounts): ExecutorCostCounts = ExecutorCostCounts(
    nodeVisits + that.nodeVisits,
    patriciaVisits + that.patriciaVisits,
    pathComparisons + that.pathComparisons,
    allocations + that.allocations,
    rounds + that.rounds,
  )

object ExecutorCostMeter:
  private final class MutableCounts:
    var nodeVisits = 0L
    var patriciaVisits = 0L
    var pathComparisons = 0L
    var allocations = 0L
    var rounds = 0L
    def snapshot: ExecutorCostCounts =
      ExecutorCostCounts(nodeVisits, patriciaVisits, pathComparisons, allocations, rounds)

  private val current = ThreadLocal[MutableCounts]()
  private val activeScopes = AtomicInteger(0)
  @volatile var patriciaInstrumentationEnabled = false

  def measure[A](operation: => A): (A, ExecutorCostCounts) =
    val previous = current.get()
    val counts = MutableCounts()
    current.set(counts)
    activeScopes.incrementAndGet()
    patriciaInstrumentationEnabled = true
    try operation -> counts.snapshot
    finally
      current.set(previous)
      if activeScopes.decrementAndGet() == 0 then patriciaInstrumentationEnabled = false

  inline private def active: MutableCounts | Null =
    if activeScopes.get() != 0 then current.get() else null

  def visitNode(count: Long = 1L): Unit =
    val value = active
    if value != null then value.nodeVisits += count

  /** One logical cursor-membership probe. Zipper operations use this instead
    * of leaving `hasChild` work invisible; it shares the semantic-node bucket
    * so existing static node-visit bounds cover both traversal and probing. */
  def cursorProbe(count: Long = 1L): Unit =
    visitNode(count)

  /** Visits to immutable Patricia-map nodes. Kept separate from semantic trie
    * nodes so disjoint joins, shared branches, and fully interwoven maps retain
    * their distinct measured asymptotics. */
  inline def visitPatricia(count: Long = 1L): Unit =
    if patriciaInstrumentationEnabled then recordPatricia(count)

  def recordPatricia(count: Long): Unit =
    val value = active
    if value != null then value.patriciaVisits += count

  def comparePath(count: Long = 1L): Unit =
    val value = active
    if value != null then value.pathComparisons += count

  def allocate(count: Long = 1L): Unit =
    val value = active
    if value != null then value.allocations += count

  def round(count: Long = 1L): Unit =
    val value = active
    if value != null then value.rounds += count
