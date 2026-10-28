package morkl

import scala.collection.immutable.{IntMap, TrieIntMapOps}
import scala.collection.mutable

enum AlgebraicEmptyReason:
  /** Every argument was empty (the only way a union can be empty). */
  case AllArguments
  /** One or more empty arguments forced the result to be empty. */
  case EmptyArguments(arguments: Int)
  /** Non-empty arguments had no common paths. */
  case Disjoint
  /** The right argument covered every path in the left argument. */
  case LeftCovered
  /** Both arguments were non-empty, but no left path had a right prefix. */
  case NoPrefixMatch

sealed trait AlgebraicResult[+A]

object AlgebraicResult:
  /** Bit masks used by Identity. Multiple bits mean the arguments are equal. */
  val Left: Int = 1
  val Right: Int = 2
  val Both: Int = Left | Right

  final case class Empty(reason: AlgebraicEmptyReason) extends AlgebraicResult[Nothing]
  final case class Identity(arguments: Int) extends AlgebraicResult[Nothing]:
    require(arguments != 0, "an algebraic identity must name at least one argument")
  final case class Bespoke[A](value: A) extends AlgebraicResult[A]

  def identifies(result: AlgebraicResult[?], argument: Int): Boolean = result match
    case Identity(arguments) => (arguments & argument) != 0
    case _ => false

  /** Equality information used while composing a parent, including empty children. */
  def equalsArgument(result: AlgebraicResult[?], argument: Int): Boolean = result match
    case Identity(arguments) => (arguments & argument) != 0
    case Empty(AlgebraicEmptyReason.AllArguments) => true
    case Empty(AlgebraicEmptyReason.EmptyArguments(arguments)) => (arguments & argument) != 0
    case _ => false

  def valueOf[A](result: AlgebraicResult[A], left: A, right: A, empty: => A): A = result match
    case Empty(_) => empty
    case Identity(arguments) => if (arguments & Left) != 0 then left else right
    case Bespoke(value) => value

/**
 * Restriction has one useful relation beyond ordinary algebraic identity:
 * `allPrefixesMatched` says every path on the right prefixed at least one path
 * in the result. A bespoke result with this flag is a prefix-order superset of
 * the right argument; without it, the result is the fully bespoke case.
 */
final case class RestrictionResult[+A](result: AlgebraicResult[A], allPrefixesMatched: Boolean):
  def sourceUnchanged: Boolean = AlgebraicResult.identifies(result, AlgebraicResult.Left)
  def equalsPrefixes: Boolean = AlgebraicResult.identifies(result, AlgebraicResult.Right)
  def sourcePathsDropped: Boolean = !sourceUnchanged
  def coversPrefixes: Boolean = allPrefixesMatched

object PathItemOrder:
  given Ordering[PathItem] with
    def compare(a: PathItem, b: PathItem): Int = a.show.compare(b.show)

  given Ordering[PathValue] with
    def compare(a: PathValue, b: PathValue): Int =
      val ai = a.items.iterator
      val bi = b.items.iterator
      val itemOrd = summon[Ordering[PathItem]]
      while ai.hasNext && bi.hasNext do
        val c = itemOrd.compare(ai.next(), bi.next())
        if c != 0 then return c
      a.items.length.compare(b.items.length)

final class PathItemInterner:
  import PathItemOrder.given

  private val ids = mutable.HashMap.empty[String, Int]
  private val items = mutable.ArrayBuffer.empty[PathItem]

  def intern(item: PathItem): Int =
    ids.getOrElseUpdate(item.show, {
      val id = items.length
      items += item
      id
    })

  def size: Int = items.length

  def encode(path: PathValue): List[Int] =
    path.items.map(intern)

  def encodeItems(path: List[PathItem]): List[Int] =
    path.map(intern)

  def decodeItem(id: Int): PathItem =
    items(id)

  def decodePath(path: Iterable[Int]): PathValue =
    PathValue(path.iterator.map(decodeItem).toList)

  def compareItemIds(a: Int, b: Int): Int =
    ExecutorCostMeter.comparePath()
    summon[Ordering[PathItem]].compare(decodeItem(a), decodeItem(b))

  def comparePaths(a: Iterable[Int], b: Iterable[Int]): Int =
    val ai = a.iterator
    val bi = b.iterator
    while ai.hasNext && bi.hasNext do
      val c = compareItemIds(ai.next(), bi.next())
      if c != 0 then return c
    if ai.hasNext then 1 else if bi.hasNext then -1 else 0

object PathItemInterner:
  val global: PathItemInterner = PathItemInterner()

trait IntPathContext:
  def resolve(pr: PathRef): List[Int] = throw RuntimeException(s"$pr path ref not resolved")
  def grown(pv: Map[PathRef, List[Int]]): IntPathContext =
    throw RuntimeException("IntPathContext.grown is unsupported by this context")

case class IntPathContextMap(m: Map[PathRef, List[Int]]) extends IntPathContext:
  override def resolve(pr: PathRef): List[Int] = m(pr)
  override def grown(pv: Map[PathRef, List[Int]]): IntPathContextMap =
    IntPathContextMap(pv.iterator.foldLeft(m) { case (current, (key, value)) =>
      if key.s == "_" then current else current.updated(key, value)
    })

object IntPathContext:
  val emptyMap: IntPathContextMap = IntPathContextMap(Map.empty)

  def fromReference(pc: PathContext, interner: PathItemInterner = PathItemInterner.global): IntPathContext = pc match
    case PathContextMap(m) => IntPathContextMap(m.view.mapValues(interner.encode).toMap)
    case other =>
      def overlay(local: Map[PathRef, List[Int]]): IntPathContext =
        new IntPathContext:
          override def resolve(pr: PathRef): List[Int] =
            local.getOrElse(pr, interner.encode(other.resolve(pr)))
          override def grown(next: Map[PathRef, List[Int]]): IntPathContext =
            overlay(local ++ next)
      overlay(Map.empty)

case class TrieSpace private (terminal: Boolean, children: IntMap[TrieSpace], pathCount: Int, nodeCount: Int, childCount: Int):
  import PathItemOrder.given

  private lazy val childrenInPathOrder: Array[(Int, TrieSpace)] =
    children.iterator.toArray.sortWith((a, b) => TrieSpace.interner.compareItemIds(a._1, b._1) < 0)

  /** Exclusive path-rank end for each ordered child, including the root
    * terminal offset. Shared by all range projections on this immutable node. */
  private lazy val orderedChildEnds: Array[Int] =
    val ends = new Array[Int](childrenInPathOrder.length)
    var rank = if terminal then 1 else 0
    var index = 0
    while index < childrenInPathOrder.length do
      rank += childrenInPathOrder(index)._2.pathCount
      ends(index) = rank
      index += 1
    ends

  def orderedChildren: Array[(Int, TrieSpace)] =
    childrenInPathOrder

  private[morkl] def orderedChildIndex(item: Int): Int =
    var low = 0
    var high = childrenInPathOrder.length - 1
    while low <= high do
      val middle = (low + high) >>> 1
      val comparison = TrieSpace.interner.compareItemIds(childrenInPathOrder(middle)._1, item)
      if comparison < 0 then low = middle + 1
      else if comparison > 0 then high = middle - 1
      else return middle
    -1

  def isEmpty: Boolean = !terminal && children.isEmpty

  def contains(p: PathValue): Boolean = containsItems(TrieSpace.intern(p))

  def containsItems(items: List[Int]): Boolean = items match
    case Nil => terminal
    case h :: t => children.get(h).exists(_.containsItems(t))

  def subtree(prefix: PathValue): Option[TrieSpace] = subtreeItems(TrieSpace.intern(prefix))

  def subtreeItems(items: List[Int]): Option[TrieSpace] =
    ExecutorCostMeter.visitNode()
    items match
      case Nil => Some(this)
      case h :: t =>
        ExecutorCostMeter.comparePath()
        children.get(h).flatMap(_.subtreeItems(t))

  def insert(p: PathValue): TrieSpace = insertItems(TrieSpace.intern(p))

  def insertItems(items: List[Int]): TrieSpace =
    val frames = mutable.ArrayBuffer.empty[(TrieSpace, Int, Option[TrieSpace])]
    var focus = this
    var remaining = items
    var missing = false
    while remaining.nonEmpty && !missing do
      val item = remaining.head
      remaining = remaining.tail
      val old = focus.children.get(item)
      frames += ((focus, item, old))
      old match
        case Some(child) => focus = child
        case None => missing = true

    var replacement =
      if missing then
        var suffix = TrieSpace.nodeKnown(terminal = true, IntMap.empty, 1, 1, 0)
        var suffixItems = remaining.reverse
        while suffixItems.nonEmpty do
          suffix = TrieSpace.nodeKnown(
            terminal = false,
            TrieIntMapOps.singleton(suffixItems.head, suffix),
            suffix.pathCount,
            suffix.nodeCount + 1,
            childCount = 1,
          )
          suffixItems = suffixItems.tail
        suffix
      else if focus.terminal then focus
      else TrieSpace.nodeKnown(
        terminal = true,
        focus.children,
        focus.pathCount + 1,
        focus.nodeCount,
        focus.childCount,
      )

    var index = frames.length - 1
    while index >= 0 do
      val (parent, item, old) = frames(index)
      if !old.exists(_.asInstanceOf[AnyRef] eq replacement.asInstanceOf[AnyRef]) then
        replacement = TrieSpace.nodeKnown(
          parent.terminal,
          TrieIntMapOps.updated(parent.children, item, replacement),
          parent.pathCount + replacement.pathCount - old.fold(0)(_.pathCount),
          parent.nodeCount + replacement.nodeCount - old.fold(0)(_.nodeCount),
          parent.childCount + (if old.isEmpty then 1 else 0),
        )
      else replacement = parent
      index -= 1
    replacement

  def toSpaceValue: SpaceValue = SpaceValue(paths.toSet)

  def encodedPaths: Vector[List[Int]] =
    val out = Vector.newBuilder[List[Int]]
    def rec(node: TrieSpace, prefix: List[Int]): Unit =
      if node.terminal then out += prefix.reverse
      node.children.foreach { (item, child) => rec(child, item :: prefix) }
    rec(this, Nil)
    out.result()

  def paths: Vector[PathValue] =
    encodedPaths.map(TrieSpace.decode)

  private def binaryValue(result: AlgebraicResult[TrieSpace], that: TrieSpace): TrieSpace = result match
    case _ => AlgebraicResult.valueOf(result, this, that, TrieSpace.empty)

  def unionResult(that: TrieSpace): AlgebraicResult[TrieSpace] =
    ExecutorCostMeter.visitNode()
    if isEmpty && that.isEmpty then AlgebraicResult.Empty(AlgebraicEmptyReason.AllArguments)
    else if isEmpty then AlgebraicResult.Identity(AlgebraicResult.Right)
    else if that.isEmpty then AlgebraicResult.Identity(AlgebraicResult.Left)
    else if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then
      AlgebraicResult.Identity(AlgebraicResult.Both)
    else
      val resultTerminal = terminal || that.terminal
      val (childResult, childAggregate) = TrieIntMapOps.withAggregateResult(
        TrieIntMapOps.unionTriesResult(children, that.children)
      )(result => AlgebraicResult.valueOf(result, children, that.children, IntMap.empty))
      val sameLeft = resultTerminal == terminal &&
        AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left)
      val sameRight = resultTerminal == that.terminal &&
        AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
      val identities =
        (if sameLeft then AlgebraicResult.Left else 0) |
          (if sameRight then AlgebraicResult.Right else 0)
      if identities != 0 then AlgebraicResult.Identity(identities)
      else
        val resultChildren = AlgebraicResult.valueOf(childResult, children, that.children, IntMap.empty)
        AlgebraicResult.Bespoke(TrieSpace.nodeFromChildren(resultTerminal, resultChildren, childAggregate))

  def union(that: TrieSpace): TrieSpace =
    binaryValue(unionResult(that), that)

  infix def |(that: TrieSpace): TrieSpace = union(that)

  def intersectionResult(that: TrieSpace): AlgebraicResult[TrieSpace] =
    ExecutorCostMeter.visitNode()
    val emptyArguments =
      (if isEmpty then AlgebraicResult.Left else 0) |
        (if that.isEmpty then AlgebraicResult.Right else 0)
    if emptyArguments != 0 then
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(emptyArguments))
    else if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then
      AlgebraicResult.Identity(AlgebraicResult.Both)
    else
      val resultTerminal = terminal && that.terminal
      val (childResult, childAggregate) = TrieIntMapOps.withAggregateResult(
        TrieIntMapOps.intersectTriesResult(children, that.children)
      )(result => AlgebraicResult.valueOf(result, children, that.children, IntMap.empty))
      val resultChildren = AlgebraicResult.valueOf(childResult, children, that.children, IntMap.empty)
      if !resultTerminal && resultChildren.isEmpty then
        AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
      else
        val sameLeft = resultTerminal == terminal &&
          AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left)
        val sameRight = resultTerminal == that.terminal &&
          AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
        val identities =
          (if sameLeft then AlgebraicResult.Left else 0) |
            (if sameRight then AlgebraicResult.Right else 0)
        if identities != 0 then AlgebraicResult.Identity(identities)
        else AlgebraicResult.Bespoke(TrieSpace.nodeFromChildren(resultTerminal, resultChildren, childAggregate))

  def intersect(that: TrieSpace): TrieSpace =
    binaryValue(intersectionResult(that), that)

  infix def &(that: TrieSpace): TrieSpace = intersect(that)

  def subtractionResult(that: TrieSpace): AlgebraicResult[TrieSpace] =
    ExecutorCostMeter.visitNode()
    if isEmpty then
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Left))
    else if that.isEmpty then AlgebraicResult.Identity(AlgebraicResult.Left)
    else if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then
      AlgebraicResult.Empty(AlgebraicEmptyReason.LeftCovered)
    else
      val resultTerminal = terminal && !that.terminal
      val (childResult, childAggregate) = TrieIntMapOps.withAggregateResult(
        TrieIntMapOps.diffTriesResult(children, that.children)
      )(result => AlgebraicResult.valueOf(result, children, that.children, IntMap.empty))
      val resultChildren = AlgebraicResult.valueOf(childResult, children, that.children, IntMap.empty)
      if !resultTerminal && resultChildren.isEmpty then
        AlgebraicResult.Empty(AlgebraicEmptyReason.LeftCovered)
      else if resultTerminal == terminal &&
          AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left)
      then AlgebraicResult.Identity(AlgebraicResult.Left)
      else AlgebraicResult.Bespoke(TrieSpace.nodeFromChildren(resultTerminal, resultChildren, childAggregate))

  def diff(that: TrieSpace): TrieSpace =
    binaryValue(subtractionResult(that), that)

  infix def -(that: TrieSpace): TrieSpace = diff(that)

  def prefix(item: Int): TrieSpace =
    if isEmpty then TrieSpace.empty
    else TrieSpace.nodeKnown(terminal = false, TrieIntMapOps.singleton(item, this), pathCount, nodeCount + 1, childCount = 1)

  def prepend(prefix: List[Int]): TrieSpace =
    prefix.foldRight(this)((item, acc) => acc.prefix(item))

  def wrap(prefix: PathValue): TrieSpace = prepend(TrieSpace.intern(prefix))
  def wrapItems(prefix: List[Int]): TrieSpace = prepend(prefix)

  def unwrap(prefix: PathValue): TrieSpace = subtree(prefix).getOrElse(TrieSpace.empty)
  def unwrapItems(prefix: List[Int]): TrieSpace = subtreeItems(prefix).getOrElse(TrieSpace.empty)

  def prefixRelation(prefixes: TrieSpace): (Boolean, Boolean) =
    val childRelation = TrieIntMapOps.prefixRelation(children, prefixes.children)
    ((!prefixes.terminal || !isEmpty) && childRelation._1) ->
      (terminal == prefixes.terminal && childRelation._2)

  def restrictionResult(prefixes: TrieSpace): RestrictionResult[TrieSpace] =
    ExecutorCostMeter.visitNode()
    ExecutorCostMeter.comparePath()
    if isEmpty && prefixes.isEmpty then
      RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.AllArguments), allPrefixesMatched = true)
    else if isEmpty then
      RestrictionResult(
        AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Left)),
        allPrefixesMatched = false
      )
    else if prefixes.isEmpty then
      RestrictionResult(
        AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Right)),
        allPrefixesMatched = true
      )
    else if this.asInstanceOf[AnyRef] eq prefixes.asInstanceOf[AnyRef] then
      RestrictionResult(AlgebraicResult.Identity(AlgebraicResult.Both), allPrefixesMatched = true)
    else if prefixes.terminal then
      val (allMatched, equal) = prefixRelation(prefixes)
      val identities = AlgebraicResult.Left | (if equal then AlgebraicResult.Right else 0)
      RestrictionResult(AlgebraicResult.Identity(identities), allMatched)
    else
      val (childOutcome, childAggregate) = TrieIntMapOps.withAggregateResult(
        TrieIntMapOps.restrictTriesResult(children, prefixes.children)
      )(outcome => AlgebraicResult.valueOf(outcome.result, children, prefixes.children, IntMap.empty))
      val resultChildren = AlgebraicResult.valueOf(
        childOutcome.result,
        children,
        prefixes.children,
        IntMap.empty
      )
      if resultChildren.isEmpty then
        RestrictionResult(
          AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch),
          childOutcome.allPrefixesMatched
        )
      else
        val sameLeft = !terminal &&
          AlgebraicResult.equalsArgument(childOutcome.result, AlgebraicResult.Left)
        val sameRight = AlgebraicResult.equalsArgument(childOutcome.result, AlgebraicResult.Right)
        val identities =
          (if sameLeft then AlgebraicResult.Left else 0) |
            (if sameRight then AlgebraicResult.Right else 0)
        val result =
          if identities != 0 then AlgebraicResult.Identity(identities)
          else AlgebraicResult.Bespoke(TrieSpace.nodeFromChildren(terminal = false, resultChildren, childAggregate))
        RestrictionResult(result, childOutcome.allPrefixesMatched)

  def restrictBy(prefixes: TrieSpace): TrieSpace =
    if isEmpty || prefixes.isEmpty then TrieSpace.empty
    else if (this.asInstanceOf[AnyRef] eq prefixes.asInstanceOf[AnyRef]) || prefixes.terminal then this
    else binaryValue(restrictionResult(prefixes).result, prefixes)

  def raffinate(prefixes: TrieSpace): TrieSpace = diff(restrictBy(prefixes))

  def concat(that: TrieSpace): TrieSpace =
    ExecutorCostMeter.visitNode()
    if isEmpty || that.isEmpty then TrieSpace.empty
    else if terminal && children.isEmpty then that
    else
      val (mapped, aggregate) = TrieIntMapOps.withAggregateResult(
        TrieIntMapOps.mapValues(children)(_.concat(that))
      )(identity)
      val descendants = TrieSpace.nodeFromChildren(terminal = false, mapped, aggregate)
      if terminal then that.union(descendants) else descendants

  def tailsUnion: TrieSpace = TrieSpace.joinAll(children.valuesIterator)

  def tailsIntersection: TrieSpace =
    if children.isEmpty then TrieSpace.empty
    else TrieSpace.meetAll(children.values)

  def nonEmptyPaths: TrieSpace =
    if terminal then TrieSpace.nodeKnown(terminal = false, children, pathCount - 1, nodeCount, childCount) else this

  def head: TrieSpace =
    if children.isEmpty then TrieSpace.empty
    else TrieSpace.node(terminal = false, children.map((item, _) => item -> TrieSpace.epsilon))

  def prefixClosure: TrieSpace =
    def markBelow(node: TrieSpace): TrieSpace =
      TrieSpace.node(terminal = true, node.children.map((item, child) => item -> markBelow(child)))
    if children.isEmpty then TrieSpace.empty
    else TrieSpace.node(terminal = false, children.map((item, child) => item -> markBelow(child)))

  def suffixClosure: TrieSpace =
    if children.isEmpty then TrieSpace.empty
    else if pathCount == 1 then TrieSpace.singlePathSuffixes(this)
    else
      val wholeNonEmpty =
        if terminal then TrieSpace.nodeKnown(terminal = false, children, pathCount - 1, nodeCount, childCount)
        else this
      val childSuffixes = TrieSpace.joinAll(children.valuesIterator.map(_.suffixClosure))
      wholeNonEmpty.union(childSuffixes)

  def tailsClosure: TrieSpace =
    if isEmpty then TrieSpace.empty
    else
      val suffixes = suffixClosure
      TrieSpace.nodeKnown(terminal = true, suffixes.children,
        suffixes.pathCount + (if suffixes.terminal then 0 else 1), suffixes.nodeCount, suffixes.childCount)

  def range(start: Int, end: Int): TrieSpace =
    if start == 0 && end == 0 then this
    else if start >= 0 then
      val lo = if start == 0 then 0 else start - 1
      if end > 0 then
        val hi = if start == 0 then end else end - 1
        if hi <= lo then TrieSpace.empty else slice(lo, hi)
      else
        val prefix = if end < 0 then dropLast(-end) else this
        prefix.slice(lo, Int.MaxValue)
    else if end == 0 then
      takeLast(-start)
    else if end < 0 then
      takeLast(-start).dropLast(-end)
    else
      val (lo, hi) = RangeBounds.normalize(pathCount, start, end)
      if hi <= lo then TrieSpace.empty else slice(lo, hi)

  def first(n: Int): TrieSpace =
    if n <= 0 then TrieSpace.empty else slice(0, n)

  def last(n: Int): TrieSpace =
    if n <= 0 then TrieSpace.empty else takeLast(n)

  private def slice(start: Int, end: Int): TrieSpace =
    if end <= start || end <= 0 || start >= pathCount then return TrieSpace.empty
    if start <= 0 && end >= pathCount then return this
    val boundedStart = start.max(0)
    val boundedEnd = end.min(pathCount)
    val keepTerminal = terminal && boundedStart == 0
    val kept = Vector.newBuilder[(Int, TrieSpace)]

    def firstEndAfter(rank: Int): Int =
      var low = 0
      var high = orderedChildEnds.length
      while low < high do
        val middle = (low + high) >>> 1
        if orderedChildEnds(middle) <= rank then low = middle + 1 else high = middle
      low

    var index = firstEndAfter(boundedStart)
    while index < childrenInPathOrder.length &&
        (if index == 0 then (if terminal then 1 else 0) else orderedChildEnds(index - 1)) < boundedEnd
    do
      val (item, child) = childrenInPathOrder(index)
      val childStart = if index == 0 then (if terminal then 1 else 0) else orderedChildEnds(index - 1)
      val childEnd = orderedChildEnds(index)
      val filtered =
        if boundedStart <= childStart && childEnd <= boundedEnd then child
        else child.slice((boundedStart - childStart).max(0), (boundedEnd - childStart).min(child.pathCount))
      if !filtered.isEmpty then kept += item -> filtered
      index += 1
    TrieSpace.node(keepTerminal, IntMap.from(kept.result()))

  private def takeLast(count: Int): TrieSpace =
    if count <= 0 then TrieSpace.empty else slice((pathCount - count).max(0), pathCount)

  private def dropLast(count: Int): TrieSpace =
    if count <= 0 then this else slice(0, (pathCount - count).max(0))

object TrieSpace:
  import PathItemOrder.given

  val interner: PathItemInterner = PathItemInterner.global
  val empty: TrieSpace = TrieSpace(terminal = false, IntMap.empty, pathCount = 0, nodeCount = 1, childCount = 0)
  val epsilon: TrieSpace = TrieSpace(terminal = true, IntMap.empty, pathCount = 1, nodeCount = 1, childCount = 0)

  def binaryValue(
    result: AlgebraicResult[TrieSpace],
    left: TrieSpace,
    right: TrieSpace
  ): TrieSpace =
    AlgebraicResult.valueOf(result, left, right, empty)

  def intern(p: PathValue): List[Int] = interner.encode(p)
  def internItems(items: List[PathItem]): List[Int] = interner.encodeItems(items)
  def decode(items: Iterable[Int]): PathValue = interner.decodePath(items)
  def comparePaths(a: Iterable[Int], b: Iterable[Int]): Int = interner.comparePaths(a, b)
  def item(id: Int): PathItem = interner.decodeItem(id)

  private val singletonItemPaths = mutable.HashMap.empty[Int, List[Int]]
  def singletonItemPath(item: Int): List[Int] =
    singletonItemPaths.getOrElseUpdate(item, item :: Nil)

  private[morkl] def replaceChild(parent: TrieSpace, item: Int, replacement: TrieSpace): TrieSpace =
    val old = parent.children.get(item)
    if old.exists(_.asInstanceOf[AnyRef] eq replacement.asInstanceOf[AnyRef]) then parent
    else
      val children = if replacement.isEmpty then TrieIntMapOps.removed(parent.children, item)
        else TrieIntMapOps.updated(parent.children, item, replacement)
      val oldPaths = old.fold(0)(_.pathCount)
      val oldNodes = old.fold(0)(_.nodeCount)
      val oldPresent = if old.isDefined then 1 else 0
      val newPresent = if replacement.isEmpty then 0 else 1
      nodeKnown(
        parent.terminal,
        children,
        parent.pathCount - oldPaths + (if replacement.isEmpty then 0 else replacement.pathCount),
        parent.nodeCount - oldNodes + (if replacement.isEmpty then 0 else replacement.nodeCount),
        parent.childCount - oldPresent + newPresent,
      )

  def prefixes(path: List[Int]): Vector[List[Int]] =
    path.indices.map(i => path.take(i + 1)).toVector

  private[morkl] def node(terminal: Boolean, children: IntMap[TrieSpace]): TrieSpace =
    val aggregate = TrieIntMapOps.aggregate(children)
    if aggregate.entryCount == aggregate.childCount then
      nodeKnown(terminal, children,
        (if terminal then 1 else 0) + aggregate.pathCount,
        1 + aggregate.nodeCount,
        aggregate.childCount)
    else
      val kept = children.filterNot(_._2.isEmpty)
      nodeFromChildren(terminal, kept)

  /** Fallback parent reconstruction for a bulk child map. Algebra normally
    * calls the aggregate-taking overload with its operation-local result. */
  private[morkl] def nodeFromChildren(terminal: Boolean, children: IntMap[TrieSpace]): TrieSpace =
    val aggregate = TrieIntMapOps.aggregate(children)
    nodeFromChildren(terminal, children, aggregate)

  private[morkl] def nodeFromChildren(
    terminal: Boolean,
    children: IntMap[TrieSpace],
    aggregate: TrieIntMapOps.ChildMapAggregate,
  ): TrieSpace =
    nodeKnown(terminal, children,
      (if terminal then 1 else 0) + aggregate.pathCount,
      1 + aggregate.nodeCount,
      aggregate.childCount)

  /** Constant-time constructor for a one-branch persistent update. The caller
    * has already derived the aggregate counts from the replaced child. Bulk
    * constructors continue to use [[node]], where scanning a wholly new child
    * map is unavoidable and linear in the output width. */
  private[morkl] def nodeKnown(
    terminal: Boolean,
    children: IntMap[TrieSpace],
    pathCount: Int,
    nodeCount: Int,
    childCount: Int,
  ): TrieSpace =
    if !terminal && childCount == 0 then empty
    else
      TrieIntMapOps.registerAggregate(children, TrieIntMapOps.ChildMapAggregate(
        pathCount - (if terminal then 1 else 0),
        nodeCount - 1,
        childCount,
        childCount,
      ))
      ExecutorCostMeter.allocate()
      TrieSpace(terminal, children, pathCount, nodeCount, childCount)

  def singleton(p: PathValue): TrieSpace = empty.insert(p)

  /** Build the finite suffix language of a sole input path as its minimal
    * acyclic suffix automaton. TrieSpace is a DAG, so the automaton can share
    * equivalent suffix states directly. Construction is O(path depth) for
    * repeated, periodic, and non-periodic labels alike; accepting states are
    * precisely the suffix-link chain of the complete path. */
  private def singlePathSuffixes(source: TrieSpace): TrieSpace =
    val items = mutable.ArrayBuffer.empty[Int]
    var cursor = source
    while !cursor.terminal do
      val (item, child) = cursor.children.head
      items += item
      cursor = child

    final class State(
      var length: Int,
      var link: Int,
      val transitions: mutable.HashMap[Int, Int],
    )

    val states = mutable.ArrayBuffer(new State(0, -1, mutable.HashMap.empty))
    var last = 0
    items.foreach { item =>
      val current = states.length
      states += new State(states(last).length + 1, 0, mutable.HashMap.empty)
      var p = last
      while p >= 0 && !states(p).transitions.contains(item) do
        states(p).transitions(item) = current
        p = states(p).link
      if p < 0 then states(current).link = 0
      else
        val q = states(p).transitions(item)
        if states(p).length + 1 == states(q).length then states(current).link = q
        else
          val clone = states.length
          states += new State(
            states(p).length + 1,
            states(q).link,
            mutable.HashMap.from(states(q).transitions),
          )
          while p >= 0 && states(p).transitions.get(item).contains(q) do
            states(p).transitions(item) = clone
            p = states(p).link
          states(q).link = clone
          states(current).link = clone
      last = current
    }

    val accepting = Array.fill(states.length)(false)
    var suffix = last
    while suffix > 0 do
      accepting(suffix) = true
      suffix = states(suffix).link

    val built = new Array[TrieSpace](states.length)
    states.indices.sortBy(index => -states(index).length).foreach { index =>
      var childMap = IntMap.empty[TrieSpace]
      states(index).transitions.foreach { (item, destination) =>
        childMap = TrieIntMapOps.updated(childMap, item, built(destination))
      }
      built(index) = node(accepting(index), childMap)
    }
    built(0)

  def fromSpaceValue(sv: SpaceValue): TrieSpace = fromPaths(sv.paths)

  def fromPaths(paths: Iterable[PathValue]): TrieSpace =
    fromEncodedPaths(paths.iterator.map(intern).toVector)

  def fromEncodedPaths(paths: Iterable[List[Int]]): TrieSpace =
    final class BuilderNode:
      var terminal = false
      val children = mutable.HashMap.empty[Int, BuilderNode]

    val root = new BuilderNode
    paths.foreach { path =>
      var node = root
      path.foreach { item =>
        node = node.children.getOrElseUpdate(item, new BuilderNode)
      }
      node.terminal = true
    }

    def freeze(node: BuilderNode): TrieSpace =
      if node.children.isEmpty then
        if node.terminal then epsilon else empty
      else
        val children = IntMap.from(node.children.iterator.map { (item, child) => item -> freeze(child) })
        TrieSpace.node(node.terminal, children)

    freeze(root)

  def joinAll(xs: IterableOnce[TrieSpace]): TrieSpace =
    val seen = java.util.IdentityHashMap[AnyRef, java.lang.Boolean]()
    val unique = Vector.newBuilder[TrieSpace]
    xs.iterator.filterNot(_.isEmpty).foreach { trie =>
      val identity = trie.asInstanceOf[AnyRef]
      if !seen.containsKey(identity) then
        seen.put(identity, java.lang.Boolean.TRUE)
        unique += trie
    }
    var tries = unique.result()
    if tries.isEmpty then empty
    else if tries.length == 1 then tries.head
    else
      while tries.length > 1 do
        val next = Vector.newBuilder[TrieSpace]
        var index = 0
        while index < tries.length do
          if index + 1 < tries.length then next += tries(index).union(tries(index + 1))
          else next += tries(index)
          index += 2
        tries = next.result()
      tries.head

  def meetAll(xs: IterableOnce[TrieSpace]): TrieSpace =
    val raw = xs.iterator.toVector
    if raw.isEmpty then empty
    else
      val unique = Vector.newBuilder[TrieSpace]
      val seen = java.util.IdentityHashMap[AnyRef, java.lang.Boolean]()
      var hasEmpty = false
      raw.foreach { trie =>
        if trie.isEmpty then hasEmpty = true
        else
          val ref = trie.asInstanceOf[AnyRef]
          if !seen.containsKey(ref) then
            seen.put(ref, java.lang.Boolean.TRUE)
            unique += trie
      }

      if hasEmpty then empty
      else
        val tries = unique.result()
        if tries.isEmpty then empty
        else if tries.length == 1 then tries.head
        else if tries.length == 2 then tries(0).intersect(tries(1))
        else
          var first = 0
          var i = 1
          while i < tries.length do
            val best = tries(first)
            val candidate = tries(i)
            if (candidate.childCount < best.childCount) ||
                (candidate.childCount == best.childCount && candidate.nodeCount < best.nodeCount) ||
                (candidate.childCount == best.childCount && candidate.nodeCount == best.nodeCount && candidate.pathCount < best.pathCount)
            then first = i
            i += 1

          var acc = tries(first)
          i = 0
          while i < tries.length && !acc.isEmpty do
            if i != first then acc = acc.intersect(tries(i))
            i += 1
          acc

  case class Cursor(
    root: TrieSpace,
    prefix: Vector[Int] = Vector.empty,
    private val cachedFocus: TrieSpace | Null = null,
    private val ancestors: List[TrieSpace] = Nil,
  ):
    def focus: TrieSpace =
      if cachedFocus == null then root.subtreeItems(prefix.toList).getOrElse(empty)
      else cachedFocus
    def down(item: PathItem): Option[Cursor] =
      down(interner.intern(item))
    def down(item: Int): Option[Cursor] =
      val here = focus
      here.children.get(item).map(child =>
        copy(prefix = prefix :+ item, cachedFocus = child, ancestors = here :: ancestors))
    def up: Option[Cursor] =
      Option.when(prefix.nonEmpty) {
        ancestors match
          case parent :: rest => copy(prefix = prefix.dropRight(1), cachedFocus = parent, ancestors = rest)
          case Nil => Cursor(root, prefix.dropRight(1))
      }
    def descend(path: PathValue): Option[Cursor] =
      intern(path).foldLeft(Option(this))((cursor, item) => cursor.flatMap(_.down(item)))
    def subtree: TrieSpace = focus

  sealed trait ZipperContext:
    def path: Vector[Int]
    def plug(focus: TrieSpace): TrieSpace
    def isRoot: Boolean

  object ZipperContext:
    case object Root extends ZipperContext:
      override val path: Vector[Int] = Vector.empty
      override def plug(focus: TrieSpace): TrieSpace = focus
      override val isRoot: Boolean = true

    case class Frame(parent: ZipperContext,
                     item: Int,
                     originalParent: TrieSpace,
                     ordered: Array[(Int, TrieSpace)] | Null,
                     index: Int) extends ZipperContext:
      override def path: Vector[Int] = parent.path :+ item
      override def plug(focus: TrieSpace): TrieSpace =
        parent.plug(TrieSpace.replaceChild(originalParent, item, focus))
      override val isRoot: Boolean = false

  case class Zipper(focus: TrieSpace, context: ZipperContext = ZipperContext.Root):
    def path: Vector[Int] = context.path
    def pathValue: PathValue = TrieSpace.decode(path)
    def whole: TrieSpace = context.plug(focus)
    def atRoot: Boolean = context.isRoot

    def down(item: PathItem): Option[Zipper] =
      down(interner.intern(item))

    def down(item: Int): Option[Zipper] =
      focus.children.get(item).map { child =>
        Zipper(
          child,
          ZipperContext.Frame(context, item, focus, null, index = -1)
        )
      }

    def descend(path: PathValue): Option[Zipper] =
      descendItems(intern(path))

    def descendItems(items: Iterable[Int]): Option[Zipper] =
      items.foldLeft(Option(this))((cursor, item) => cursor.flatMap(_.down(item)))

    def up: Option[Zipper] = context match
      case ZipperContext.Root => None
      case ZipperContext.Frame(parent, item, originalParent, _, _) =>
        Some(Zipper(TrieSpace.replaceChild(originalParent, item, focus), parent))

    def toRoot: Zipper =
      var cursor = this
      var next = cursor.up
      while next.isDefined do
        cursor = next.get
        next = cursor.up
      cursor

    def graft(replacement: TrieSpace): Zipper =
      copy(focus = replacement)

    def removeFocus: Zipper =
      graft(TrieSpace.empty)

    def insertAtFocus(path: PathValue): Zipper =
      insertItemsAtFocus(intern(path))

    def insertItemsAtFocus(path: List[Int]): Zipper =
      copy(focus = focus.insertItems(path))

    def firstChild: Option[Zipper] =
      focus.orderedChildren.headOption.map((item, child) =>
        Zipper(child, ZipperContext.Frame(context, item, focus, focus.orderedChildren, index = 0))
      )

    def nextSibling: Option[Zipper] =
      sibling(delta = 1)

    def previousSibling: Option[Zipper] =
      sibling(delta = -1)

    private def sibling(delta: Int): Option[Zipper] = context match
      case ZipperContext.Root => None
      case ZipperContext.Frame(parent, item, originalParent, ordered, index) =>
        val updatedParent = TrieSpace.replaceChild(originalParent, item, focus)
        val siblings = if ordered == null then originalParent.orderedChildren else ordered
        val anchor = if index >= 0 then index else originalParent.orderedChildIndex(item)
        var nextIndex = anchor + delta
        while nextIndex >= 0 && nextIndex < siblings.length &&
            !updatedParent.children.contains(siblings(nextIndex)._1)
        do nextIndex += delta
        Option.when(nextIndex >= 0 && nextIndex < siblings.length) {
          val nextItem = siblings(nextIndex)._1
          val nextFocus = updatedParent.children(nextItem)
          Zipper(nextFocus, ZipperContext.Frame(parent, nextItem, updatedParent, siblings, nextIndex))
        }

trait TrieSpaceContext:
  def resolve(sm: SpaceMention): TrieSpace = throw RuntimeException(s"$sm trie space mention not resolved")
  def grown(pv: Map[SpaceMention, TrieSpace]): TrieSpaceContext =
    throw RuntimeException("TrieSpaceContext.grown is unsupported by this context")

case class TrieSpaceContextMap(m: Map[SpaceMention, TrieSpace]) extends TrieSpaceContext:
  override def resolve(sm: SpaceMention): TrieSpace = m(sm)
  override def grown(pv: Map[SpaceMention, TrieSpace]): TrieSpaceContextMap =
    TrieSpaceContextMap(pv.iterator.foldLeft(m) { case (current, (key, value)) =>
      if key.s == "_" then current else current.updated(key, value)
    })

object TrieSpaceContext:
  val emptyMap: TrieSpaceContextMap = TrieSpaceContextMap(Map.empty)
  def fromReference(sc: SpaceContextMap): TrieSpaceContextMap =
    TrieSpaceContextMap(sc.m.view.mapValues(TrieSpace.fromSpaceValue).toMap)

def evalTrie(s: Space)(using
  pc: PathContext = PathContext.emptyMap,
  sc: TrieSpaceContext = TrieSpaceContext.emptyMap,
  rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
): TrieSpace =
  val rootPc = IntPathContext.fromReference(pc, TrieSpace.interner)

  val spaceDependencyCache = java.util.IdentityHashMap[AnyRef, mutable.HashMap[(String, String), Boolean]]()
  val pathDependencyCache = java.util.IdentityHashMap[AnyRef, mutable.HashMap[(String, String), Boolean]]()

  def recp(x: Path)(using ipc: IntPathContext, tsc: TrieSpaceContext): List[Int] = x match
    case Path.Deref(pr) => ipc.resolve(pr)
    case Path.Constant(pi) => TrieSpace.intern(pi)
    case Path.Concat(_, _) =>
      val output = List.newBuilder[Int]
      val pending = mutable.ArrayDeque[Path](x)
      while pending.nonEmpty do
        pending.removeHead() match
          case Path.Concat(left, right) =>
            pending.prepend(right)
            pending.prepend(left)
          case factor => output ++= recp(factor)
      output.result()
    case Path.GroundedPP(p, f) => TrieSpace.intern(f(TrieSpace.decode(recp(p))))
    case Path.GroundedSP(s, f) => TrieSpace.intern(f(recs(s).toSpaceValue))

  def spaceDependsOnBound(s: Space, symbol: PathRef, rest: SpaceMention): Boolean =
    val key = symbol.s -> rest.s
    val byBinder = spaceDependencyCache.computeIfAbsent(s.asInstanceOf[AnyRef], _ => mutable.HashMap.empty)
    byBinder.getOrElseUpdate(key, {
      val (spaces, paths) = collect(s)(
        spre = { case Space.Mention(sm) if sm.s == rest.s => () },
        ppre = { case Path.Deref(pr) if pr.s == symbol.s => () },
      )
      spaces.nonEmpty || paths.nonEmpty
    })

  def pathDependsOnBound(p: Path, symbol: PathRef, rest: SpaceMention): Boolean =
    val key = symbol.s -> rest.s
    val byBinder = pathDependencyCache.computeIfAbsent(p.asInstanceOf[AnyRef], _ => mutable.HashMap.empty)
    byBinder.getOrElseUpdate(key, {
      val (spaces, paths) = collect(Space.Singleton(p))(
        spre = { case Space.Mention(sm) if sm.s == rest.s => () },
        ppre = { case Path.Deref(pr) if pr.s == symbol.s => () },
      )
      spaces.nonEmpty || paths.nonEmpty
    })

  def recs(x: Space)(using ipc: IntPathContext, tsc: TrieSpaceContext): TrieSpace = x match
    case Space.Empty => TrieSpace.empty
    case Space.Call(rp, refs, mentions) =>
      val refvs = refs.map(recp)
      val mentionvs = mentions.map(recs)
      val Routine(_, refns, mentionns, body) = rc(rp)
      val pctx = IntPathContextMap(Map.from(refns zip refvs))
      val sctx = TrieSpaceContextMap(Map.from(mentionns zip mentionvs))
      body match
        case Space.Union(l, Space.Call(`rp`, `refs`, `mentions`)) =>
          val refsStable = (refs zip refvs).forall((p, pv) => pv == evalTriePath(p)(using pctx, sctx, rc))
          val spacesStable = (mentions zip mentionvs).forall((s, sv) => sv == recs(s)(using pctx, sctx))
          if refsStable && spacesStable then recs(l)(using pctx, sctx)
          else recs(body)(using pctx, sctx)
        case _ => recs(body)(using pctx, sctx)
    case Space.Mention(p) => tsc.resolve(p)
    case Space.Singleton(p) => TrieSpace.empty.insertItems(recp(p))
    case Space.Literal(sv) => TrieSpace.fromSpaceValue(sv)
    case Space.Union(x, y) => recs(x).union(recs(y))
    case Space.Intersection(x, y) => recs(x).intersect(recs(y))
    case Space.Subtraction(x, y) => recs(x).diff(recs(y))
    case Space.Restriction(x, prefixes) => recs(x).restrictBy(recs(prefixes))
    case Space.Raffination(x, prefixes) => recs(x).raffinate(recs(prefixes))
    case Space.Composition(x, y) => recs(x).concat(recs(y))
    case Space.Wrap(src, p) => recs(src).wrapItems(recp(p))
    case Space.Unwrap(src, p) => recs(src).unwrapItems(recp(p))
    case Space.TailsUnion(src) => recs(src).tailsUnion
    case Space.TailsIntersection(src) => recs(src).tailsIntersection
    case Space.PrefixClosure(src) => recs(src).prefixClosure
    case Space.SuffixClosure(src) => recs(src).suffixClosure
    case Space.TailsClosure(src) => recs(src).tailsClosure
    case Space.Iteration(src, symbol, rest, templates) =>
      val srcTrie = recs(src)
      def singletonRangeSelected(start: Int, end: Int): Boolean =
        RangeBounds.normalize(size = 1, start, end) == (0 -> 1)
      def evalTemplate(template: Space): TrieSpace = template match
        case Space.Empty => TrieSpace.empty
        case Space.Mention(sm) if sm == rest => srcTrie.tailsUnion
        case Space.Singleton(Path.Deref(pr)) if pr == symbol => srcTrie.head
        case Space.Range(Space.Mention(sm), start, end) if sm == rest =>
          if start == 0 && end == 0 then srcTrie.tailsUnion
          else TrieSpace.joinAll(srcTrie.children.iterator.map((_, tail) => tail.range(start, end)))
        case Space.Range(Space.Singleton(Path.Deref(pr)), start, end) if pr == symbol =>
          if singletonRangeSelected(start, end) then srcTrie.head else TrieSpace.empty
        case Space.Range(Space.Wrap(Space.Mention(sm), Path.Deref(pr)), start, end) if sm == rest && pr == symbol =>
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h)))
        case Space.Range(Space.Wrap(Space.Mention(sm), Path.Concat(prefix, Path.Deref(pr))), start, end)
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h))).wrapItems(staticPrefix)
        case Space.Range(Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Mention(sm)), start, end) if sm == rest && pr == symbol =>
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h)))
        case Space.Range(Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Mention(sm)), start, end)
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h))).wrapItems(staticPrefix)
        case Space.Wrap(Space.Mention(sm), Path.Deref(pr)) if sm == rest && pr == symbol =>
          srcTrie.nonEmptyPaths
        case Space.Wrap(Space.Mention(sm), Path.Concat(prefix, Path.Deref(pr))) if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          srcTrie.nonEmptyPaths.wrapItems(recp(prefix))
        case Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Mention(sm)) if sm == rest && pr == symbol =>
          srcTrie.nonEmptyPaths
        case Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Mention(sm)) if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          srcTrie.nonEmptyPaths.wrapItems(recp(prefix))
        case Space.Wrap(Space.Range(Space.Mention(sm), start, end), Path.Deref(pr)) if sm == rest && pr == symbol =>
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h)))
        case Space.Wrap(Space.Range(Space.Mention(sm), start, end), Path.Concat(prefix, Path.Deref(pr)))
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h))).wrapItems(staticPrefix)
        case Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Range(Space.Mention(sm), start, end)) if sm == rest && pr == symbol =>
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h)))
        case Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Range(Space.Mention(sm), start, end))
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h))).wrapItems(staticPrefix)
        case _ if !spaceDependsOnBound(template, symbol, rest) =>
          if srcTrie.childCount == 0 then TrieSpace.empty else recs(template)
        case Space.Union(left, right) =>
          evalTemplate(left).union(evalTemplate(right))
        case Space.Wrap(inner, prefix) if !pathDependsOnBound(prefix, symbol, rest) =>
          evalTemplate(inner).wrapItems(recp(prefix))
        case Space.Unwrap(inner, prefix) if !pathDependsOnBound(prefix, symbol, rest) =>
          evalTemplate(inner).unwrapItems(recp(prefix))
        case Space.Singleton(Path.Concat(prefix, suffix)) if !pathDependsOnBound(prefix, symbol, rest) =>
          evalTemplate(Space.Singleton(suffix)).wrapItems(recp(prefix))
        case Space.Composition(left, right) if !spaceDependsOnBound(right, symbol, rest) =>
          evalTemplate(left).concat(recs(right))
        case Space.Composition(left, right) if !spaceDependsOnBound(left, symbol, rest) =>
          recs(left).concat(evalTemplate(right))
        case Space.Intersection(left, right) if !spaceDependsOnBound(right, symbol, rest) =>
          evalTemplate(left).intersect(recs(right))
        case Space.Intersection(left, right) if !spaceDependsOnBound(left, symbol, rest) =>
          recs(left).intersect(evalTemplate(right))
        case Space.Subtraction(left, right) if !spaceDependsOnBound(right, symbol, rest) =>
          evalTemplate(left).diff(recs(right))
        case Space.Restriction(inner, prefixes) if !spaceDependsOnBound(prefixes, symbol, rest) =>
          evalTemplate(inner).restrictBy(recs(prefixes))
        case Space.Raffination(inner, prefixes) if !spaceDependsOnBound(prefixes, symbol, rest) =>
          val selected = evalTemplate(inner)
          selected.diff(selected.restrictBy(recs(prefixes)))
        case Space.TailsUnion(inner) =>
          evalTemplate(inner).tailsUnion
        case Space.PrefixClosure(inner) =>
          evalTemplate(inner).prefixClosure
        case Space.SuffixClosure(inner) =>
          evalTemplate(inner).suffixClosure
        case Space.TailsClosure(inner) =>
          evalTemplate(inner).tailsClosure
        case _ =>
          TrieSpace.joinAll(srcTrie.children.iterator.map { (h, tail) =>
            ExecutorCostMeter.round()
            recs(template)(using ipc.grown(Map(symbol -> TrieSpace.singletonItemPath(h))), tsc.grown(Map(rest -> tail)))
          })
      evalTemplate(templates)
    case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
      var accValue = recp(initial)
      val out = Vector.newBuilder[TrieSpace]
      for (h, tail) <- recs(src).orderedChildren do
        ExecutorCostMeter.round()
        val pctx = ipc.grown(Map(acc -> accValue, symbol -> List(h)))
        val sctx = tsc.grown(Map(rest -> tail))
        out += recs(templates)(using pctx, sctx)
        accValue = evalTriePath(update)(using pctx, sctx, rc)
      TrieSpace.joinAll(out.result())
    case Space.Fixpoint(initial, variable, step) =>
      var current = recs(initial)
      var changed = true
      while changed do
        ExecutorCostMeter.round()
        val stepped = recs(step)(using ipc, tsc.grown(Map(variable -> current)))
        val next = current.union(stepped)
        changed = next != current
        current = next
      current
    case Space.GroundedPS(p, f) => TrieSpace.fromSpaceValue(f(TrieSpace.decode(recp(p))))
    case Space.GroundedSS(src, f) => TrieSpace.fromSpaceValue(f(recs(src).toSpaceValue))
    case Space.Range(x, start, end) => recs(x).range(start, end)

  def evalTriePath(p: Path)(using IntPathContext, TrieSpaceContext, PartialFunction[RoutinePtr, Routine]): List[Int] =
    recp(p)

  recs(s)(using rootPc, sc)

def evalTrieValue(s: Space)(using
  pc: PathContext = PathContext.emptyMap,
  sc: TrieSpaceContext = TrieSpaceContext.emptyMap,
  rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
): SpaceValue =
  evalTrie(s).toSpaceValue

def execTrie(rog: RecursiveOpGraph,
             stack: collection.mutable.Stack[Array[PathValue | TrieSpace | Null]],
             index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): Unit =
  val l = rog.level
  var c = 0
  val s = stack.top
  inline def pos = (l, c)
  extension (p: (Int, Int)) inline def sget: TrieSpace =
    stack(stack.length - 1 - p._1)(p._2).asInstanceOf[TrieSpace]
  extension (p: (Int, Int)) inline def pget: PathValue =
    stack(stack.length - 1 - p._1)(p._2).asInstanceOf[PathValue]
  def tagged(packed: TrieSpace, tag: PathValue): TrieSpace =
    packed.unwrap(tag)
  def taggedSingletonPath(packed: TrieSpace, tag: PathValue): PathValue =
    tagged(packed, tag).paths.headOption.getOrElse(throw IllegalStateException(s"Fold subgraph did not produce ${tag.show} update"))

  while c < rog.nodes.length do
    rog.nodes(c) match
      case Left(Node(op, constant, kind, inputs)) => kind match
        case "path" => s(c) = op match
          case "ExtractPathRef" => pos.pget
          case "Constant" => rog.pathValue(constant)
          case "Concat" => PathValue(inputs(0).pget.items ++ inputs(1).pget.items)
        case "space" =>
          if op != "ExtractSpaceMention" && op != "Alias" && op != "Literal" && op != "Empty" then
            ExecutorCostMeter.visitNode()
          s(c) = op match
          case "Empty" => TrieSpace.empty
          case "Call" =>
            val code = index(constant)
            val cstack = collection.mutable.Stack(new Array[PathValue | TrieSpace | Null](code.nodes.length))
            for (arg, i) <- inputs.zipWithIndex do cstack.top(i) = stack(stack.length - 1 - arg._1)(arg._2)
            execTrie(code, cstack, index)
            cstack.top.last.asInstanceOf[TrieSpace]
          case "ExtractSpaceMention" => pos.sget
          case "Alias" => inputs(0).sget
          case "Singleton" => TrieSpace.singleton(inputs(0).pget)
          case "Literal" => rog.literalTrieValue(constant)
          case "Union" => inputs(0).sget.union(inputs(1).sget)
          case "Intersection" => inputs(0).sget.intersect(inputs(1).sget)
          case "Restriction" => inputs(0).sget.restrictBy(inputs(1).sget)
          case "Raffination" => inputs(0).sget.raffinate(inputs(1).sget)
          case "Subtraction" => inputs(0).sget.diff(inputs(1).sget)
          case "Composition" => inputs(0).sget.concat(inputs(1).sget)
          case "Wrap" => inputs(0).sget.wrap(inputs(1).pget)
          case "Unwrap" => inputs(0).sget.unwrap(inputs(1).pget)
          case "TailsUnion" => inputs(0).sget.tailsUnion
          case "TailsIntersection" => inputs(0).sget.tailsIntersection
          case "PrefixClosure" => inputs(0).sget.prefixClosure
          case "SuffixClosure" => inputs(0).sget.suffixClosure
          case "TailsClosure" => inputs(0).sget.tailsClosure
          case "Iteration" => throw IllegalStateException("Iteration should be represented as a recursive subgraph, not a flat operation node")
          case "Range" =>
            val (start, end) = rog.rangeBounds(constant)
            inputs(0).sget.range(start, end)
      case Right(sg: RecursiveOpGraph) =>
        val Node(op, _, _, inputs) = sg.root
        ExecutorCostMeter.visitNode()
        op match
          case "Routine" => throw IllegalStateException("Nested Routine subgraphs are not executable without an explicit Call node")
          case "Iteration" =>
            val outputs = Vector.newBuilder[TrieSpace]
            val frame = new Array[PathValue | TrieSpace | Null](sg.nodes.length)
            for (h, tail) <- inputs(0).sget.children do
              ExecutorCostMeter.round()
              frame(0) = TrieSpace.decode(List(h))
              frame(1) = tail
              stack.push(frame)
              execTrie(sg, stack, index)
              stack.pop()
              outputs += frame.last.asInstanceOf[TrieSpace]
            s(c) = TrieSpace.joinAll(outputs.result())
          case "Fold" =>
            var accValue = inputs(1).pget
            val outputs = Vector.newBuilder[TrieSpace]
            val frame = new Array[PathValue | TrieSpace | Null](sg.nodes.length)
            for (h, tail) <- inputs(0).sget.orderedChildren do
              ExecutorCostMeter.round()
              frame(0) = accValue
              frame(1) = TrieSpace.decode(List(h))
              frame(2) = tail
              stack.push(frame)
              execTrie(sg, stack, index)
              stack.pop()
              val packed = frame.last.asInstanceOf[TrieSpace]
              outputs += tagged(packed, GraphFoldTags.Body)
              accValue = taggedSingletonPath(packed, GraphFoldTags.Update)
            s(c) = TrieSpace.joinAll(outputs.result())
          case "Fixpoint" =>
            var current = inputs(0).sget
            var changed = true
            val frame = new Array[PathValue | TrieSpace | Null](sg.nodes.length)
            while changed do
              ExecutorCostMeter.round()
              frame(0) = current
              stack.push(frame)
              execTrie(sg, stack, index)
              stack.pop()
              val next = current.union(frame.last.asInstanceOf[TrieSpace])
              changed = next != current
              current = next
            s(c) = current
    c += 1

def execT(rog: RecursiveOpGraph,
          stack: collection.mutable.Stack[Array[List[Int] | TrieSpace | Null]],
          index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): Unit =
  val l = rog.level
  var c = 0
  val s = stack.top
  inline def pos = (l, c)
  extension (p: (Int, Int)) inline def sget: TrieSpace =
    stack(stack.length - 1 - p._1)(p._2).asInstanceOf[TrieSpace]
  extension (p: (Int, Int)) inline def pget: List[Int] =
    stack(stack.length - 1 - p._1)(p._2).asInstanceOf[List[Int]]
  def tagged(packed: TrieSpace, tag: PathValue): TrieSpace =
    packed.unwrapItems(TrieSpace.intern(tag))
  def taggedSingletonPath(packed: TrieSpace, tag: PathValue): List[Int] =
    tagged(packed, tag).encodedPaths.headOption.getOrElse(throw IllegalStateException(s"Fold subgraph did not produce ${tag.show} update"))

  while c < rog.nodes.length do
    rog.nodes(c) match
      case Left(Node(op, constant, kind, inputs)) => kind match
        case "path" => s(c) = op match
          case "ExtractPathRef" => pos.pget
          case "Constant" => rog.intPathValue(constant)
          case "Concat" => inputs(0).pget ++ inputs(1).pget
        case "space" =>
          if op != "ExtractSpaceMention" && op != "Alias" && op != "Literal" && op != "Empty" then
            ExecutorCostMeter.visitNode()
          s(c) = op match
          case "Empty" => TrieSpace.empty
          case "Call" =>
            val code = index(constant)
            val cstack = collection.mutable.Stack(new Array[List[Int] | TrieSpace | Null](code.nodes.length))
            for (arg, i) <- inputs.zipWithIndex do
              cstack.top(i) = stack(stack.length - 1 - arg._1)(arg._2)
            execT(code, cstack, index)
            cstack.top.last.asInstanceOf[TrieSpace]
          case "ExtractSpaceMention" => pos.sget
          case "Alias" => inputs(0).sget
          case "Singleton" => TrieSpace.empty.insertItems(inputs(0).pget)
          case "Literal" => rog.literalTrieValue(constant)
          case "Union" => inputs(0).sget.union(inputs(1).sget)
          case "Intersection" => inputs(0).sget.intersect(inputs(1).sget)
          case "Restriction" => inputs(0).sget.restrictBy(inputs(1).sget)
          case "Raffination" => inputs(0).sget.raffinate(inputs(1).sget)
          case "Subtraction" => inputs(0).sget.diff(inputs(1).sget)
          case "Composition" => inputs(0).sget.concat(inputs(1).sget)
          case "Wrap" => inputs(0).sget.wrapItems(inputs(1).pget)
          case "Unwrap" => inputs(0).sget.unwrapItems(inputs(1).pget)
          case "TailsUnion" => inputs(0).sget.tailsUnion
          case "TailsIntersection" => inputs(0).sget.tailsIntersection
          case "PrefixClosure" => inputs(0).sget.prefixClosure
          case "SuffixClosure" => inputs(0).sget.suffixClosure
          case "TailsClosure" => inputs(0).sget.tailsClosure
          case "Iteration" => throw IllegalStateException("Iteration should be represented as a recursive subgraph, not a flat operation node")
          case "Range" =>
            val (start, end) = rog.rangeBounds(constant)
            inputs(0).sget.range(start, end)
      case Right(sg: RecursiveOpGraph) =>
        val Node(op, _, _, inputs) = sg.root
        ExecutorCostMeter.visitNode()
        op match
          case "Routine" => throw IllegalStateException("Nested Routine subgraphs are not executable without an explicit Call node")
          case "Iteration" =>
            val outputs = Vector.newBuilder[TrieSpace]
            val frame = new Array[List[Int] | TrieSpace | Null](sg.nodes.length)
            for (h, tail) <- inputs(0).sget.children do
              ExecutorCostMeter.round()
              frame(0) = TrieSpace.singletonItemPath(h)
              frame(1) = tail
              stack.push(frame)
              execT(sg, stack, index)
              stack.pop()
              outputs += frame.last.asInstanceOf[TrieSpace]
            s(c) = TrieSpace.joinAll(outputs.result())
          case "Fold" =>
            var accValue = inputs(1).pget
            val outputs = Vector.newBuilder[TrieSpace]
            val frame = new Array[List[Int] | TrieSpace | Null](sg.nodes.length)
            for (h, tail) <- inputs(0).sget.orderedChildren do
              ExecutorCostMeter.round()
              frame(0) = accValue
              frame(1) = TrieSpace.singletonItemPath(h)
              frame(2) = tail
              stack.push(frame)
              execT(sg, stack, index)
              stack.pop()
              val packed = frame.last.asInstanceOf[TrieSpace]
              outputs += tagged(packed, GraphFoldTags.Body)
              accValue = taggedSingletonPath(packed, GraphFoldTags.Update)
            s(c) = TrieSpace.joinAll(outputs.result())
          case "Fixpoint" =>
            var current = inputs(0).sget
            var changed = true
            val frame = new Array[List[Int] | TrieSpace | Null](sg.nodes.length)
            while changed do
              ExecutorCostMeter.round()
              frame(0) = current
              stack.push(frame)
              execT(sg, stack, index)
              stack.pop()
              val next = current.union(frame.last.asInstanceOf[TrieSpace])
              changed = next != current
              current = next
            s(c) = current
    c += 1
