package scala.collection.immutable

import morkl.{AlgebraicEmptyReason, AlgebraicResult, ExecutorCostMeter, RestrictionResult, TrieSpace}
import java.lang.ref.WeakReference
import java.util.IdentityHashMap

/** Patricia-trie child-map algebra with provenance propagation. */
object TrieIntMapOps:
  import IntMapUtils.{hasMatch, join, shorter, zero}

  /** Aggregate metadata for one Patricia child map. `entryCount` includes
    * empty-valued tips so the defensive bulk constructor can detect and prune
    * them without first scanning the map. */
  final case class ChildMapAggregate(
    pathCount: Int,
    nodeCount: Int,
    childCount: Int,
    entryCount: Int,
  ):
    def +(that: ChildMapAggregate): ChildMapAggregate = ChildMapAggregate(
      pathCount + that.pathCount,
      nodeCount + that.nodeCount,
      childCount + that.childCount,
      entryCount + that.entryCount,
    )

  object ChildMapAggregate:
    val empty: ChildMapAggregate = ChildMapAggregate(0, 0, 0, 0)

  /** Weak identity cache over immutable Patricia nodes. Algebra creates only
    * the touched Patricia spine; unchanged branches retain identity, so their
    * aggregate is recovered in O(1). Computing the aggregate of a fresh bulk
    * map remains linear in that newly constructed map. */
  private object AggregateCache:
    private final class Entry(value: IntMap[TrieSpace]) extends WeakReference[IntMap[TrieSpace]](value):
      val hash: Int = System.identityHashCode(value)

    private var entries = new Array[Entry | Null](1024)
    private var aggregates = new Array[ChildMapAggregate | Null](1024)
    private var occupied = 0

    private def index(hash: Int, length: Int): Int = hash & (length - 1)

    private def resize(): Unit =
      val oldEntries = entries
      val oldAggregates = aggregates
      var live = 0
      var liveIndex = 0
      while liveIndex < oldEntries.length do
        val entry = oldEntries(liveIndex)
        if entry != null && entry.get() != null then live += 1
        liveIndex += 1
      // A half-full table can consist almost entirely of cleared weak
      // references. Compact it at the current capacity instead of doubling a
      // tombstone population; grow only when the live working set requires it.
      val newLength = if live * 2 >= oldEntries.length then oldEntries.length * 2 else oldEntries.length
      entries = new Array[Entry | Null](newLength)
      aggregates = new Array[ChildMapAggregate | Null](newLength)
      occupied = 0
      var oldIndex = 0
      while oldIndex < oldEntries.length do
        val entry = oldEntries(oldIndex)
        if entry != null && entry.get() != null then
          var target = index(entry.hash, entries.length)
          while entries(target) != null do target = (target + 1) & (entries.length - 1)
          entries(target) = entry
          aggregates(target) = oldAggregates(oldIndex)
          occupied += 1
        oldIndex += 1

    /** Allocation-free identity lookup and one weak-reference allocation per
      * new Patricia node. Open addressing avoids wrapper keys and hash-table
      * nodes on this hot metadata path. */
    def get(map: IntMap[TrieSpace]): ChildMapAggregate | Null = synchronized {
      val hash = System.identityHashCode(map)
      var slot = index(hash, entries.length)
      var entry = entries(slot)
      while entry != null do
        val value = entry.get()
        if entry.hash == hash && value != null &&
            (value.asInstanceOf[AnyRef] eq map.asInstanceOf[AnyRef])
        then return aggregates(slot)
        slot = (slot + 1) & (entries.length - 1)
        entry = entries(slot)
      null
    }

    def put(map: IntMap[TrieSpace], aggregate: ChildMapAggregate): ChildMapAggregate =
      // A fixed-width scan is O(1). Keeping tiny maps out of the synchronized
      // weak cache removes its memory and lock cost from narrow workloads while
      // retaining summaries exactly where width-sensitive asymptotics matter.
      if aggregate.entryCount <= 8 then aggregate
      else synchronized(putWide(map, aggregate))

    /** Promote one operation's persistent summaries under one cache lock.
      * Interwoven algebra can construct O(W) live Patricia nodes; locking once
      * preserves that exact work without adding O(W) monitor transitions. */
    def putAll(values: IdentityHashMap[AnyRef, ChildMapAggregate]): Unit = synchronized {
      val iterator = values.entrySet().iterator()
      while iterator.hasNext do
        val entry = iterator.next()
        if entry.getValue.entryCount > 8 then
          putWide(entry.getKey.asInstanceOf[IntMap[TrieSpace]], entry.getValue)
    }

    private def putWide(map: IntMap[TrieSpace], aggregate: ChildMapAggregate): ChildMapAggregate = {
      if occupied * 2 >= entries.length then resize()
      val hash = System.identityHashCode(map)
      var slot = index(hash, entries.length)
      var firstDead = -1
      var entry = entries(slot)
      while entry != null do
        val value = entry.get()
        if value == null && firstDead < 0 then firstDead = slot
        else if entry.hash == hash &&
            (value.asInstanceOf[AnyRef] eq map.asInstanceOf[AnyRef])
        then return aggregates(slot).asInstanceOf[ChildMapAggregate]
        slot = (slot + 1) & (entries.length - 1)
        entry = entries(slot)
      val target = if firstDead >= 0 then firstDead else slot
      if entries(target) == null then occupied += 1
      entries(target) = new Entry(map)
      aggregates(target) = aggregate
      aggregate
    }

  def aggregate(map: IntMap[TrieSpace]): ChildMapAggregate =
    map match
      case IntMap.Nil => return ChildMapAggregate.empty
      case IntMap.Tip(_, child) => return childAggregate(child)
      case _ => ()
    val local = LocalAggregates.get()
    val localValue = if local == null then null else local.get(map.asInstanceOf[AnyRef])
    val cached = if localValue != null then localValue else AggregateCache.get(map)
    if cached != null then cached
    else
      ExecutorCostMeter.visitPatricia()
      val computed = map match
        case IntMap.Nil => ChildMapAggregate.empty
        case IntMap.Tip(_, child) =>
          if child.isEmpty then ChildMapAggregate(0, 0, 0, 1)
          else ChildMapAggregate(child.pathCount, child.nodeCount, 1, 1)
        case IntMap.Bin(_, _, left, right) => aggregate(left) + aggregate(right)
      if local == null then AggregateCache.put(map, computed)
      else
        registerConstructed(map, computed)
        computed

  def registerAggregate(map: IntMap[TrieSpace], aggregate: ChildMapAggregate): Unit =
    AggregateCache.put(map, aggregate)

  private object LocalAggregates:
    val pending = new IdentityHashMap[AnyRef, ChildMapAggregate](0)
    private val current = ThreadLocal[IdentityHashMap[AnyRef, ChildMapAggregate]]()
    def get(): IdentityHashMap[AnyRef, ChildMapAggregate] | Null = current.get()
    def set(value: IdentityHashMap[AnyRef, ChildMapAggregate]): Unit = current.set(value)
    def clear(): Unit = current.remove()

  /** Run one algebraic child-map operation with allocation-cheap aggregate
    * propagation. Nested TrieSpace operations share the same scope. Only the
    * final parent map is promoted to the weak cross-operation cache by
    * `nodeKnown`; ephemeral intermediate Patricia nodes never enter it. */
  def withAggregateResult[A](operation: => A)(resultMap: A => IntMap[TrieSpace]): (A, ChildMapAggregate) =
    val inherited = LocalAggregates.get()
    val owner = inherited == null
    if owner then LocalAggregates.set(LocalAggregates.pending)
    try
      val result = operation
      result -> aggregate(resultMap(result))
    finally if owner then
      val completed = LocalAggregates.get()
      if completed != null && !(completed eq LocalAggregates.pending) then
        AggregateCache.putAll(completed)
      LocalAggregates.clear()

  private def registerConstructed(map: IntMap[TrieSpace], aggregate: ChildMapAggregate): Unit =
    var local = LocalAggregates.get()
    if local eq LocalAggregates.pending then
      local = new IdentityHashMap[AnyRef, ChildMapAggregate]()
      LocalAggregates.set(local)
    if local == null then registerAggregate(map, aggregate)
    else local.put(map.asInstanceOf[AnyRef], aggregate)

  private def childAggregate(child: TrieSpace): ChildMapAggregate =
    if child.isEmpty then ChildMapAggregate(0, 0, 0, 1)
    else ChildMapAggregate(child.pathCount, child.nodeCount, 1, 1)

  private def aggregateShallow(map: IntMap[TrieSpace]): ChildMapAggregate = map match
    case IntMap.Nil => ChildMapAggregate.empty
    case IntMap.Tip(_, child) => childAggregate(child)
    case _ => aggregate(map)

  /** Patricia constructors which preserve aggregate metadata on every newly
    * allocated map node. Persistent updates therefore cost exactly the touched
    * Patricia spine; parent TrieSpace construction never has to rediscover a
    * result-wide summary. */
  private def tipKnown(key: Int, child: TrieSpace): IntMap[TrieSpace] =
    val result = IntMap.Tip(key, child)
    registerConstructed(result, childAggregate(child))
    result

  private def binKnown(
    prefix: Int,
    mask: Int,
    left: IntMap[TrieSpace],
    right: IntMap[TrieSpace],
  ): IntMap[TrieSpace] =
    val result = IntMap.Bin(prefix, mask, left, right)
    registerConstructed(result, aggregateShallow(left) + aggregateShallow(right))
    result

  private def joinKnown(
    prefix1: Int,
    left: IntMap[TrieSpace],
    prefix2: Int,
    right: IntMap[TrieSpace],
  ): IntMap[TrieSpace] =
    val result = join(prefix1, left, prefix2, right)
    registerConstructed(result, aggregateShallow(left) + aggregateShallow(right))
    result

  private def binPruneKnown(
    prefix: Int,
    mask: Int,
    left: IntMap[TrieSpace],
    right: IntMap[TrieSpace],
  ): IntMap[TrieSpace] =
    if left eq IntMap.Nil then right
    else if right eq IntMap.Nil then left
    else binKnown(prefix, mask, left, right)

  /** Aggregate-preserving Patricia update. This mirrors IntMap.updated but
    * registers every new spine node, so later algebra can reuse untouched
    * branch summaries in constant time. */
  def updated(
    map: IntMap[TrieSpace],
    key: Int,
    child: TrieSpace,
  ): IntMap[TrieSpace] =
    ExecutorCostMeter.visitPatricia()
    map match
    case IntMap.Nil => tipKnown(key, child)
    case IntMap.Tip(existing, _) if existing == key => tipKnown(key, child)
    case tip @ IntMap.Tip(existing, _) => joinKnown(key, tipKnown(key, child), existing, tip)
    case bin @ IntMap.Bin(prefix, mask, left, right) =>
      if hasMatch(key, prefix, mask) then
        if zero(key, mask) then binKnown(prefix, mask, updated(left, key, child), right)
        else binKnown(prefix, mask, left, updated(right, key, child))
      else joinKnown(key, tipKnown(key, child), prefix, bin)

  def removed(map: IntMap[TrieSpace], key: Int): IntMap[TrieSpace] =
    ExecutorCostMeter.visitPatricia()
    map match
    case IntMap.Nil => map
    case IntMap.Tip(existing, _) => if existing == key then IntMap.Nil else map
    case bin @ IntMap.Bin(prefix, mask, left, right) =>
      if !hasMatch(key, prefix, mask) then bin
      else if zero(key, mask) then binPruneKnown(prefix, mask, removed(left, key), right)
      else binPruneKnown(prefix, mask, left, removed(right, key))

  def singleton(key: Int, child: TrieSpace): IntMap[TrieSpace] = tipKnown(key, child)

  /** Shape-preserving value transform. Keys cannot collide, so rebuilding a
    * union tree is unnecessary; unchanged Patricia topology is retained and
    * every output aggregate is registered bottom-up. */
  def mapValues(
    map: IntMap[TrieSpace],
  )(transform: TrieSpace => TrieSpace): IntMap[TrieSpace] =
    ExecutorCostMeter.visitPatricia()
    map match
      case IntMap.Nil => IntMap.Nil
      case IntMap.Tip(key, value) =>
        val replacement = transform(value)
        if replacement.isEmpty then IntMap.Nil else tipKnown(key, replacement)
      case IntMap.Bin(prefix, mask, left, right) =>
        binPruneKnown(prefix, mask, mapValues(left)(transform), mapValues(right)(transform))

  private def lookup(map: IntMap[TrieSpace], key: Int): Option[TrieSpace] =
    ExecutorCostMeter.visitPatricia()
    map match
      case IntMap.Nil => None
      case IntMap.Tip(existing, value) => Option.when(existing == key)(value)
      case IntMap.Bin(prefix, mask, left, right) =>
        if !hasMatch(key, prefix, mask) then None
        else lookup(if zero(key, mask) then left else right, key)

  private def valueOf(
    result: AlgebraicResult[IntMap[TrieSpace]],
    left: IntMap[TrieSpace],
    right: IntMap[TrieSpace]
  ): IntMap[TrieSpace] = result match
    case AlgebraicResult.Empty(_) => IntMap.Nil
    case AlgebraicResult.Identity(arguments) =>
      if (arguments & AlgebraicResult.Left) != 0 then left else right
    case AlgebraicResult.Bespoke(value) => value

  private def identities(left: Boolean, right: Boolean): Int =
    (if left then AlgebraicResult.Left else 0) |
      (if right then AlgebraicResult.Right else 0)

  private def nonEmptyResult(
    value: => IntMap[TrieSpace],
    sameLeft: Boolean,
    sameRight: Boolean
  ): AlgebraicResult[IntMap[TrieSpace]] =
    val mask = identities(sameLeft, sameRight)
    if mask != 0 then AlgebraicResult.Identity(mask)
    else AlgebraicResult.Bespoke(value)

  def unionTriesResult(
    a: IntMap[TrieSpace],
    b: IntMap[TrieSpace]
  ): AlgebraicResult[IntMap[TrieSpace]] =
    ExecutorCostMeter.visitPatricia()
    (a, b) match
    case (IntMap.Nil, IntMap.Nil) =>
      AlgebraicResult.Empty(AlgebraicEmptyReason.AllArguments)
    case (IntMap.Nil, _) => AlgebraicResult.Identity(AlgebraicResult.Right)
    case (_, IntMap.Nil) => AlgebraicResult.Identity(AlgebraicResult.Left)
    case _ if a eq b => AlgebraicResult.Identity(AlgebraicResult.Both)
    case (IntMap.Tip(leftKey, left), IntMap.Tip(rightKey, right)) if leftKey != rightKey =>
      AlgebraicResult.Bespoke(joinKnown(leftKey, a, rightKey, b))
    case (IntMap.Tip(key, left), IntMap.Tip(_, right)) =>
      val childResult = left.unionResult(right)
      nonEmptyResult(
        tipKnown(key, TrieSpace.binaryValue(childResult, left, right)),
        AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
        AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right),
      )
    case (IntMap.Tip(k, v), _) =>
      lookup(b, k) match
        case None => AlgebraicResult.Bespoke(updated(b, k, v))
        case Some(w) =>
          val childResult = v.unionResult(w)
          val child = TrieSpace.binaryValue(childResult, v, w)
          b match
            case IntMap.Tip(_, _) =>
              nonEmptyResult(
                tipKnown(k, child),
                AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
                AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
              )
            case _ =>
              if AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right) then
                AlgebraicResult.Identity(AlgebraicResult.Right)
              else AlgebraicResult.Bespoke(updated(b, k, child))
    case (_, IntMap.Tip(k, w)) =>
      lookup(a, k) match
        case None => AlgebraicResult.Bespoke(updated(a, k, w))
        case Some(v) =>
          val childResult = v.unionResult(w)
          if AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left) then
            AlgebraicResult.Identity(AlgebraicResult.Left)
          else AlgebraicResult.Bespoke(updated(a, k, TrieSpace.binaryValue(childResult, v, w)))
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then AlgebraicResult.Bespoke(joinKnown(p1, a, p2, b))
        else
          val recurseLeft = zero(p2, m1)
          val childResult = unionTriesResult(if recurseLeft then l1 else r1, b)
          if AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left) then
            AlgebraicResult.Identity(AlgebraicResult.Left)
          else
            val child = valueOf(childResult, if recurseLeft then l1 else r1, b)
            AlgebraicResult.Bespoke(
              if recurseLeft then binKnown(p1, m1, child, r1)
              else binKnown(p1, m1, l1, child)
            )
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then AlgebraicResult.Bespoke(joinKnown(p1, a, p2, b))
        else
          val recurseLeft = zero(p1, m2)
          val rightBranch = if recurseLeft then l2 else r2
          val childResult = unionTriesResult(a, rightBranch)
          if AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right) then
            AlgebraicResult.Identity(AlgebraicResult.Right)
          else
            val child = valueOf(childResult, a, rightBranch)
            AlgebraicResult.Bespoke(
              if recurseLeft then binKnown(p2, m2, child, r2)
              else binKnown(p2, m2, l2, child)
            )
      else if p1 == p2 then
        val leftResult = unionTriesResult(l1, l2)
        val rightResult = unionTriesResult(r1, r2)
        nonEmptyResult(
          binKnown(p1, m1, valueOf(leftResult, l1, l2), valueOf(rightResult, r1, r2)),
          AlgebraicResult.equalsArgument(leftResult, AlgebraicResult.Left) &&
            AlgebraicResult.equalsArgument(rightResult, AlgebraicResult.Left),
          AlgebraicResult.equalsArgument(leftResult, AlgebraicResult.Right) &&
            AlgebraicResult.equalsArgument(rightResult, AlgebraicResult.Right)
        )
      else AlgebraicResult.Bespoke(joinKnown(p1, a, p2, b))

  def unionTries(a: IntMap[TrieSpace], b: IntMap[TrieSpace]): IntMap[TrieSpace] =
    valueOf(unionTriesResult(a, b), a, b)

  def intersectTriesResult(
    a: IntMap[TrieSpace],
    b: IntMap[TrieSpace]
  ): AlgebraicResult[IntMap[TrieSpace]] =
    ExecutorCostMeter.visitPatricia()
    (a, b) match
    case (IntMap.Nil, IntMap.Nil) =>
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Both))
    case (IntMap.Nil, _) =>
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Left))
    case (_, IntMap.Nil) =>
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Right))
    case _ if a eq b => AlgebraicResult.Identity(AlgebraicResult.Both)
    case (IntMap.Tip(leftKey, _), IntMap.Tip(rightKey, _)) if leftKey != rightKey =>
      AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
    case (IntMap.Tip(key, left), IntMap.Tip(_, right)) =>
      left.intersectionResult(right) match
        case AlgebraicResult.Empty(_) => AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
        case childResult =>
          nonEmptyResult(
            tipKnown(key, TrieSpace.binaryValue(childResult, left, right)),
            AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
            AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right),
          )
    case (IntMap.Tip(k, v), _) =>
      lookup(b, k) match
        case None => AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
        case Some(w) =>
          val childResult = v.intersectionResult(w)
          childResult match
            case AlgebraicResult.Empty(_) => AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
            case _ =>
              val child = TrieSpace.binaryValue(childResult, v, w)
              b match
                case IntMap.Tip(_, _) =>
                  nonEmptyResult(
                    tipKnown(k, child),
                    AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
                    AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
                  )
                case _ =>
                  nonEmptyResult(
                    tipKnown(k, child),
                    AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
                    sameRight = false
                  )
    case (_, IntMap.Tip(k, w)) =>
      lookup(a, k) match
        case None => AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
        case Some(v) =>
          val childResult = v.intersectionResult(w)
          childResult match
            case AlgebraicResult.Empty(_) => AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
            case _ =>
              nonEmptyResult(
                tipKnown(k, TrieSpace.binaryValue(childResult, v, w)),
                sameLeft = false,
                AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
              )
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
        else
          val leftBranch = if zero(p2, m1) then l1 else r1
          val childResult = intersectTriesResult(leftBranch, b)
          childResult match
            case AlgebraicResult.Empty(_) => childResult
            case _ =>
              nonEmptyResult(
                valueOf(childResult, leftBranch, b),
                sameLeft = false,
                AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
              )
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
        else
          val rightBranch = if zero(p1, m2) then l2 else r2
          val childResult = intersectTriesResult(a, rightBranch)
          childResult match
            case AlgebraicResult.Empty(_) => childResult
            case _ =>
              nonEmptyResult(
                valueOf(childResult, a, rightBranch),
                AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
                sameRight = false
              )
      else if p1 == p2 then
        val leftResult = intersectTriesResult(l1, l2)
        val rightResult = intersectTriesResult(r1, r2)
        val left = valueOf(leftResult, l1, l2)
        val right = valueOf(rightResult, r1, r2)
        if (left eq IntMap.Nil) && (right eq IntMap.Nil) then
          AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)
        else
          nonEmptyResult(
            binPruneKnown(p1, m1, left, right),
            AlgebraicResult.equalsArgument(leftResult, AlgebraicResult.Left) &&
              AlgebraicResult.equalsArgument(rightResult, AlgebraicResult.Left),
            AlgebraicResult.equalsArgument(leftResult, AlgebraicResult.Right) &&
              AlgebraicResult.equalsArgument(rightResult, AlgebraicResult.Right)
          )
      else AlgebraicResult.Empty(AlgebraicEmptyReason.Disjoint)

  def intersectTries(a: IntMap[TrieSpace], b: IntMap[TrieSpace]): IntMap[TrieSpace] =
    valueOf(intersectTriesResult(a, b), a, b)

  def diffTriesResult(
    a: IntMap[TrieSpace],
    b: IntMap[TrieSpace]
  ): AlgebraicResult[IntMap[TrieSpace]] =
    ExecutorCostMeter.visitPatricia()
    (a, b) match
    case (IntMap.Nil, _) =>
      AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Left))
    case (_, IntMap.Nil) => AlgebraicResult.Identity(AlgebraicResult.Left)
    case _ if a eq b => AlgebraicResult.Empty(AlgebraicEmptyReason.LeftCovered)
    case (IntMap.Tip(leftKey, _), IntMap.Tip(rightKey, _)) if leftKey != rightKey =>
      AlgebraicResult.Identity(AlgebraicResult.Left)
    case (IntMap.Tip(key, left), IntMap.Tip(_, right)) =>
      left.subtractionResult(right) match
        case AlgebraicResult.Empty(_) => AlgebraicResult.Empty(AlgebraicEmptyReason.LeftCovered)
        case childResult if AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left) =>
          AlgebraicResult.Identity(AlgebraicResult.Left)
        case childResult =>
          AlgebraicResult.Bespoke(tipKnown(key, TrieSpace.binaryValue(childResult, left, right)))
    case (IntMap.Tip(k, v), _) =>
      lookup(b, k) match
        case None => AlgebraicResult.Identity(AlgebraicResult.Left)
        case Some(w) =>
          v.subtractionResult(w) match
            case AlgebraicResult.Empty(_) => AlgebraicResult.Empty(AlgebraicEmptyReason.LeftCovered)
            case childResult if AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left) =>
              AlgebraicResult.Identity(AlgebraicResult.Left)
            case childResult =>
              AlgebraicResult.Bespoke(tipKnown(k, TrieSpace.binaryValue(childResult, v, w)))
    case (_, IntMap.Tip(k, w)) =>
      lookup(a, k) match
        case None => AlgebraicResult.Identity(AlgebraicResult.Left)
        case Some(v) =>
          val childResult = v.subtractionResult(w)
          if AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left) then
            AlgebraicResult.Identity(AlgebraicResult.Left)
          else
            val replacement = TrieSpace.binaryValue(childResult, v, w)
            AlgebraicResult.Bespoke(if replacement.isEmpty then removed(a, k) else updated(a, k, replacement))
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then AlgebraicResult.Identity(AlgebraicResult.Left)
        else
          val recurseLeft = zero(p2, m1)
          val leftBranch = if recurseLeft then l1 else r1
          val childResult = diffTriesResult(leftBranch, b)
          if AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left) then
            AlgebraicResult.Identity(AlgebraicResult.Left)
          else
            val child = valueOf(childResult, leftBranch, b)
            AlgebraicResult.Bespoke(
              if recurseLeft then binPruneKnown(p1, m1, child, r1)
              else binPruneKnown(p1, m1, l1, child)
            )
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then AlgebraicResult.Identity(AlgebraicResult.Left)
        else diffTriesResult(a, if zero(p1, m2) then l2 else r2)
      else if p1 == p2 then
        val leftResult = diffTriesResult(l1, l2)
        val rightResult = diffTriesResult(r1, r2)
        val left = valueOf(leftResult, l1, l2)
        val right = valueOf(rightResult, r1, r2)
        if (left eq IntMap.Nil) && (right eq IntMap.Nil) then
          AlgebraicResult.Empty(AlgebraicEmptyReason.LeftCovered)
        else if AlgebraicResult.equalsArgument(leftResult, AlgebraicResult.Left) &&
            AlgebraicResult.equalsArgument(rightResult, AlgebraicResult.Left)
        then AlgebraicResult.Identity(AlgebraicResult.Left)
        else AlgebraicResult.Bespoke(binPruneKnown(p1, m1, left, right))
      else AlgebraicResult.Identity(AlgebraicResult.Left)

  def diffTries(a: IntMap[TrieSpace], b: IntMap[TrieSpace]): IntMap[TrieSpace] =
    valueOf(diffTriesResult(a, b), a, b)

  def restrictTriesResult(
    x: IntMap[TrieSpace],
    p: IntMap[TrieSpace]
  ): RestrictionResult[IntMap[TrieSpace]] =
    ExecutorCostMeter.visitPatricia()
    (x, p) match
    case (IntMap.Nil, IntMap.Nil) =>
      RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.AllArguments), allPrefixesMatched = true)
    case (IntMap.Nil, _) =>
      RestrictionResult(
        AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Left)),
        allPrefixesMatched = false
      )
    case (_, IntMap.Nil) =>
      RestrictionResult(
        AlgebraicResult.Empty(AlgebraicEmptyReason.EmptyArguments(AlgebraicResult.Right)),
        allPrefixesMatched = true
      )
    case _ if x eq p =>
      RestrictionResult(AlgebraicResult.Identity(AlgebraicResult.Both), allPrefixesMatched = true)
    case (IntMap.Tip(leftKey, _), IntMap.Tip(rightKey, _)) if leftKey != rightKey =>
      RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch), allPrefixesMatched = false)
    case (IntMap.Tip(key, left), IntMap.Tip(_, right)) =>
      val child = left.restrictionResult(right)
      child.result match
        case AlgebraicResult.Empty(_) =>
          RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch), allPrefixesMatched = false)
        case childResult =>
          RestrictionResult(
            nonEmptyResult(
              tipKnown(key, TrieSpace.binaryValue(childResult, left, right)),
              AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
              AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right),
            ),
            child.allPrefixesMatched,
          )
    case (IntMap.Tip(k, v), _) =>
      lookup(p, k) match
        case None =>
          RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch), allPrefixesMatched = false)
        case Some(w) =>
          val child = v.restrictionResult(w)
          child.result match
            case AlgebraicResult.Empty(_) =>
              RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch), allPrefixesMatched = false)
            case childResult =>
              p match
                case IntMap.Tip(_, _) =>
                  RestrictionResult(
                    nonEmptyResult(
                      tipKnown(k, TrieSpace.binaryValue(childResult, v, w)),
                      AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
                      AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
                    ),
                    child.allPrefixesMatched
                  )
                case _ =>
                  RestrictionResult(
                    nonEmptyResult(
                      tipKnown(k, TrieSpace.binaryValue(childResult, v, w)),
                      AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
                      sameRight = false
                    ),
                    allPrefixesMatched = false
                  )
    case (_, IntMap.Tip(k, w)) =>
      lookup(x, k) match
        case None =>
          RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch), allPrefixesMatched = false)
        case Some(v) =>
          val child = v.restrictionResult(w)
          child.result match
            case AlgebraicResult.Empty(_) =>
              RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch), child.allPrefixesMatched)
            case childResult =>
              RestrictionResult(
                nonEmptyResult(
                  tipKnown(k, TrieSpace.binaryValue(childResult, v, w)),
                  sameLeft = false,
                  AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
                ),
                child.allPrefixesMatched
              )
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then
          RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch), allPrefixesMatched = false)
        else
          val leftBranch = if zero(p2, m1) then l1 else r1
          val child = restrictTriesResult(leftBranch, p)
          child.result match
            case AlgebraicResult.Empty(_) => child
            case childResult =>
              RestrictionResult(
                nonEmptyResult(
                  valueOf(childResult, leftBranch, p),
                  sameLeft = false,
                  AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Right)
                ),
                child.allPrefixesMatched
              )
      else if shorter(m2, m1) then
        if !hasMatch(p1, p2, m2) then
          RestrictionResult(AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch), allPrefixesMatched = false)
        else
          val rightBranch = if zero(p1, m2) then l2 else r2
          val child = restrictTriesResult(x, rightBranch)
          child.result match
            case AlgebraicResult.Empty(_) =>
              RestrictionResult(child.result, allPrefixesMatched = false)
            case childResult =>
              RestrictionResult(
                nonEmptyResult(
                  valueOf(childResult, x, rightBranch),
                  AlgebraicResult.equalsArgument(childResult, AlgebraicResult.Left),
                  sameRight = false
                ),
                allPrefixesMatched = false
              )
      else if p1 == p2 then
        val leftOutcome = restrictTriesResult(l1, l2)
        val rightOutcome = restrictTriesResult(r1, r2)
        val left = valueOf(leftOutcome.result, l1, l2)
        val right = valueOf(rightOutcome.result, r1, r2)
        if (left eq IntMap.Nil) && (right eq IntMap.Nil) then
          RestrictionResult(
            AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch),
            leftOutcome.allPrefixesMatched && rightOutcome.allPrefixesMatched
          )
        else
          RestrictionResult(
            nonEmptyResult(
              binPruneKnown(p1, m1, left, right),
              AlgebraicResult.equalsArgument(leftOutcome.result, AlgebraicResult.Left) &&
                AlgebraicResult.equalsArgument(rightOutcome.result, AlgebraicResult.Left),
              AlgebraicResult.equalsArgument(leftOutcome.result, AlgebraicResult.Right) &&
                AlgebraicResult.equalsArgument(rightOutcome.result, AlgebraicResult.Right)
            ),
            leftOutcome.allPrefixesMatched && rightOutcome.allPrefixesMatched
          )
      else RestrictionResult(
        AlgebraicResult.Empty(AlgebraicEmptyReason.NoPrefixMatch),
        allPrefixesMatched = false
      )

  def restrictTries(x: IntMap[TrieSpace], p: IntMap[TrieSpace]): IntMap[TrieSpace] =
    valueOf(restrictTriesResult(x, p).result, x, p)

  def prefixRelation(x: IntMap[TrieSpace], p: IntMap[TrieSpace]): (Boolean, Boolean) =
    ExecutorCostMeter.visitPatricia()
    (x, p) match
    case (IntMap.Nil, IntMap.Nil) => true -> true
    case (_, IntMap.Nil) => true -> false
    case (IntMap.Nil, _) => false -> false
    case _ if x eq p => true -> true
    case (IntMap.Tip(k, v), _) =>
      lookup(p, k) match
        case None => false -> false
        case Some(w) =>
          val relation = v.prefixRelation(w)
          val onlyKey = p.isInstanceOf[IntMap.Tip[?]]
          (onlyKey && relation._1) -> (onlyKey && relation._2)
    case (_, IntMap.Tip(k, w)) =>
      lookup(x, k) match
        case None => false -> false
        case Some(v) => v.prefixRelation(w)._1 -> false
    case (IntMap.Bin(p1, m1, l1, r1), IntMap.Bin(p2, m2, l2, r2)) =>
      if shorter(m1, m2) then
        if !hasMatch(p2, p1, m1) then false -> false
        else prefixRelation(if zero(p2, m1) then l1 else r1, p)._1 -> false
      else if shorter(m2, m1) then false -> false
      else if p1 == p2 then
        val left = prefixRelation(l1, l2)
        val right = prefixRelation(r1, r2)
        (left._1 && right._1) -> (left._2 && right._2)
      else false -> false
