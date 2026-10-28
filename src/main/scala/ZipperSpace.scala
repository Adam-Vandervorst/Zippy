package morkl

import scala.collection.immutable.IntMap
import scala.collection.mutable

trait SpaceZipper:
  def terminal: Boolean
  def child(item: Int): SpaceZipper
  def childKeys: IterableOnce[Int]
  def knownEmpty: Boolean = false
  /** A cheap exact value or upper bound for the number of immediate keys.
    * Consumers may use this to choose which operand to enumerate, but never
    * for denotational decisions.  In particular, virtual unions can add their
    * operand hints without forcing either child iterator. */
  def childKeySizeHint: Option[Int] = None
  def nonterminal: Boolean = !terminal
  def childKeySet: Set[Int] = childrenIterator.map(_._1).toSet
  def observation: SpaceZipper.Observation =
    SpaceZipper.Observation(nullable = terminal, nonterminal = nonterminal, empty = isEmpty, childKeys = childKeySet)
  def childKeySize: Int = childKeys.iterator.size
  def childrenIterator: Iterator[(Int, SpaceZipper)] =
    childKeys.iterator.map(k => k -> child(k)).filterNot(_._2.isEmpty)
  def concrete: Option[TrieSpace] = None
  def isEmpty: Boolean = !terminal && !childrenIterator.hasNext
  protected final def meteredChildProbe(result: => Boolean): Boolean =
    ExecutorCostMeter.cursorProbe()
    result
  protected final def meteredChildKeys(keys: Iterator[Int]): Iterator[Int] =
    keys.map { key =>
      ExecutorCostMeter.cursorProbe()
      key
    }
  def hasChild(item: Int): Boolean = meteredChildProbe(!child(item).isEmpty)
  protected final def pathCountByTraversal: Int =
    (if terminal then 1 else 0) + childrenIterator.map(_._2.pathCount).sum
  lazy val pathCount: Int =
    concrete.fold(pathCountByTraversal)(_.pathCount)
  def orderedChildrenIterator: Iterator[(Int, SpaceZipper)] =
    orderedChildren.iterator
  def orderedChildren: Array[(Int, SpaceZipper)] =
    childrenIterator.toArray.sortWith((a, b) => TrieSpace.comparePaths(a._1 :: Nil, b._1 :: Nil) < 0)
  def orderedChildIndex(item: Int, ordered: Array[(Int, SpaceZipper)]): Int =
    var low = 0
    var high = ordered.length - 1
    while low <= high do
      val middle = (low + high) >>> 1
      val comparison = TrieSpace.interner.compareItemIds(ordered(middle)._1, item)
      if comparison < 0 then low = middle + 1
      else if comparison > 0 then high = middle - 1
      else return middle
    -1
  protected final def materializeByTraversal: TrieSpace =
    val children = childrenIterator.flatMap { (item, z) =>
      val childTrie = z.materialize
      Option.when(!childTrie.isEmpty)(item -> childTrie)
    }
    TrieSpace.node(terminal, IntMap.from(children))
  def materialize: TrieSpace =
    concrete.getOrElse(materializeByTraversal)
  def toSpaceValue: SpaceValue = materialize.toSpaceValue

object SpaceZipper:
  case class Observation(nullable: Boolean, nonterminal: Boolean, empty: Boolean, childKeys: Set[Int]):
    require(nullable != nonterminal, "nullable and nonterminal must be exact complements")

  object Observation:
    def fromTrie(space: TrieSpace): Observation =
      Observation(
        nullable = space.terminal,
        nonterminal = !space.terminal,
        empty = space.isEmpty,
        childKeys = space.children.keySet
      )

  val empty: SpaceZipper = Trie(TrieSpace.empty)
  val epsilon: SpaceZipper = Trie(TrieSpace.epsilon)

  def traversal(space: TrieSpace): SpaceZipper = Trie(space)
  def singleton(path: List[Int]): SpaceZipper = Trie(TrieSpace.empty.insertItems(path))
  def literal(sv: SpaceValue): SpaceZipper = Trie(TrieSpace.fromSpaceValue(sv))
  private def storedConcrete(z: SpaceZipper): Option[TrieSpace] = z match
    case Trie(space) => Some(space)
    case Memo(src) => storedConcrete(src)
    case _ => None
  private[morkl] def storedTrie(z: SpaceZipper): Option[TrieSpace] =
    storedConcrete(z)
  private def sameValue(a: SpaceZipper, b: SpaceZipper): Boolean =
    (a.asInstanceOf[AnyRef] eq b.asInstanceOf[AnyRef]) ||
      ((storedConcrete(a), storedConcrete(b)) match
        case (Some(x), Some(y)) => x.asInstanceOf[AnyRef] eq y.asInstanceOf[AnyRef]
        case _ => false)
  private def identityKey(z: SpaceZipper): AnyRef =
    storedConcrete(z).fold(z.asInstanceOf[AnyRef])(_.asInstanceOf[AnyRef])
  private def uniqueByIdentity(zs: Iterator[SpaceZipper]): Vector[SpaceZipper] =
    val seen = java.util.IdentityHashMap[AnyRef, java.lang.Boolean]()
    val out = Vector.newBuilder[SpaceZipper]
    zs.foreach { z =>
      val key = identityKey(z)
      if !seen.containsKey(key) then
        seen.put(key, java.lang.Boolean.TRUE)
        out += z
    }
    out.result()
  private def joinParts(z: SpaceZipper): Vector[SpaceZipper] = z match
    case Memo(JoinAll(children)) => children
    case JoinAll(children) => children
    case _ => Vector(z)
  private def meetParts(z: SpaceZipper): Vector[SpaceZipper] = z match
    case Memo(Intersection(left, right)) => Vector(left, right)
    case Intersection(left, right) => Vector(left, right)
    case Memo(MeetAll(children)) => children
    case MeetAll(children) => children
    case _ => Vector(z)
  private def nativeRange(z: SpaceZipper, start: Int, end: Int): Option[TrieSpace] = z match
    case Trie(space) => Some(space.range(start, end))
    case Memo(src) => nativeRange(src, start, end)
    case _ => None
  private def nativeRangeNormalized(z: SpaceZipper, lo: Int, hi: Int): Option[TrieSpace] =
    def bounds(size: Int): (Int, Int) =
      val clampedLo = lo.max(0).min(size)
      val clampedHi = hi.max(0).min(size)
      val start = if clampedLo == 0 then 0 else clampedLo + 1
      val end =
        if clampedHi == size then 0
        else if start == 0 then clampedHi
        else clampedHi + 1
      start -> end

    z match
      case Trie(space) =>
        val (start, end) = bounds(space.pathCount)
        Some(space.range(start, end))
      case Memo(src) => nativeRangeNormalized(src, lo, hi)
      case _ => None
  private def saturatingAdd(a: Int, b: Int): Int =
    val sum = a.toLong + b.toLong
    if sum > Int.MaxValue then Int.MaxValue
    else if sum < Int.MinValue then Int.MinValue
    else sum.toInt
  private def memo(z: SpaceZipper): SpaceZipper = z match
    case Trie(_) | Memo(_) => z
    case _ => Memo(z)
  enum IterTemplateTag:
    case Tail
    case Head
    case Reconstruct
    case PrefixedReconstruct(prefix: List[Int])
    case RangeTail(start: Int, end: Int)
    case RangeReconstruct(start: Int, end: Int)
    case PrefixedRangeReconstruct(prefix: List[Int], start: Int, end: Int)

  /** A cursor backed by a higher-order fixpoint engine rather than by one of
    * the first-order zipper constructors below. Artifact exporters can name
    * this boundary and materialize it explicitly without silently treating an
    * unrelated future zipper implementation as a concrete trie. */
  private[morkl] sealed trait DeferredFixpointFocus extends SpaceZipper

  /** A call boundary for structurally certified, well-founded recursion.
    * Construction records the recursive arguments without expanding the
    * callee; the body is unfolded only when a consumer observes the result.
    * `knownEmpty` deliberately remains conservative so union construction
    * cannot force an unbounded recursive expansion. */
  private final class DeferredRoutineCall(thunk: () => SpaceZipper) extends SpaceZipper:
    private lazy val expanded = thunk()
    override def knownEmpty: Boolean = false
    override def terminal: Boolean = expanded.terminal
    override def child(item: Int): SpaceZipper = expanded.child(item)
    override def childKeys: IterableOnce[Int] = expanded.childKeys
    override def childKeySize: Int = expanded.childKeySize
    override def childKeySizeHint: Option[Int] = expanded.childKeySizeHint
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = expanded.childrenIterator
    override def isEmpty: Boolean = expanded.isEmpty
    override lazy val pathCount: Int = expanded.pathCount
    override def materialize: TrieSpace = expanded.materialize

  private[morkl] def deferredRoutineCall(thunk: () => SpaceZipper): SpaceZipper =
    new DeferredRoutineCall(thunk)

  def union(a: SpaceZipper, b: SpaceZipper): SpaceZipper =
    if sameValue(a, b) then a
    else if a.knownEmpty then b
    else if b.knownEmpty then a
    else memo(Union(a, b))
  def intersection(a: SpaceZipper, b: SpaceZipper): SpaceZipper =
    if sameValue(a, b) then a
    else if a.knownEmpty || b.knownEmpty then empty
    else
      val parts = uniqueByIdentity(meetParts(a).iterator ++ meetParts(b).iterator)
      if parts.exists(_.knownEmpty) then empty
      else if parts.length == 1 then parts.head
      else
        val concreteParts = parts.map(storedConcrete)
        if concreteParts.forall(_.isDefined) then
          val concrete = concreteParts.flatten
          if concrete.length == 2 then Trie(concrete(0).intersect(concrete(1)))
          else Trie(TrieSpace.meetAll(concrete))
        else if parts.length == 2 then memo(Intersection(parts(0), parts(1)))
        else memo(MeetAll(parts))
  def subtraction(a: SpaceZipper, b: SpaceZipper): SpaceZipper =
    if sameValue(a, b) then empty
    else if a.knownEmpty || b.knownEmpty then a
    else memo(Subtraction(a, b))
  def restriction(a: SpaceZipper, prefixes: SpaceZipper): SpaceZipper =
    if a.knownEmpty || prefixes.knownEmpty then empty
    else if prefixes.terminal then a
    else
      a match
        case Memo(Subtraction(left, right)) => subtraction(restriction(left, prefixes), right)
        case Subtraction(left, right) => subtraction(restriction(left, prefixes), right)
        case Memo(Union(left, right)) => union(restriction(left, prefixes), restriction(right, prefixes))
        case Union(left, right) => union(restriction(left, prefixes), restriction(right, prefixes))
        case _ => memo(Restriction(a, prefixes))
  def joinAll(zs: IterableOnce[SpaceZipper]): SpaceZipper =
    val kept = uniqueByIdentity(zs.iterator.filterNot(_.knownEmpty))
    if kept.isEmpty then empty else if kept.length == 1 then kept.head else memo(JoinAll(kept))
  def meetAll(zs: IterableOnce[SpaceZipper]): SpaceZipper =
    val kept = uniqueByIdentity(zs.iterator)
    if kept.isEmpty || kept.exists(_.knownEmpty) then empty
    else if kept.length == 1 then kept.head
    else memo(MeetAll(kept))
  def concat(a: SpaceZipper, b: SpaceZipper): SpaceZipper =
    if a.knownEmpty || b.knownEmpty then empty else memo(Concat(a, b))
  def head(src: SpaceZipper): SpaceZipper =
    if src.knownEmpty then empty else memo(Head(src))
  def iteration(src: SpaceZipper,
                branch: (Int, SpaceZipper) => SpaceZipper,
                template: Option[IterTemplateTag] = None): SpaceZipper =
    if src.knownEmpty then empty else memo(Iteration(src, branch, template))
  def fixpoint(src: SpaceZipper, template: IterTemplateTag): SpaceZipper =
    if src.knownEmpty then empty else memo(Fixpoint(src, template))
  /** A general inflationary fixpoint whose observable trie equations are
    * saturated only when a terminal or child frontier is requested. */
  def fixpoint(src: SpaceZipper)(step: SpaceZipper => SpaceZipper): SpaceZipper =
    new DemandFixpointEngine(src, step).root
  /** A lazy exact fallback for fixpoint steps that are not proved positive.
    * The first observation performs the same synchronous Kleene rounds as the
    * reference evaluator; construction itself never starts a round. */
  def synchronousFixpoint(src: SpaceZipper)(step: SpaceZipper => SpaceZipper): SpaceZipper =
    new SynchronousFixpointEngine(src, current => step(traversal(current)).materialize).root
  /** Exact synchronous fallback whose whole round is already expressed in
    * native TrieSpace algebra. It remains lazy until the first observation. */
  def synchronousFixpointNative(src: SpaceZipper)(step: TrieSpace => TrieSpace): SpaceZipper =
    new SynchronousFixpointEngine(src, step).root
  def whenHeaded(src: SpaceZipper, value: => SpaceZipper): SpaceZipper =
    if src.knownEmpty then empty else memo(HeadedGuard(src, () => value))
  def wrap(src: SpaceZipper, prefix: List[Int]): SpaceZipper =
    if src.knownEmpty then empty else if prefix.isEmpty then src else memo(Prefix(prefix, src))
  def unwrap(src: SpaceZipper, prefix: List[Int]): SpaceZipper =
    prefix.foldLeft(src) { (z, item) =>
      ExecutorCostMeter.visitNode()
      ExecutorCostMeter.comparePath()
      if z.knownEmpty then empty else z.child(item)
    }
  def range(src: SpaceZipper, start: Int, end: Int): SpaceZipper =
    if src.knownEmpty then empty
    else src match
      case Prefix(prefix, inner) if prefix.nonEmpty =>
        wrap(range(inner, start, end), prefix)
      case Memo(Prefix(prefix, inner)) if prefix.nonEmpty =>
        wrap(range(inner, start, end), prefix)
      case _ =>
        rangeNonPrefix(src, start, end)

  private def rangeNonPrefix(src: SpaceZipper, start: Int, end: Int): SpaceZipper =
    if src.knownEmpty then empty
    else if start == 0 && end == 0 then src
    else if start >= 0 then
      val lo = if start == 0 then 0 else start - 1
      if end > 0 then
        val hi = if start == 0 then end else end - 1
        rangeNormalized(src, lo, hi)
      else
        val prefix = if end < 0 then dropLast(src, -end) else src
        rangeNormalized(prefix, lo, Int.MaxValue)
    else if end == 0 then
      last(src, -start)
    else if end < 0 then
      dropLast(last(src, -start), -end)
    else nativeRange(src, start, end).fold {
      val (lo, hi) = RangeBounds.normalize(src.pathCount, start, end)
      rangeNormalized(src, lo, hi)
    }(Trie(_))

  private def last(src: SpaceZipper, n: Int): SpaceZipper =
    if n <= 0 || src.knownEmpty then empty
    else nativeRange(src, -n, 0).fold(memo(LastRange(src, n)))(Trie(_))

  private def dropLast(src: SpaceZipper, n: Int): SpaceZipper =
    if n <= 0 || src.knownEmpty then src
    else src match
      case DropLastRange(base, m) => dropLast(base, saturatingAdd(m, n))
      case Memo(DropLastRange(base, m)) => dropLast(base, saturatingAdd(m, n))
      case _ => memo(DropLastRange(src, n))

  private def patchChild(parent: SpaceZipper, item: Int, replacement: SpaceZipper): SpaceZipper =
    if replacement.isEmpty && !parent.hasChild(item) then parent
    else if sameValue(parent.child(item), replacement) then parent
    else (storedConcrete(parent), storedConcrete(replacement)) match
      case (Some(parentTrie), Some(replacementTrie)) => Trie(TrieSpace.replaceChild(parentTrie, item, replacementTrie))
      case _ => memo(PatchChild(parent, item, replacement))

  private def rangeNormalized(src: SpaceZipper, lo: Int, hi: Int): SpaceZipper =
    if hi <= lo then empty
    else if lo == 0 && hi == Int.MaxValue then src
    else src match
      case Range(base, baseLo, baseHi) =>
        rangeNormalized(base, saturatingAdd(baseLo, lo), saturatingAdd(baseLo, hi).min(baseHi))
      case Memo(Range(base, baseLo, baseHi)) =>
        rangeNormalized(base, saturatingAdd(baseLo, lo), saturatingAdd(baseLo, hi).min(baseHi))
      case _ =>
        val exactCount =
          storedConcrete(src).map(_.pathCount)
        if exactCount.exists(count => lo == 0 && hi >= count) then src
        else Range(src, lo, hi)

  private def unionKeys(a: IterableOnce[Int], b: IterableOnce[Int]): IterableOnce[Int] =
    val keys = mutable.LinkedHashSet.empty[Int]
    keys ++= a.iterator
    keys ++= b.iterator
    keys

  private def addKeyHints(values: IterableOnce[SpaceZipper]): Option[Int] =
    var total = 0L
    val iterator = values.iterator
    while iterator.hasNext do
      iterator.next().childKeySizeHint match
        case Some(value) => total = (total + value.toLong).min(Int.MaxValue.toLong)
        case None => return None
    Some(total.toInt)

  private def smallerByKeys(left: SpaceZipper, right: SpaceZipper): (SpaceZipper, SpaceZipper) =
    (left.childKeySizeHint, right.childKeySizeHint) match
      case (Some(l), Some(r)) => if l <= r then left -> right else right -> left
      case (Some(_), None) => left -> right
      case (None, Some(_)) => right -> left
      case _ => if left.childKeySize <= right.childKeySize then left -> right else right -> left

  private def smallestByKeys(zs: Vector[SpaceZipper]): SpaceZipper =
    zs.filter(_.childKeySizeHint.nonEmpty).minByOption(_.childKeySizeHint.get)
      .getOrElse(zs.minBy(_.childKeySize))

  private def closureReachable(root: SpaceZipper): Vector[SpaceZipper] =
    val seen = java.util.IdentityHashMap[AnyRef, java.lang.Boolean]()
    val out = Vector.newBuilder[SpaceZipper]
    val stack = mutable.ArrayDeque.empty[SpaceZipper]

    def enqueue(z: SpaceZipper): Unit =
      val key = identityKey(z)
      if !seen.containsKey(key) then
        seen.put(key, java.lang.Boolean.TRUE)
        stack.prepend(z)

    enqueue(root)
    while stack.nonEmpty do
      val focus = stack.removeHead()
      out += focus
      focus.childrenIterator.foreach((_, child) => enqueue(child))
    out.result()

  private case class ClosureSummary(
    reachable: Vector[SpaceZipper],
    frontierMap: Map[Int, Vector[SpaceZipper]],
    allTailFrontiers: Vector[SpaceZipper],
  )

  /** One traversal supplies every suffix-closure projection. Previous code
    * discarded `closureFrontierMap` values and repeated the reachable-graph
    * walk independently for every queried head. */
  private def closureSummary(root: SpaceZipper): ClosureSummary =
    val reachable = closureReachable(root)
    val byKey = mutable.LinkedHashMap.empty[Int, mutable.Builder[SpaceZipper, Vector[SpaceZipper]]]
    val all = Vector.newBuilder[SpaceZipper]
    reachable.foreach { focus =>
      focus.childrenIterator.foreach { (item, tail) =>
        if !tail.isEmpty then
          byKey.getOrElseUpdate(item, Vector.newBuilder[SpaceZipper]) += tail
          all += tail
      }
    }
    ClosureSummary(
      reachable,
      byKey.iterator.map((item, tails) => item -> uniqueByIdentity(tails.result().iterator)).toMap,
      uniqueByIdentity(all.result().iterator),
    )

  /** Exact synchronous fallback for order-sensitive fixpoint steps. A lazy
    * prefix solver cannot retroactively recover a Range member that was true
    * in an earlier global approximation but was not demanded in that round. */
  private def kleeneUnion(initial: SpaceZipper)(step: SpaceZipper => SpaceZipper): SpaceZipper =
    var current = initial.materialize
    var changed = true
    while changed do
      ExecutorCostMeter.round()
      val stepped = step(traversal(current)).materialize
      val next = current.union(stepped)
      changed = next != current
      current = next
    traversal(current)

  /** Whole-round native boundary for fixpoints whose semantics already force
    * complete synchronous materialization. No cursor selectivity remains to
    * justify rebuilding a virtual IterationChild tree in each round. */
  private def kleeneUnionNative(initial: SpaceZipper)(step: TrieSpace => TrieSpace): SpaceZipper =
    var current = initial.materialize
    var changed = true
    while changed do
      ExecutorCostMeter.round()
      val next = current.union(step(current))
      changed = next != current
      current = next
    traversal(current)

  private def directTailFrontier(src: SpaceZipper, item: Int): Vector[SpaceZipper] =
    val tail = src.child(item)
    if tail.isEmpty then Vector.empty else Vector(tail)

  private def frontierCandidates(active: SpaceZipper): Vector[SpaceZipper] = active match
    case Memo(src) => frontierCandidates(src)
    case FrontierUnion(suffix: SuffixClosure) =>
      suffix.allTailFrontiers
    case FrontierUnion(tails: TailsClosure) =>
      tails.allTailFrontiers
    case FrontierUnion(src) =>
      uniqueByIdentity(src.childrenIterator.map(_._2))
    case FrontierTailUnion(suffix: SuffixClosure, item) =>
      suffix.tailFrontiers(item)
    case FrontierTailUnion(tails: TailsClosure, item) =>
      tails.tailFrontiers(item)
    case FrontierTailUnion(src, item) =>
      directTailFrontier(src, item)
    case FrontierChildUnion(src, item) =>
      uniqueByIdentity(frontierCandidates(src).iterator.map(_.child(item)).filterNot(_.isEmpty))
    case FrontierState(src) =>
      frontierCandidates(src)
    case _ =>
      Vector.empty

  sealed trait CursorContext:
    def path: Vector[Int]
    def plug(focus: SpaceZipper): SpaceZipper
    def isRoot: Boolean

  object CursorContext:
    case object Root extends CursorContext:
      override val path: Vector[Int] = Vector.empty
      override def plug(focus: SpaceZipper): SpaceZipper = focus
      override val isRoot: Boolean = true

    case class Child(parent: CursorContext,
                     item: Int,
                     originalParent: SpaceZipper,
                     ordered: Array[(Int, SpaceZipper)] | Null,
                     index: Int) extends CursorContext:
      override def path: Vector[Int] = parent.path :+ item
      override def plug(focus: SpaceZipper): SpaceZipper =
        parent.plug(patchChild(originalParent, item, focus))
      override val isRoot: Boolean = false

  case class Cursor(focus: SpaceZipper, context: CursorContext = CursorContext.Root):
    def path: Vector[Int] = context.path
    def pathValue: PathValue = TrieSpace.decode(path)
    def whole: SpaceZipper = context.plug(focus)
    def wholeTrie: TrieSpace = whole.materialize
    def atRoot: Boolean = context.isRoot

    def down(item: Int): Option[Cursor] =
      val child = focus.child(item)
      Option.when(!child.isEmpty) {
        Cursor(child, CursorContext.Child(context, item, focus, null, index = -1))
      }

    def down(item: PathItem): Option[Cursor] =
      down(TrieSpace.interner.intern(item))

    def descendItems(items: Iterable[Int]): Option[Cursor] =
      items.foldLeft(Option(this))((cursor, item) => cursor.flatMap(_.down(item)))

    def descend(path: PathValue): Option[Cursor] =
      descendItems(TrieSpace.intern(path))

    def up: Option[Cursor] = context match
      case CursorContext.Root => None
      case CursorContext.Child(parent, item, originalParent, _, _) =>
        Some(Cursor(patchChild(originalParent, item, focus), parent))

    def toRoot: Cursor =
      var cursor = this
      var next = cursor.up
      while next.isDefined do
        cursor = next.get
        next = cursor.up
      cursor

    def graft(replacement: SpaceZipper): Cursor =
      copy(focus = replacement)

    def removeFocus: Cursor =
      graft(empty)

    def insertAtFocus(path: PathValue): Cursor =
      insertItemsAtFocus(TrieSpace.intern(path))

    def insertItemsAtFocus(path: List[Int]): Cursor =
      graft(union(focus, singleton(path)))

    def firstChild: Option[Cursor] =
      focus.orderedChildren.headOption.map((item, child) =>
        Cursor(child, CursorContext.Child(context, item, focus, focus.orderedChildren, index = 0))
      )

    def nextSibling: Option[Cursor] =
      sibling(delta = 1)

    def previousSibling: Option[Cursor] =
      sibling(delta = -1)

    private def sibling(delta: Int): Option[Cursor] = context match
      case CursorContext.Root => None
      case CursorContext.Child(parent, item, originalParent, ordered, index) =>
        val updatedParent = patchChild(originalParent, item, focus)
        val siblings = if ordered == null then originalParent.orderedChildren else ordered
        val anchor = if index >= 0 then index else originalParent.orderedChildIndex(item, siblings)
        var nextIndex = anchor + delta
        while nextIndex >= 0 && nextIndex < siblings.length && !updatedParent.hasChild(siblings(nextIndex)._1) do
          nextIndex += delta
        Option.when(nextIndex >= 0 && nextIndex < siblings.length) {
          val nextItem = siblings(nextIndex)._1
          val nextFocus = updatedParent.child(nextItem)
          Cursor(nextFocus, CursorContext.Child(parent, nextItem, updatedParent, siblings, nextIndex))
        }

  case class Trie(space: TrieSpace) extends SpaceZipper:
    override def terminal: Boolean = space.terminal
    override def concrete: Option[TrieSpace] = Some(space)
    override def knownEmpty: Boolean = space.isEmpty
    override def isEmpty: Boolean = space.isEmpty
    override lazy val pathCount: Int = space.pathCount
    override def child(item: Int): SpaceZipper =
      space.children.get(item).fold(empty)(Trie(_))
    override def hasChild(item: Int): Boolean = meteredChildProbe(space.children.contains(item))
    override def childKeySize: Int = space.childCount
    override def childKeySizeHint: Option[Int] = Some(space.childCount)
    override def childKeys: IterableOnce[Int] = meteredChildKeys(space.children.keysIterator)
    override def childKeySet: Set[Int] = space.children.keySet
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      space.children.iterator.map((item, child) => item -> Trie(child))
    override def orderedChildrenIterator: Iterator[(Int, SpaceZipper)] =
      space.orderedChildren.iterator.map((item, child) => item -> Trie(child))
    override def orderedChildren: Array[(Int, SpaceZipper)] =
      space.orderedChildren.map((item, child) => item -> Trie(child))
    override def materialize: TrieSpace = space

  case class Memo(src: SpaceZipper) extends SpaceZipper:
    private val childCache = mutable.HashMap.empty[Int, SpaceZipper]
    override lazy val terminal: Boolean = src.terminal
    override def concrete: Option[TrieSpace] = src.concrete
    override def knownEmpty: Boolean = src.knownEmpty
    override lazy val childKeySize: Int = childKeyVector.length
    override def childKeySizeHint: Option[Int] = src.childKeySizeHint
    private lazy val childKeyVector: Vector[Int] = src.childKeys.iterator.toVector
    override def childKeys: IterableOnce[Int] = childKeyVector.iterator
    override def child(item: Int): SpaceZipper =
      childCache.getOrElseUpdate(item, memo(src.child(item)))
    override lazy val isEmpty: Boolean = src.isEmpty
    override def hasChild(item: Int): Boolean = src.hasChild(item)
    private lazy val childrenVector: Vector[(Int, SpaceZipper)] =
      childKeyVector.iterator.map(k => k -> child(k)).filterNot(_._2.isEmpty).toVector
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = childrenVector.iterator
    override lazy val pathCount: Int = src.pathCount
    override lazy val orderedChildren: Array[(Int, SpaceZipper)] =
      childrenVector.toArray.sortWith((a, b) => TrieSpace.comparePaths(a._1 :: Nil, b._1 :: Nil) < 0)
    override lazy val materialize: TrieSpace = src.materialize

  case class Union(left: SpaceZipper, right: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = left.knownEmpty && right.knownEmpty
    override def concrete: Option[TrieSpace] =
      for
        l <- left.concrete
        r <- right.concrete
      yield l.union(r)
    override def terminal: Boolean = left.terminal || right.terminal
    override def isEmpty: Boolean = left.isEmpty && right.isEmpty
    override def hasChild(item: Int): Boolean =
      meteredChildProbe(left.hasChild(item) || right.hasChild(item))
    override def child(item: Int): SpaceZipper = union(left.child(item), right.child(item))
    override def childKeys: IterableOnce[Int] = unionKeys(left.childKeys, right.childKeys)
    override def childKeySizeHint: Option[Int] = addKeyHints(Vector(left, right))

  case class JoinAll(children: Vector[SpaceZipper]) extends SpaceZipper:
    override def knownEmpty: Boolean = children.forall(_.knownEmpty)
    override def concrete: Option[TrieSpace] =
      val concreteChildren = children.map(_.concrete)
      Option.when(concreteChildren.forall(_.isDefined))(TrieSpace.joinAll(concreteChildren.flatten))
    override def terminal: Boolean = children.exists(_.terminal)
    override def isEmpty: Boolean = children.forall(_.isEmpty)
    override def hasChild(item: Int): Boolean =
      meteredChildProbe(children.exists(_.hasChild(item)))
    override def child(item: Int): SpaceZipper = joinAll(children.iterator.map(_.child(item)))
    override def childKeySizeHint: Option[Int] = addKeyHints(children)
    override def childKeys: IterableOnce[Int] =
      val keys = mutable.LinkedHashSet.empty[Int]
      children.foreach(z => keys ++= z.childKeys.iterator)
      keys

  case class Intersection(left: SpaceZipper, right: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = left.knownEmpty || right.knownEmpty
    override def concrete: Option[TrieSpace] =
      for
        l <- left.concrete
        r <- right.concrete
      yield l.intersect(r)
    override def terminal: Boolean = left.terminal && right.terminal
    override def child(item: Int): SpaceZipper = intersection(left.child(item), right.child(item))
    override def childKeySizeHint: Option[Int] =
      (left.childKeySizeHint, right.childKeySizeHint) match
        case (Some(l), Some(r)) => Some(l.min(r))
        case (hint @ Some(_), None) => hint
        case (None, hint @ Some(_)) => hint
        case _ => None
    override def childKeys: IterableOnce[Int] =
      val (small, large) = smallerByKeys(left, right)
      small.childKeys.iterator.filter(large.hasChild)
    /** Do not synthesize a concrete virtual operand merely to count or emit a
      * demanded intersection.  Stored tries still use the native merge; a
      * virtual side is probed only along keys supplied by the smaller side. */
    override lazy val pathCount: Int =
      if storedConcrete(left).nonEmpty && storedConcrete(right).nonEmpty then concrete.get.pathCount
      else pathCountByTraversal
    override def materialize: TrieSpace =
      if storedConcrete(left).nonEmpty && storedConcrete(right).nonEmpty then concrete.get
      else materializeByTraversal

  case class MeetAll(children: Vector[SpaceZipper]) extends SpaceZipper:
    override def knownEmpty: Boolean = children.exists(_.knownEmpty)
    override def concrete: Option[TrieSpace] =
      val concreteChildren = children.map(_.concrete)
      Option.when(concreteChildren.forall(_.isDefined))(TrieSpace.meetAll(concreteChildren.flatten))
    override def terminal: Boolean = children.forall(_.terminal)
    override def child(item: Int): SpaceZipper = meetAll(children.iterator.map(_.child(item)))
    override def childKeySizeHint: Option[Int] =
      children.iterator.flatMap(_.childKeySizeHint).minOption
    override def childKeys: IterableOnce[Int] =
      val small = smallestByKeys(children)
      small.childKeys.iterator.filter(k => children.forall(_.hasChild(k)))
    override lazy val pathCount: Int =
      if children.forall(storedConcrete(_).nonEmpty) then concrete.get.pathCount else pathCountByTraversal
    override def materialize: TrieSpace =
      if children.forall(storedConcrete(_).nonEmpty) then concrete.get else materializeByTraversal

  case class Subtraction(left: SpaceZipper, right: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = left.knownEmpty
    override def concrete: Option[TrieSpace] =
      for
        l <- left.concrete
        r <- right.concrete
      yield l.diff(r)
    override def terminal: Boolean = left.terminal && !right.terminal
    override def child(item: Int): SpaceZipper = subtraction(left.child(item), right.child(item))
    override def childKeySize: Int = left.childKeySize
    override def childKeySizeHint: Option[Int] = left.childKeySizeHint
    override def childKeys: IterableOnce[Int] = left.childKeys

  case class Restriction(src: SpaceZipper, prefixes: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = src.knownEmpty || prefixes.knownEmpty
    override def concrete: Option[TrieSpace] =
      for
        s <- src.concrete
        p <- prefixes.concrete
      yield s.restrictBy(p)
    override def terminal: Boolean = prefixes.terminal && src.terminal
    override def child(item: Int): SpaceZipper =
      if prefixes.terminal then src.child(item)
      else restriction(src.child(item), prefixes.child(item))
    override def childKeys: IterableOnce[Int] =
      if prefixes.terminal then src.childKeys
      else
        val (small, large) = smallerByKeys(src, prefixes)
        small.childKeys.iterator.filter(large.hasChild)

  case class Concat(left: SpaceZipper, right: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = left.knownEmpty || right.knownEmpty
    override def isEmpty: Boolean = left.isEmpty || right.isEmpty
    override def terminal: Boolean = left.terminal && right.terminal
    override def materialize: TrieSpace =
      if knownEmpty then TrieSpace.empty else left.materialize.concat(right.materialize)
    override def child(item: Int): SpaceZipper =
      union(
        if left.terminal then right.child(item) else empty,
        if left.hasChild(item) then concat(left.child(item), right) else empty
      )
    override def childKeys: IterableOnce[Int] =
      if left.terminal then unionKeys(left.childKeys, right.childKeys) else left.childKeys
    override def childKeySize: Int =
      if left.terminal then childKeys.iterator.size else left.childKeySize

  case class Prefix(prefix: List[Int], src: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = src.knownEmpty
    override def isEmpty: Boolean = src.isEmpty
    override def concrete: Option[TrieSpace] =
      src.concrete.map(_.wrapItems(prefix))
    override def terminal: Boolean = prefix.isEmpty && src.terminal
    override def child(item: Int): SpaceZipper = prefix match
      case Nil => src.child(item)
      case head :: tail if head == item => wrap(src, tail)
      case _ => empty
    override def childKeys: IterableOnce[Int] =
      prefix match
        case Nil => src.childKeys
        case head :: _ => Iterator.single(head)
    override def childKeySize: Int =
      if prefix.isEmpty then src.childKeySize else 1
    override def childKeySizeHint: Option[Int] =
      if prefix.isEmpty then src.childKeySizeHint else Some(1)
    override lazy val materialize: TrieSpace =
      src.materialize.wrapItems(prefix)

  case class NonEmpty(src: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = src.knownEmpty
    override def terminal: Boolean = false
    override def child(item: Int): SpaceZipper = src.child(item)
    override def hasChild(item: Int): Boolean = src.hasChild(item)
    override def childKeys: IterableOnce[Int] = src.childKeys
    override def childKeySize: Int = src.childKeySize
    override def childKeySizeHint: Option[Int] = src.childKeySizeHint
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = src.childrenIterator

  case class TailsUnion(src: SpaceZipper) extends SpaceZipper:
    private lazy val concreteValue: Option[TrieSpace] =
      src.concrete.map(_.tailsUnion)
    override def knownEmpty: Boolean = src.knownEmpty
    override def concrete: Option[TrieSpace] =
      concreteValue
    private lazy val tails: Vector[SpaceZipper] = src.childrenIterator.map(_._2).toVector
    private lazy val joined: SpaceZipper = joinAll(tails)
    override def terminal: Boolean = joined.terminal
    override def child(item: Int): SpaceZipper = joined.child(item)
    override def childKeys: IterableOnce[Int] = joined.childKeys
    override def childKeySize: Int = joined.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = joined.childrenIterator
    override lazy val pathCount: Int =
      concreteValue.fold((if terminal then 1 else 0) + childrenIterator.map(_._2.pathCount).sum)(_.pathCount)

  case class TailsIntersection(src: SpaceZipper) extends SpaceZipper:
    private lazy val concreteValue: Option[TrieSpace] =
      src.concrete.map(_.tailsIntersection)
    override def knownEmpty: Boolean = src.knownEmpty
    override def concrete: Option[TrieSpace] =
      concreteValue
    private lazy val met: SpaceZipper = meetAll(src.childrenIterator.map(_._2).toVector)
    override def terminal: Boolean = met.terminal
    override def child(item: Int): SpaceZipper = met.child(item)
    override def childKeys: IterableOnce[Int] = met.childKeys
    override def childKeySize: Int = met.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = met.childrenIterator
    override lazy val pathCount: Int =
      concreteValue.fold((if terminal then 1 else 0) + childrenIterator.map(_._2.pathCount).sum)(_.pathCount)

  case class FrontierUnion(src: SpaceZipper) extends SpaceZipper:
    private lazy val candidates: Vector[SpaceZipper] = frontierCandidates(this)
    private lazy val joined: SpaceZipper = joinAll(candidates)
    override def knownEmpty: Boolean = candidates.isEmpty || candidates.forall(_.knownEmpty)
    override def terminal: Boolean = joined.terminal
    override def child(item: Int): SpaceZipper = FrontierState(FrontierChildUnion(this, item))
    override def childKeys: IterableOnce[Int] = joined.childKeys
    override def childKeySize: Int = joined.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      childKeys.iterator.map(item => item -> child(item)).filterNot(_._2.isEmpty)

  case class FrontierTailUnion(src: SpaceZipper, item: Int) extends SpaceZipper:
    private lazy val candidates: Vector[SpaceZipper] = frontierCandidates(this)
    private lazy val joined: SpaceZipper = joinAll(candidates)
    override def knownEmpty: Boolean = candidates.isEmpty || candidates.forall(_.knownEmpty)
    override def terminal: Boolean = joined.terminal
    override def child(key: Int): SpaceZipper = FrontierState(FrontierChildUnion(this, key))
    override def childKeys: IterableOnce[Int] = joined.childKeys
    override def childKeySize: Int = joined.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      childKeys.iterator.map(key => key -> child(key)).filterNot(_._2.isEmpty)

  case class FrontierChildUnion(src: SpaceZipper, item: Int) extends SpaceZipper:
    private lazy val candidates: Vector[SpaceZipper] = frontierCandidates(this)
    private lazy val joined: SpaceZipper = joinAll(candidates)
    override def knownEmpty: Boolean = candidates.isEmpty || candidates.forall(_.knownEmpty)
    override def terminal: Boolean = joined.terminal
    override def child(key: Int): SpaceZipper = FrontierState(FrontierChildUnion(this, key))
    override def childKeys: IterableOnce[Int] = joined.childKeys
    override def childKeySize: Int = joined.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      childKeys.iterator.map(key => key -> child(key)).filterNot(_._2.isEmpty)

  case class FrontierState(active: SpaceZipper) extends SpaceZipper:
    private lazy val candidates: Vector[SpaceZipper] = frontierCandidates(active)
    private lazy val joined: SpaceZipper = joinAll(candidates)
    override def knownEmpty: Boolean = candidates.isEmpty || candidates.forall(_.knownEmpty)
    override def terminal: Boolean = joined.terminal
    override def child(item: Int): SpaceZipper = FrontierState(FrontierChildUnion(active, item))
    override def childKeys: IterableOnce[Int] = joined.childKeys
    override def childKeySize: Int = joined.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      childKeys.iterator.map(item => item -> child(item)).filterNot(_._2.isEmpty)
    override lazy val pathCount: Int =
      (if terminal then 1 else 0) + childrenIterator.map(_._2.pathCount).sum

  case class PrefixClosure(src: SpaceZipper, belowHead: Boolean = false) extends SpaceZipper:
    override def knownEmpty: Boolean = src.knownEmpty
    override def concrete: Option[TrieSpace] =
      Option.when(!belowHead)(src.concrete).flatten.map(_.prefixClosure)
    override def terminal: Boolean = belowHead && !src.isEmpty
    override def child(item: Int): SpaceZipper = PrefixClosure(src.child(item), belowHead = true)
    override def childKeys: IterableOnce[Int] = src.childKeys
    override def childKeySize: Int = src.childKeySize

  case class SuffixClosure(src: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = src.knownEmpty
    override def concrete: Option[TrieSpace] =
      src.concrete.map(_.suffixClosure)
    private lazy val summary = closureSummary(src)
    private lazy val keys: Vector[Int] = summary.frontierMap.keys.toVector
    private[morkl] def tailFrontiers(item: Int): Vector[SpaceZipper] =
      summary.frontierMap.getOrElse(item, Vector.empty)
    private[morkl] def allTailFrontiers: Vector[SpaceZipper] =
      summary.allTailFrontiers
    override def terminal: Boolean = false
    override def child(item: Int): SpaceZipper = FrontierState(FrontierTailUnion(this, item))
    override def childKeys: IterableOnce[Int] = keys.iterator
    override def childKeySize: Int = keys.length
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      keys.iterator.map(item => item -> child(item)).filterNot(_._2.isEmpty)

  case class TailsClosure(src: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = src.knownEmpty
    override def concrete: Option[TrieSpace] =
      src.concrete.map(_.tailsClosure)
    private lazy val suffixes: SuffixClosure = SuffixClosure(src)
    private[morkl] def tailFrontiers(item: Int): Vector[SpaceZipper] =
      suffixes.tailFrontiers(item)
    private[morkl] def allTailFrontiers: Vector[SpaceZipper] =
      suffixes.allTailFrontiers
    override def terminal: Boolean = !src.isEmpty
    override def child(item: Int): SpaceZipper = FrontierState(FrontierTailUnion(this, item))
    override def childKeys: IterableOnce[Int] = suffixes.childKeys
    override def childKeySize: Int = suffixes.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      childKeys.iterator.map(item => item -> child(item)).filterNot(_._2.isEmpty)

  case class Head(src: SpaceZipper) extends SpaceZipper:
    override def knownEmpty: Boolean = src.knownEmpty
    override def concrete: Option[TrieSpace] =
      src.concrete.map(_.head)
    override def terminal: Boolean = false
    override def child(item: Int): SpaceZipper =
      if src.hasChild(item) then epsilon else empty
    override def hasChild(item: Int): Boolean = src.hasChild(item)
    override def childKeys: IterableOnce[Int] = src.childKeys
    override def childKeySize: Int = src.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      childKeys.iterator.filter(src.hasChild).map(_ -> epsilon)
    override lazy val pathCount: Int =
      childrenIterator.length

  case class Iteration(src: SpaceZipper,
                       branch: (Int, SpaceZipper) => SpaceZipper,
                       template: Option[IterTemplateTag] = None) extends SpaceZipper:
    private val branchCache = mutable.HashMap.empty[Int, SpaceZipper]
    private val genericChildCache = mutable.HashMap.empty[Int, SpaceZipper]
    private def branchFor(head: Int): SpaceZipper =
      branchCache.getOrElseUpdate(head, {
        ExecutorCostMeter.round()
        branch(head, src.child(head))
      })
    private lazy val branchKeys: Vector[Int] =
      src.childKeys.iterator.filter(src.hasChild).toVector
    private def branchesIterator: Iterator[SpaceZipper] =
      branchKeys.iterator.map(branchFor)
    private lazy val genericTerminal: Boolean =
      branchesIterator.exists(_.terminal)
    private def genericChild(item: Int): SpaceZipper =
      genericChildCache.getOrElseUpdate(item, memo(IterationChild(branchKeys, head => branchFor(head).child(item))))
    private lazy val genericChildKeyVector: Vector[Int] =
      val keys = mutable.LinkedHashSet.empty[Int]
      branchesIterator.foreach(branch => keys ++= branch.childKeys.iterator)
      keys.toVector
    private lazy val genericChildren: Vector[(Int, SpaceZipper)] =
      genericChildKeyVector.iterator
        .map(item => item -> genericChild(item))
        .filterNot(_._2.isEmpty)
        .toVector
    private lazy val direct: Option[SpaceZipper] = template match
      case Some(IterTemplateTag.Tail) => Some(TailsUnion(src))
      case Some(IterTemplateTag.Head) => Some(Head(src))
      case Some(IterTemplateTag.Reconstruct) => Some(NonEmpty(src))
      case Some(IterTemplateTag.PrefixedReconstruct(prefix)) =>
        Some(wrap(NonEmpty(src), prefix))
      case Some(IterTemplateTag.PrefixedRangeReconstruct(prefix, start, end)) if prefix.nonEmpty =>
        val ranged =
          Iteration(
            src,
            (head, tail) => wrap(range(tail, start, end), List(head)),
            Some(IterTemplateTag.RangeReconstruct(start, end))
          )
        Some(wrap(memo(ranged), prefix))
      case _ => None

    private def rangeTailBranch(head: Int, start: Int, end: Int): SpaceZipper =
      range(src.child(head), start, end)

    private def rangeTailSummary(start: Int, end: Int): (Boolean, Vector[(Int, SpaceZipper)]) =
      var nullable = false
      val firstByKey = mutable.LinkedHashMap.empty[Int, SpaceZipper]
      val collisions = mutable.HashMap.empty[Int, mutable.ArrayBuffer[SpaceZipper]]
      branchKeys.foreach { head =>
        val ranged = rangeTailBranch(head, start, end)
        nullable ||= ranged.terminal
        ranged.childrenIterator.foreach { (item, child) =>
          firstByKey.get(item) match
            case Some(first) =>
              collisions.getOrElseUpdate(item, mutable.ArrayBuffer(first)) += child
            case None =>
              firstByKey += item -> child
        }
      }
      val children = firstByKey.iterator
        .map { (item, first) => item -> collisions.get(item).fold(first)(joinAll) }
        .filterNot(_._2.isEmpty)
        .toVector
      nullable -> children

    private def rangeReconstructChild(item: Int, start: Int, end: Int): SpaceZipper =
      if src.hasChild(item) then range(src.child(item), start, end) else empty

    private def rangeReconstructChildren(start: Int, end: Int): Vector[(Int, SpaceZipper)] =
      branchKeys.iterator
        .map(item => item -> rangeReconstructChild(item, start, end))
        .filterNot(_._2.isEmpty)
        .toVector

    private lazy val rangeTailSummaryCache: Option[(Boolean, Vector[(Int, SpaceZipper)])] = template match
      case Some(IterTemplateTag.RangeTail(start, end)) =>
        Some(rangeTailSummary(start, end))
      case _ => None

    private lazy val specializedChildren: Option[Vector[(Int, SpaceZipper)]] = template match
      case Some(IterTemplateTag.RangeTail(_, _)) =>
        rangeTailSummaryCache.map(_._2)
      case Some(IterTemplateTag.RangeReconstruct(start, end)) =>
        Some(rangeReconstructChildren(start, end))
      case Some(IterTemplateTag.PrefixedRangeReconstruct(Nil, start, end)) =>
        Some(rangeReconstructChildren(start, end))
      case _ => None

    private lazy val specializedTerminal: Option[Boolean] = template match
      case Some(IterTemplateTag.RangeTail(_, _)) =>
        rangeTailSummaryCache.map(_._1)
      case Some(IterTemplateTag.RangeReconstruct(_, _)) |
          Some(IterTemplateTag.PrefixedRangeReconstruct(Nil, _, _)) =>
        Some(false)
      case _ => None

    override def knownEmpty: Boolean = src.knownEmpty
    override def terminal: Boolean =
      direct.map(_.terminal).getOrElse(specializedTerminal.getOrElse(genericTerminal))
    override def child(item: Int): SpaceZipper =
      direct.map(_.child(item)).getOrElse(template match
        case Some(IterTemplateTag.RangeTail(start, end)) =>
          joinAll(branchKeys.iterator.map(head => rangeTailBranch(head, start, end).child(item)))
        case Some(IterTemplateTag.RangeReconstruct(start, end)) =>
          rangeReconstructChild(item, start, end)
        case Some(IterTemplateTag.PrefixedRangeReconstruct(Nil, start, end)) =>
          rangeReconstructChild(item, start, end)
        case _ =>
          genericChild(item)
      )
    override def childKeys: IterableOnce[Int] =
      direct.map(_.childKeys).getOrElse(specializedChildren match
        case Some(children) => children.iterator.map(_._1)
        case None => genericChildren.iterator.map(_._1)
      )
    override def childKeySize: Int =
      direct.map(_.childKeySize).getOrElse(specializedChildren.fold(genericChildren.length)(_.length))
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      direct.map(_.childrenIterator).getOrElse(specializedChildren.fold(genericChildren.iterator)(_.iterator))
    override lazy val pathCount: Int =
      direct.map(_.pathCount).getOrElse((if terminal then 1 else 0) + childrenIterator.map(_._2.pathCount).sum)
    override lazy val materialize: TrieSpace =
      direct.map(_.materialize).getOrElse(
        TrieSpace.joinAll(branchKeys.iterator.map(head => branchFor(head).materialize))
      )

  case class IterationChild(heads: Vector[Int], focusForHead: Int => SpaceZipper) extends SpaceZipper:
    private val focusCache = mutable.HashMap.empty[Int, SpaceZipper]
    private val childCache = mutable.HashMap.empty[Int, SpaceZipper]
    private def focus(head: Int): SpaceZipper =
      focusCache.getOrElseUpdate(head, focusForHead(head))
    private def fociIterator: Iterator[SpaceZipper] =
      heads.iterator.map(focus)
    private lazy val childKeyVector: Vector[Int] =
      val keys = mutable.LinkedHashSet.empty[Int]
      fociIterator.foreach(z => keys ++= z.childKeys.iterator)
      keys.toVector
    override def knownEmpty: Boolean =
      heads.isEmpty || fociIterator.forall(_.knownEmpty)
    override lazy val terminal: Boolean =
      fociIterator.exists(_.terminal)
    override def child(item: Int): SpaceZipper =
      childCache.getOrElseUpdate(item, memo(IterationChild(heads, head => focus(head).child(item))))
    override def childKeys: IterableOnce[Int] =
      childKeyVector.iterator
    override def childKeySize: Int =
      childKeyVector.length
    override lazy val isEmpty: Boolean =
      !terminal && childrenVector.isEmpty
    private lazy val childrenVector: Vector[(Int, SpaceZipper)] =
      childKeyVector.iterator
        .map(item => item -> child(item))
        .filterNot(_._2.isEmpty)
        .toVector
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      childrenVector.iterator
    override lazy val pathCount: Int =
      (if terminal then 1 else 0) + childrenVector.iterator.map(_._2.pathCount).sum
    override lazy val materialize: TrieSpace =
      TrieSpace.joinAll(heads.iterator.map(head => focus(head).materialize))

  /** Shared solver for the cyclic trie equations induced by
    *
    *   state = initial \/ step(state)
    *
    * A cell stores only monotone observations (nullable and candidate child
    * keys) for one demanded prefix. Re-entrant reads during a solver round see
    * the preceding approximation; newly demanded dependency cells enqueue the
    * next round. No path outside the dependency cone of the consumer is
    * materialized. */
  private final class DemandFixpointEngine(
    initial: SpaceZipper,
    step: SpaceZipper => SpaceZipper,
  ):
    private final class Cell:
      var terminal = false
      var keys = Set.empty[Int]
      var terminalDemanded = false
      var keysDemanded = false

    private val cells = mutable.LinkedHashMap.empty[Vector[Int], Cell]
    private val initialFocuses = mutable.HashMap.empty[Vector[Int], SpaceZipper]
    private var solving = false
    private var version = 0L
    private var stabilizedVersion = -1L
    private var roundStepRoot: SpaceZipper | Null = null
    private var roundTerminals = Map.empty[Vector[Int], Boolean]
    private var roundKeys = Map.empty[Vector[Int], Set[Int]]

    val root: SpaceZipper = focus(Vector.empty)

    private def descend(value: SpaceZipper, path: Vector[Int]): SpaceZipper =
      path.foldLeft(value)((current, item) => current.child(item))

    private def initialAt(path: Vector[Int]): SpaceZipper =
      initialFocuses.getOrElseUpdate(path, descend(initial, path))

    private def steppedAt(path: Vector[Int]): SpaceZipper =
      val current = roundStepRoot
      if current == null then throw IllegalStateException("demand fixpoint step requested outside a solver round")
      descend(current, path)

    private def cell(path: Vector[Int]): Cell =
      cells.getOrElseUpdate(path, {
        version += 1
        new Cell
      })

    def focus(path: Vector[Int]): DemandFixpointFocus =
      // Cells, rather than cursor wrappers, carry the shared approximation.
      // Fresh wrappers ensure inherited lazy observations such as `pathCount`
      // cannot survive into a later solver version (Range uses those
      // observations to select its border children).
      new DemandFixpointFocus(this, path)

    private def demand(path: Vector[Int], terminal: Boolean): Cell = synchronized {
      val value = cell(path)
      if terminal && !value.terminalDemanded then
        value.terminalDemanded = true
        version += 1
      else if !terminal && !value.keysDemanded then
        value.keysDemanded = true
        version += 1
      if !solving && stabilizedVersion != version then stabilize()
      value
    }

    def terminal(path: Vector[Int]): Boolean =
      val value = demand(path, terminal = true)
      if solving then roundTerminals.getOrElse(path, false) else value.terminal
    def keys(path: Vector[Int]): Set[Int] =
      val value = demand(path, terminal = false)
      if solving then roundKeys.getOrElse(path, Set.empty) else value.keys

    private def stabilize(): Unit =
      solving = true
      try
        var changed = true
        while changed do
          val before = version
          ExecutorCostMeter.round()
          // A Kleene round is synchronous: every dependency read observes the
          // same preceding approximation. This is required even for
          // inflationary fixpoints whose step contains an order-sensitive
          // operator such as Range; updating sibling cells in place would
          // otherwise make the result depend on traversal order.
          roundTerminals = cells.iterator.map((path, value) => path -> value.terminal).toMap
          roundKeys = cells.iterator.map((path, value) => path -> value.keys).toMap
          // Iteration and Memo nodes intentionally cache branch/key frontiers.
          // Rebuild the virtual step once per approximation so those caches
          // observe heads discovered by the preceding solver round.
          roundStepRoot = step(focus(Vector.empty))
          val snapshot = cells.toVector
          snapshot.foreach { (path, value) =>
            if value.terminalDemanded && !value.terminal then
              if initialAt(path).terminal || steppedAt(path).terminal then
                value.terminal = true
                version += 1
            if value.keysDemanded then
              val discovered =
                initialAt(path).childKeys.iterator.toSet ++ steppedAt(path).childKeys.iterator
              val enlarged = value.keys ++ discovered
              if enlarged.size != value.keys.size then
                value.keys = enlarged
                version += 1
          }
          changed = version != before
        stabilizedVersion = version
      finally
        roundStepRoot = null
        roundTerminals = Map.empty
        roundKeys = Map.empty
        solving = false

  private final class DemandFixpointFocus(
    engine: DemandFixpointEngine,
    path: Vector[Int],
  ) extends DeferredFixpointFocus:
    override def terminal: Boolean = engine.terminal(path)
    override def child(item: Int): SpaceZipper = engine.focus(path :+ item)
    override def childKeys: IterableOnce[Int] = engine.keys(path)
    override def knownEmpty: Boolean = false

  /** Delays an exact global iteration until a consumer actually observes the
    * result. This is intentionally separate from DemandFixpointEngine: an
    * order-sensitive or negative step can have transient outputs that a
    * prefix-only monotone cell cannot reconstruct after the fact. */
  private final class SynchronousFixpointEngine(
    src: SpaceZipper,
    step: TrieSpace => TrieSpace,
  ):
    private lazy val lowered = kleeneUnionNative(src)(step)
    val root: SpaceZipper = focus(Vector.empty)
    def focus(path: Vector[Int]): SpaceZipper = new SynchronousFixpointFocus(this, path)
    def at(path: Vector[Int]): SpaceZipper =
      path.foldLeft(lowered)((current, item) => current.child(item))

  private final class SynchronousFixpointFocus(
    engine: SynchronousFixpointEngine,
    path: Vector[Int],
  ) extends DeferredFixpointFocus:
    private def observed = engine.at(path)
    override def terminal: Boolean = observed.terminal
    // Prefix navigation itself is not an observation. In particular, source
    // Unwrap lowering can install a focused cursor without starting the exact
    // rounds during transpileZ construction.
    override def child(item: Int): SpaceZipper = engine.focus(path :+ item)
    override def hasChild(item: Int): Boolean = observed.hasChild(item)
    override def childKeys: IterableOnce[Int] = observed.childKeys
    override def childKeySize: Int = observed.childKeySize
    override def childKeySizeHint: Option[Int] = None
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = observed.childrenIterator
    override def concrete: Option[TrieSpace] = observed.concrete
    override def isEmpty: Boolean = observed.isEmpty
    override lazy val pathCount: Int = observed.pathCount
    override def materialize: TrieSpace = observed.materialize

  /** Defers the "iteration source has a head" guard used by a branch body
    * that is independent of its binders. This matters when the source itself
    * is a cyclic demand fixpoint: construction must not query the cycle. */
  case class HeadedGuard(src: SpaceZipper, value: () => SpaceZipper) extends SpaceZipper:
    private lazy val guarded = value()
    private def enabled: Boolean = src.childKeys.iterator.exists(src.hasChild)
    override def knownEmpty: Boolean = src.knownEmpty || guarded.knownEmpty
    override def terminal: Boolean = enabled && guarded.terminal
    override def child(item: Int): SpaceZipper = if enabled then guarded.child(item) else empty
    override def childKeys: IterableOnce[Int] = if enabled then guarded.childKeys else Iterator.empty
    override def childKeySizeHint: Option[Int] = guarded.childKeySizeHint

  case class Fixpoint(src: SpaceZipper, template: IterTemplateTag) extends SpaceZipper:
    private lazy val lowered: SpaceZipper = template match
      case IterTemplateTag.Tail => TailsClosure(src)
      case IterTemplateTag.Head => union(src, Head(src))
      case IterTemplateTag.Reconstruct => src
      case tag @ IterTemplateTag.RangeTail(start, end) =>
        kleeneUnion(src) { state =>
          iteration(
            state,
            (_head, tail) => range(tail, start, end),
            Some(tag)
          )
        }
      case IterTemplateTag.PrefixedReconstruct(Nil) |
          IterTemplateTag.RangeReconstruct(_, _) |
          IterTemplateTag.PrefixedRangeReconstruct(Nil, _, _) =>
        src
      case other =>
        throw UnsupportedOperationException(
          s"unsupported potentially length-growing zipper fixpoint template: $other"
        )
    override def knownEmpty: Boolean = lowered.knownEmpty
    override def concrete: Option[TrieSpace] = lowered.concrete
    override def terminal: Boolean = lowered.terminal
    override def child(item: Int): SpaceZipper = lowered.child(item)
    override def childKeys: IterableOnce[Int] = lowered.childKeys
    override def childKeySize: Int = lowered.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = lowered.childrenIterator
    override lazy val pathCount: Int = lowered.pathCount

  case class PatchChild(parent: SpaceZipper, item: Int, replacement: SpaceZipper) extends SpaceZipper:
    private lazy val original = parent.child(item)
    private lazy val hadChild = !original.isEmpty
    private lazy val hasReplacement = !replacement.isEmpty
    override def terminal: Boolean = parent.terminal
    override def child(key: Int): SpaceZipper =
      if key == item then replacement else parent.child(key)
    override def hasChild(key: Int): Boolean =
      if key == item then meteredChildProbe(!replacement.isEmpty) else parent.hasChild(key)
    override lazy val isEmpty: Boolean =
      !terminal && childKeySize == 0
    override lazy val childKeySize: Int =
      parent.childKeySize - (if hadChild then 1 else 0) + (if hasReplacement then 1 else 0)
    override def childKeys: IterableOnce[Int] =
      parent.childKeys.iterator.filter(_ != item) ++ Option.when(hasReplacement)(item).iterator
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      parent.childrenIterator.filter(_._1 != item) ++ Option.when(hasReplacement)(item -> replacement).iterator
    override lazy val orderedChildren: Array[(Int, SpaceZipper)] =
      childrenIterator.toArray.sortWith((a, b) => TrieSpace.comparePaths(a._1 :: Nil, b._1 :: Nil) < 0)
    override lazy val pathCount: Int =
      parent.pathCount - (if hadChild then original.pathCount else 0) + (if hasReplacement then replacement.pathCount else 0)

  case class Range(src: SpaceZipper, lo: Int, hi: Int) extends SpaceZipper:
    override def knownEmpty: Boolean = hi <= lo || src.knownEmpty
    override def concrete: Option[TrieSpace] =
      nativeRangeNormalized(src, lo, hi)
    override def terminal: Boolean = src.terminal && lo <= 0 && 0 < hi
    override lazy val pathCount: Int =
      (if terminal then 1 else 0) + childrenIterator.map(_._2.pathCount).sum
    private val childCache = mutable.HashMap.empty[Int, SpaceZipper]
    private lazy val sourceChildren = src.orderedChildren
    private lazy val sourceEnds = Array.fill(sourceChildren.length)(Int.MinValue)
    private var computedThrough = -1
    private var computedRank = if src.terminal then 1 else 0
    /** Extend cumulative ranks monotonically. Independent child queries share
      * this frontier, so every preceding sibling is sized at most once. */
    private def endAt(index: Int): Int = synchronized {
      while computedThrough < index do
        computedThrough += 1
        computedRank += sourceChildren(computedThrough)._2.pathCount
        sourceEnds(computedThrough) = computedRank
      sourceEnds(index)
    }
    private def childStart(index: Int): Int =
      if index == 0 then (if src.terminal then 1 else 0) else endAt(index - 1)
    private def keyIndex(item: Int): Int = src.orderedChildIndex(item, sourceChildren)
    private def selectedChild(item: Int): SpaceZipper =
      if knownEmpty then empty
      else
        val index = keyIndex(item)
        if index < 0 then empty
        else
          val start = childStart(index)
          if start >= hi then empty
          else if lo > start && endAt(index) <= lo then empty
          else rangeNormalized(sourceChildren(index)._2, (lo - start).max(0), hi - start)
    private lazy val selectedChildren: Vector[(Int, SpaceZipper)] =
      val kept = Vector.newBuilder[(Int, SpaceZipper)]
      var index = 0
      while index < sourceChildren.length && endAt(index) <= lo do index += 1
      while index < sourceChildren.length && childStart(index) < hi do
        val (item, child) = sourceChildren(index)
        val start = childStart(index)
        val end = endAt(index)
        val filtered =
          if lo <= start && end <= hi then child
          else rangeNormalized(child, (lo - start).max(0), (hi - start).min(child.pathCount))
        if !filtered.isEmpty then kept += item -> filtered
        index += 1
      kept.result()
    override def child(item: Int): SpaceZipper =
      childCache.getOrElseUpdate(item, selectedChild(item))
    override def hasChild(item: Int): Boolean =
      meteredChildProbe(!child(item).isEmpty)
    override def childKeys: IterableOnce[Int] =
      selectedChildren.iterator.map(_._1)
    override def childKeySize: Int =
      selectedChildren.length
    override def childrenIterator: Iterator[(Int, SpaceZipper)] =
      selectedChildren.iterator
    override lazy val orderedChildren: Array[(Int, SpaceZipper)] =
      selectedChildren.toArray

  case class LastRange(src: SpaceZipper, count: Int) extends SpaceZipper:
    override def knownEmpty: Boolean = count <= 0 || src.knownEmpty
    override def concrete: Option[TrieSpace] =
      nativeRange(src, -count, 0)
    private lazy val total = (if src.terminal then 1 else 0) + src.orderedChildren.iterator.map(_._2.pathCount).sum
    private lazy val selected = Range(src, (total - count).max(0), total)
    private lazy val sourceChildren = src.orderedChildren
    private val childCache = mutable.HashMap.empty[Int, SpaceZipper]
    private var suffixComputedFrom = -1
    private var suffixCount = 0
    private def countStrictlyRight(index: Int): Int = synchronized {
      if suffixComputedFrom < 0 then suffixComputedFrom = sourceChildren.length
      while suffixComputedFrom > index + 1 do
        suffixComputedFrom -= 1
        suffixCount += sourceChildren(suffixComputedFrom)._2.pathCount
      suffixCount
    }
    private def selectedChild(item: Int): SpaceZipper =
      val index = src.orderedChildIndex(item, sourceChildren)
      if index < 0 then empty
      else
        val remaining = count - countStrictlyRight(index)
        if remaining <= 0 then empty else last(sourceChildren(index)._2, remaining)
    override def terminal: Boolean = selected.terminal
    override def child(item: Int): SpaceZipper = childCache.getOrElseUpdate(item, selectedChild(item))
    override def hasChild(item: Int): Boolean = selected.hasChild(item)
    override def childKeys: IterableOnce[Int] = selected.childKeys
    override def childKeySize: Int = selected.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = selected.childrenIterator
    override lazy val orderedChildren: Array[(Int, SpaceZipper)] = selected.orderedChildren
    override lazy val pathCount: Int = selected.pathCount

  case class DropLastRange(src: SpaceZipper, count: Int) extends SpaceZipper:
    override def knownEmpty: Boolean = src.knownEmpty
    override def concrete: Option[TrieSpace] =
      nativeRange(src, 0, -count)
    private lazy val total = (if src.terminal then 1 else 0) + src.orderedChildren.iterator.map(_._2.pathCount).sum
    private lazy val selected = Range(src, 0, (total - count).max(0))
    private lazy val sourceChildren = src.orderedChildren
    private val childCache = mutable.HashMap.empty[Int, SpaceZipper]
    private var suffixComputedFrom = -1
    private var suffixCount = 0
    private def countStrictlyRight(index: Int): Int = synchronized {
      if suffixComputedFrom < 0 then suffixComputedFrom = sourceChildren.length
      while suffixComputedFrom > index + 1 do
        suffixComputedFrom -= 1
        suffixCount += sourceChildren(suffixComputedFrom)._2.pathCount
      suffixCount
    }
    private def selectedChild(item: Int): SpaceZipper =
      val index = src.orderedChildIndex(item, sourceChildren)
      if index < 0 then empty
      else
        val remaining = count - countStrictlyRight(index)
        if remaining <= 0 then sourceChildren(index)._2
        else dropLast(sourceChildren(index)._2, remaining)
    override def terminal: Boolean = selected.terminal
    override def child(item: Int): SpaceZipper = childCache.getOrElseUpdate(item, selectedChild(item))
    override def hasChild(item: Int): Boolean = selected.hasChild(item)
    override def childKeys: IterableOnce[Int] = selected.childKeys
    override def childKeySize: Int = selected.childKeySize
    override def childrenIterator: Iterator[(Int, SpaceZipper)] = selected.childrenIterator
    override lazy val orderedChildren: Array[(Int, SpaceZipper)] = selected.orderedChildren
    override lazy val pathCount: Int = selected.pathCount

trait ZipperSpaceContext:
  def resolve(sm: SpaceMention): SpaceZipper = throw RuntimeException(s"$sm zipper space mention not resolved")
  def grown(pv: Map[SpaceMention, SpaceZipper]): ZipperSpaceContext =
    throw RuntimeException("ZipperSpaceContext.grown is unsupported by this context")

case class ZipperSpaceContextMap(m: Map[SpaceMention, SpaceZipper]) extends ZipperSpaceContext:
  override def resolve(sm: SpaceMention): SpaceZipper = m(sm)
  override def grown(pv: Map[SpaceMention, SpaceZipper]): ZipperSpaceContextMap =
    ZipperSpaceContextMap(pv.iterator.foldLeft(m) { case (current, (key, value)) =>
      if key.s == "_" then current else current.updated(key, value)
    })

object ZipperSpaceContext:
  val emptyMap: ZipperSpaceContextMap = ZipperSpaceContextMap(Map.empty)
  def fromTrie(sc: TrieSpaceContextMap): ZipperSpaceContextMap =
    ZipperSpaceContextMap(sc.m.view.mapValues(SpaceZipper.traversal).toMap)
  def fromReference(sc: SpaceContextMap): ZipperSpaceContextMap =
    fromTrie(TrieSpaceContext.fromReference(sc))

def transpileZ(s: Space)(using
  pc: PathContext = PathContext.emptyMap,
  sc: ZipperSpaceContext = ZipperSpaceContext.emptyMap,
  rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
): SpaceZipper =
  val rootPc = IntPathContext.fromReference(pc, TrieSpace.interner)
  val spaceDependencyCache = java.util.IdentityHashMap[AnyRef, mutable.HashMap[(String, String), Boolean]]()
  val pathDependencyCache = java.util.IdentityHashMap[AnyRef, mutable.HashMap[(String, String), Boolean]]()

  def topLevelSelfUnion(body: Space, rp: RoutinePtr): Boolean = body match
    case Space.Union(_, Space.Call(`rp`, _, _)) => true
    case Space.Union(Space.Call(`rp`, _, _), _) => true
    case _ => false

  def containsRoutineCall(s: Space, rp: RoutinePtr): Boolean =
    def recp(p: Path): Boolean = p match
      case Path.Deref(_) | Path.Constant(_) => false
      case Path.Concat(l, r) => recp(l) || recp(r)
      case Path.GroundedPP(p, _) => recp(p)
      case Path.GroundedSP(s, _) => recs(s)
    def recs(x: Space): Boolean = x match
      case Space.Call(`rp`, _, _) => true
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => false
      case Space.Call(_, refs, mentions) => refs.exists(recp) || mentions.exists(recs)
      case Space.Singleton(p) => recp(p)
      case Space.Union(a, b) => recs(a) || recs(b)
      case Space.Intersection(a, b) => recs(a) || recs(b)
      case Space.Subtraction(a, b) => recs(a) || recs(b)
      case Space.Restriction(a, b) => recs(a) || recs(b)
      case Space.Raffination(a, b) => recs(a) || recs(b)
      case Space.Composition(a, b) => recs(a) || recs(b)
      case Space.Iteration(src, _, _, templates) => recs(src) || recs(templates)
      case Space.Fold(src, initial, _, _, _, templates, update) =>
        recs(src) || recp(initial) || recs(templates) || recp(update)
      case Space.Fixpoint(initial, _, step) => recs(initial) || recs(step)
      case Space.Wrap(src, p) => recs(src) || recp(p)
      case Space.Unwrap(src, p) => recs(src) || recp(p)
      case Space.TailsUnion(src) => recs(src)
      case Space.TailsIntersection(src) => recs(src)
      case Space.PrefixClosure(src) => recs(src)
      case Space.SuffixClosure(src) => recs(src)
      case Space.TailsClosure(src) => recs(src)
      case Space.GroundedPS(p, _) => recp(p)
      case Space.GroundedSS(src, _) => recs(src)
      case Space.Range(src, _, _) => recs(src)
    recs(s)

  def recp(x: Path)(using ipc: IntPathContext, zsc: ZipperSpaceContext): List[Int] = x match
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

  def intersectionOperands(x: Space): Vector[Space] =
    val output = Vector.newBuilder[Space]
    val pending = mutable.ArrayDeque[Space](x)
    while pending.nonEmpty do
      pending.removeHead() match
        case Space.Intersection(left, right) =>
          pending.prepend(right)
          pending.prepend(left)
        case other => output += other
    output.result()

  /** Whether an expression observes a fixpoint state at all, respecting the
    * two space binders that can shadow it. Host path callbacks may embed a
    * space expression, so path traversal is part of the check. */
  def dependsOnState(expression: Space, variable: SpaceMention): Boolean =
    def recp(path: Path, bound: Set[String]): Boolean = path match
      case Path.Deref(_) | Path.Constant(_) => false
      case Path.Concat(left, right) => recp(left, bound) || recp(right, bound)
      case Path.GroundedPP(src, _) => recp(src, bound)
      case Path.GroundedSP(src, _) => recs(src, bound)
    def recs(value: Space, bound: Set[String]): Boolean = value match
      case Space.Mention(sm) => sm.s == variable.s && !bound(variable.s)
      case Space.Empty | Space.Literal(_) => false
      case Space.Call(_, refs, mentions) =>
        refs.exists(recp(_, bound)) || mentions.exists(recs(_, bound))
      case Space.Singleton(path) => recp(path, bound)
      case Space.Union(left, right) => recs(left, bound) || recs(right, bound)
      case Space.Intersection(left, right) => recs(left, bound) || recs(right, bound)
      case Space.Subtraction(left, right) => recs(left, bound) || recs(right, bound)
      case Space.Restriction(src, prefixes) => recs(src, bound) || recs(prefixes, bound)
      case Space.Raffination(src, prefixes) => recs(src, bound) || recs(prefixes, bound)
      case Space.Composition(left, right) => recs(left, bound) || recs(right, bound)
      case Space.Iteration(src, _, rest, templates) =>
        recs(src, bound) || recs(templates, bound + rest.s)
      case Space.Fold(src, initial, _, _, rest, templates, update) =>
        recs(src, bound) || recp(initial, bound) ||
          recs(templates, bound + rest.s) || recp(update, bound)
      case Space.Fixpoint(initial, boundVariable, step) =>
        recs(initial, bound) || recs(step, bound + boundVariable.s)
      case Space.Wrap(src, prefix) => recs(src, bound) || recp(prefix, bound)
      case Space.Unwrap(src, prefix) => recs(src, bound) || recp(prefix, bound)
      case Space.TailsUnion(src) => recs(src, bound)
      case Space.TailsIntersection(src) => recs(src, bound)
      case Space.PrefixClosure(src) => recs(src, bound)
      case Space.SuffixClosure(src) => recs(src, bound)
      case Space.TailsClosure(src) => recs(src, bound)
      case Space.GroundedPS(path, _) => recp(path, bound)
      case Space.GroundedSS(src, _) => recs(src, bound)
      case Space.Range(src, _, _) => recs(src, bound)
    recs(expression, Set.empty)

  /** Structural proof obligation for DemandFixpointEngine. The admitted
    * operators are monotone in every state-dependent operand and expose
    * membership through local trie equations. Range and TailsIntersection are
    * order/cardinality-sensitive; subtraction and raffination are admitted
    * only when their negative operand is state-independent. Fold, nested
    * fixpoints, calls and host callbacks are rejected when state-dependent.
    *
    * Positivity alone is not a productivity proof: state-dependent generic
    * iteration and head-stripping projections can answer a shallow output
    * observation from a deeper state prefix. Those forms use the exact lazy
    * synchronous fallback unless an earlier dedicated template handles them. */
  def demandFixpointPositive(expression: Space, variable: SpaceMention): Boolean =
    if !dependsOnState(expression, variable) then true
    else expression match
      case Space.Mention(sm) => sm.s == variable.s
      case Space.Union(left, right) =>
        demandFixpointPositive(left, variable) && demandFixpointPositive(right, variable)
      case Space.Intersection(left, right) =>
        demandFixpointPositive(left, variable) && demandFixpointPositive(right, variable)
      case Space.Subtraction(left, right) =>
        demandFixpointPositive(left, variable) && !dependsOnState(right, variable)
      case Space.Restriction(src, prefixes) =>
        demandFixpointPositive(src, variable) && demandFixpointPositive(prefixes, variable)
      case Space.Raffination(src, prefixes) =>
        demandFixpointPositive(src, variable) && !dependsOnState(prefixes, variable)
      case Space.Composition(left, right) =>
        // Concatenation dependencies are at the same or a shorter demanded
        // path. Static/state-dependent Wrap has the same causal direction.
        demandFixpointPositive(left, variable) && demandFixpointPositive(right, variable)
      // Generic iteration binds the recursive source's tail. Even a positive
      // body can therefore answer a shallow observation from a strictly
      // deeper state focus and grow an unbounded dependency chain. Exact bare
      // Tail/Head/Reconstruct templates are selected before this predicate.
      case Space.Iteration(_, _, _, _) => false
      case Space.Wrap(src, prefix) =>
        demandFixpointPositive(src, variable) &&
          !dependsOnState(Space.Singleton(prefix), variable)
      // Unwrap(outputPrefix) asks the recursive state at a strictly deeper
      // path. DemandFixpointFocus deliberately cannot claim unknown focuses
      // empty, so even a finite result can create an unbounded dependency
      // chain (a, a.a, ...). Exact synchronous rounds are required.
      case Space.Unwrap(_, _) => false
      // These projections can answer a shallow observation only by exploring
      // arbitrarily deeper recursive focuses. A bare TailsUnion(state) is
      // handled earlier by the dedicated finite Tail template; generic nested
      // forms require exact synchronous rounds.
      case Space.TailsUnion(_) |
          Space.PrefixClosure(_) |
          Space.SuffixClosure(_) |
          Space.TailsClosure(_) => false
      case Space.Empty | Space.Literal(_) => true
      case Space.Call(_, _, _) |
          Space.Singleton(_) |
          Space.Fold(_, _, _, _, _, _, _) |
          Space.Fixpoint(_, _, _) |
          Space.TailsIntersection(_) |
          Space.GroundedPS(_, _) |
          Space.GroundedSS(_, _) |
          Space.Range(_, _, _) => false

  def recs(x: Space)(using ipc: IntPathContext, zsc: ZipperSpaceContext): SpaceZipper = x match
    case Space.Empty => SpaceZipper.empty
    case call @ Space.Call(rp, refs, mentions) =>
      val lowered = Supercompiler.lowerFixpointCalls(call, rc)
      if lowered != call then recs(lowered)
      else
        val refvs = refs.map(recp)
        val routine @ Routine(_, refns, mentionns, body) = rc(rp)
        val mentionZippers = mentions.map(recs)
        val recursive = topLevelSelfUnion(body, rp) || containsRoutineCall(body, rp)
        if recursive && !Supercompiler.wellFoundedPartitionRecursion(routine, rc) then
          throw UnsupportedOperationException(
            s"zipper transpile cannot safely lower recursive routine call ${rp.s}; " +
              "the routine is outside the union-saturating fixpoint fragment"
          )
        else
          val pctx = IntPathContextMap(Map.from(refns zip refvs))
          val sctx = ZipperSpaceContextMap(Map.from(mentionns zip mentionZippers))
          if recursive then SpaceZipper.deferredRoutineCall(() => recs(body)(using pctx, sctx))
          else recs(body)(using pctx, sctx)
    case Space.Mention(sm) => zsc.resolve(sm)
    case Space.Singleton(p) => SpaceZipper.singleton(recp(p))
    case Space.Literal(sv) => SpaceZipper.literal(sv)
    case Space.Union(x, y) => SpaceZipper.union(recs(x), recs(y))
    case Space.Intersection(x, y) =>
      val operands = intersectionOperands(x) ++ intersectionOperands(y)
      if operands.length == 2 then SpaceZipper.intersection(recs(x), recs(y))
      else
        val zippers = operands.map(recs)
        val concrete = zippers.map(SpaceZipper.storedTrie)
        if concrete.forall(_.isDefined) then SpaceZipper.traversal(TrieSpace.meetAll(concrete.flatten))
        else SpaceZipper.meetAll(zippers)
    case Space.Subtraction(x, y) => SpaceZipper.subtraction(recs(x), recs(y))
    case Space.Restriction(x, prefixes) => SpaceZipper.restriction(recs(x), recs(prefixes))
    case Space.Raffination(x, prefixes) =>
      val src = recs(x)
      SpaceZipper.subtraction(src, SpaceZipper.restriction(src, recs(prefixes)))
    case Space.Composition(x, y) => SpaceZipper.concat(recs(x), recs(y))
    case Space.Wrap(src, p) => SpaceZipper.wrap(recs(src), recp(p))
    case Space.Unwrap(src, p) => SpaceZipper.unwrap(recs(src), recp(p))
    case Space.TailsUnion(src) => SpaceZipper.TailsUnion(recs(src))
    case Space.TailsIntersection(src) => SpaceZipper.TailsIntersection(recs(src))
    case Space.PrefixClosure(src) => SpaceZipper.PrefixClosure(recs(src))
    case Space.SuffixClosure(src) => SpaceZipper.SuffixClosure(recs(src))
    case Space.TailsClosure(src) => SpaceZipper.TailsClosure(recs(src))
    case Space.Iteration(src, symbol, rest, templates) =>
      val srcZ = recs(src)
      def singletonRangeSelected(start: Int, end: Int): Boolean =
        RangeBounds.normalize(size = 1, start, end) == (0 -> 1)
      def lowerTemplate(template: Space): SpaceZipper = template match
        case Space.Empty => SpaceZipper.empty
        case Space.Mention(sm) if sm == rest =>
          SpaceZipper.TailsUnion(srcZ)
        case Space.Singleton(Path.Deref(pr)) if pr == symbol =>
          SpaceZipper.head(srcZ)
        case Space.Range(Space.Mention(sm), start, end) if sm == rest =>
          if start == 0 && end == 0 then SpaceZipper.TailsUnion(srcZ)
          else SpaceZipper.iteration(
            srcZ,
            (_head, tail) => SpaceZipper.range(tail, start, end),
            Some(SpaceZipper.IterTemplateTag.RangeTail(start, end))
          )
        case Space.Range(Space.Singleton(Path.Deref(pr)), start, end) if pr == symbol =>
          if singletonRangeSelected(start, end) then SpaceZipper.head(srcZ) else SpaceZipper.empty
        case Space.Range(Space.Wrap(Space.Mention(sm), Path.Deref(pr)), start, end) if sm == rest && pr == symbol =>
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, start, end), List(head)),
            Some(SpaceZipper.IterTemplateTag.RangeReconstruct(start, end))
          )
        case Space.Range(Space.Wrap(Space.Mention(sm), Path.Concat(prefix, Path.Deref(pr))), start, end)
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, start, end), staticPrefix ++ List(head)),
            Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(staticPrefix, start, end))
          )
        case Space.Range(Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Mention(sm)), start, end) if sm == rest && pr == symbol =>
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, start, end), List(head)),
            Some(SpaceZipper.IterTemplateTag.RangeReconstruct(start, end))
          )
        case Space.Range(Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Mention(sm)), start, end)
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, start, end), staticPrefix ++ List(head)),
            Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(staticPrefix, start, end))
          )
        case Space.Wrap(Space.Mention(sm), Path.Deref(pr)) if sm == rest && pr == symbol =>
          SpaceZipper.NonEmpty(srcZ)
        case Space.Wrap(Space.Mention(sm), Path.Concat(prefix, Path.Deref(pr))) if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(tail, staticPrefix ++ List(head)),
            Some(SpaceZipper.IterTemplateTag.PrefixedReconstruct(staticPrefix))
          )
        case Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Mention(sm)) if sm == rest && pr == symbol =>
          SpaceZipper.NonEmpty(srcZ)
        case Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Mention(sm)) if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(tail, staticPrefix ++ List(head)),
            Some(SpaceZipper.IterTemplateTag.PrefixedReconstruct(staticPrefix))
          )
        case Space.Wrap(Space.Range(Space.Mention(sm), start, end), Path.Deref(pr)) if sm == rest && pr == symbol =>
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, start, end), List(head)),
            Some(SpaceZipper.IterTemplateTag.RangeReconstruct(start, end))
          )
        case Space.Wrap(Space.Range(Space.Mention(sm), start, end), Path.Concat(prefix, Path.Deref(pr)))
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, start, end), staticPrefix ++ List(head)),
            Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(staticPrefix, start, end))
          )
        case Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Range(Space.Mention(sm), start, end)) if sm == rest && pr == symbol =>
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, start, end), List(head)),
            Some(SpaceZipper.IterTemplateTag.RangeReconstruct(start, end))
          )
        case Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Range(Space.Mention(sm), start, end))
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          SpaceZipper.iteration(
            srcZ,
            (head, tail) => SpaceZipper.wrap(SpaceZipper.range(tail, start, end), staticPrefix ++ List(head)),
            Some(SpaceZipper.IterTemplateTag.PrefixedRangeReconstruct(staticPrefix, start, end))
          )
        case _ if !spaceDependsOnBound(template, symbol, rest) =>
          SpaceZipper.whenHeaded(srcZ, recs(template))
        case Space.Union(left, right) =>
          SpaceZipper.union(lowerTemplate(left), lowerTemplate(right))
        case Space.Wrap(inner, prefix) if !pathDependsOnBound(prefix, symbol, rest) =>
          SpaceZipper.wrap(lowerTemplate(inner), recp(prefix))
        case Space.Unwrap(inner, prefix) if !pathDependsOnBound(prefix, symbol, rest) =>
          SpaceZipper.unwrap(lowerTemplate(inner), recp(prefix))
        case Space.Singleton(Path.Concat(prefix, suffix)) if !pathDependsOnBound(prefix, symbol, rest) =>
          SpaceZipper.wrap(lowerTemplate(Space.Singleton(suffix)), recp(prefix))
        case Space.Composition(left, right) if !spaceDependsOnBound(right, symbol, rest) =>
          SpaceZipper.concat(lowerTemplate(left), recs(right))
        case Space.Composition(left, right) if !spaceDependsOnBound(left, symbol, rest) =>
          SpaceZipper.concat(recs(left), lowerTemplate(right))
        case Space.Intersection(left, right) if !spaceDependsOnBound(right, symbol, rest) =>
          SpaceZipper.intersection(lowerTemplate(left), recs(right))
        case Space.Intersection(left, right) if !spaceDependsOnBound(left, symbol, rest) =>
          SpaceZipper.intersection(recs(left), lowerTemplate(right))
        case Space.Subtraction(left, right) if !spaceDependsOnBound(right, symbol, rest) =>
          SpaceZipper.subtraction(lowerTemplate(left), recs(right))
        case Space.Restriction(inner, prefixes) if !spaceDependsOnBound(prefixes, symbol, rest) =>
          SpaceZipper.restriction(lowerTemplate(inner), recs(prefixes))
        case Space.Raffination(inner, prefixes) if !spaceDependsOnBound(prefixes, symbol, rest) =>
          val selected = lowerTemplate(inner)
          SpaceZipper.subtraction(selected, SpaceZipper.restriction(selected, recs(prefixes)))
        case Space.TailsUnion(Space.Wrap(Space.Mention(sm), Path.Concat(prefix, Path.Deref(pr))))
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          SpaceZipper.TailsUnion(SpaceZipper.wrap(SpaceZipper.NonEmpty(srcZ), recp(prefix)))
        case Space.TailsUnion(Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Mention(sm)))
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          SpaceZipper.TailsUnion(SpaceZipper.wrap(SpaceZipper.NonEmpty(srcZ), recp(prefix)))
        case Space.TailsUnion(inner) =>
          SpaceZipper.TailsUnion(lowerTemplate(inner))
        case Space.PrefixClosure(inner) =>
          SpaceZipper.PrefixClosure(lowerTemplate(inner))
        case Space.SuffixClosure(inner) =>
          SpaceZipper.SuffixClosure(lowerTemplate(inner))
        case Space.TailsClosure(inner) =>
          SpaceZipper.TailsClosure(lowerTemplate(inner))
        case _ =>
          SpaceZipper.iteration(srcZ, (head, tail) =>
            recs(template)(using
              ipc.grown(Map(symbol -> TrieSpace.singletonItemPath(head))),
              zsc.grown(Map(rest -> tail))
            )
          )
      lowerTemplate(templates)
    case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
      var accValue = recp(initial)
      val out = Vector.newBuilder[SpaceZipper]
      for (head, tail) <- recs(src).orderedChildren do
        ExecutorCostMeter.round()
        val pctx = ipc.grown(Map(acc -> accValue, symbol -> TrieSpace.singletonItemPath(head)))
        val sctx = zsc.grown(Map(rest -> tail))
        out += recs(templates)(using pctx, sctx)
        accValue = recp(update)(using pctx, sctx)
      SpaceZipper.joinAll(out.result())
    case Space.Fixpoint(initial, variable, step) =>
      val initialZ = recs(initial)
      def fixpointIterationTag(step: Space): Option[SpaceZipper.IterTemplateTag] = step match
        case Space.TailsUnion(Space.Mention(sm)) if sm == variable =>
          Some(SpaceZipper.IterTemplateTag.Tail)
        case Space.Iteration(Space.Mention(sm), symbol, rest, template) if sm == variable =>
          template match
            case Space.Mention(tm) if tm == rest =>
              Some(SpaceZipper.IterTemplateTag.Tail)
            case Space.Singleton(Path.Deref(pr)) if pr == symbol =>
              Some(SpaceZipper.IterTemplateTag.Head)
            case Space.Wrap(Space.Mention(tm), Path.Deref(pr)) if tm == rest && pr == symbol =>
              Some(SpaceZipper.IterTemplateTag.Reconstruct)
            case Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Mention(tm)) if tm == rest && pr == symbol =>
              Some(SpaceZipper.IterTemplateTag.Reconstruct)
            case Space.Range(Space.Mention(tm), 0, 0) if tm == rest =>
              Some(SpaceZipper.IterTemplateTag.Tail)
            case Space.Range(Space.Mention(tm), start, end) if tm == rest =>
              Some(SpaceZipper.IterTemplateTag.RangeTail(start, end))
            case Space.Range(Space.Wrap(Space.Mention(tm), Path.Deref(pr)), start, end) if tm == rest && pr == symbol =>
              Some(SpaceZipper.IterTemplateTag.RangeReconstruct(start, end))
            case Space.Range(Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Mention(tm)), start, end) if tm == rest && pr == symbol =>
              Some(SpaceZipper.IterTemplateTag.RangeReconstruct(start, end))
            case Space.Wrap(Space.Range(Space.Mention(tm), start, end), Path.Deref(pr)) if tm == rest && pr == symbol =>
              Some(SpaceZipper.IterTemplateTag.RangeReconstruct(start, end))
            case Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Range(Space.Mention(tm), start, end)) if tm == rest && pr == symbol =>
              Some(SpaceZipper.IterTemplateTag.RangeReconstruct(start, end))
            case _ =>
              None
        case _ =>
          None

      step match
        case Space.Mention(sm) if sm == variable =>
          initialZ
        case _ =>
          fixpointIterationTag(step) match
            case Some(tag) =>
              SpaceZipper.fixpoint(initialZ, tag)
            case None =>
              val lowerStep = (state: SpaceZipper) =>
                recs(step)(using ipc, zsc.grown(Map(variable -> state)))
              if demandFixpointPositive(step, variable) then
                SpaceZipper.fixpoint(initialZ)(lowerStep)
              else
                (ipc, zsc) match
                  case (IntPathContextMap(paths), ZipperSpaceContextMap(spaces)) =>
                    val nativePaths = PathContextMap(paths.view.mapValues(TrieSpace.decode).toMap)
                    lazy val nativeSpaces = TrieSpaceContextMap(
                      spaces.view.mapValues(_.materialize).toMap
                    )
                    SpaceZipper.synchronousFixpointNative(initialZ) { state =>
                      evalTrie(step)(using
                        nativePaths,
                        nativeSpaces.grown(Map(variable -> state)),
                        rc,
                      )
                    }
                  case _ => SpaceZipper.synchronousFixpoint(initialZ)(lowerStep)
    case Space.GroundedPS(p, f) => SpaceZipper.literal(f(TrieSpace.decode(recp(p))))
    case Space.GroundedSS(src, f) => SpaceZipper.literal(f(recs(src).toSpaceValue))
    case Space.Range(x, start, end) => SpaceZipper.range(recs(x), start, end)

  recs(s)(using rootPc, sc)

def evalZ(s: Space)(using
  pc: PathContext = PathContext.emptyMap,
  sc: ZipperSpaceContext = ZipperSpaceContext.emptyMap,
  rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
): TrieSpace =
  transpileZ(s).materialize

def evalZValue(s: Space)(using
  pc: PathContext = PathContext.emptyMap,
  sc: ZipperSpaceContext = ZipperSpaceContext.emptyMap,
  rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
): SpaceValue =
  evalZ(s).toSpaceValue

def execZ(s: Space)(using
  pc: PathContext = PathContext.emptyMap,
  sc: ZipperSpaceContext = ZipperSpaceContext.emptyMap,
  rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
): TrieSpace =
  evalZ(s)
