import scala.collection.immutable.{IntMap, TrieIntMapOps}
import scala.collection.mutable

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
    val n = mutable.Map.from(m)
    pv.foreachEntry((k, v) =>
      if k.s != "_" then n.update(k, v)
    )
    IntPathContextMap(n.toMap)

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

  def orderedChildren: Array[(Int, TrieSpace)] =
    childrenInPathOrder

  def isEmpty: Boolean = !terminal && children.isEmpty

  def contains(p: PathValue): Boolean = containsItems(TrieSpace.intern(p))

  def containsItems(items: List[Int]): Boolean = items match
    case Nil => terminal
    case h :: t => children.get(h).exists(_.containsItems(t))

  def subtree(prefix: PathValue): Option[TrieSpace] = subtreeItems(TrieSpace.intern(prefix))

  def subtreeItems(items: List[Int]): Option[TrieSpace] = items match
    case Nil => Some(this)
    case h :: t => children.get(h).flatMap(_.subtreeItems(t))

  def insert(p: PathValue): TrieSpace = insertItems(TrieSpace.intern(p))

  def insertItems(items: List[Int]): TrieSpace = items match
    case Nil => TrieSpace.node(terminal = true, children)
    case h :: t =>
      val child = children.getOrElse(h, TrieSpace.empty).insertItems(t)
      TrieSpace.node(terminal, children.updated(h, child))

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

  def union(that: TrieSpace): TrieSpace =
    if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then this
    else if this.isEmpty then that
    else if that.isEmpty then this
    else
      TrieSpace.node(terminal || that.terminal,
        TrieIntMapOps.unionTries(children, that.children))

  infix def |(that: TrieSpace): TrieSpace = union(that)

  def intersect(that: TrieSpace): TrieSpace =
    if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then this
    else if this.isEmpty || that.isEmpty then TrieSpace.empty
    else
      TrieSpace.node(terminal && that.terminal,
        TrieIntMapOps.intersectTries(children, that.children))

  infix def &(that: TrieSpace): TrieSpace = intersect(that)

  def diff(that: TrieSpace): TrieSpace =
    if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then TrieSpace.empty
    else if this.isEmpty || that.isEmpty then this
    else
      TrieSpace.node(terminal && !that.terminal,
        TrieIntMapOps.diffTries(children, that.children))

  infix def -(that: TrieSpace): TrieSpace = diff(that)

  def prefix(item: Int): TrieSpace =
    if isEmpty then TrieSpace.empty
    else TrieSpace.node(terminal = false, IntMap(item -> this))

  def prepend(prefix: List[Int]): TrieSpace =
    prefix.foldRight(this)((item, acc) => acc.prefix(item))

  def wrap(prefix: PathValue): TrieSpace = prepend(TrieSpace.intern(prefix))
  def wrapItems(prefix: List[Int]): TrieSpace = prepend(prefix)

  def unwrap(prefix: PathValue): TrieSpace = subtree(prefix).getOrElse(TrieSpace.empty)
  def unwrapItems(prefix: List[Int]): TrieSpace = subtreeItems(prefix).getOrElse(TrieSpace.empty)

  def restrictBy(prefixes: TrieSpace): TrieSpace =
    if isEmpty || prefixes.isEmpty then TrieSpace.empty
    else if prefixes.terminal then this
    else
      TrieSpace.node(terminal = false,
        TrieIntMapOps.restrictTries(children, prefixes.children))

  def raffinate(prefixes: TrieSpace): TrieSpace = diff(restrictBy(prefixes))

  def concat(that: TrieSpace): TrieSpace =
    if isEmpty || that.isEmpty then TrieSpace.empty
    else
      val fromTerminal = if terminal then that else TrieSpace.empty
      val fromChildren = children.iterator.map { (item, child) => child.concat(that).prefix(item) }
      TrieSpace.joinAll(fromTerminal +: fromChildren.toVector)

  def tailsUnion: TrieSpace = TrieSpace.joinAll(children.valuesIterator)

  def tailsIntersection: TrieSpace =
    if children.isEmpty then TrieSpace.empty
    else TrieSpace.meetAll(children.values)

  def nonEmptyPaths: TrieSpace =
    if terminal then TrieSpace.node(terminal = false, children) else this

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
    else
      val wholeNonEmpty = TrieSpace.node(terminal = false, children)
      val childSuffixes = TrieSpace.joinAll(children.valuesIterator.map(_.suffixClosure))
      wholeNonEmpty.union(childSuffixes)

  def tailsClosure: TrieSpace =
    if isEmpty then TrieSpace.empty
    else
      val suffixes = suffixClosure
      TrieSpace.node(terminal = true, suffixes.children)

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
    var rank = 0
    var keepTerminal = false
    val kept = Vector.newBuilder[(Int, TrieSpace)]
    if terminal then
      keepTerminal = start <= 0 && 0 < end
      rank = 1

    val it = childrenInPathOrder.iterator
    var done = false
    while !done && it.hasNext do
      val (item, child) = it.next()
      val childStart = rank
      val childEnd = rank + child.pathCount
      if childStart >= end then done = true
      else if childEnd <= start then rank = childEnd
      else
        val filtered =
          if start <= childStart && childEnd <= end then child
          else child.slice((start - childStart).max(0), (end - childStart).min(child.pathCount))
        if !filtered.isEmpty then kept += item -> filtered
        rank = childEnd
    TrieSpace.node(keepTerminal, IntMap.from(kept.result()))

  private def takeLast(count: Int): TrieSpace =
    if count <= 0 then TrieSpace.empty
    else
      var remaining = count
      val kept = Vector.newBuilder[(Int, TrieSpace)]
      val it = childrenInPathOrder.reverseIterator
      while remaining > 0 && it.hasNext do
        val (item, child) = it.next()
        val childCount = child.pathCount
        if childCount <= remaining then
          kept += item -> child
          remaining -= childCount
        else
          val filtered = child.takeLast(remaining)
          if !filtered.isEmpty then kept += item -> filtered
          remaining = 0
      val keepTerminal = terminal && remaining > 0
      TrieSpace.node(keepTerminal, IntMap.from(kept.result()))

  private def dropLast(count: Int): TrieSpace =
    if count <= 0 then this
    else
      var remaining = count
      val kept = Vector.newBuilder[(Int, TrieSpace)]
      val it = childrenInPathOrder.reverseIterator
      while it.hasNext do
        val (item, child) = it.next()
        if remaining <= 0 then kept += item -> child
        else
          val childCount = child.pathCount
          if childCount <= remaining then remaining -= childCount
          else
            val filtered = child.dropLast(remaining)
            if !filtered.isEmpty then kept += item -> filtered
            remaining = 0
      val keepTerminal = terminal && remaining <= 0
      TrieSpace.node(keepTerminal, IntMap.from(kept.result()))

object TrieSpace:
  import PathItemOrder.given

  val interner: PathItemInterner = PathItemInterner.global
  val empty: TrieSpace = TrieSpace(terminal = false, IntMap.empty, pathCount = 0, nodeCount = 1, childCount = 0)
  val epsilon: TrieSpace = TrieSpace(terminal = true, IntMap.empty, pathCount = 1, nodeCount = 1, childCount = 0)

  def intern(p: PathValue): List[Int] = interner.encode(p)
  def internItems(items: List[PathItem]): List[Int] = interner.encodeItems(items)
  def decode(items: Iterable[Int]): PathValue = interner.decodePath(items)
  def comparePaths(a: Iterable[Int], b: Iterable[Int]): Int = interner.comparePaths(a, b)
  def item(id: Int): PathItem = interner.decodeItem(id)

  private val singletonItemPaths = mutable.HashMap.empty[Int, List[Int]]
  def singletonItemPath(item: Int): List[Int] =
    singletonItemPaths.getOrElseUpdate(item, item :: Nil)

  def prefixes(path: List[Int]): Vector[List[Int]] =
    path.indices.map(i => path.take(i + 1)).toVector

  def postfixes(path: List[Int]): Vector[List[Int]] =
    path.indices.map(i => path.drop(i)).toVector

  private[morkl] def node(terminal: Boolean, children: IntMap[TrieSpace]): TrieSpace =
    var paths = if terminal then 1 else 0
    var nodes = 1
    var childCount = 0
    var hasEmptyChild = false
    children.valuesIterator.foreach { child =>
      if child.isEmpty then hasEmptyChild = true
      else
        paths += child.pathCount
        nodes += child.nodeCount
        childCount += 1
    }
    if !terminal && childCount == 0 then empty
    else
      val kept = if hasEmptyChild then children.filterNot(_._2.isEmpty) else children
      TrieSpace(terminal, kept, paths, nodes, childCount)

  def singleton(p: PathValue): TrieSpace = empty.insert(p)

  def fromSpaceValue(sv: SpaceValue): TrieSpace = fromPaths(sv.paths)

  def fromPaths(paths: Iterable[PathValue]): TrieSpace =
    paths.foldLeft(empty)(_.insert(_))

  def fromEncodedPaths(paths: Iterable[List[Int]]): TrieSpace =
    paths.foldLeft(empty)(_.insertItems(_))

  def joinAll(xs: IterableOnce[TrieSpace]): TrieSpace =
    val tries = xs.iterator.filterNot(_.isEmpty).toVector
    if tries.isEmpty then empty
    else if tries.length == 1 then tries.head
    else
      var terminal = false
      val buckets = mutable.HashMap.empty[Int, mutable.ArrayBuffer[TrieSpace]]
      tries.foreach { trie =>
        terminal ||= trie.terminal
        trie.children.foreach { (key, child) =>
          buckets.getOrElseUpdate(key, mutable.ArrayBuffer.empty) += child
        }
      }
      val childPairs = buckets.iterator.map { (key, bucket) =>
        key -> joinAll(bucket)
      }
      node(terminal, IntMap.from(childPairs))

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

  case class Cursor(root: TrieSpace, prefix: Vector[Int] = Vector.empty):
    def focus: TrieSpace = root.subtreeItems(prefix.toList).getOrElse(empty)
    def down(item: PathItem): Option[Cursor] =
      down(interner.intern(item))
    def down(item: Int): Option[Cursor] =
      if focus.children.contains(item) then Some(copy(prefix = prefix :+ item)) else None
    def up: Option[Cursor] =
      Option.when(prefix.nonEmpty)(copy(prefix = prefix.dropRight(1)))
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
                     parentTerminal: Boolean,
                     siblings: IntMap[TrieSpace]) extends ZipperContext:
      override def path: Vector[Int] = parent.path :+ item
      override def plug(focus: TrieSpace): TrieSpace =
        val children =
          if focus.isEmpty then siblings
          else siblings.updated(item, focus)
        parent.plug(TrieSpace.node(parentTerminal, children))
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
          ZipperContext.Frame(context, item, focus.terminal, focus.children.removed(item))
        )
      }

    def descend(path: PathValue): Option[Zipper] =
      descendItems(intern(path))

    def descendItems(items: Iterable[Int]): Option[Zipper] =
      items.foldLeft(Option(this))((cursor, item) => cursor.flatMap(_.down(item)))

    def up: Option[Zipper] = context match
      case ZipperContext.Root => None
      case ZipperContext.Frame(parent, item, parentTerminal, siblings) =>
        val children =
          if focus.isEmpty then siblings
          else siblings.updated(item, focus)
        Some(Zipper(TrieSpace.node(parentTerminal, children), parent))

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
        Zipper(child, ZipperContext.Frame(context, item, focus.terminal, focus.children.removed(item)))
      )

    def nextSibling: Option[Zipper] =
      sibling(delta = 1)

    def previousSibling: Option[Zipper] =
      sibling(delta = -1)

    private def sibling(delta: Int): Option[Zipper] = context match
      case ZipperContext.Root => None
      case ZipperContext.Frame(parent, item, parentTerminal, siblings) =>
        val parentChildren =
          if focus.isEmpty then siblings
          else siblings.updated(item, focus)
        val ordered = parentChildren.iterator.toArray
          .sortWith((a, b) => TrieSpace.interner.compareItemIds(a._1, b._1) < 0)
        val index = ordered.indexWhere(_._1 == item)
        val anchor =
          if index >= 0 then index
          else ordered.indexWhere((key, _) => TrieSpace.interner.compareItemIds(item, key) < 0) match
            case -1 => ordered.length
            case insertion => insertion
        val nextIndex = if index >= 0 then index + delta else if delta > 0 then anchor else anchor - 1
        Option.when(nextIndex >= 0 && nextIndex < ordered.length) {
          val (nextItem, nextFocus) = ordered(nextIndex)
          Zipper(
            nextFocus,
            ZipperContext.Frame(parent, nextItem, parentTerminal, parentChildren.removed(nextItem))
          )
        }

trait TrieSpaceContext:
  def resolve(sm: SpaceMention): TrieSpace = throw RuntimeException(s"$sm trie space mention not resolved")
  def grown(pv: Map[SpaceMention, TrieSpace]): TrieSpaceContext =
    throw RuntimeException("TrieSpaceContext.grown is unsupported by this context")

case class TrieSpaceContextMap(m: Map[SpaceMention, TrieSpace]) extends TrieSpaceContext:
  override def resolve(sm: SpaceMention): TrieSpace = m(sm)
  override def grown(pv: Map[SpaceMention, TrieSpace]): TrieSpaceContextMap =
    val n = collection.mutable.Map.from(m)
    pv.foreachEntry((k, v) =>
      if k.s != "_" then n.update(k, v)
    )
    TrieSpaceContextMap(n.toMap)

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

  def recp(x: Path)(using ipc: IntPathContext, tsc: TrieSpaceContext): List[Int] = x match
    case Path.Deref(pr) => ipc.resolve(pr)
    case Path.Constant(pi) => TrieSpace.intern(pi)
    case Path.Concat(l, r) => recp(l) ++ recp(r)
    case Path.GroundedPP(p, f) => TrieSpace.intern(f(TrieSpace.decode(recp(p))))
    case Path.GroundedSP(s, f) => TrieSpace.intern(f(recs(s).toSpaceValue))

  def spaceDependsOnBound(s: Space, symbol: PathRef, rest: SpaceMention): Boolean =
    val (spaces, paths) = collect(s)(
      spre = { case Space.Mention(sm) if sm.s == rest.s => () },
      ppre = { case Path.Deref(pr) if pr.s == symbol.s => () },
    )
    spaces.nonEmpty || paths.nonEmpty

  def pathDependsOnBound(p: Path, symbol: PathRef, rest: SpaceMention): Boolean =
    val (spaces, paths) = collect(Space.Singleton(p))(
      spre = { case Space.Mention(sm) if sm.s == rest.s => () },
      ppre = { case Path.Deref(pr) if pr.s == symbol.s => () },
    )
    spaces.nonEmpty || paths.nonEmpty

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
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).wrapItems(staticPrefix ++ TrieSpace.singletonItemPath(h))))
        case Space.Range(Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Mention(sm)), start, end) if sm == rest && pr == symbol =>
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h)))
        case Space.Range(Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Mention(sm)), start, end)
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).wrapItems(staticPrefix ++ TrieSpace.singletonItemPath(h))))
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
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).wrapItems(staticPrefix ++ TrieSpace.singletonItemPath(h))))
        case Space.Composition(Space.Singleton(Path.Deref(pr)), Space.Range(Space.Mention(sm), start, end)) if sm == rest && pr == symbol =>
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).prefix(h)))
        case Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Range(Space.Mention(sm), start, end))
            if sm == rest && pr == symbol && !pathDependsOnBound(prefix, symbol, rest) =>
          val staticPrefix = recp(prefix)
          TrieSpace.joinAll(srcTrie.children.iterator.map((h, tail) => tail.range(start, end).wrapItems(staticPrefix ++ TrieSpace.singletonItemPath(h))))
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
            recs(template)(using ipc.grown(Map(symbol -> TrieSpace.singletonItemPath(h))), tsc.grown(Map(rest -> tail)))
          })
      evalTemplate(templates)
    case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
      var accValue = recp(initial)
      val out = Vector.newBuilder[TrieSpace]
      for (h, tail) <- recs(src).orderedChildren do
        val pctx = ipc.grown(Map(acc -> accValue, symbol -> List(h)))
        val sctx = tsc.grown(Map(rest -> tail))
        out += recs(templates)(using pctx, sctx)
        accValue = evalTriePath(update)(using pctx, sctx, rc)
      TrieSpace.joinAll(out.result())
    case Space.Fixpoint(initial, variable, step) =>
      var current = recs(initial)
      var changed = true
      while changed do
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
        case "space" => s(c) = op match
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
        op match
          case "Routine" => throw IllegalStateException("Nested Routine subgraphs are not executable without an explicit Call node")
          case "Iteration" =>
            val outputs = Vector.newBuilder[TrieSpace]
            val frame = new Array[PathValue | TrieSpace | Null](sg.nodes.length)
            for (h, tail) <- inputs(0).sget.children do
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
        case "space" => s(c) = op match
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
        op match
          case "Routine" => throw IllegalStateException("Nested Routine subgraphs are not executable without an explicit Call node")
          case "Iteration" =>
            val outputs = Vector.newBuilder[TrieSpace]
            val frame = new Array[List[Int] | TrieSpace | Null](sg.nodes.length)
            for (h, tail) <- inputs(0).sget.children do
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
              frame(0) = current
              stack.push(frame)
              execT(sg, stack, index)
              stack.pop()
              val next = current.union(frame.last.asInstanceOf[TrieSpace])
              changed = next != current
              current = next
            s(c) = current
    c += 1
