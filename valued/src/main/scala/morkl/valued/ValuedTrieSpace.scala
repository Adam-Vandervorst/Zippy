package morkl.valued

import morkl.{PathItem, PathValue, TrieSpace}
import scala.collection.immutable.IntMap

trait MergeLattice[V]:
  def join(left: V, right: V): V
  def meet(left: V, right: V): V

final case class ValuedTrieSpace[V] private (
  terminal: Option[V],
  children: IntMap[ValuedTrieSpace[V]]
):
  private lazy val childrenInPathOrder: Array[(Int, ValuedTrieSpace[V])] =
    children.iterator.toArray.sortWith((a, b) => TrieSpace.interner.compareItemIds(a._1, b._1) < 0)

  def orderedChildren: Array[(Int, ValuedTrieSpace[V])] =
    childrenInPathOrder

  def isEmpty: Boolean = terminal.isEmpty && children.isEmpty

  def lookup(path: PathValue): Option[V] =
    lookupItems(TrieSpace.intern(path))

  def lookupItems(items: List[Int]): Option[V] = items match
    case Nil => terminal
    case head :: tail => children.get(head).flatMap(_.lookupItems(tail))

  def put(path: PathValue, value: V)(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    putItems(TrieSpace.intern(path), value)

  def putItems(items: List[Int], value: V)(using lattice: MergeLattice[V]): ValuedTrieSpace[V] = items match
    case Nil =>
      ValuedTrieSpace.node(terminal = terminal.fold(Some(value))(existing => Some(lattice.join(existing, value))), children)
    case head :: tail =>
      val child = children.getOrElse(head, ValuedTrieSpace.empty[V]).putItems(tail, value)
      ValuedTrieSpace.node(terminal, children.updated(head, child))

  def toMap: Map[PathValue, V] =
    encodedEntries.iterator.map((items, value) => TrieSpace.decode(items) -> value).toMap

  def union(that: ValuedTrieSpace[V])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then this
    else if isEmpty then that
    else if that.isEmpty then this
    else
      val mergedTerminal = (terminal, that.terminal) match
        case (Some(left), Some(right)) => Some(lattice.join(left, right))
        case (Some(value), None) => Some(value)
        case (None, Some(value)) => Some(value)
        case (None, None) => None
      ValuedTrieSpace.node(mergedTerminal, mergeChildren(that) { (left, right) =>
        left.union(right)
      })

  infix def |(that: ValuedTrieSpace[V])(using MergeLattice[V]): ValuedTrieSpace[V] =
    union(that)

  def intersect(that: ValuedTrieSpace[V])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then this
    else if isEmpty || that.isEmpty then ValuedTrieSpace.empty[V]
    else
      val mergedTerminal = for
        left <- terminal
        right <- that.terminal
      yield lattice.meet(left, right)
      val kept =
        children.iterator.flatMap { (key, child) =>
          that.children.get(key).map(other => key -> child.intersect(other))
        }
      ValuedTrieSpace.node(mergedTerminal, IntMap.from(kept))

  infix def &(that: ValuedTrieSpace[V])(using MergeLattice[V]): ValuedTrieSpace[V] =
    intersect(that)

  def diff(that: ValuedTrieSpace[V]): ValuedTrieSpace[V] =
    if this.asInstanceOf[AnyRef] eq that.asInstanceOf[AnyRef] then ValuedTrieSpace.empty[V]
    else if isEmpty || that.isEmpty then this
    else
      val keptTerminal = if that.terminal.isDefined then None else terminal
      val kept =
        children.iterator.map { (key, child) =>
          val filtered = that.children.get(key).fold(child)(child.diff)
          key -> filtered
        }
      ValuedTrieSpace.node(keptTerminal, IntMap.from(kept))

  infix def -(that: ValuedTrieSpace[V]): ValuedTrieSpace[V] =
    diff(that)

  def child(item: PathItem): ValuedTrieSpace[V] =
    childItem(TrieSpace.interner.intern(item))

  def childItem(item: Int): ValuedTrieSpace[V] =
    children.getOrElse(item, ValuedTrieSpace.empty[V])

  def wrap(prefix: PathValue): ValuedTrieSpace[V] =
    wrapItems(TrieSpace.intern(prefix))

  def wrapItems(prefix: List[Int]): ValuedTrieSpace[V] =
    prefix.foldRight(this) { (item, acc) =>
      ValuedTrieSpace.node(None, IntMap(item -> acc))
    }

  def unwrap(prefix: PathValue): ValuedTrieSpace[V] =
    unwrapItems(TrieSpace.intern(prefix))

  def unwrapItems(prefix: List[Int]): ValuedTrieSpace[V] = prefix match
    case Nil => this
    case head :: tail => children.get(head).fold(ValuedTrieSpace.empty[V])(_.unwrapItems(tail))

  def concat(that: ValuedTrieSpace[V])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    if isEmpty || that.isEmpty then ValuedTrieSpace.empty[V]
    else
      var out = ValuedTrieSpace.empty[V]
      for
        (leftPath, leftValue) <- encodedEntries
        (rightPath, rightValue) <- that.encodedEntries
      do out = out.putItems(leftPath ++ rightPath, lattice.join(leftValue, rightValue))
      out

  def restrictBy(prefixes: ValuedTrieSpace[V])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    if isEmpty || prefixes.isEmpty then ValuedTrieSpace.empty[V]
    else
      encodedEntries.foldLeft(ValuedTrieSpace.empty[V]) { case (acc, (path, value)) =>
        if prefixes.encodedEntries.exists((prefix, _) => path.startsWith(prefix)) then acc.putItems(path, value)
        else acc
      }

  def raffinate(prefixes: ValuedTrieSpace[V])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    diff(restrictBy(prefixes))

  def tailsUnion(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    ValuedTrieSpace.joinAll(children.valuesIterator)

  def tailsIntersection(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    if children.isEmpty then ValuedTrieSpace.empty[V]
    else ValuedTrieSpace.meetAll(children.valuesIterator)

  def nonEmptyPaths: ValuedTrieSpace[V] =
    ValuedTrieSpace.node(None, children)

  def head(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    children.iterator.foldLeft(ValuedTrieSpace.empty[V]) { case (acc, (item, child)) =>
      val values = child.encodedEntries.map(_._2)
      if values.isEmpty then acc
      else acc.putItems(item :: Nil, values.reduce(lattice.join))
    }

  def prefixClosure(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    encodedEntries.foldLeft(ValuedTrieSpace.empty[V]) { case (acc, (path, value)) =>
      path.indices.foldLeft(acc) { (next, i) =>
        next.putItems(path.take(i + 1), value)
      }
    }

  def suffixClosure(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    encodedEntries.foldLeft(ValuedTrieSpace.empty[V]) { case (acc, (path, value)) =>
      path.indices.foldLeft(acc) { (next, i) =>
        next.putItems(path.drop(i), value)
      }
    }

  def tailsClosure(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    if isEmpty then ValuedTrieSpace.empty[V]
    else suffixClosure.putItems(Nil, encodedEntries.map(_._2).reduce(lattice.join))

  private def encodedEntries: Vector[(List[Int], V)] =
    val out = Vector.newBuilder[(List[Int], V)]
    def rec(node: ValuedTrieSpace[V], prefix: List[Int]): Unit =
      node.terminal.foreach(value => out += prefix.reverse -> value)
      node.children.foreach { (item, child) => rec(child, item :: prefix) }
    rec(this, Nil)
    out.result()

  private def mergeChildren(that: ValuedTrieSpace[V])(merge: (ValuedTrieSpace[V], ValuedTrieSpace[V]) => ValuedTrieSpace[V]): IntMap[ValuedTrieSpace[V]] =
    val keys = children.keySet ++ that.children.keySet
    IntMap.from(keys.iterator.map { key =>
      val left = children.getOrElse(key, ValuedTrieSpace.empty[V])
      val right = that.children.getOrElse(key, ValuedTrieSpace.empty[V])
      key -> merge(left, right)
    })

object ValuedTrieSpace:
  def empty[V]: ValuedTrieSpace[V] =
    ValuedTrieSpace(None, IntMap.empty)

  private[morkl] def node[V](terminal: Option[V], children: IntMap[ValuedTrieSpace[V]]): ValuedTrieSpace[V] =
    val kept =
      if children.valuesIterator.exists(_.isEmpty) then children.filterNot(_._2.isEmpty)
      else children
    if terminal.isEmpty && kept.isEmpty then empty[V]
    else ValuedTrieSpace(terminal, kept)

  def singleton[V](path: PathValue, value: V)(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    empty[V].put(path, value)

  def fromEntries[V](entries: Iterable[(PathValue, V)])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    entries.foldLeft(empty[V]) { case (acc, (path, value)) => acc.put(path, value) }

  def joinAll[V](tries: IterableOnce[ValuedTrieSpace[V]])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    tries.iterator.foldLeft(empty[V])(_ union _)

  def meetAll[V](tries: IterableOnce[ValuedTrieSpace[V]])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] =
    val it = tries.iterator
    if !it.hasNext then empty[V]
    else
      var out = it.next()
      while it.hasNext do out = out.intersect(it.next())
      out

  sealed trait ZipperContext[V]:
    def path: Vector[Int]
    def plug(focus: ValuedTrieSpace[V]): ValuedTrieSpace[V]
    def isRoot: Boolean

  object ZipperContext:
    final case class Root[V]() extends ZipperContext[V]:
      override val path: Vector[Int] = Vector.empty
      override def plug(focus: ValuedTrieSpace[V]): ValuedTrieSpace[V] = focus
      override val isRoot: Boolean = true

    final case class Frame[V](
      parent: ZipperContext[V],
      item: Int,
      parentTerminal: Option[V],
      siblings: IntMap[ValuedTrieSpace[V]]
    ) extends ZipperContext[V]:
      override def path: Vector[Int] = parent.path :+ item
      override def plug(focus: ValuedTrieSpace[V]): ValuedTrieSpace[V] =
        val children =
          if focus.isEmpty then siblings
          else siblings.updated(item, focus)
        parent.plug(ValuedTrieSpace.node(parentTerminal, children))
      override val isRoot: Boolean = false

  final case class Zipper[V](
    focus: ValuedTrieSpace[V],
    context: ZipperContext[V] = ZipperContext.Root[V]()
  ):
    def path: Vector[Int] = context.path
    def pathValue: PathValue = TrieSpace.decode(path)
    def whole: ValuedTrieSpace[V] = context.plug(focus)
    def atRoot: Boolean = context.isRoot

    def down(item: PathItem): Option[Zipper[V]] =
      down(TrieSpace.interner.intern(item))

    def down(item: Int): Option[Zipper[V]] =
      focus.children.get(item).map { child =>
        Zipper(
          child,
          ZipperContext.Frame(context, item, focus.terminal, focus.children.removed(item))
        )
      }

    def descend(path: PathValue): Option[Zipper[V]] =
      descendItems(TrieSpace.intern(path))

    def descendItems(items: Iterable[Int]): Option[Zipper[V]] =
      items.foldLeft(Option(this))((cursor, item) => cursor.flatMap(_.down(item)))

    def up: Option[Zipper[V]] = context match
      case ZipperContext.Root() => None
      case ZipperContext.Frame(parent, item, parentTerminal, siblings) =>
        val children =
          if focus.isEmpty then siblings
          else siblings.updated(item, focus)
        Some(Zipper(ValuedTrieSpace.node(parentTerminal, children), parent))

    def toRoot: Zipper[V] =
      var cursor = this
      var next = cursor.up
      while next.isDefined do
        cursor = next.get
        next = cursor.up
      cursor

    def graft(replacement: ValuedTrieSpace[V]): Zipper[V] =
      copy(focus = replacement)

    def removeFocus: Zipper[V] =
      graft(ValuedTrieSpace.empty[V])

    def putAtFocus(path: PathValue, value: V)(using MergeLattice[V]): Zipper[V] =
      putItemsAtFocus(TrieSpace.intern(path), value)

    def putItemsAtFocus(path: List[Int], value: V)(using MergeLattice[V]): Zipper[V] =
      copy(focus = focus.putItems(path, value))

    def firstChild: Option[Zipper[V]] =
      focus.orderedChildren.headOption.map { (item, child) =>
        Zipper(child, ZipperContext.Frame(context, item, focus.terminal, focus.children.removed(item)))
      }

    def nextSibling: Option[Zipper[V]] =
      sibling(delta = 1)

    def previousSibling: Option[Zipper[V]] =
      sibling(delta = -1)

    private def sibling(delta: Int): Option[Zipper[V]] = context match
      case ZipperContext.Root() => None
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

sealed trait ValuedSpace[V]

object ValuedSpace:
  final case class Empty[V]() extends ValuedSpace[V]
  final case class Literal[V](value: ValuedTrieSpace[V]) extends ValuedSpace[V]
  final case class Union[V](left: ValuedSpace[V], right: ValuedSpace[V]) extends ValuedSpace[V]
  final case class Intersection[V](left: ValuedSpace[V], right: ValuedSpace[V]) extends ValuedSpace[V]
  final case class Diff[V](left: ValuedSpace[V], right: ValuedSpace[V]) extends ValuedSpace[V]
  final case class Product[V](left: ValuedSpace[V], right: ValuedSpace[V]) extends ValuedSpace[V]
  final case class Restriction[V](source: ValuedSpace[V], prefixes: ValuedSpace[V]) extends ValuedSpace[V]
  final case class Raffination[V](source: ValuedSpace[V], prefixes: ValuedSpace[V]) extends ValuedSpace[V]
  final case class Wrap[V](source: ValuedSpace[V], prefix: PathValue) extends ValuedSpace[V]
  final case class Unwrap[V](source: ValuedSpace[V], prefix: PathValue) extends ValuedSpace[V]
  final case class TailsUnion[V](source: ValuedSpace[V]) extends ValuedSpace[V]
  final case class TailsIntersection[V](source: ValuedSpace[V]) extends ValuedSpace[V]
  final case class NonEmpty[V](source: ValuedSpace[V]) extends ValuedSpace[V]
  final case class Head[V](source: ValuedSpace[V]) extends ValuedSpace[V]
  final case class PrefixClosure[V](source: ValuedSpace[V]) extends ValuedSpace[V]
  final case class SuffixClosure[V](source: ValuedSpace[V]) extends ValuedSpace[V]
  final case class TailsClosure[V](source: ValuedSpace[V]) extends ValuedSpace[V]

  def literal[V](entries: (PathValue, V)*)(using MergeLattice[V]): ValuedSpace[V] =
    Literal(ValuedTrieSpace.fromEntries(entries))

  def eval[V](space: ValuedSpace[V])(using lattice: MergeLattice[V]): ValuedTrieSpace[V] = space match
    case Empty() => ValuedTrieSpace.empty[V]
    case Literal(value) => value
    case Union(left, right) => eval(left).union(eval(right))
    case Intersection(left, right) => eval(left).intersect(eval(right))
    case Diff(left, right) => eval(left).diff(eval(right))
    case Product(left, right) => eval(left).concat(eval(right))
    case Restriction(source, prefixes) => eval(source).restrictBy(eval(prefixes))
    case Raffination(source, prefixes) => eval(source).raffinate(eval(prefixes))
    case Wrap(source, prefix) => eval(source).wrap(prefix)
    case Unwrap(source, prefix) => eval(source).unwrap(prefix)
    case TailsUnion(source) => eval(source).tailsUnion
    case TailsIntersection(source) => eval(source).tailsIntersection
    case NonEmpty(source) => eval(source).nonEmptyPaths
    case Head(source) => eval(source).head
    case PrefixClosure(source) => eval(source).prefixClosure
    case SuffixClosure(source) => eval(source).suffixClosure
    case TailsClosure(source) => eval(source).tailsClosure
