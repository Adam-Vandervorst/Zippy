package scala.collection.immutable

/** A READ-ONLY VIEW of `IntMap`'s Patricia structure, for the event semantics (tasks.md A1).
 *
 *  `IntMap.Bin` / `IntMap.Tip` / `IntMap.Nil` are `private[immutable]`, which is why `IntTrieOps`
 *  lives in this package.  The event SEMANTICS (`SpatialSemantics.scala`, package `morkl`) has to
 *  state what a Patricia descent costs in terms of the two maps' structure — "one visit per node of
 *  the merged Patricia shape, one entry operation per single-key probe" — and that statement is
 *  about the SHAPE of the maps, not about `IntTrieOps`'s code.  This object exposes exactly the shape
 *  and the four bit predicates the shape is defined by, and nothing that mutates.
 *
 *  The nodes are returned as the ORIGINAL map objects (`l`/`r` are the real sub-maps), so a
 *  semantics that reasons about POINTER SHARING — "the same child object handed in twice is one
 *  operand" — can test `eq` on them, which is the relation the executors' sharing conventions are
 *  stated in (docs/SPATIAL_SEMANTICS.md §3). */
object IntMapView:
  enum Shape[+A]:
    case Nil
    case Tip(key: Int, value: A)
    case Bin(prefix: Int, mask: Int, left: IntMap[A], right: IntMap[A])

  def shape[A](m: IntMap[A]): Shape[A] = m match
    case IntMap.Nil => Shape.Nil
    case IntMap.Tip(k, v) => Shape.Tip(k, v)
    case IntMap.Bin(p, mk, l, r) => Shape.Bin(p, mk, l, r)

  /** the canonical empty map object, for `eq` tests */
  val empty: IntMap[Nothing] = IntMap.Nil
  def isNil[A](m: IntMap[A]): Boolean = m eq IntMap.Nil

  // the four bit predicates a big-endian Patricia tree is defined by (scala.collection.BitOperations)
  def zero(i: Int, mask: Int): Boolean = IntMapUtils.zero(i, mask)
  def hasMatch(key: Int, prefix: Int, mask: Int): Boolean = IntMapUtils.hasMatch(key, prefix, mask)
  def shorter(m1: Int, m2: Int): Boolean = IntMapUtils.shorter(m1, m2)
  def maskOf(i: Int, mask: Int): Int = IntMapUtils.mask(i, mask)
  /** `IntMapUtils.join` — the smart constructor that hangs two disjoint-prefix maps under a fresh `Bin` */
  def join[A](p1: Int, t1: IntMap[A], p2: Int, t2: IntMap[A]): IntMap[A] = IntMapUtils.join(p1, t1, p2, t2)
  /** a `Bin` built directly — the spec's reconstruction step, exactly `IntMap.Bin(p, m, l, r)` */
  def bin[A](prefix: Int, mask: Int, left: IntMap[A], right: IntMap[A]): IntMap[A] = IntMap.Bin(prefix, mask, left, right)
  def tip[A](key: Int, value: A): IntMap[A] = IntMap.Tip(key, value)
