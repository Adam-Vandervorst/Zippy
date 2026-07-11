package morkl.valued

import morkl.{PathValue, Syntax}
import morkl.Syntax.{*, given}
import munit.FunSuite

class ValuedTrieSpaceTest extends FunSuite:
  test("valued trie oracle merges payloads with the selected lattice") {
    given MergeLattice[Int] with
      def join(left: Int, right: Int): Int = left.max(right)
      def meet(left: Int, right: Int): Int = left.min(right)

    val left = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("a") -> 1,
      Syntax.parse("a.x") -> 4,
      Syntax.parse("b.y") -> 2,
    ))
    val right = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("a") -> 7,
      Syntax.parse("b.y") -> 5,
      Syntax.parse("c") -> 3,
    ))

    assertEquals((left union right).lookup(Syntax.parse("a")), Some(7))
    assertEquals((left union right).lookup(Syntax.parse("b.y")), Some(5))
    assertEquals((left intersect right).lookup(Syntax.parse("a")), Some(1))
    assertEquals((left intersect right).lookup(Syntax.parse("b.y")), Some(2))
    assertEquals((left diff right).lookup(Syntax.parse("a")), None)
    assertEquals((left diff right).lookup(Syntax.parse("a.x")), Some(4))
  }

  test("valued trie oracle preserves payloads through structural path operations") {
    given MergeLattice[Int] with
      def join(left: Int, right: Int): Int = left + right
      def meet(left: Int, right: Int): Int = left.min(right)

    val source = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("a.x") -> 2,
      Syntax.parse("a.y") -> 3,
      Syntax.parse("b.x") -> 5,
    ))
    val suffix = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("z") -> 11,
    ))

    assertEquals(source.child("a").lookup(Syntax.parse("x")), Some(2))
    assertEquals(source.wrap(Syntax.parse("root")).unwrap(Syntax.parse("root")).toMap, source.toMap)
    assertEquals(source.head.lookup(Syntax.parse("a")), Some(5))
    assertEquals(source.tailsUnion.lookup(Syntax.parse("x")), Some(7))
    assertEquals(source.concat(suffix).lookup(Syntax.parse("a.x.z")), Some(13))
  }

  test("valued space evaluator composes native payload operations") {
    given MergeLattice[Int] with
      def join(left: Int, right: Int): Int = left + right
      def meet(left: Int, right: Int): Int = left.min(right)

    val source = ValuedSpace.literal(
      Syntax.parse("a.x") -> 2,
      Syntax.parse("a.y") -> 3,
      Syntax.parse("b.x") -> 5,
      Syntax.parse("b.z") -> 7,
    )
    val suffix = ValuedSpace.literal(Syntax.parse("z") -> 11)
    val expr =
      ValuedSpace.Union(
        ValuedSpace.Product(ValuedSpace.Unwrap(source, Syntax.parse("a")), suffix),
        ValuedSpace.Head(source),
      )

    assertEquals(ValuedSpace.eval(expr).toMap, Map(
      Syntax.parse("x.z") -> 13,
      Syntax.parse("y.z") -> 14,
      Syntax.parse("a") -> 5,
      Syntax.parse("b") -> 12,
    ))
  }

  test("valued space evaluator dispatches native operators to valued tries") {
    given MergeLattice[Int] with
      def join(left: Int, right: Int): Int = left.max(right)
      def meet(left: Int, right: Int): Int = left.min(right)

    val left = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("a.x") -> 4,
      Syntax.parse("a.y") -> 2,
      Syntax.parse("b.z") -> 8,
    ))
    val right = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("a.y") -> 9,
      Syntax.parse("c") -> 3,
    ))
    val prefixes = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("a") -> 1,
    ))
    val l = ValuedSpace.Literal(left)
    val r = ValuedSpace.Literal(right)
    val p = ValuedSpace.Literal(prefixes)

    val cases = Vector(
      ValuedSpace.Union(l, r) -> left.union(right),
      ValuedSpace.Intersection(l, r) -> left.intersect(right),
      ValuedSpace.Diff(l, r) -> left.diff(right),
      ValuedSpace.Restriction(l, p) -> left.restrictBy(prefixes),
      ValuedSpace.Raffination(l, p) -> left.raffinate(prefixes),
      ValuedSpace.Wrap(l, Syntax.parse("root")) -> left.wrap(Syntax.parse("root")),
      ValuedSpace.Unwrap(ValuedSpace.Wrap(l, Syntax.parse("root")), Syntax.parse("root")) -> left,
      ValuedSpace.TailsUnion(l) -> left.tailsUnion,
      ValuedSpace.TailsIntersection(l) -> left.tailsIntersection,
      ValuedSpace.NonEmpty(ValuedSpace.literal(PathValue(Nil) -> 99, Syntax.parse("q") -> 4)) ->
        ValuedTrieSpace.singleton(Syntax.parse("q"), 4),
      ValuedSpace.Head(l) -> left.head,
      ValuedSpace.PrefixClosure(l) -> left.prefixClosure,
      ValuedSpace.SuffixClosure(l) -> left.suffixClosure,
      ValuedSpace.TailsClosure(l) -> left.tailsClosure,
    )

    cases.zipWithIndex.foreach { case ((expr, expected), i) =>
      assertEquals(ValuedSpace.eval(expr).toMap, expected.toMap, s"valued op case $i")
    }
  }

  test("valued zipper preserves the whole trie across focus movement and edits") {
    given MergeLattice[Int] with
      def join(left: Int, right: Int): Int = left + right
      def meet(left: Int, right: Int): Int = left.min(right)

    val source = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("a.old") -> 1,
      Syntax.parse("b.peer") -> 2,
      Syntax.parse("c.peer") -> 3,
    ))

    val atA = ValuedTrieSpace.Zipper(source).down("a").get
    assertEquals(atA.pathValue, Syntax.parse("a"))
    assertEquals(atA.whole.toMap, source.toMap)

    val editedA = atA.graft(ValuedTrieSpace.singleton(Syntax.parse("fresh"), 9))
    val editedWhole = ValuedTrieSpace.fromEntries(Vector(
      Syntax.parse("a.fresh") -> 9,
      Syntax.parse("b.peer") -> 2,
      Syntax.parse("c.peer") -> 3,
    ))
    assertEquals(editedA.whole.toMap, editedWhole.toMap)

    val atB = editedA.nextSibling.get
    assertEquals(atB.pathValue, Syntax.parse("b"))
    assertEquals(atB.whole.toMap, editedWhole.toMap)

    val backToA = atB.previousSibling.get
    assertEquals(backToA.pathValue, Syntax.parse("a"))
    assertEquals(backToA.focus.toMap, Map(Syntax.parse("fresh") -> 9))
    assertEquals(backToA.removeFocus.whole.toMap, Map(
      Syntax.parse("b.peer") -> 2,
      Syntax.parse("c.peer") -> 3,
    ))
  }
