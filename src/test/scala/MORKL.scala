package morkl

import morkl.Space.DropHead
import munit.FunSuite
import morkl.Syntax.{x, *, given}


/*class MORKL2Path extends FunSuite:
  import Path.*
  test("basic path ref") {
      assert(eval(Concat("family.child", Deref("person")))(using PathContext.mixed()).show == "family.child.person_YLQg")
  }
end MORKL2Path*/

class MORKL2Space extends FunSuite:
  import Path.*
  import Space.*

  test("union") {
    given PathContext()
    given SpaceContext()
    val separate = Union(Union(Literal(SpaceValue("a")), Literal(SpaceValue("b"))), Literal(SpaceValue("c")))
    assert(eval(separate) == SpaceValue("a", "b", "c"))
  }

  test("intersection context") {
    given PathContext()
    given SpaceContext = SpaceContext.constant(Map(SpaceMention("lhS") -> SpaceValue("a", "b", "c"),
                                                   SpaceMention("rhS") -> SpaceValue("a", "c", "e")))
    val abc_ace = Intersection(S"lhS", S"rhS")
    val ac = Union(Literal(SpaceValue("a")), Literal(SpaceValue("c")))
    assert(eval(abc_ace) == eval(ac))
  }

//  test("subtraction") {
//    given PathContext()
//    given SpaceContext()
//    val abc_ce = Subtraction(Space("a", "b", "c"), Space("c", "e"))
//    val ab = Space("a", "b")
//    assert(eval(abc_ce) == eval(ab))
//  }
//
//  test("restriction") {
//    given PathContext()
//    given SpaceContext()
//    val lhs = Restriction(Composition(ss"Foo", Union(Union(
//      Composition(ss"Bar", Space("1", "2", "3")),
//      Composition(ss"Baz", Space("A", "B", "C"))),
//      Composition(ss"Cux", Space("Red", "Blue")))), Space("Foo.Bar", "Foo.Baz"))
//    val rhs = Composition(ss"Foo", Union(
//      Composition(ss"Bar", Space("1", "2", "3")),
//      Composition(ss"Baz", Space("A", "B", "C"))))
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("composition") {
//    given PathContext()
//    given SpaceContext()
//    val prefixed = Composition(ss"Foo", Space("bar", "baz", "cux"))
//    val separated = Space("Foo.bar", "Foo.baz", "Foo.cux")
//    assert(eval(prefixed) == eval(separated))
//    val xyz_ab = Composition(Space("x", "y", "z"), Space("a", "b"))
//    val composed = Space("x.a", "y.a", "z.a", "x.b", "y.b", "z.b")
//    assert(eval(xyz_ab) == eval(composed))
//    val structure = Composition(Space("Foo.Bar", "Foo.Baz"), Space("A.1", "A.2"))
//    val composed_structure = Space("Foo.Bar.A.1", "Foo.Bar.A.2", "Foo.Baz.A.1", "Foo.Baz.A.2")
//    assert(eval(structure) == eval(composed_structure))
//  }
//
//  test("subspace") {
//    given PathContext()
//    given SpaceContext()
//    val lhs = Subspace(Composition(ss"Foo", Union(
//      Composition(ss"Bar", Space("1", "2", "3")),
//      Composition(ss"Baz", Space("A", "B", "C")))), "Foo.Baz")
//    val rhs = Space("A", "B", "C")
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("drophead") {
//    given PathContext()
//    given SpaceContext()
//    val lhs = DropHead(Composition(ss"Foo", Union(
//      Composition(ss"Bar", Space("1", "2", "3")),
//      Composition(ss"Baz", Space("A", "B", "C")))))
//    val rhs = Union(
//      Composition(ss"Bar", Space("1", "2", "3")),
//      Composition(ss"Baz", Space("A", "B", "C")))
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("transformation") {
//    given PathContext()
//    given SpaceContext()
//    val lhs = Transformation(Composition(ss"Foo", Union(Union(
//      Composition(ss"Bar", Space("1", "2", "3")),
//      Composition(ss"Baz", Space("A", "B", "C"))),
//      Composition(ss"Cux", Space("Red", "Blue")))), "$_.Cux.$c", "Result.Color.$c")
//    val rhs = Space("Result.Color.Red", "Result.Color.Blue")
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("left_residual") {
//    given PathContext()
//    given SpaceContext()
//    // all prefixes we can add to y such prefix.y <= x
//    val x = Composition(Singleton("Test.Foo"), Union(Union(
//      Composition(ss"Bar", Space("1", "2", "3", "4", "5", "6")),
//      Composition(ss"Baz", Space("1", "2", "3", "A", "B", "C"))),
//      Composition(ss"Cux", Space("Red", "Blue"))))
//    val y = Space("1", "2", "3")
//    val lhs = LeftResidual(x, y)
//    val rhs = Space("Test.Foo.Bar", "Test.Foo.Baz")
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("right_residual") {
//    given PathContext()
//    given SpaceContext()
//    // all postfixes we can add to y such y.postfix <= x
//    val x = Composition(Singleton("Test.Foo"), Union(Union(
//      Composition(ss"Bar", Space("1", "2", "3", "4", "5", "6")),
//      Composition(ss"Baz", Space("1", "2", "3", "A", "B", "C"))),
//      Composition(ss"Cux", Space("Red", "Blue"))))
//    val y = Space("Test.Foo.Bar", "Test.Foo.Baz")
//    val lhs = RightResidual(y, x)
//    val rhs = Space("1", "2", "3")
//    assert(eval(lhs) == eval(rhs))
//  }
end MORKL2Space

object Graphs:
  val scc_context = SpaceContextMap(Map(
    /*
    a  ->  b   x  <->  y
      \           \    ^
        ◢           ◢  |
    c  <-  d           z
     */
    SpaceMention("g1") -> SpaceValue("edge.a.b", "edge.a.d", "edge.d.c", "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y"),
    /*
    a  ->  b   x  <->  y  s -> t -> u -> v -> w
      \           \    ^
        ◢           ◢  |
    c  <-  d           z
     */
    SpaceMention("g2") -> SpaceValue("edge.a.b", "edge.a.d", "edge.d.c", "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y",
      "edge.s.t", "edge.t.u", "edge.u.v", "edge.v.w"),
    /*
    a  ->  b   x  <->  y  s -> t -> u -> v -> w -> s
      \           \    ^
        ◢           ◢  |
    c  <-  d           z
     */
    SpaceMention("g3") -> SpaceValue("edge.a.b", "edge.a.d", "edge.d.c", "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y",
      "edge.s.t", "edge.t.u", "edge.u.v", "edge.v.w", "edge.w.s")))
end Graphs

class AuntQuery extends FunSuite:
  import Space.*
  import AuntQuery.*

  test("add_index") {
//    val rhs = S"ifamily" \/ S"ifamily".transform("parent.$x.$y", "child.$y.$x")
    val rhs = S"ifamily"
      \/ ("child" x S"ifamily"("parent").iter(P"x", S"r", S"r".iter(P"y", S"_", Singleton(P"y" x P"x"))))
      \/ ("person" x S"ifamily"("female"))
      \/ ("person" x S"ifamily"("male"))
    assert(eval(rhs)(using PathContext.emptyMap, initial_context) == eval(S"family")(using PathContext(), context))
  }

  test("query via restriction") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context

    assert(eval(S"family" <| Literal(SpaceValue("male", "female"))) ==
      SpaceValue("female.Ann", "female.Liz", "female.Pam", "female.Pat", "male.Bob", "male.Jim", "male.Tom"))

    assert(eval(S"family" <| Literal(SpaceValue("parent.Bob", "child.Bob"))) ==
      SpaceValue("child.Bob.Pam", "child.Bob.Tom", "parent.Bob.Ann", "parent.Bob.Pat"))
  }

  test("parent_query") {
    given PathContext()
    given SpaceContext = context
    val lhs = "Parent" x (S"family"("child") <| S"people")
    val rhs = SpaceValue("Parent.Bob.Tom", "Parent.Pat.Bob", "Parent.Bob.Pam", "Parent.Liz.Tom", "Parent.Ann.Bob", "Parent.Jim.Pat")
    assert(eval(lhs) == rhs)
  }

  test("mother_query") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context

    val res = "Mother" x S"people".iter(P"person", S"_",
      sP"person" x (S"family"("child")(P"person") /\ S"family"("female"))
    )

    assert(eval(res) == SpaceValue("Mother.Jim.Pat", "Mother.Bob.Pam"))
  }

  test("sister_query") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    val res = "Sister" x S"people".iter(P"person", S"_",
      P"person" x ((DropHead(S"family"("parent") <| S"family"("child" x P"person")) /\ S"family"("female")) \ sP"person")
    )

    assert(eval(res) == SpaceValue("Sister.Ann.Pat", "Sister.Pat.Ann", "Sister.Bob.Liz"))
  }

  test("aunt_query") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    val res = "Aunt" x S"people".iter(P"person", S"_",
      P"person" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x P"person"))) \ S"family"("child" x P"person")) /\ S"family"("female"))
    )

    assert(eval(res) == SpaceValue("Aunt.Ann.Liz", "Aunt.Jim.Ann", "Aunt.Pat.Liz"))
  }

  val predecessor_helper_routine = R"predecessor_helper"(S"family", S"oldest", S"people") :=
    S"people" \/ R"predecessor_helper"(S"family",
      DropHead(S"family"("child") <| S"oldest"),
      S"people" \/ DropHead(S"family"("child") <| S"oldest"))

  test("predecessors_query") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    given PartialFunction[RoutinePtr, Routine] = { case RoutinePtr("predecessor_helper") => predecessor_helper_routine }

    val lhs = "Predecessor" x S"people".iter(P"person", S"_",
      P"person" x R"predecessor_helper"(S"family", sP"person", Space.Empty)
    )

    val rhs = "Predecessor" x (
      ("Ann" x Literal(SpaceValue("Bob", "Pam", "Tom"))) \/
      ("Bob" x Literal(SpaceValue("Pam", "Tom"))) \/
      ("Jim" x Literal(SpaceValue("Bob", "Pam", "Pat", "Tom"))) \/
      ("Liz" x Literal(SpaceValue("Tom"))) \/
      ("Pat" x Literal(SpaceValue("Bob", "Pam", "Tom")))
    )

    assert(eval(lhs) == eval(rhs))
  }
end AuntQuery

object AuntQuery:
  /*
  Tom x Pam
   |   \
  Liz  Bob
       / \
    Ann   Pat
           |
          Jim
   */

  val initial_context = SpaceContextMap(Map(SpaceMention("ifamily") -> SpaceValue(
    "parent.Tom.Bob",
    "parent.Pam.Bob",
    "parent.Tom.Liz",
    "parent.Bob.Ann",
    "parent.Bob.Pat",
    "parent.Pat.Jim",
    "female.Pam", "female.Liz", "female.Pat", "female.Ann",
    "male.Tom", "male.Bob", "male.Jim")))

  val context = SpaceContextMap(Map(
    SpaceMention("family") -> SpaceValue(
      "parent.Tom.Bob", "child.Bob.Tom",
      "parent.Pam.Bob", "child.Bob.Pam",
      "parent.Tom.Liz", "child.Liz.Tom",
      "parent.Bob.Ann", "child.Ann.Bob",
      "parent.Bob.Pat", "child.Pat.Bob",
      "parent.Pat.Jim", "child.Jim.Pat",
      "female.Pam", "female.Liz", "female.Pat", "female.Ann",
      "male.Tom", "male.Bob", "male.Jim",
      "person.Tom", "person.Bob", "person.Jim", "person.Pam", "person.Liz", "person.Pat", "person.Ann"),
    SpaceMention("people") -> SpaceValue("Tom", "Bob", "Jim", "Pam", "Liz", "Pat", "Ann")))
end AuntQuery

class Poly extends FunSuite:
  import Space.*

  test("composition") {
    val _1 = Literal(SpaceValue("0"))
    val _2 = Literal(SpaceValue("0", "1"))
    val _3 = Literal(SpaceValue("0", "1", "2"))
    val _4 = Literal(SpaceValue("0", "1", "2", "3"))
    val p1 = ("³" x _1 x S"y" x S"y" x S"y") \/ ("¹" x _1 x S"y")  // y^3 + y
    val p2 = ("⁴" x _1 x S"y" x S"y" x S"y" x S"y") \/ ("²" x _1 x S"y" x S"y") \/ ("⁰" x _1 x ss"u")  // y^4 + y^2 + 1
    assert(eval(p1 \/ p2)(using sc=SpaceContextMap(Map(SpaceMention("y") -> SpaceValue("y")))) == SpaceValue("².0.y.y", "³.0.y.y.y", "¹.0.y", "⁰.0.u", "⁴.0.y.y.y.y"))
    assert(eval(p1.iter(P"o1", S"r1", S"r1".iter(P"f1", S"ps1",
                p2.iter(P"o2", S"r2", S"r2".iter(P"f2", S"ps2",
                  P"o1" x P"o2" x P"f1" x P"f2" x S"ps1" x S"ps2")))))(using sc=SpaceContextMap(Map(SpaceMention("y") -> SpaceValue("$y")))) == SpaceValue("³.².0.0.$y.$y.$y.$y.$y", "³.⁰.0.0.$y.$y.$y.u", "³.⁴.0.0.$y.$y.$y.$y.$y.$y.$y", "¹.².0.0.$y.$y.$y", "¹.⁰.0.0.$y.u", "¹.⁴.0.0.$y.$y.$y.$y.$y"))
    // x.y.z
    // x.0.(y,z)
    // y.1.(x,z)
    // z.2.(x,y)

    // x.y.z.w
    // x.0.(y,z,w)
    // y.1.(x,z,w)
    // z.2.(x,y,w)
    // w.3.(x,y,z)

  }
end Poly

class Imperative extends FunSuite:
  import Space.*

  test("union iter transpiled") {
    val code = transpile(Routines.union_iter_routine)
    println(code.show)

    val stack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](code.nodes.length))
    stack.top(0) = SpaceValue("a.1", "a.2", "a.3", "b.foo", "c.d.e.f")
    stack.top(1) = SpaceValue("a.1", "a.2", "a.3", "b.bar", "x.y.z.w")
    exec(code, stack)
    assert(stack.top.last.asInstanceOf[SpaceValue] == SpaceValue("a.Left.1", "a.Left.2", "a.Left.3", "a.Right.1", "a.Right.2", "a.Right.3", "b.Left.foo", "b.Right.bar", "c.Left.d.e.f", "x.Right.y.z.w"))
  }

  test("aunt query pretty") {
//    println(aunt_query_routine.show)
  }

  test("aunt query transpiled") {
//    println(transpile(aunt_query_routine).show)
//    println(transpile(child_routine).show)
  }

  test("scc transpiled") {
//    println(transpile(scc_routine).show)
//    println("optimized")
//    println(optimize_sharing(transpile(scc_routine)).show)
//    println(prune_redundant(optimize_sharing(transpile(scc_routine))).show)
  }

  test("aunt query exec") {
    val code = transpile(Routines.aunt_query_routine, None)
//    println(code.show)
    val stack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](code.nodes.length))
    stack.top(0) = AuntQuery.context.resolve(SpaceMention("family"))
    stack.top(1) = AuntQuery.context.resolve(SpaceMention("people"))
    exec(code, stack)
    assert(stack.top.last.asInstanceOf[SpaceValue] == SpaceValue("Aunt.Ann.Liz", "Aunt.Jim.Ann", "Aunt.Pat.Liz"))
  }

  test("scc exec") {
    val code = transpile(Routines.seedless_scc_routine, None)
    val reachable_code = transpile(Routines.reachable_routine, None)
    //    println(code.show)
    val graph = eval(Literal(Graphs.scc_context.resolve(SpaceMention("g2")))("edge"))
    val transpose = eval(Literal(graph).iter(P"x", S"r", S"r".iter(P"y", S"_", Singleton(P"y" x P"x"))))
    val nodes = eval(Literal(graph).iter(P"fwd", S"_1", sP"fwd") \/ Literal(transpose).iter(P"bwd", S"_2", sP"bwd"))

    val stack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](code.nodes.length))
    stack.top(0) = graph
    stack.top(1) = transpose
    stack.top(2) = nodes
    exec(code, stack, {case "seedless_scc" => code; case "reachable" => reachable_code})
    println(stack.top.last.asInstanceOf[SpaceValue])
//    assert(stack.top.last.asInstanceOf[SpaceValue] == SpaceValue("Aunt.Ann.Liz", "Aunt.Jim.Ann", "Aunt.Pat.Liz"))
  }

  test("mermaid") {
    mermaid(optimize_sharing(transpile(Routines.union_iter_routine)))
  }

  test("push out") {
    {
    val code = transpile(R"test"(P"k", S"xs") :=
      S"xs".iter(P"x", S"r",
        S"r"(P"k" x "test")))
    assert(code.show == """Routine[test](): space
                           |0 ExtractPathRef[k](): path
                           |1 ExtractSpaceMention[xs](): space
                           |2 Iteration[]((0,1)): space
                           |  0 ExtractPathRef[x](): path
                           |  1 ExtractSpaceMention[r](): space
                           |  2 Constant[test](): path
                           |  3 Concat[]((0,0), (1,2)): path
                           |  4 Unwrap[]((1,1), (1,3)): space""".stripMargin)
    assert(optimize(code).show == """Routine[test](): space
                                     |0 ExtractPathRef[k](): path
                                     |1 ExtractSpaceMention[xs](): space
                                     |2 Constant[test](): path
                                     |3 Concat[]((0,0), (0,2)): path
                                     |4 Iteration[]((0,1)): space
                                     |  0 ExtractPathRef[x](): path
                                     |  1 ExtractSpaceMention[r](): space
                                     |  2 Unwrap[]((1,1), (0,3)): space""".stripMargin)
    }
    {
      val code = transpile(Routines.union_iter_routine)
      assert(code.show == """Routine[union_iter](): space
                            |0 ExtractSpaceMention[xs](): space
                            |1 ExtractSpaceMention[ys](): space
                            |2 Iteration[]((0,0)): space
                            |  0 ExtractPathRef[x](): path
                            |  1 ExtractSpaceMention[rx](): space
                            |  2 Constant[Left](): path
                            |  3 Concat[]((1,0), (1,2)): path
                            |  4 Wrap[]((1,1), (1,3)): space
                            |3 Iteration[]((0,1)): space
                            |  0 ExtractPathRef[y](): path
                            |  1 ExtractSpaceMention[ry](): space
                            |  2 Constant[Right](): path
                            |  3 Concat[]((1,0), (1,2)): path
                            |  4 Wrap[]((1,1), (1,3)): space
                            |4 Union[]((0,2), (0,3)): space""".stripMargin)
      assert(optimize(code).show == """Routine[union_iter](): space
                                      |0 ExtractSpaceMention[xs](): space
                                      |1 ExtractSpaceMention[ys](): space
                                      |2 Constant[Left](): path
                                      |3 Iteration[]((0,0)): space
                                      |  0 ExtractPathRef[x](): path
                                      |  1 ExtractSpaceMention[rx](): space
                                      |  2 Concat[]((1,0), (0,2)): path
                                      |  3 Wrap[]((1,1), (1,2)): space
                                      |4 Constant[Right](): path
                                      |5 Iteration[]((0,1)): space
                                      |  0 ExtractPathRef[y](): path
                                      |  1 ExtractSpaceMention[ry](): space
                                      |  2 Concat[]((1,0), (0,4)): path
                                      |  3 Wrap[]((1,1), (1,2)): space
                                      |6 Union[]((0,3), (0,5)): space""".stripMargin)
    }
    {
      val code = transpile(Routines.seedless_scc_routine)
      assert(code.show == """Routine[seedless_scc](): space
                            |0 ExtractSpaceMention[fwd](): space
                            |1 ExtractSpaceMention[bwd](): space
                            |2 ExtractSpaceMention[nodes](): space
                            |3 Limit[1]((0,2)): space
                            |4 Iteration[]((0,3)): space
                            |  0 ExtractPathRef[v](): path
                            |  1 ExtractSpaceMention[_](): space
                            |  2 Singleton[]((1,0)): space
                            |  3 Call[reachable]((0,0), (0,2), (1,2)): space
                            |  4 Singleton[]((1,0)): space
                            |  5 Call[reachable]((0,1), (0,2), (1,4)): space
                            |  6 Intersection[]((1,3), (1,5)): space
                            |  7 Singleton[]((1,0)): space
                            |  8 Subtraction[]((1,6), (1,7)): space
                            |  9 Wrap[]((1,8), (1,0)): space
                            |  10 Singleton[]((1,0)): space
                            |  11 Call[reachable]((0,0), (0,2), (1,10)): space
                            |  12 Singleton[]((1,0)): space
                            |  13 Call[reachable]((0,1), (0,2), (1,12)): space
                            |  14 Subtraction[]((1,11), (1,13)): space
                            |  15 Call[scc]((0,0), (0,1), (1,14)): space
                            |  16 Union[]((1,9), (1,15)): space
                            |  17 Singleton[]((1,0)): space
                            |  18 Call[reachable]((0,1), (0,2), (1,17)): space
                            |  19 Singleton[]((1,0)): space
                            |  20 Call[reachable]((0,0), (0,2), (1,19)): space
                            |  21 Subtraction[]((1,18), (1,20)): space
                            |  22 Call[scc]((0,0), (0,1), (1,21)): space
                            |  23 Union[]((1,16), (1,22)): space
                            |  24 Singleton[]((1,0)): space
                            |  25 Call[reachable]((0,0), (0,2), (1,24)): space
                            |  26 Subtraction[]((0,2), (1,25)): space
                            |  27 Singleton[]((1,0)): space
                            |  28 Call[reachable]((0,1), (0,2), (1,27)): space
                            |  29 Subtraction[]((1,26), (1,28)): space
                            |  30 Call[scc]((0,0), (0,1), (1,29)): space
                            |  31 Union[]((1,23), (1,30)): space""".stripMargin)
      assert(optimize(code).show == """Routine[seedless_scc](): space
                                      |0 ExtractSpaceMention[fwd](): space
                                      |1 ExtractSpaceMention[bwd](): space
                                      |2 ExtractSpaceMention[nodes](): space
                                      |3 Limit[1]((0,2)): space
                                      |4 Iteration[]((0,3)): space
                                      |  0 ExtractPathRef[v](): path
                                      |  1 ExtractSpaceMention[_](): space
                                      |  2 Singleton[]((1,0)): space
                                      |  3 Call[reachable]((0,0), (0,2), (1,2)): space
                                      |  4 Call[reachable]((0,1), (0,2), (1,2)): space
                                      |  5 Intersection[]((1,3), (1,4)): space
                                      |  6 Subtraction[]((1,5), (1,2)): space
                                      |  7 Wrap[]((1,6), (1,0)): space
                                      |  8 Subtraction[]((1,3), (1,4)): space
                                      |  9 Call[scc]((0,0), (0,1), (1,8)): space
                                      |  10 Union[]((1,7), (1,9)): space
                                      |  11 Subtraction[]((1,4), (1,3)): space
                                      |  12 Call[scc]((0,0), (0,1), (1,11)): space
                                      |  13 Union[]((1,10), (1,12)): space
                                      |  14 Subtraction[]((0,2), (1,3)): space
                                      |  15 Subtraction[]((1,14), (1,4)): space
                                      |  16 Call[scc]((0,0), (0,1), (1,15)): space
                                      |  17 Union[]((1,13), (1,16)): space""".stripMargin)
    }
  }
end Imperative

class Routines extends FunSuite:
  import Space.*
  import Routines.*
  import AuntQuery.context
  import Graphs.scc_context

  test("eval routine") {
    val lpeople = Literal(SpaceValue("Tom", "Bob", "Jim"))
    val e = R"aunts"(S"family", lpeople)
    val result = SpaceValue("Aunt.Jim.Ann")
    assert(eval(e)(using PathContext.emptyMap, context, Map(RoutinePtr("aunts") -> aunt_query_routine)) == result)
  }

  test("transitive") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = scc_context
    val graph = S"g1"
    val lhs = "edge" x R"transitive"(graph("edge"))
    val rhs = "edge" x (("a" x Literal(SpaceValue("b", "d", "c"))) \/
      ("d" x Literal(SpaceValue("c"))) \/
      (Literal(SpaceValue("x", "y", "z")) x Literal(SpaceValue("x", "y", "z"))))
    assert(eval(lhs)(using rc = Map(RoutinePtr("transitive") -> transitive_routine)) == eval(rhs))
  }

  test("reachable") {
    val graph = S"g2"
    val transpose = graph("edge").iter(P"x", S"r", S"r".iter(P"y", S"_", Singleton(P"y" x P"x")))
    val nodes = graph("edge").iter(P"fwd", S"_1", sP"fwd") \/ transpose.iter(P"bwd", S"_2", sP"bwd")
    val fwd_t = R"reachable"(graph("edge"), nodes, ss"t")
    assert(eval(fwd_t)(using rc = Map(RoutinePtr("reachable") -> reachable_routine), sc = scc_context) == SpaceValue("t", "u", "v", "w"))
    val fwd_s_no_v = R"reachable"(graph("edge"), nodes \ ss"v", ss"s")
    assert(eval(fwd_s_no_v)(using rc = Map(RoutinePtr("reachable") -> reachable_routine), sc = scc_context) == SpaceValue("s", "t", "u"))
    val bwd_c = R"reachable"(transpose, nodes, ss"c")
    assert(eval(bwd_c)(using rc = Map(RoutinePtr("reachable") -> reachable_routine), sc = scc_context) == SpaceValue("c", "d", "a"))
    val fwd_a_no_ad = R"reachable"(graph("edge") \ Singleton("a.d"), nodes, ss"a")
    assert(eval(fwd_a_no_ad)(using rc = Map(RoutinePtr("reachable") -> reachable_routine), sc = scc_context) == SpaceValue("a", "b"))
  }

  test("scc") {
    given PathContext = PathContext.emptyMap
    val graph = S"g3"
    val transpose = graph("edge").iter(P"x", S"r", S"r".iter(P"y", S"_", Singleton(P"y" x P"x")))
    val nodes = graph("edge").iter(P"fwd", S"_1", sP"fwd") \/ transpose.iter(P"bwd", S"_2", sP"bwd")
    val e = R"scc"("42", graph("edge"), transpose, nodes)
    assert(eval(e)(using rc = Map(RoutinePtr("reachable") -> reachable_routine, RoutinePtr("scc") -> scc_routine), sc = scc_context) == SpaceValue("w.s", "w.t", "w.u", "w.v", "z.x", "z.y"))
  }
end Routines

object Routines:
  import Space.*
  import Grounded.sample

  val child_routine = R"child"(S"family") :=
    ("child" x S"family"("parent").iter(P"x", S"r", S"r".iter(P"y", S"_", Singleton(P"y" x P"x"))))

  val aunt_query_routine = R"aunts"(S"family", S"people") :=
    "Aunt" x S"people".iter(P"person", S"_",
      P"person" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x P"person"))) \ S"family"("child" x P"person")) /\ S"family"("female")))

  val transitive_routine = R"transitive"(S"edges") :=
    S"edges" \/ R"transitive"(S"edges" \/ S"edges".iter(P"n", S"nbs", P"n" x DropHead(S"edges" <| S"nbs")))

  val reachable_routine = R"reachable"(S"edges", S"nodemask", S"reach") :=
    S"reach" \/ R"reachable"(S"edges", S"nodemask",
      S"reach" \/ DropHead(S"edges" <| (S"reach" /\ S"nodemask")) /\ S"nodemask")

  val scc_routine = R"scc"(P"seed", S"fwd", S"bwd", S"nodes") :=
    sample(Singleton("seed" x P"seed") \/ Singleton("count.1") \/ ("space" x S"nodes")).iter(P"v", S"_", {
      val pred: Space = R"reachable"(S"fwd", S"nodes", sP"v")
      val desc: Space = R"reachable"(S"bwd", S"nodes", sP"v")
      (P"v" x ((pred /\ desc) \ sP"v")) \/
        R"scc"(P"seed" x "0", S"fwd", S"bwd", pred \ desc) \/
        R"scc"(P"seed" x "1", S"fwd", S"bwd", desc \ pred) \/
        R"scc"(P"seed" x "2", S"fwd", S"bwd", (S"nodes" \ pred) \ desc)
    })

  val seedless_scc_routine = R"seedless_scc"(S"fwd", S"bwd", S"nodes") :=
    First(1, S"nodes").iterh(P"v", {
      val pred: Space = R"reachable"(S"fwd", S"nodes", sP"v")
      val desc: Space = R"reachable"(S"bwd", S"nodes", sP"v")
      (P"v" x ((pred /\ desc) \ sP"v")) \/
        R"scc"(S"fwd", S"bwd", pred \ desc) \/
        R"scc"(S"fwd", S"bwd", desc \ pred) \/
        R"scc"(S"fwd", S"bwd", (S"nodes" \ pred) \ desc)
    })

  def fixpoint(f: Space => Space) = RoutinePtr(s"step${f.hashCode()}")(S"last") :=
    S"last" \/ R"step${f.hashCode()}"(S"last" \/ f(S"last"))

  val or_else_routine = R"or_else"(S"e", S"backup") :=
    (ss"E" \ Head("E" x S"e")).tee(S"backup")

  val union_iter_routine = R"union_iter"(S"xs", S"ys") :=
    S"xs".iter(P"x", S"rx", P"x" x "Left" x S"rx") \/
      S"ys".iter(P"y", S"ry", P"y" x "Right" x S"ry")
end Routines


class Fuzzy extends FunSuite:
  import Space.*

  val temperature = SpaceContextMap(Map(SpaceMention("world_slice") -> SpaceValue(
//    "0.0.0.0.0.",
//    "0.0.0.0.1.",
//    "0.0.0.1.0.",
    "0.0.0.1.1.H",
    "0.0.1.0.0.M",
//    "0.0.1.0.1.",
    "0.0.1.1.0.M",
//    "0.0.1.1.1.",
    "0.1.0.0.0.M",
    "0.1.0.0.1.M",
    "0.1.0.1.0.C",
//    "0.1.0.1.1.",
//    "0.1.1.0.0.",
//    "0.1.1.0.1.",
    "0.1.1.1.0.C",
    "0.1.1.1.1.M",
//    "1.0.0.0.0.",
//    "1.0.0.0.1.",
    "1.0.0.1.0.H",
//    "1.0.0.1.1.",
    "1.0.1.0.0.M",
//    "1.0.1.0.1.",
    "1.0.1.1.0.M",
    "1.0.1.1.1.H",
//    "1.1.0.0.0.",
//    "1.1.0.0.1.",
//    "1.1.0.1.0.",
    "1.1.0.1.1.H",
    "1.1.1.0.0.M",
    "1.1.1.0.1.C",
//    "1.1.1.1.0.",
    "1.1.1.1.1.H",
  )))

  def about(point: Int, surrounding: Int): SpaceValue = interval(point - surrounding, point + surrounding)
  def interval(start: Int, end: Int, height: Int = 5, trail: Vector[Boolean] = Vector()): SpaceValue =
    val lowest = trail.padTo(height, false).reverseIterator.zipWithIndex.foldLeft(0){case (k, (b, i)) => if b then k + (1 << i) else k}
    val middle = trail.appended(true).padTo(height, false).reverseIterator.zipWithIndex.foldLeft(0){case (k, (b, i)) => if b then k + (1 << i) else k}
    val highest = trail.padTo(height, true).reverseIterator.zipWithIndex.foldLeft(0){case (k, (b, i)) => if b then k + (1 << i) else k}
    if start == lowest && end == highest then SpaceValue(trail.map(if _ then "1" else "0").mkString("."))
    else if start < middle && end >= middle then SpaceValue(interval(start, middle - 1, height, trail.appended(false)).paths union interval(middle, end, height, trail.appended(true)).paths)
    else if end < middle then interval(start, end, height, trail.appended(false))
    else interval(start, end, height, trail.appended(true)) // start >= middle

//    if start == lowest && end == highest then Singleton("$")
//    else if start < middle && end >= middle then Union("0" x interval(start, middle - 1, height, trail.appended(false)), "1" x interval(middle, end, height, trail.appended(true)))
//    else if end < middle then "0" x interval(start, end, height, trail.appended(false))
//    else "1" x interval(start, end, height, trail.appended(true)) // start >= middle

  test("temperature") {
    given SpaceContext = temperature
    assert(eval(S"world_slice" <| Space.Literal(about(1, 1))) == SpaceValue())
    assert(eval(S"world_slice" <| Space.Literal(interval(3, 4))) == SpaceValue("0.0.0.1.1.H", "0.0.1.0.0.M"))
    assert(eval(S"world_slice" <| Space.Literal(about(12, 3))) == SpaceValue("0.1.0.0.1.M", "0.1.0.1.0.C", "0.1.1.1.0.C", "0.1.1.1.1.M"))
    assert(eval(S"world_slice" <| Space.Literal(interval(18, 21))) == SpaceValue("1.0.0.1.0.H", "1.0.1.0.0.M"))
    assert(eval(S"world_slice" <| Space.Literal(interval(16, 31))) == SpaceValue("1.0.0.1.0.H", "1.0.1.0.0.M", "1.0.1.1.0.M", "1.0.1.1.1.H", "1.1.0.1.1.H", "1.1.1.0.0.M", "1.1.1.0.1.C", "1.1.1.1.1.H"))
  }
end Fuzzy

class Unification extends FunSuite:
  import Space.*

  import Unification.*

  test("renameFrom") {
    assert(("$x.$y.$x" renameFrom "$a.$b.$a") == Syntax.parse("$a.$b.$a"))
    assert(("$x.c.$x" renameFrom "$a.c.$b") == Syntax.parse("$a.c.$a"))
    assert(("s.$x.$y" renameFrom "s.$a.$a") == Syntax.parse("s.$a.$y"))
    assert(("$x.p.$y.$x" renameFrom "$a.q.$a.$b") == Syntax.parse("$a.p.$y.$a"))
  }

//  enum Spec:
//    case Constant(s: String)
//    case Variable(s: String)
//  case class PathSpec(keys: Spec)

  test("query") {
    given SpaceContext = context
    assert(eval(Q(S"sequences", "$x.$y.$z")) == context.resolve(SpaceMention("sequences")))
    assert(eval(Q(S"sequences", "$x.c.$x")) == SpaceValue("a.c.a.c"))
    assert(eval(Q(S"sequences", "$x.$y.$x.$y")) == SpaceValue("a.c.a.c", "b.a.b.a.b.a"))
    assert(eval(Q(S"sequences", "b.$x.$x.$y")) == SpaceValue("b.a.a.b", "b.e.e.b", "b.e.e.b.b.e.e.b", "b.e.e.p.b.o.o.p"))
    assert(eval(Q(S"sequences", "b.$x.$x.$e1.b.$y.$y.$e2")) == SpaceValue("b.e.e.b.b.e.e.b", "b.e.e.p.b.o.o.p"))
  }

  test("transform") {
    given SpaceContext = context
    assert(eval(T(S"sequences", "$x.$y.$z", "$x.$z.$y")) == SpaceValue("a.a.c.c", "b.a.a.b", "b.b.a.a.b.a", "b.e.e.b", "b.e.e.b.b.e.e.b", "b.e.e.p.b.o.o.p"))
    assert(eval(T(S"sequences", "b.$x.$x.$e1.b.$y.$y.$e2", "b.$y.$y.$e1.b.$x.$x.$e2")) == SpaceValue("b.e.e.b.b.e.e.b", "b.o.o.p.b.e.e.p"))
    assert(eval(T(S"sequences", "b.$x.$x.$e1.b.$y.$y.$e2", "b.$y.$x.$e1")) == SpaceValue("b.e.e.b", "b.o.e.p"))
  }

  test("double transform") {
    given SpaceContext = context
    assert(eval(DQT(S"sequences", "$x", "$y", "$x.$y")) == eval(("a" x S"sequences") \/ ("b" x S"sequences")))
    assert(eval(DQT(S"sequences", "$x.$a", "$x.$b", "$a.$b")) == SpaceValue("a.a.a.b", "a.a.b.a.b.a", "a.e.e.b", "a.e.e.b.b.e.e.b", "a.e.e.p.b.o.o.p", "c.c.a.c", "e.a.a.b", "e.a.b.a.b.a", "e.e.e.b", "e.e.e.b.b.e.e.b", "e.e.e.p.b.o.o.p"))
    assert(eval(DQT(S"sequences", "b.a.a.$x", "b.e.e.$y", "$x.$y")) == SpaceValue("b.b", "b.b.b.e.e.b", "b.p.b.o.o.p"))
    assert(eval(DQT(S"sequences", "a.$x", "b.$y", "$x.$y")) == SpaceValue("c.a.a.b", "c.a.b.a.b.a", "c.e.e.b", "c.e.e.b.b.e.e.b", "c.e.e.p.b.o.o.p"))
    assert(eval(DQT(S"sequences", "$x.a.$y", "$x.e.$z", "$x.$y.$z")) == SpaceValue("b.a.e.b", "b.a.e.b.b.e.e.b", "b.a.e.p.b.o.o.p", "b.b.e.b", "b.b.e.b.b.e.e.b", "b.b.e.p.b.o.o.p"))
  }

  test("transpile transform") {
    {
      // {(foo $x), (bar $y), (baz $z)} => {(cux $x), (cux $y), (cux $z)}
      val expr = MQMT(S"s", List("foo.$x", "bar.$y", "baz.$z"), List("cux.$x", "cux.$y", "cux.$z"))
      val f = all_forever(_, List(Lower.ConcatSingleton_Iter, Lower.IterUnion_Indep))

//      R"union_example", "s"), Wrap(Unwrap(S"s", "foo") \/ Unwrap(S"s", "bar") \/ Unwrap(S"s", "baz"), "cux"))

      assert(optimize(transpile(R"union"(S"s") := f(expr))).show
      == """Routine[union](): space
           |0 ExtractSpaceMention[s](): space
           |1 Constant[foo](): path
           |2 Unwrap[]((0,0), (0,1)): space
           |3 Iteration[x]((0,2)): space
           |  0 ExtractPathRef[x](): path
           |  1 ExtractSpaceMention[x_](): space
           |  2 Singleton[]((1,0)): space
           |4 Constant[cux](): path
           |5 Wrap[]((0,3), (0,4)): space
           |6 Constant[bar](): path
           |7 Unwrap[]((0,0), (0,6)): space
           |8 Iteration[y]((0,7)): space
           |  0 ExtractPathRef[y](): path
           |  1 ExtractSpaceMention[y_](): space
           |  2 Singleton[]((1,0)): space
           |9 Wrap[]((0,8), (0,4)): space
           |10 Constant[baz](): path
           |11 Unwrap[]((0,0), (0,10)): space
           |12 Iteration[z]((0,11)): space
           |  0 ExtractPathRef[z](): path
           |  1 ExtractSpaceMention[z_](): space
           |  2 Singleton[]((1,0)): space
           |13 Wrap[]((0,12), (0,4)): space
           |14 Union[]((0,9), (0,13)): space
           |15 Union[]((0,5), (0,14)): space""".stripMargin)
    }/*
    {
      val expr = MQT(S"s", List("bar.$x.$y", "foo.$z.$w"), "cux.$y.$w")
//      println(expr.show)
      val f = all_forever(_, List(Lower.ConcatSingleton_Iter, Lower.IterUnion_Indep, Lower.Wrap_Iter, Lower.Iter_Ident))
//      println(f(expr).show)
      assert(optimize(transpile(R"union", "s"), f(expr)))).show
        == """Routine[union](): space
             |0 ExtractSpaceMention[s](): space
             |1 Constant[bar](): path
             |2 Unwrap[]((0,0), (0,1)): space
             |3 Constant[foo](): path
             |4 Unwrap[]((0,0), (0,3)): space
             |5 Iteration[x]((0,2)): space
             |  0 ExtractPathRef[x](): path
             |  1 ExtractSpaceMention[x_](): space
             |  2 Iteration[y]((1,1)): space
             |    0 ExtractPathRef[y](): path
             |    1 ExtractSpaceMention[y_](): space
             |    2 Iteration[z]((0,4)): space
             |      0 ExtractPathRef[z](): path
             |      1 ExtractSpaceMention[z_](): space
             |    3 Wrap[]((2,2), (2,0)): space
             |6 Constant[cux](): path
             |7 Wrap[]((0,5), (0,6)): space""".stripMargin)
    }*/
    {
//      val expr = MQMT(S"s", List("bar.$x", "foo.$x"), List("cux.$x"))
//      val expr = DQT(S"s", "bar.$x", "foo.$x", "cux.$x") // , "baz.$x"

//      println(eval(Space.Literal(SpaceValue("foo.a", "foo.b"))("foo.a")))
//      println(eval(Space.Literal(SpaceValue("foo.a", "foo.b"))("foo")("a")))
//      println(eval(Space.Literal(SpaceValue("foo.a", "foo.b")).iter(P"x", S"ys", S"ys"("a"))))
//      val expr = TQT(S"s", "foo.$x", "bar.$x", "baz.$x", "cux.$x")
//      val expr = TQT(S"s", "foo.$x", "bar.$x", "baz.$y", "cux.$x")
      val expr = TQT(S"s", "$x.foo", "$x.bar", "$y.baz", "cux.$x")
      println(expr.show)
    }
  }

  test("unify") {
    given SpaceContext = SpaceContextMap(Map(
      //     [2][2] $ a [2] _1  a  unification
      //     [2][2] b $ [2]  b _1  ==>
      //     [2][2] b a [2]  b  a
      SpaceMention("e0lhs") -> SpaceValue(
        "0.0.$x",
        "0.1.a",
        "1.0.$x",
        "1.1.a"
      ),
      SpaceMention("e0rhs") -> SpaceValue(
        "0.0.b",
        "0.1.$y",
        "1.0.b",
        "1.1.$y"
      ),
      //   [4]  $  $ _1 _2  unification
      //   [4]  $  $ _2 _1  ==>
      //   [4]  $ _1 _1 _1
      SpaceMention("e1lhs") -> SpaceValue(
        "0.$s",
        "1.$t",
        "2.$s",
        "3.$t"
      ),
      SpaceMention("e1rhs") -> SpaceValue(
        "0.$x",
        "1.$y",
        "2.$y",
        "3.$s"
      ),
      // ($z (h $z $w) (f $w))
      // ((f $x) (h $y (f a)) $y)
      SpaceMention("e2lhs") -> SpaceValue(
        "0.$z",
        "1.0.h",
        "1.1.$z",
        "1.2.$w",
        "2.0.f",
        "2.1.$w",
      ),
      SpaceMention("e2rhs") -> SpaceValue(
        "0.0.f",
        "0.1.$x",
        "1.0.h",
        "1.1.$y",
        "1.2.0.f",
        "1.2.1.a",
        "2.$y"
      )
    ))


    val vars = Space.Literal(SpaceValue("$x", "$y", "$z", "$w", "$s", "$t", "$u", "$v"))
    val children = Space.Literal(SpaceValue("0", "1", "2", "3", "4"))
    given PartialFunction[RoutinePtr, Routine] = {
      case RoutinePtr("subst") => R"subst"(P"v", S"x", S"e") := {
        (S"x" /\ sP"v").iter(P"m", S"_", S"e") \/
        ((S"x" \ sP"v") \| children).iter(P"s", S"_", sP"s") \/
        children.iter(P"c", S"_",
          (P"c" x (S"x" <| sP"c").iter(P"_", S"st", R"subst"(P"v", S"st", S"e"))))
      }
      case RoutinePtr("descend") => R"descend"(S"x", S"y") := {
        (S"x" /\ vars).iter(P"v", S"_", "bind" x P"v" x (S"y" \ S"x")) \/
        (S"y" /\ vars).iter(P"v", S"_", "bind" x P"v" x (S"x" \ S"y")) \/
        (((S"x" \ vars) \| children) \ S"y").iter(P"v", S"_", "conflict" x P"v" x (S"y" \ vars)) \/
        children.iter(P"c", S"_",
          (S"x" <| sP"c").iter(P"_", S"st", R"descend"(S"st", S"y"(P"c"))))
      }
      case RoutinePtr("unify") => R"descend"(S"x", S"y") := {
        val bind_or_conflict = R"descend"(S"x", S"y")
        (bind_or_conflict.on_empty(S"x") \/ (bind_or_conflict <| ss"conflict")) \/
        bind_or_conflict("conflict").on_empty(First(1, Head(bind_or_conflict("bind"))).iter(P"v", S"_",
          R"unify"(
            R"subst"(P"v", S"x", bind_or_conflict("bind")(P"v")),
            R"subst"(P"v", S"y", bind_or_conflict("bind")(P"v"))
          )
        ))
      }
    }

//    println(eval(S"e0"("L")).prettyLines)
//    println("---")
//    println(eval(R"subst"(Vector("$x"), Vector(S"e0", Space.Literal(SpaceValue("L.p", "R.q"))))).prettyLines)
//    println("---")
//    println(eval(R"descend"(Space.Literal(SpaceValue("L.p", "R.L.a", "R.R.$y")), Space.Literal(SpaceValue("L.p", "R.$x"))))).prettyLines)
    println(eval(R"unify"(S"e0lhs", S"e0rhs")).prettyLines)
    println("---")
    println(eval(R"unify"(S"e1lhs", S"e1rhs")).prettyLines)
    println("---")
    println(eval(R"unify"(S"e2lhs", S"e2rhs")).prettyLines)
  }

  test("overlap") {
    // overlap( {(: a2 (A 2)) (: a1 (A 1))}, {(: $a1 (A $v1)) (: $a2 (A $v2))}) = {((: a2 (A 2)))} {(: a1 (A 1)) (: a1 (A 1))} {}

    given SpaceContext = SpaceContextMap(Map(
      //     overlap( {(: a A)}, {(: $x A), (: (f $x) B)} ) = ({} {(: a A)} {(: (f a) B)})
      // while lhs /\ rhs not empty
      //  find binding or conflict
      //  on binding, apply binding to every term
      //  on conflict, move the involved terms to their respective sides
      //  else done
      SpaceMention("e0lhs") -> SpaceValue(
        "0.:.*.0",
        "1.a.*.0",
        "2.A.*.0"
      ),
      SpaceMention("e0rhs") -> SpaceValue(
        "0.:.*.1",
        "1.$x.*.1",
        "2.A.*.1",
        "0.:.*.2",
        "1.0.f.*.2",
        "1.1.$x.*.2",
        "2.B.*.2"
      )
    ))


    val vars = Space.Literal(SpaceValue("$x", "$y", "$z", "$w", "$s", "$t", "$u", "$v"))
    val children = Space.Literal(SpaceValue("0", "1", "2", "3", "4"))
    val lhs_ids = Space.Literal(SpaceValue("0"))
    val rhs_ids = Space.Literal(SpaceValue("1", "2"))

    given PartialFunction[RoutinePtr, Routine] = {
      case RoutinePtr("substone") => R"subst"(P"v", S"x", S"e") := {
        (S"x" <| sP"v").iter(P"m", S"_", S"e") \/
          ((S"x" \| sP"v") \| children) \/
          children.iter(P"c", S"_",
            (P"c" x (S"x" <| sP"c").iter(P"_", S"st", R"subst"(P"v", S"st", S"e"))))
      }
      case RoutinePtr("subst") => R"subst"(P"v", S"x", S"e") := {
        (S"x" <| sP"v").iter(P"m", S"r", S"e" x S"r") \/
        ((S"x" \| sP"v") \| children) \/
          children.iter(P"c", S"_",
            (P"c" x (S"x" <| sP"c").iter(P"_", S"st", R"subst"(P"v", S"st", S"e"))))
      }
      case RoutinePtr("descend") => R"descend"(S"lhsm", S"rhsm") := {
//        ("evaluating" x S"superposition") \/
        ("bindl" x (S"lhsm" <| vars) x (S"rhsm" \| vars)) \/
        ("bindr" x (S"rhsm" <| vars) x (S"lhsm" \| vars)) \/
        ("conflict" x { // coalesce into single conflict
          val lhs_pc = ((S"lhsm" \| vars) \| children)
          val rhs_pc = ((S"rhsm" \| vars) \| children)
          val pure_lhs_pc = lhs_pc \| Head(rhs_pc)
          val pure_rhs_pc = rhs_pc \| Head(lhs_pc)
          Head(pure_lhs_pc) x Head(pure_rhs_pc) x pure_lhs_pc
        }) \/
        children.iter(P"c", S"_",
          (S"lhsm" <| sP"c").iter(P"_", S"st", R"descend"(S"st", S"rhsm"(P"c"))))
      }
//      case RoutinePtr("unify") => R"descend", "lhsm", "rhsm"), {
//        val bind_ior_conflict = R"descend"(S"lhsm", S"rhsm"))
//        (bind_ior_conflict.on_empty(S"x") \/ (bind_or_conflict <| ss"conflict")) \/
//          bind_or_conflict("conflict").on_empty(First(1, Head(bind_or_conflict("bind"))).iter(P"v", S"_",
//            R"unify"(
//              R"subst"(Vector(P"v"), Vector(S"x", bind_or_conflict("bind")(P"v"))),
//              R"subst"(Vector(P"v"), Vector(S"y", bind_or_conflict("bind")(P"v")))
//            ))
//          ))
//      })
    }

//$a.*.1
//0.f.*.2
//1.$a.*.2
//a.*.0
    // split superposition
//    println(eval(S"e0lhs" \/ S"e0rhs").prettyLines)
    val conflicts = Space.Literal(SpaceValue("conflict.lhs.a.*.0", "conflict.rhs.B.*.2"))
    println(eval(R"descend"(S"e0lhs", S"e0rhs")).prettyLines)
    println("---")
    println(eval(R"subst"("$x", S"e0rhs", Space.Literal(SpaceValue("a")))).prettyLines)
    println("---")
    println(eval( conflicts("conflict")("lhs")  ).prettyLines)
  }

  test("division") {
    given SpaceContext = SpaceContextMap(Map(
      SpaceMention("DB") -> SpaceValue(
        "Completed.Fred.Database1",
        "Completed.Fred.Database2",
        "Completed.Fred.Compiler1",
        "Completed.Eugene.Database1",
        "Completed.Eugene.Compiler1",
        "Completed.Sarah.Database1",
        "Completed.Sarah.Database2",
        "DBProject.Database1",
        "DBProject.Database2",
      )))

    def Head(x: Space): Space = x.iter(P"i", S"r", sP"i")
    val program = R"÷"(S"db") := {
      val students = Head(S"db"("Completed"))
      students \ Head((students x S"db"("DBProject")) \ S"db"("Completed"))
    }

    println(program.show)
    println(transpile(program).show)
    println(optimize(transpile(program)).show)
  }

//  test("sexpr") {
//    R"sym", "size_data"), {
//      S"size_data"("1").iter(P"x", S"_", P"x") \/
//      S"size_data"("2").iter(P"x", S"ys", S"ys".iter(P"y", S"_", P"x" x P"y"))
//    })
//
//    R"var", "data", "bindings"), {
//      S"data"("$").iter(P"x", S"_", P"x") \/
//      S"data".iter(P"x", S"ys", R"convert"(S"bindings"(P"x"), S"ys")  )
//    })
//
//    R"convert", "pattern", "rest"), {
//      (S"data" <| arity)
//      (S"data" <| symbol_size)
//      (S"data" <| Singleton("$")).iter(P"_", S"_", R"expr"(S"rest")))
//
//      S"data"("$").iter(P"x", S"_", P"x") \/
//        S"data".iter(P"x", S"ys", R"convert"(S"bindings"(P"x")))
//    })
//  }

  def headk(space: Space, k: Int): Space =
    space.iter(Path.Deref(PathRef(s"h$k")), Space.Mention(SpaceMention(s"t$k")),
      if k == 1 then Singleton(Path.Deref(PathRef(s"h$k")))
      else Path.Deref(PathRef(s"h$k")) x headk(Space.Mention(SpaceMention(s"t$k")), k - 1))

  test("sudoku") {
    // column-row
    Map((0, 2) -> 3, (1, 1) -> 4, (2, 2) -> 2, (3, 3) -> 1)

    given SpaceContext = SpaceContextMap(Map(
      SpaceMention("p1") -> SpaceValue(
        "Cell.0.2.3",
        "Cell.1.1.4",
        "Cell.2.2.2",
        "Cell.3.3.1",
      )))
    given PartialFunction[RoutinePtr, Routine] = {
      case RoutinePtr("remaining") => R"remaining"() := Space.Empty
    }

    val indices = Space.Literal(SpaceValue("0", "1", "2", "3"))
    val options = Space.Literal(SpaceValue("1", "2", "3", "4"))
    val blocks = Space.Literal(SpaceValue("0.0.0", "0.0.1", "0.1.0", "0.1.1",
                                          "1.2.0", "1.2.1", "1.3.0", "1.3.1",
                                          "2.0.2", "2.0.3", "2.1.2", "2.1.3",
                                          "3.2.2", "3.2.3", "3.3.2", "3.3.3"))
    val all = "Cell" x indices x indices x options
    val initial = (all \| headk(S"p1", 3)) \/ S"p1"
    val column_deductions = indices.iter(P"c", S"_", "Deduction" x "remaining" x "Cell" x P"c" x indices.iter(P"r", S"_", P"r" x "Cell" x P"c" x (indices \ sP"r")))
    val row_deductions = indices.iter(P"r", S"_", "Deduction" x "remaining" x "Cell" x indices.iter(P"c", S"_", P"c" x P"r" x "Cell" x (indices \ sP"c") x sP"r"))
    val block_deductions = blocks.iter(P"b", S"locs", "Deduction" x "remaining" x "Cell" x S"locs".iter(P"c", S"rs", P"c" x S"rs".iter(P"r", S"_", P"r" x ("Cell" x (blocks(P"b") \ Singleton(P"c" x P"r"))))))
    val deductions = column_deductions \/ row_deductions \/ block_deductions
    val run_deductions = deductions("Deduction").iter(P"d", S"rem", (sP"remaining" /\ sP"d").tee(
//      R"remaining"(S"r"))
      S"rem"("Cell").iter(P"cx", S"rx_r", S"rx_r".iter(P"rx", S"other", {
//      case s if s.size == 1 => inf.bottom - s.head
        val lvs = initial(P"cx")(P"rx")
        (First(1, lvs) /\ Last(1, lvs)).iter(P"s", S"_",
          ("rem" x headk(S"other", 3)) \/ ("add" x headk(S"other", 3) x (options \ sP"s"))
        )
      }))
    ))


    println(eval(block_deductions).prettyLines)
  }

  test("gol") {
    //   0  1  2  3  4
    // 0
    // 1    x
    // 2 x     x
    // 3          x
    // 4
    // (evolves into square)
    given SpaceContext = SpaceContextMap(Map(
      SpaceMention("Living") -> SpaceValue(
        "Cell.0.2",
        "Cell.1.1",
        "Cell.2.2",
        "Cell.3.3"),
      SpaceMention("Boundary") -> SpaceValue("0", "1", "2", "3", "4")
    ))
    extension (p: Path) def + (s: Space): Space = ("+" x p x s).arithmetic
    extension (p: Path) def `+₂` (s: Space): Space = ("+₂" x p x s).arithmetic
    extension (s: Space) def arithmetic: Space = Space.GroundedSS(s, s => SpaceValue(
      (for case PathValue(PathItem.Symbol("+")::PathItem.Symbol(x)::PathItem.Symbol(y)::Nil) <- s.paths yield
        PathValue(PathItem.Symbol((x.toInt + y.toInt).toString)::Nil)) union
      (for case PathValue(PathItem.Symbol("+₂")::PathItem.Symbol(x0)::PathItem.Symbol(x1)::
                                                 PathItem.Symbol(y0)::PathItem.Symbol(y1)::Nil) <- s.paths yield
        PathValue(PathItem.Symbol((x0.toInt + y0.toInt).toString)::PathItem.Symbol((x1.toInt + y1.toInt).toString)::Nil))
    ))
    def card(space: Space): Path = Path.GroundedSP(space, sv => PathValue(List(PathItem.Symbol(sv.paths.size.toString))))
    given PartialFunction[RoutinePtr, Routine] = {
      case RoutinePtr("neigh") => R"neigh"(P"coord") := {
        val offsets = Space.Literal(SpaceValue("-1", "0", "1"))
        (P"coord" `+₂` (offsets x offsets)) \ sP"coord"
      }
      case RoutinePtr("nextStep") => R"nextStep"(S"field") := "Cell" x ((
        S"field"("Cell").iter(P"x", S"ys", S"ys".iter(P"y", S"_",
          DropHead((Singleton(card(R"neigh"(P"x" x P"y") /\ S"field"("Cell"))) /\ ss"2") x Singleton(P"x" x P"y"))))
        \/
        S"field"("Cell").iter(P"x", S"ys", S"ys".iter(P"y", S"_",
          R"neigh"(P"x" x P"y"))).iter(P"x", S"ys", S"ys".iter(P"y", S"_",
          DropHead((Singleton(card(R"neigh"(P"x" x P"y") /\ S"field"("Cell"))) /\ ss"3") x Singleton(P"x" x P"y"))))
      ): Space)
    }

    println(eval(R"nextStep"(S"Living")).prettyLines)
    assert(eval(R"nextStep"(R"nextStep"(S"Living"))).prettyLines == "Cell.1.1\nCell.1.2\nCell.2.1\nCell.2.2")
  }

/*  test("multi transform") {
    given SpaceContext = context

//    println(MQT(S"sequences", List("$x", "$y", "$z"), "$z.$y.$x").show)
    assert(eval(MQT(S"graph"("edge"), List("$x.$y", "$y.$z", "$z.$x"), "$z.$y.$x")) == SpaceValue("x.y.z", "y.z.x", "z.x.y"))
    assert(eval(MQT(S"graph"("edge"), List("$x.$y", "$y.$z", "$z.$w"), "start.$x.end.$w")) == SpaceValue("start.s.end.v", "start.t.end.w", "start.x.end.x", "start.x.end.y", "start.x.end.z", "start.y.end.x", "start.y.end.y", "start.z.end.y", "start.z.end.z"))
//    val code = optimize(transpile(R"3-paths", "graph"),
//      MQT(S"graph"("edge"), List("$x.$y", "$y.$z", "$z.$u", "$u.$v", "$v.$w"), "start.$x.end.$w")
//    )))
    println(MQT(S"graph"("edge"), List("$x.$y", "$y.$z", "$z.$w"), "start.$x.end.$w").show)

    val code = R"3-paths", "graph"),
      MQT(S"graph"("edge"), List("$x.$y", "$y.$z", "$z.$u", "$u.$v", "$v.$w", "$w.$x"), "$w.$v.$u.$z.$y.$x")
    )

    println(code.show)
    println()
//    val po_code = push_out(code)
//    println(po_code.show)
//    println(mermaid(code))
//    println(mermaid())
//    println(MQT(S"graph"("edge"), List("$x.$y", "$y.$z", "$z.$w"), "start.$x.end.$w").show)
//    println(transpile(R"paths-3", "g"), MQT(S"g", List("$x.$y", "$y.$z", "$z.$w"), "start.$x.end.$w"))).show)
//    println(push_out(transpile(R"paths-3", "g"), MQT(S"g", List("$x.$y", "$y.$z", "$z.$w"), "start.$x.end.$w")))).show)
  }*/

  test("graphviz") {
//    val program = transpile(R"paths-3", "g"), MQT(S"g", List("$x.$y", "$y.$z", "$z.$w"), "start.$x.end.$w")))
//    graphviz(program)
  }

//  test("alpha rule") {
//    /*
//    (ɑ-rule $ex) =
//      {(Rem $r), (Add $a)} = $ex \{ ((ɑ $i) $q $y)
//                                    ($x $p (ɑ $i)) } =>
//                                  { (Rem ($x $p (ɑ $i)))
//                                    (Rem ((ɑ $i) $q $y))
//                                    (Add ($x $p $y)) }
//      ($ex \ $r) \/ a
//     */
//    val alpha_rule = R"ɑ-rule", "ex"), {
//      val t = MQMT(S"ex", List("3.2.ɑ.$i.$q.$y", "3.$x.$p.2.ɑ.$i"),
//                          List("2.Rem.3.$x.$p.2.ɑ.$i", "2.Rem.3.2.ɑ.$i.$q.$y", "2.Add.3.$x.$p.$y"))
//      (S"ex" \ t("2.Rem")) \/ t("2.Add")
//    })
//    println(optimize(transpile(alpha_rule)).show)
//  }

end Unification

object Unification:
  import Space.*
  val context = SpaceContextMap(Map(
    SpaceMention("sequences") -> SpaceValue(
      "b.a.a.b",
      "b.e.e.b",
      "b.e.e.b.b.e.e.b",
      "b.e.e.p.b.o.o.p",
      "b.a.b.a.b.a",
      "a.c.a.c",
    ),
    SpaceMention("graph") -> SpaceValue(
      "edge.a.b", "edge.a.d", "edge.d.c",
      "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y",
      "edge.s.t", "edge.t.u", "edge.u.v", "edge.v.w",
    )))

  def U(src: Space, p: PathValue, c: (Space, Map[String, PathRef]) => Space, bound: Map[String, PathRef] = Map.empty): Space = p.items match
    case h :: tail => h match
      case PathItem.Symbol(s) => U(Unwrap(src, Path.Constant(PathValue(h :: Nil))), PathValue(tail), c, bound)
      case PathItem.Arity(a) => U(Unwrap(src, Path.Constant(PathValue(h :: Nil))), PathValue(tail), c, bound)
      case PathItem.Variable(n) =>
        if bound.contains(n) then U(Unwrap(src, Path.Deref(bound(n))), PathValue(tail), c, bound)
        else Space.Iteration(src, PathRef(n), SpaceMention(n + "_"),
          U(Space.Mention(SpaceMention(n + "_")), PathValue(tail), c, bound + (n -> PathRef(n))))
    case Nil => c(src, bound)

  def C(t: PathValue, bound: Map[String, PathRef] = Map.empty): Path =
    t.items.map {
      case h@PathItem.Symbol(n) => Path.Constant(PathValue(h :: Nil))
      case h@PathItem.Arity(k) => Path.Constant(PathValue(h :: Nil))
      case PathItem.Variable(n) => Path.Deref(bound(n))
    }.reduceRight(_ x _)

  def W(src: Space, t: PathValue, bound: Map[String, PathRef] = Map.empty): Space =
    t.items.foldRight(src)((h, r) => h match
      case PathItem.Symbol(n) => Path.Constant(PathValue(h :: Nil)) x r
      case PathItem.Arity(k) => Path.Constant(PathValue(h :: Nil)) x r
      case PathItem.Variable(n) => Path.Deref(bound(n)) x r)

  def Q(src: Space, p: PathValue): Space =
    U(src, p, W(_, p, _))

  def T(src: Space, p: PathValue, t: PathValue): Space =
    U(src, p, W(_, t, _))

  def DQT(src: Space, p: PathValue, q: PathValue, t: PathValue): Space =
    U(src, p, (s, b) => U(src, q, (ss, bb) => W(
//      U(s, p) /\ ss
      Space.Empty

      , t, bb), b))

  def TQT(src: Space, p: PathValue, q: PathValue, r: PathValue, t: PathValue): Space = {
    // W(Space.Empty, t, bbb)
    U(src, p, (s, b) => U(src, q, (ss, bb) => U(src, r, (sss, bbb) => { println(s"3 $p $q $r $bbb"); W(Space.Empty, t, bbb) }, bb), b))
  }

  // determine maximal sharing, sort `ps` from lowest to highest freedom
  def MQT(src: Space, ps: List[PathValue], t: PathValue, r: Option[Space] = None, bound: Map[String, PathRef] = Map.empty): Space = ps match
    case p :: ps => U(src, p, (s, b) => MQT(src, ps, t, Some(s), b), bound)
    case Nil => W(r.get, t, bound)

  /// uhm, why do we drop (s
  def MQMT(src: Space, ps: List[PathValue], ts: List[PathValue], bound: Map[String, PathRef] = Map.empty): Space = ps match
    case p :: ps => U(src, p, (s, b) => MQMT(src, ps, ts, b), bound)
    case Nil => ts.map(t => Singleton(C(t, bound))).reduceRight(_ \/ _)
end Unification


class Lowering extends FunSuite:
  test("DropHead iter subs") {
    val code = Lower.DropHead_Iteration(Routines.aunt_query_routine.body)
    assert(code.show == ("Aunt" x S"people".iter(P"person", S"_",
      (P"person" x (((S"family"("parent") <| (S"family"("child") <| S"family"("child" x P"person")).iter(P"_", S"s90ea6c6d", S"s90ea6c6d")).iter(P"_", S"sd4835f8c", S"sd4835f8c") \ S"family"("child" x P"person")) /\ S"family"("female")))
    )).show)
  }

  test("aunt query specialize") {
    val literal_people = subs(Routines.aunt_query_routine.body)(spre={ case Space.Mention(SpaceMention("people")) => Space.Literal(SpaceValue("Xeya", "Jim")) })
//    "Aunt" x Literal(SpaceValue("Jim", "Xeya")).iter(P"person", S"_",
//      P"person" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x P"person"))) \ S"family"("child" x P"person")) /\ S"family"("female")))
    val unrolled_people = Lower.IterateLiteral_Union(literal_people)
//    "Aunt" x (("Xeya" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x "Xeya"))) \ S"family"("child" x "Xeya")) /\ S"family"("female")))
//           \/ ("Jim" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x "Jim"))) \ S"family"("child" x "Jim")) /\ S"family"("female"))))
    val folded_people = Lower.Concat_Path(unrolled_people)
//    "Aunt" x (("Xeya" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child.Xeya"))) \ S"family"("child.Xeya")) /\ S"family"("female")))
//           \/ ("Jim" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child.Jim"))) \ S"family"("child.Jim")) /\ S"family"("female"))))
    assert(folded_people.show == ("Aunt" x (("Xeya" x ((DropHead((S"family"("parent") <| DropHead((S"family"("child") <| S"family"("child.Xeya"))))) \ S"family"("child.Xeya")) /\ S"family"("female"))) \/ ("Jim" x ((DropHead((S"family"("parent") <| DropHead((S"family"("child") <| S"family"("child.Jim"))))) \ S"family"("child.Jim")) /\ S"family"("female"))))).show)
  }
end Lowering


class SpacialType extends FunSuite:
//  R"aunts", "family", "people"),
//    "Aunt" x S"people".iter(P"person", S"_",
//      P"person" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x P"person"))) \ S"family"("child" x P"person")) /\ S"family"("female")))
//  )

  test("aunt query input type") {
//    INPUT TYPE: "people" x $person \/
//      "family" x ("parent" x _ \/
//                  "child" x _ x _ \/
//                  "female" x _)
    val code = Lower.DropHead_Iteration(Routines.aunt_query_routine.body)
    println(code.show)
    println(itypes(code).show)

    ("Aunt" x S"people".iter(P"person", S"_",
      (P"person" x (((S"family"("parent") <|
        (S"family"("child") <| S"family"("child" x P"person")).iter(P"_", S"s90ea6c6d", S"s90ea6c6d")
        ).iter(P"_", S"sd4835f8c", S"sd4835f8c") \ S"family"("child" x P"person")) /\ S"family"("female")))
    ))
  }

  test("aunt query output type") {
//    OUTPUT TYPE: "Aunt" x $person x _
//    val code = Lower.DropHead_Iteration(Routines.aunt_query_routine.body)
    val code = Routines.child_routine.body
    println(code.show)
    println(itypes(code).show)
    println(otypes(code).show)

  }
end SpacialType


class Grounded extends FunSuite:
  import Space.*

  val context = SpaceContextMap(Map(
    SpaceMention("family") -> SpaceValue(
      "parent.Tom.Bob", "child.Bob.Tom",
      "parent.Pam.Bob", "child.Bob.Pam",
      "parent.Tom.Liz", "child.Liz.Tom",
      "parent.Bob.Ann", "child.Ann.Bob",
      "parent.Bob.Pat", "child.Pat.Bob",
      "parent.Pat.Jim", "child.Jim.Pat",
      "female.Pam", "female.Liz", "female.Pat", "female.Ann",
      "male.Tom", "male.Bob", "male.Jim",
      "person.Tom", "person.Bob", "person.Jim", "person.Pam", "person.Liz", "person.Pat", "person.Ann"),
    SpaceMention("people") -> SpaceValue("Tom", "Bob", "Jim", "Pam", "Liz", "Pat", "Ann")))

  def hash(path: Path): Path =
    Path.GroundedPP(path, pv => PathValue(List(PathItem.Symbol("R" + pv.hashCode().toHexString))))

  def hash(space: Space): Path =
    Path.GroundedSP(space, sv => PathValue(List(PathItem.Symbol("R" + sv.hashCode().toHexString))))

  def trace(path: Path)(using ab: collection.mutable.ArrayBuffer[PathValue]): Path =
    Path.GroundedPP(path, pv => { ab.addOne(pv); pv })

  def spacesize(space: Space): Path =
    Path.GroundedSP(space, sv => PathValue(List(PathItem.Symbol(sv.paths.size.toString))))

  def spaceout(space: Space)(using ab: collection.mutable.ArrayBuffer[SpaceValue]): Path =
    Path.GroundedSP(space, sv => { ab.addOne(sv); PathValue(List(PathItem.Symbol("unit")))  })

  def range(path: Path): Space =
    Space.GroundedPS(path, x => x.items.map{ case PathItem.Symbol(s) => s.toIntOption } match
      case Seq(Some(stop)) => SpaceValue(Set.from((0 until stop).map(i => PathValue(List(PathItem.Symbol(i.toString))))))
      case Seq(Some(start), Some(stop), Some(step)) => SpaceValue(Set.from((start until stop by step).map(i => PathValue(List(PathItem.Symbol(i.toString)))))))

  def transitive(space: Space): Space =
    Space.GroundedSS(space, sv => {
      var otsv = sv
      var tsv = eval(Literal(sv) \/ Literal(sv).iter(P"x", S"r", P"x" x DropHead(Literal(sv) <| S"r")))(using PathContext.emptyMap, SpaceContextMap(Map()))
      while otsv != tsv do
        otsv = tsv
        tsv = eval(Literal(otsv) \/ Literal(otsv).iter(P"x", S"r", P"x" x DropHead(Literal(otsv) <| S"r")))(using PathContext.emptyMap, SpaceContextMap(Map()))
      tsv
    })

  test("PP hash") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    val e = S"family"("parent").iter(P"x", S"r", S"r".iter(P"y", S"_", Singleton(hash(P"x" x P"y"))))

    assert(eval(e) == SpaceValue("R2606dfba", "R86aea026", "Rc50d6b68", "Re4c8532", "Re59e471", "Re7a6b6e1"))
  }

  test("PP trace") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    given ps: collection.mutable.ArrayBuffer[PathValue] = collection.mutable.ArrayBuffer.empty

    val e = S"family"("parent").iter(P"x", S"r", S"r".iter(P"y", S"_", Singleton(trace(P"x" x P"y"))))

    eval(e)
    assert(ps.map(_.show).mkString("; ") == "Tom.Liz; Tom.Bob; Pat.Jim; Bob.Ann; Bob.Pat; Pam.Bob")
  }

  test("SP spacesize") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context

    val e = S"family"("parent").iter(P"x", S"r", Singleton(P"x" x "has" x spacesize(S"r") x "children"))

    assert(eval(e) == SpaceValue("Bob.has.2.children", "Pam.has.1.children", "Pat.has.1.children", "Tom.has.2.children"))
  }

  test("SP spaceout") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    val e = S"family"("parent").iter(P"x", S"r", Singleton(spaceout(S"r")))

    assert(eval(e) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("Bob", "Liz"), SpaceValue("Jim"), SpaceValue("Ann", "Pat"), SpaceValue("Bob")))
  }

  test("PS range") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context

    val e = range("0.10.2").iter(P"x", S"_1", range("1" x P"x" x "1").iter(P"y", S"_2", Singleton("pair" x P"x" x P"y")))

    assert(eval(e) == SpaceValue("pair.2.1", "pair.4.1", "pair.4.2", "pair.4.3", "pair.6.1", "pair.6.2", "pair.6.3", "pair.6.4", "pair.6.5", "pair.8.1", "pair.8.2", "pair.8.3", "pair.8.4", "pair.8.5", "pair.8.6", "pair.8.7"))
  }

  test("SS transitive") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    /*
    a  ->  b   x  <->  y
      \           \    ^
        ◢           ◢  |
    c  <-  d           z
     */
    val graph = Literal(SpaceValue("edge.a.b", "edge.a.d", "edge.d.c", "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y"))
    val lhs = "edge" x transitive(graph("edge"))
    val rhs = "edge" x (("a" x Literal(SpaceValue("b", "d", "c"))) \/
                        ("d" x Literal(SpaceValue("c"))) \/
                        (Literal(SpaceValue("x", "y", "z")) x Literal(SpaceValue("x", "y", "z"))))
    assert(eval(lhs) == eval(rhs))
  }

end Grounded

object Grounded:
  import Space.*

  def sample(space: Space): Space =
    Space.GroundedSS(space, sv => {
      val seed = eval(Literal(sv)("seed")).paths.head.show.hashCode
      val count = eval(Literal(sv)("count")).paths.head.show.toInt
      val space = eval(Literal(sv)("space")).paths
      val r = util.Random(seed)
      SpaceValue(Set.from(r.shuffle(space.toSeq).take(count)))
    })

end Grounded

class Datalog extends FunSuite:
  import Space.*
  import Unification.MQT
  import Routines.fixpoint

  test("trans naive") {
    //  path(x, y) :- (edge(x, y))
    //  path(x, z) :- (path(x, y), path(y, z))
    val r = fixpoint(last => MQT(last, List("edge.$x.$y"), "path.$x.$y") \/
                             MQT(last, List("path.$x.$y", "path.$y.$z"), "path.$x.$z"))
    val r_name = r.name

    val initial = SpaceValue("edge.a.b", "edge.b.c", "edge.c.d", "edge.d.e")
    assert(eval(r_name(Literal(initial))("path"))(using rc = {case `r_name` => r}) ==
      SpaceValue("a.b", "a.c", "a.d", "a.e", "b.c", "b.d", "b.e", "c.d", "c.e", "d.e"))
  }

  test("trans semi-naive") {
    //  path(x, y) :- (edge(x, y))
    //  path(x, z) :- (path(x, y), path(y, z))
    val r = fixpoint(last => ("complete" x (last("complete") \/ last("delta"))) \/ ("delta.path" x (
      (MQT(last, List("complete.edge.$x.$y"), "$x.$y") \/
       MQT(last, List("complete.path.$x.$y", "delta.path.$y.$z"), "$x.$z") \/
       MQT(last, List("delta.path.$x.$y", "complete.path.$y.$z"), "$x.$z") \/
       MQT(last, List("delta.path.$x.$y", "delta.path.$y.$z"), "$x.$z"))
        \ (last("complete.path") \/ last("delta.path")))))
    val r_name = r.name

    val data = Literal(SpaceValue("edge.a.b", "edge.b.c", "edge.c.d", "edge.d.e"))
    val initial = ("delta" x (MQT(data, List("edge.$x.$y"), "path.$x.$y") \/ MQT(data, List("path.$x.$y", "path.$y.$z"), "path.$x.$z"))) \/ ("complete" x data)
    assert(eval(r_name(initial)("complete.path"))(using rc = {case `r_name` => r}) ==
      SpaceValue("a.b", "a.c", "a.d", "a.e", "b.c", "b.d", "b.e", "c.d", "c.e", "d.e"))
  }
end Datalog

class UnionFind extends FunSuite:
  import Space.*

  val tree0 = SpaceValue("parent.4.3", "parent.3.0", "parent.0.0", "parent.1.0", "parent.2.5", "parent.5.5")

  val find_routine = R"find"(P"x", S"tree") :=
    (S"tree"(P"x") \ sP"x").iter(P"p", S"_", R"find"(P"p", ((S"tree" \ Singleton(P"x" x P"p")) \/ (P"x" x S"tree"(P"p"))))) \/
    (ss"tobeempty" \ ("tobeempty" x (S"tree"(P"x") \ sP"x") ).iter(P"H", S"E", sP"H")).iter(P"T", S"N",
      ("res" x sP"x") \/ ("tree" x S"tree"))


//  val union_routine = R"union", Vector("x", "y"), Vector("tree"),
//
//  )

  test("find") {
    given PartialFunction[RoutinePtr, Routine] = { case RoutinePtr("find") => find_routine }
    println(eval(R"find"(P"4", Literal(tree0)("parent"))).prettyLines)
  }

end UnionFind

/*
class IV extends FunSuite:
  import Space.*

  def highest(s: Space, backup: PathValue): Path =
    Path.GroundedSP(s, sv => sv.paths.flatMap(_.items.headOption).maxByOption(_.show).fold(backup)(x => PathValue(List(x))))

  def lowest(s: Space, backup: PathValue): Path =
    Path.GroundedSP(s, sv => sv.paths.flatMap(_.items.headOption).minByOption(_.show).fold(backup)(x => PathValue(List(x))))

  def or_else(e: Space, todo: Space): Space = // or
    e \/ (ss"tobeempty" \ ("tobeempty" x e).iter(P"H", S"E", SP"H")).iter(P"T", S"N", todo)

  def add(path: Path): Path =
    Path.GroundedPP(path, x => x.items.map { case PathItem.Symbol(s) => s.toIntOption } match
      case Seq(Some(x), Some(y)) => PathValue(List(PathItem.Symbol((x + y).toString))))

  def sub(path: Path): Path =
    Path.GroundedPP(path, x => x.items.map { case PathItem.Symbol(s) => s.toIntOption } match
      case Seq(Some(x), Some(y)) => PathValue(List(PathItem.Symbol((x - y).toString))))

  def spacesize(space: Space): Path =
    Path.GroundedSP(space, sv => PathValue(List(PathItem.Symbol(sv.paths.size.toString))))

  def maxsymbol(space: Space): Space =
    Space.GroundedSS(space, sv =>
      sv.paths.flatMap(_.items.headOption).maxByOption(_.show) match
        case Some(v) => SpaceValue(PathValue(List(v)))
        case None => SpaceValue()
    )

  def range(path: Path): Space =
    Space.GroundedPS(path, x => x.items.map { case PathItem.Symbol(s) => s.toIntOption } match
      case Seq(Some(stop)) => SpaceValue((0 until stop).map(i => PathValue(List(PathItem.Symbol(i.toString)))).toSet)
      case Seq(Some(start), Some(stop), Some(step)) => SpaceValue((start until stop by step).map(i => PathValue(List(PathItem.Symbol(i.toString)))).toSet))

  def map(v: Space, f: Space => Space): Space =
    v.iter(P"i", S"v", P"i" x f(S"v"))

  def flatMap(f: Space => Space): Routine = routine(s"flatMap${f.hashCode()}", Vector("i", "j"), Vector("v"), {
    (P"i" x S"v"(P"i")).iter(P"_", S"r",
    R"shift_right"(Vector(P"j"), Vector(f(S"r"))) \/
      or_else(maxsymbol(f(S"r")).iter(P"ms", S"__", Singleton(add(P"ms" x "1"))), ss"0").iter(P"mss", S"___",
        RoutinePtr(s"flatMap${f.hashCode()}")(Vector(add(P"i" x "1"), add(P"j" x P"mss")), Vector(S"v")))
    )
  })

  // can be done grounded by bit shifting
  val shift_right_routine = R"shift_right", Vector("o"), Vector("xs"),
    S"xs".iter(P"x", S"r", add(P"x" x P"o") x S"r")
  )

  val shift_left_routine = R"shift_left", Vector("o"), Vector("xs"),
    S"xs".iter(P"x", S"r", sub(P"x" x P"o") x S"r")
  )

  val concat_routine = R"concat", "xs", "ys"),
    or_else(maxsymbol(S"xs").iter(P"ms", S"_",
      S"xs" \/ R"shift_right"(Vector(add(P"ms" x "1")), Vector(S"ys"))), S"ys")
  )

  // [a, b, c, d].drop(2) == [c, d]
  val drop_routine = R"concat", Vector("k"), Vector("xs"),
    maxsymbol(S"xs").iter(P"ms", S"_",
      R"shift_left"(Vector(P"k"), Vector(S"xs" <| range(P"k" x add(P"ms" x "1") x "1"))))
  )

  // [a, b, c, d].take(2) == [a, b]
  val take_routine = R"concat", Vector("k"), Vector("xs"),
    S"xs" <| range("0" x P"k" x "1")
  )

  val copy_routine = R"copy", "xs", "m"),
    maxsymbol(S"xs").iter(P"ms", S"ms_",
      range("0" x add(P"ms" x "1") x "1").fold("0", "j", "i", "_",
        range(P"j" x add(P"j" x highest(S"m"(P"i"), "0")) x "1") x S"xs"(P"i"),
        add(P"j" x highest(S"m"(P"i"), "0"))
      )
    )
  )

  // index(1 -> a, 100 -> b, 200 -> c) == [a, b, c]
  val index_routine = R"index", "xs"),
    S"xs".fold("0", "i", "_", "v",
      P"i" x S"v",
      add(P"i" x "1")
    )
  )

  // zip_with_f([a, b, c], [foo, bar]) == [f(a, foo), f(b, bar)]
  def zip_with_routine(combine: (Space, Space) => Space) = routine(s"zip_with${combine.hashCode()}", "xs", "ys"),
    min(highest(maxsymbol(S"xs"), "0") x highest(maxsymbol(S"ys"), "0")).iter(P"ms", S"ms_",
      range("0" x add(P"ms" x "1") x "1").iter(P"i", S"_",
        P"i" x combine(S"xs"(P"i"), S"ys"(P"i"))
      )
    )
  )

  def odd_even_sort(lt: (Space, Space) => Path): Routine = routine(s"odd_even_sort${lt.hashCode()}", Vector("n", "k"), Vector("xs"),
    ite(
      P"k" == P"n",
      S"xs",
      RoutinePtr(s"odd_even_sort${lt.hashCode()}")(Vector(P"n", sub(P"k" x "1")), Vector(range("0" x P"n" x "2").iter(P"i", S"_",
        ite(
          lt(S"xs"(P"i"), S"xs"(add(P"i" x "1"))),
          (P"i" x S"xs"(P"i")) \/ (add(P"i" x "1") x S"xs"(add(P"i" x "1"))),
          (add(P"i" x "1") x S"xs"(P"i")) \/ (P"i" x S"xs"(add(P"i" x "1")))
        )
      ))
    ))
  )

  def quick_sort(lt: (Space, Space) => Path): Routine = routine(s"quick_sort${lt.hashCode()}", Vector("lo", "hi"), Vector("xs"),
    maxsymbol(S"xs").iter(P"ms", S"ms_", {
      val pivot = S"xs"(P"ms")
      val partition = (S"xs" <| range(P"lo" x P"hi" x "1")).fold(P"lo", "i", "j", "x",
        ite(
          lte(S"x", pivot),
          P"i" x "x",
        ),
        ite(
          lte(S"x", pivot),
          add(P"i" x "1"),
          P"i"
        )
      )
      RoutinePtr(s"quick_sort${lt.hashCode()}")(???) \/ RoutinePtr(s"quick_sort${lt.hashCode()}")(???)
    })
  )

  given vectorOps: PartialFunction[RoutinePtr, Routine] = Map(RoutinePtr("shift_left") -> shift_left_routine, RoutinePtr("shift_right") -> shift_right_routine,
    RoutinePtr("concat") -> concat_routine, RoutinePtr("drop") -> drop_routine, RoutinePtr("take") -> take_routine)

  test("access") {
    val xs = SpaceValue("0.a", "1.b", "2.c", "3.d", "4.e")

    assert(eval(Unwrap(Literal(xs), "1")) == SpaceValue("b"))
    assert(eval(DropHead(Literal(xs) <| range("1.3.1"))) == SpaceValue("b", "c"))
    assert(eval(DropHead(Literal(xs) <| range("0.6.2"))) == SpaceValue("a", "c", "e"))
  }

  test("map") {
    val xs = SpaceValue("0.a", "1.b", "2.c", "3.d", "4.e")
    val capital = SpaceValue("a.A", "b.B", "c.C", "d.D", "e.E")
    // [a, b, c, d, e]
    eval(Literal(xs).iter(P"i", S"vs", P"i" x S"vs".iter(P"v", S"_", Literal(capital)(P"v")))) ==
      SpaceValue("0.A", "1.B", "2.C", "3.D", "4.E")
  }

  test("concat") {
    val xs = SpaceValue("0.a", "1.b", "2.c")
    val ys = SpaceValue("0.foo", "1.bar")

    assert(eval(R"concat"(Literal(xs), Literal(ys)))) == SpaceValue("0.a", "1.b", "2.c", "3.foo", "4.bar"))
  }

  test("swap_halves") {
    val xs = SpaceValue("0.a", "1.b", "2.c", "3.x", "4.y", "5.z")

    assert(eval(R"concat"(
      R"take"(Vector("3"), Vector(Literal(xs))),
      R"drop"(Vector("3"), Vector(Literal(xs))),
    ))) == SpaceValue("0.a", "1.b", "2.c", "3.x", "4.y", "5.z"))
  }

  test("copy") {
    val xs = SpaceValue("0.a", "1.b", "2.c", "3.d", "4.e")
    val mask = SpaceValue("0.2", "1.1", "2.0", "3.0", "4.1")

    val out = SpaceValue("0.a", "1.a", "2.b", "3.e")


  }

  test("flatMap doubling") {
    // [e, e]
    val fm = flatMap(e => ("0" x e) \/ ("1" x e))
    val fm_name = fm.name

    val xs = SpaceValue("0.a", "1.b", "2.c")

//    R"flatMap19", Vector("i", "j"), Vector("v"),
//      (P"i" x (("0" x S"v"(P"i")) \/ ("1" x S"v"(P"i")))).iter(P"_", S"r",
//       (shift_right(P"j"; S"r") \/ flatMap19(PP13(P"i" x "1"), PP13(P"j" x PP13(SP16(S"r") x "1")); S"v"))
//      )
//    )
    assert(eval(fm_name(Vector("0", "0"), Vector(Literal(xs))))(using rc = vectorOps orElse {case `fm_name` => fm}) ==
      SpaceValue("0.a", "1.a", "2.b", "3.b", "4.c", "5.c"))
  }

  test("flatMap filter") {
    // if 10 <= e < 100 then [e] else []
    val fm = flatMap(e => ss"0" x (e /\ range("10.100.1")))
    val fm_name = fm.name

    val xs = SpaceValue("0.2", "1.15", "2.8", "3.15", "4.17", "5.9", "6.11")

    assert(eval(fm_name(Vector("0", "0"), Vector(Literal(xs))))(using rc = vectorOps orElse { case `fm_name` => fm }) ==
      SpaceValue("0.15", "1.15", "2.17", "3.11"))
  }

  test("odd even sort") {

  }
end IV
*/
