package morkl

import morkl.Space.Singleton
import munit.FunSuite
import morkl.Syntax.{x, *, given}
import org.apache.jena.sparql.expr.{E_Bound, E_Equals, E_GreaterThan, E_GreaterThanOrEqual, E_LessThanOrEqual, E_LogicalAnd, E_LogicalNot, E_LogicalOr, E_NotEquals, Expr, ExprFunction, ExprList}


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
//    val lhs = Restriction(Composition(Singleton("Foo"), Union(Union(
//      Composition(Singleton("Bar"), Space("1", "2", "3")),
//      Composition(Singleton("Baz"), Space("A", "B", "C"))),
//      Composition(Singleton("Cux"), Space("Red", "Blue")))), Space("Foo.Bar", "Foo.Baz"))
//    val rhs = Composition(Singleton("Foo"), Union(
//      Composition(Singleton("Bar"), Space("1", "2", "3")),
//      Composition(Singleton("Baz"), Space("A", "B", "C"))))
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("composition") {
//    given PathContext()
//    given SpaceContext()
//    val prefixed = Composition(Singleton("Foo"), Space("bar", "baz", "cux"))
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
//    val lhs = Subspace(Composition(Singleton("Foo"), Union(
//      Composition(Singleton("Bar"), Space("1", "2", "3")),
//      Composition(Singleton("Baz"), Space("A", "B", "C")))), "Foo.Baz")
//    val rhs = Space("A", "B", "C")
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("drophead") {
//    given PathContext()
//    given SpaceContext()
//    val lhs = DropHead(Composition(Singleton("Foo"), Union(
//      Composition(Singleton("Bar"), Space("1", "2", "3")),
//      Composition(Singleton("Baz"), Space("A", "B", "C")))))
//    val rhs = Union(
//      Composition(Singleton("Bar"), Space("1", "2", "3")),
//      Composition(Singleton("Baz"), Space("A", "B", "C")))
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("transformation") {
//    given PathContext()
//    given SpaceContext()
//    val lhs = Transformation(Composition(Singleton("Foo"), Union(Union(
//      Composition(Singleton("Bar"), Space("1", "2", "3")),
//      Composition(Singleton("Baz"), Space("A", "B", "C"))),
//      Composition(Singleton("Cux"), Space("Red", "Blue")))), "$_.Cux.$c", "Result.Color.$c")
//    val rhs = Space("Result.Color.Red", "Result.Color.Blue")
//    assert(eval(lhs) == eval(rhs))
//  }
//
//  test("left_residual") {
//    given PathContext()
//    given SpaceContext()
//    // all prefixes we can add to y such prefix.y <= x
//    val x = Composition(Singleton("Test.Foo"), Union(Union(
//      Composition(Singleton("Bar"), Space("1", "2", "3", "4", "5", "6")),
//      Composition(Singleton("Baz"), Space("1", "2", "3", "A", "B", "C"))),
//      Composition(Singleton("Cux"), Space("Red", "Blue"))))
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
//      Composition(Singleton("Bar"), Space("1", "2", "3", "4", "5", "6")),
//      Composition(Singleton("Baz"), Space("1", "2", "3", "A", "B", "C"))),
//      Composition(Singleton("Cux"), Space("Red", "Blue"))))
//    val y = Space("Test.Foo.Bar", "Test.Foo.Baz")
//    val lhs = RightResidual(y, x)
//    val rhs = Space("1", "2", "3")
//    assert(eval(lhs) == eval(rhs))
//  }
end MORKL2Space

class AuntQuery extends FunSuite:
  import Space.*
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

  test("add_index") {
//    val rhs = S"ifamily" \/ S"ifamily".transform("parent.$x.$y", "child.$y.$x")
    val rhs = S"ifamily"
      \/ ("child" x S"ifamily"("parent").iter("x", "r", S"r".iter("y", "_", Singleton(P"y" x P"x"))))
      \/ ("person" x S"ifamily"("female"))
      \/ ("person" x S"ifamily"("male"))
    assert(eval(rhs)(using PathContext.emptyMap, initial_context) == eval(S"family")(using PathContext(), context))
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
    
    val res = "Mother" x S"people".iter("person", "_",
      P"person" x (S"family"("child" x P"person") /\ S"family"("female"))
    )

    assert(eval(res) == SpaceValue("Mother.Jim.Pat", "Mother.Bob.Pam"))
  }

  test("sister_query") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    val res = "Sister" x S"people".iter("person", "_",
      P"person" x ((DropHead(S"family"("parent") <| S"family"("child" x P"person")) /\ S"family"("female")) \ Singleton(P"person"))
    )

    assert(eval(res) == SpaceValue("Sister.Ann.Pat", "Sister.Pat.Ann", "Sister.Bob.Liz"))
  }

  test("aunt_query") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    val res = "Aunt" x S"people".iter("person", "_",
      P"person" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x P"person"))) \ S"family"("child" x P"person")) /\ S"family"("female"))
    )

    assert(eval(res) == SpaceValue("Aunt.Ann.Liz", "Aunt.Jim.Ann", "Aunt.Pat.Liz"))
  }

/*  test("predecessors_query") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context

    val res = "Predecessor" x R"people".iter($"person",
      {
        val pred0 = R"family.child"($"person")
        var oldest0 = pred0

        pred1 = pred0 \/ oldest0
        oldest1 = DropHead(R"family.child" <| oldest0)

        pred2 = pred1 \/ oldest1
        oldest2 = DropHead(R"family.child" <| oldest1)

        Space.Literal(SpaceValue("1", "2")).fix($"i",
          ("pred" x $"i" x Read("pred" x Call($"decr", $"i")) \/ Read("oldest" x Call($"decr", $"i"))) \/
          ("oldest" x $"i" x DropHead(R"family.child" <| Read("oldest" x Call($"decr", $"i"))))
        )


        val pred = R"family.child"($"person")
        var oldest = pred
        while eval(oldest).nonEmpty do
          pred = pred \/ oldest
          oldest = DropHead(family("child") <| oldest)
      }

      $"person" x ((DropHead(R"family.parent" <| DropHead(R"family.child" <| R"family.child"($"person"))) \ R"family.child"($"person")) /\ R"family.female")
    )

      for person <- eval(people) do
        var pred = family(Concat("child", person))
        var oldest = pred
        while eval(oldest).nonEmpty do
          pred = pred \/ oldest
          oldest = DropHead(family("child") <| oldest)
        println(S"$person : ${eval(pred)}")
  }*/
end AuntQuery

class Imperative extends FunSuite:
  import Space.*

  val aunt_query_routine = routine("aunts", Vector(), Vector("family", "people"),
    "Aunt" x S"people".iter("person", "_",
      P"person" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x P"person"))) \ S"family"("child" x P"person")) /\ S"family"("female")))
  )

  val scc_routine = routine("scc", Vector(), Vector("fwd", "bwd", "nodes"),
    Limit(1, S"nodes").iter("v", "_",  {
      val pred: Space = R"reachable"(Vector(), Vector(S"fwd", S"nodes", Singleton(P"v")))
      val desc: Space = R"reachable"(Vector(), Vector(S"bwd", S"nodes", Singleton(P"v")))
      (P"v" x ((pred /\ desc) \ Singleton(P"v"))) \/
        R"scc"(Vector(), Vector(S"fwd", S"bwd", pred \ desc)) \/
        R"scc"(Vector(), Vector(S"fwd", S"bwd", desc \ pred)) \/
        R"scc"(Vector(), Vector(S"fwd", S"bwd", (S"nodes" \ pred) \ desc))
    })
  )

  val union_iter_routine = routine("union_iter", Vector(), Vector("xs", "ys"),
    S"xs".iter("x", "rx", P"x" x "Left" x S"rx") \/
    S"ys".iter("y", "ry", P"y" x "Right" x S"ry")
  )

  test("aunt query pretty") {
//    println(aunt_query_routine.show)
  }

  test("aunt query transpiled") {
//    println(transpile(aunt_query_routine).show)
  }

  test("scc transpiled") {
//    println(transpile(scc_routine).show)
//    println("optimized")
//    println(optimize_sharing(transpile(scc_routine)).show)
//    println(prune_redundant(optimize_sharing(transpile(scc_routine))).show)
  }

  test("transpile union iter") {
//    println(transpile(union_iter_routine).show)
  }
end Imperative

class Routines extends FunSuite:
  import Space.*

  def sample(space: Space): Space =
    Space.GroundedSS(space, sv => {
      val seed = eval(Literal(sv)("seed")).paths.head.show.hashCode
      val count = eval(Literal(sv)("count")).paths.head.show.toInt
      val space = eval(Literal(sv)("space")).paths
      val r = util.Random(seed)
      SpaceValue(r.shuffle(space.toSeq).take(count).toSet)
    })

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

  val aunt_query_routine = routine("aunts", Vector(), Vector("family", "people"),
    "Aunt" x S"people".iter("person", "_",
      P"person" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x P"person"))) \ S"family"("child" x P"person")) /\ S"family"("female")))
  )

  test("eval routine") {
    val lpeople = Literal(SpaceValue("Tom", "Bob", "Jim"))
    val e = R"aunts"(Vector(), Vector(S"family", lpeople))
    val result = SpaceValue("Aunt.Jim.Ann")
    assert(eval(e)(using PathContext.emptyMap, context, Map(RoutinePtr("aunts") -> aunt_query_routine)) == result)
  }

  val transitive_routine = routine("transitive", Vector(), Vector("edges"),
    S"edges" \/ R"transitive"(Vector(), Vector(S"edges" \/ S"edges".iter("n", "nbs", P"n" x DropHead(S"edges" <| S"nbs"))))
  )

  val reachable_routine = routine("reachable", Vector(), Vector("edges", "nodemask", "reach"),
    S"reach" \/ R"reachable"(Vector(), Vector(S"edges", S"nodemask",
      S"reach" \/ DropHead(S"edges" <| (S"reach" /\ S"nodemask")) /\ S"nodemask"))
  )

  val scc_routine = routine("scc", Vector("seed"), Vector("fwd", "bwd", "nodes"),
    sample(Singleton("seed" x P"seed") \/ Singleton("count.1") \/ ("space" x S"nodes")).iter("v", "_",  {
      val pred: Space = R"reachable"(Vector(), Vector(S"fwd", S"nodes", Singleton(P"v")))
      val desc: Space = R"reachable"(Vector(), Vector(S"bwd", S"nodes", Singleton(P"v")))
      (P"v" x ((pred /\ desc) \ Singleton(P"v"))) \/
      R"scc"(Vector(P"seed" x "0"), Vector(S"fwd", S"bwd", pred \ desc)) \/
      R"scc"(Vector(P"seed" x "1"), Vector(S"fwd", S"bwd", desc \ pred)) \/
      R"scc"(Vector(P"seed" x "2"), Vector(S"fwd", S"bwd", (S"nodes" \ pred) \ desc))
    })
  )

  test("transitive") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    /*
    a  ->  b   x  <->  y
      \           \    ^
        ◢           ◢  |
    c  <-  d           z
     */
    val graph = Literal(SpaceValue("edge.a.b", "edge.a.d", "edge.d.c", "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y"))
    val lhs = "edge" x R"transitive"(Vector(), Vector(graph("edge")))
    val rhs = "edge" x (("a" x Literal(SpaceValue("b", "d", "c"))) \/
      ("d" x Literal(SpaceValue("c"))) \/
      (Literal(SpaceValue("x", "y", "z")) x Literal(SpaceValue("x", "y", "z"))))
    assert(eval(lhs)(using rc = Map(RoutinePtr("transitive") -> transitive_routine)) == eval(rhs))
  }

  test("reachable") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    /*
    a  ->  b   x  <->  y  s -> t -> u -> v -> w
      \           \    ^
        ◢           ◢  |
    c  <-  d           z
     */
    val graph = Literal(SpaceValue("edge.a.b", "edge.a.d", "edge.d.c", "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y",
                                   "edge.s.t", "edge.t.u", "edge.u.v", "edge.v.w"))
    val transpose = graph("edge").iter("x", "r", S"r".iter("y", "_", Singleton(P"y" x P"x")))
    val nodes = graph("edge").iter("fwd", "_1", Singleton(P"fwd")) \/ transpose.iter("bwd", "_2", Singleton(P"bwd"))
    val fwd_t = R"reachable"(Vector(), Vector(graph("edge"), nodes, Singleton("t")))
    assert(eval(fwd_t)(using rc = Map(RoutinePtr("reachable") -> reachable_routine)) == SpaceValue("t", "u", "v", "w"))
    val fwd_s_no_v = R"reachable"(Vector(), Vector(graph("edge"), nodes \ Singleton("v"), Singleton("s")))
    assert(eval(fwd_s_no_v)(using rc = Map(RoutinePtr("reachable") -> reachable_routine)) == SpaceValue("s", "t", "u"))
    val bwd_c = R"reachable"(Vector(), Vector(transpose, nodes, Singleton("c")))
    assert(eval(bwd_c)(using rc = Map(RoutinePtr("reachable") -> reachable_routine)) == SpaceValue("c", "d", "a"))
    val fwd_a_no_ad = R"reachable"(Vector(), Vector(graph("edge") \ Singleton("a.d"), nodes, Singleton("a")))
    assert(eval(fwd_a_no_ad)(using rc = Map(RoutinePtr("reachable") -> reachable_routine)) == SpaceValue("a", "b"))
  }

  test("scc") {
    given PathContext = PathContext.emptyMap

    given SpaceContext = context

    /*
    a  ->  b   x  <->  y  s -> t -> u -> v -> w -> s
      \           \    ^
        ◢           ◢  |
    c  <-  d           z
     */
    val graph = Literal(SpaceValue("edge.a.b", "edge.a.d", "edge.d.c", "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y",
      "edge.s.t", "edge.t.u", "edge.u.v", "edge.v.w", "edge.w.s"))
    val transpose = graph("edge").iter("x", "r", S"r".iter("y", "_", Singleton(P"y" x P"x")))
    val nodes = graph("edge").iter("fwd", "_1", Singleton(P"fwd")) \/ transpose.iter("bwd", "_2", Singleton(P"bwd"))
    val e = R"scc"(Vector("42"), Vector(graph("edge"), transpose, nodes))
    assert(eval(e)(using rc = Map(RoutinePtr("reachable") -> reachable_routine, RoutinePtr("scc") -> scc_routine)) == SpaceValue("w.s", "w.t", "w.u", "w.v", "z.x", "z.y"))
  }
end Routines


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

  def symbol_concat(path: Path, sep: String = " "): Path =
    Path.GroundedPP(path, pv => PathValue(List(PathItem.Symbol(pv.items.map(_.show).mkString(sep)))))

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
      case Seq(Some(stop)) => SpaceValue((0 until stop).map(i => PathValue(List(PathItem.Symbol(i.toString)))).toSet)
      case Seq(Some(start), Some(stop), Some(step)) => SpaceValue((start until stop by step).map(i => PathValue(List(PathItem.Symbol(i.toString)))).toSet))

  def transitive(space: Space): Space =
    Space.GroundedSS(space, sv => {
      var otsv = sv
      var tsv = eval(Literal(sv) \/ Literal(sv).iter("x", "r", P"x" x DropHead(Literal(sv) <| S"r")))(using PathContext.emptyMap, SpaceContextMap(Map()))
      while otsv != tsv do
        otsv = tsv
        tsv = eval(Literal(otsv) \/ Literal(otsv).iter("x", "r", P"x" x DropHead(Literal(otsv) <| S"r")))(using PathContext.emptyMap, SpaceContextMap(Map()))
      tsv
    })

  test("PP hash") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    val e = S"family"("parent").iter("x", "r", S"r".iter("y", "_", Singleton(hash(P"x" x P"y"))))

    assert(eval(e) == SpaceValue("R2606dfba", "R86aea026", "Rc50d6b68", "Re4c8532", "Re59e471", "Re7a6b6e1"))
  }

  test("PP trace") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    given ps: collection.mutable.ArrayBuffer[PathValue] = collection.mutable.ArrayBuffer.empty

    val e = S"family"("parent").iter("x", "r", S"r".iter("y", "_", Singleton(trace(P"x" x P"y"))))

    eval(e)
    assert(ps.map(_.show).mkString("; ") == "Tom.Liz; Tom.Bob; Pat.Jim; Bob.Ann; Bob.Pat; Pam.Bob")
  }

  test("SP spacesize") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context

    val e = S"family"("parent").iter("x", "r", Singleton(P"x" x "has" x spacesize(S"r") x "children"))

    assert(eval(e) == SpaceValue("Bob.has.2.children", "Pam.has.1.children", "Pat.has.1.children", "Tom.has.2.children"))
  }

  test("SP spaceout") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    val e = S"family"("parent").iter("x", "r", Singleton(spaceout(S"r")))

    assert(eval(e) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("Bob", "Liz"), SpaceValue("Jim"), SpaceValue("Ann", "Pat"), SpaceValue("Bob")))
  }

  test("PS range") {
    given PathContext = PathContext.emptyMap
    given SpaceContext = context

    val e = range("0.10.2").iter("x", "_1", range("1" x P"x" x "1").iter("y", "_2", Singleton("pair" x P"x" x P"y")))

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



class SPARQL extends FunSuite:
  import Space.*

  val grounded = Grounded()
  import grounded.{spaceout, range}

  def Head(s: Space): Space = s.iter("s", "_", Singleton(P"s"))

  extension (s: Space)
    def tee(run: Space): Space = s.iter("_1", "_2", run)

  val context: SpaceContextMap = SpaceContextMap(Map(
    SpaceMention("SPO") -> SpaceValue(
      "A.isa.Person", "A.name.Alice", "A.age.25", "Alice.family.Smith", "Alice.given.Lis",
      "B.isa.Person", "B.name.Bob", "B.age.12",
      "C.name.Charlie"),
    SpaceMention("PSO") -> SpaceValue(
      "age.A.25", "age.B.12",
      "isa.A.Person", "isa.B.Person",
      "name.A.Alice", "name.B.Bob", "name.C.Charlie",
      "family.Alice.Smith", "given.Alice.Lis"),
    SpaceMention("POS") -> SpaceValue(
      "age.12.B", "age.25.A",
      "isa.Person.A", "isa.Person.B",
      "name.Alice.A", "name.Bob.B", "name.Charlie.C",
      "family.Smith.Alice", "given.Lis.Alice")
  ))

  val loves: SpaceContextMap = SpaceContextMap(Map(
    SpaceMention("SPO") -> SpaceValue(
      "Harry.loves.Macbeth",
      "Harry.loves.Taylor",
      "Macbeth.loves.Harry",
      "Macbeth.loves.Taylor"),
    SpaceMention("PSO") -> SpaceValue(
      "loves.Harry.Macbeth",
      "loves.Harry.Taylor",
      "loves.Macbeth.Harry",
      "loves.Macbeth.Taylor"
  )))

  val name_fn: SpaceContextMap =  SpaceContextMap(Map(
    SpaceMention("SPO") -> SpaceValue(
      "A.a.Person",
      "B.a.Person",
      "C.a.Person",
      "A.name.Alice_Eve",
      //"B.name.Bob_Morley",
      "A.FN.Alice",
      "B.FN.Bob"),
    SpaceMention("OPS") -> SpaceValue(
      "Person.a.A",
      "Person.a.B",
      "Person.a.C",
      "Alice_Eve.name.A",
      //"Bob_Morley.name.B",
      "Alice.FN.A",
      "Bob.FN.B",
  )))


  test("loves example") {
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    //val l = S"PSO"("loves").iter("s", "os", S"os".iter("o", "_", Singleton("person1" x P"s") \/ Singleton("person2" x P"o") ))
    val l2 = S"PSO"("loves").iter("s", "o", S"o".iter("o", "_", Singleton(spaceout(Singleton( P"s" x P"o" )))))
    assert(eval(l2)(using sc = loves) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("Harry.Taylor"), SpaceValue("Harry.Macbeth"), SpaceValue("Macbeth.Taylor"), SpaceValue("Macbeth.Harry")))
  }

  test("if nonEmpty") {
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    //  ?x a Person
    //  OPTIONAL {?x name ?name}
    //  OPTIONAL {?x FN ?name}

    val e = S"OPS"("Person.a").iter("x", "-", {
      val some = "Some" x S"SPO"(P"x" x "name")
      val other = "Other" x S"SPO"(P"x" x "FN")
      (some("Some") \/
      (Singleton("Some") \ Head(some)).tee(other("Other"))).iter("head", "tail", Singleton(spaceout(P"head" x S"tail")))
    })

    println(eval(e)(using sc = name_fn).prettyLines)
  }


  // (x.X, name.NAME)
  test("basic pattern") {
    given SpaceContext = context

    // SPO -> PSO
    val spo_to_pso = S"SPO".iter("s", "po", S"po".iter("p", "o", Singleton(P"p" x P"s") x S"o"))
    assert(eval(spo_to_pso) == eval(S"PSO"))

    // SPO -> POS
    val spo_to_pos = S"SPO".iter("s", "po", S"po".iter("p", "o", Singleton(P"p") x S"o" x Singleton(P"s")))
    assert(eval(spo_to_pos) == eval(S"POS"))

    //SELECT ?x ?fname
    //WHERE {
    // ?x isa Person
    // ?x <http://www.w3.org/2001/vcard-rdf/3.0#FN>  ?fname
    // }
    val basic_pattern_person = "person" x S"POS"("isa" x "Person")
    assert(eval(basic_pattern_person) == SpaceValue("person.A", "person.B"))

    val basic_pattern_name = "name" x S"POS"("isa" x "Person").iter("x", "_", S"PSO"("name" x P"x"))
    assert(eval(basic_pattern_name) == SpaceValue("name.Alice", "name.Bob"))

    val basic_pattern = S"POS"("isa" x "Person").iter("x", "_", ("name" x S"PSO"("name" x P"x")) \/ ("person" x Singleton(P"x")))
    assert(eval(basic_pattern) == SpaceValue("person.A", "name.Alice", "person.B", "name.Bob"))


    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    val basic_pattern_ = S"POS"("isa" x "Person").iter("x", "_", Singleton(spaceout(("name" x S"PSO"("name" x P"x")) \/ ("person" x Singleton(P"x")))))
    assert(eval(basic_pattern_) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("person.A", "name.Alice"), SpaceValue("person.B", "name.Bob")))

  }

  test("blank nodes") {
    given SpaceContext = context

    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    //PREFIX vcard:  	<http://www.w3.org/2001/vcard-rdf/3.0#>
    //
    //SELECT ?y ?givenName
    //WHERE
    // { ?y vcard:Family "Smith" .
    //   ?y vcard:Given  ?givenName .
    // }

    val pos = S"POS"

    val basic_blank_nodes = pos("family" x "Smith").iter("y", "_", Singleton("y" x P"y") \/ ("given" x S"SPO"(P"y" x "given")))
    assert(eval(basic_blank_nodes) == SpaceValue("given.Lis", "y.Alice"))

    val basic_blank_nodes_ = S"POS"("family" x "Smith").iter("y", "_", Singleton(spaceout(Singleton("y" x P"y") \/ ("given" x S"SPO"(P"y" x "given")))))
    assert(eval(basic_blank_nodes_) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("y.Alice", "given.Lis")))

  }

  test("filter") {
    given SpaceContext = context
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    // PREFIX info: <http://somewhere/peopleInfo#>
    //
    // SELECT ?resource
    // WHERE
    //  {
    //	?resource info:age ?age .
    //	FILTER (?age >= 24)
    //  }


    val filter_values = (S"POS"("age") <| range("24.200.1")).iter("age", "resource", Singleton(spaceout("resource" x S"resource")))
    assert(eval(filter_values) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("resource.A")))
  }

  test("optionals") {
    given SpaceContext = context
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    // PREFIX info:	<http://somewhere/peopleInfo#>
    // PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
    //
    // SELECT ?name ?age
    // WHERE
    // {
    // 	?person vcard:FN  ?name .
    // 	OPTIONAL { ?person info:age ?age }
    // }
    val pso = "PSO"
    val a = S"PSO"("name").iter("person", "names", {
      val age = "names" x S"SPO"(P"person" x "age")
      Singleton(spaceout(("name" x S"names") \/ ("age" x age("names"))))
    }
    )

    val a_ = S"PSO"("name").iter("person", "names", {
      Singleton(spaceout(("name" x S"names") \/ ("age" x S"SPO"(P"person" x "age"))))
    }
    )

    assert(eval(a) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("name.Charlie"), SpaceValue("name.Alice", "age.25"), SpaceValue("age.12", "name.Bob")))
    ps.clear()
    assert(eval(a_) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("name.Charlie"), SpaceValue("name.Alice", "age.25"), SpaceValue("age.12", "name.Bob")))


  }

  test("optional_with_filters") {
    given SpaceContext = context
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty
    // SELECT ?name ?age
    // WHERE
    // {
    //   ?person vcard:FN  ?name .
    //   OPTIONAL { ?person info:age ?age . FILTER ( ?age > 24 ) }
    // }

    val e = S"PSO"("name").iter("person", "names", S"PSO"("name" x P"person").iter("name", "_", {
      val age = S"SPO"(P"person" x "age") <| range("24.200.1")
      Singleton(spaceout(Singleton("name" x P"name") \/ ("age" x age)))
    }))

    assert(eval(e) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("name.Charlie"), SpaceValue("name.Alice", "age.25"), SpaceValue("name.Bob")))
    ps.clear()

  }
  test("dependent_optionals") {
    given SpaceContext = name_fn
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    // SELECT ?name
    // WHERE
    // {
    //   ?x a foaf:Person .
    //   OPTIONAL { ?x foaf:name ?name }
    //   OPTIONAL { ?x vCard:FN  ?name }
    // }

    val e = S"OPS"("Person.a").iter("x", "-", {
      val some = "Some" x S"SPO"(P"x" x "name")
      val other = "Other" x S"SPO"(P"x" x "FN")
      (some("Some") \/
        (Singleton("Some") \ Head(some)).tee(other("Other"))).iter("head", "tail", Singleton(spaceout("name" x P"head" x S"tail")))
    })

    assert(eval(e) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("name.Alice_Eve"), SpaceValue("name.Bob")))

    //println(ps.toList)

  }

  test("dependent_optionals2") {

    val books: SpaceContextMap =  SpaceContextMap(Map(
      SpaceMention("SPO") -> SpaceValue(
        "HP.a.Book",
        "LOTR.a.Book",
        "HP.author.R",
        "LOTR.author.T",
        "R.name.JKRowling"),
      SpaceMention("OPS") -> SpaceValue(
        "Book.a.HP",
        "Book.a.LOTR",
        "R.author.HP",
        "T.author.LOTR",
        "JKRowling.name.R"
      )))

    given SpaceContext = books

    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    // SELECT ?book ?authorName
    // WHERE {
    //   ?book a ex:Book .
    //
    //   OPTIONAL {
    //     ?book ex:author ?author .
    //     ?author foaf:name ?authorName .
    //   }
    // }
    val e = S"OPS"("Book.a").iter("book", "_", {
      val author = S"SPO"(P"book" x "author")
      val authorName = author.iter("author", "_", S"SPO"(P"author" x "name"))
      Singleton(spaceout(Singleton("book" x P"book") \/ ("authorName" x authorName)))
    })

    eval(e)
    //assert(ps.toList == List(SpaceValue("book.HP", "authorName.JKROWLING")))
  }
end SPARQL

class AlgebraSPARQL extends FunSuite:
  val sparql = SPARQL()
  import sparql.{Head, tee}

  val grounded = Grounded()
  import grounded.{range, hash}

  type VarMapping = Space  // space with paths of the form varname.value
  type VarMappings = Space  // space with paths of the form hash.varname.value


  def get_incompatible(s1: VarMapping, s2: VarMapping): VarMapping =
    (Head(s1) /\ Head(s2)).iter("v", "_", {
      P"v" x (s1(P"v") \ s2(P"v"))
    })

  def if_empty_do(e: Space, todo: Space): Space =
    (Singleton("tobeempty") \ Head("tobeempty" x e)).tee(todo)

  def if_nonempty_else(e: Space, ifempty: Space): Space =
    e \/ if_empty_do(e, ifempty)

  def join(s1: VarMapping, s2: VarMapping): VarMapping =
    (Singleton("incompatible") \ Head("incompatible" x get_incompatible(s1, s2))).tee(s1 \/ s2)

  def join2(s1: VarMapping, s2: VarMapping): VarMapping =
    if_empty_do(get_incompatible(s1, s2), s1 \/ s2)

  def hyperJoin(s1: VarMappings, s2: VarMappings): VarMappings =
    // s1.iter("h1", "tail1", S"tail1")
    s1.iter("h1", "tail1", s2.iter("h2", "tail2", hash(join2(S"tail1", S"tail2")) x join2(S"tail1", S"tail2")))

  def difference(s1: VarMapping, s2: VarMapping): VarMapping =
    // assuming filter = True
    get_incompatible(s1, s2).tee(s1)

  def hyperDifference(s1: VarMappings, s2: VarMappings, filter: VarMapping => VarMapping = (s => s)): VarMappings =
    // Diff(Ω1, Ω2, expr) =
    //        { μ | μ in Ω1 such that for all μ′ in Ω2, μ and μ′ are not compatible }
    //            set-union
    //        { μ | μ in Ω1 such that for all μ′ in Ω2, μ and μ' are compatible and expr(merge(μ, μ')) is false }

    // val p1 = s1.iter("hash1", "tail1", if_empty_do(s2.iter("hash2", "tail2", if_empty_do(get_incompatible(S"tail1", S"tail2"), Singleton("compatible"))), P"hash1" x S"tail1"))
    // val p2 = s1.iter("hash1", "tail1", if_empty_do(s2.iter("hash2", "tail2", get_incompatible(S"tail1", S"tail2") \/ filter(S"tail1" \/ S"tail2")), P"hash1" x S"tail1"))
    // p1 \/ p2

    // Diff(Ω1, Ω2, expr) =
    //        { μ | μ such that for all μ′, μ and μ' are not compatible or expr(merge(μ, μ')) is false}

    val p = s1.iter("hash1", "tail1", if_empty_do(s2.iter("hash2", "tail2", if_empty_do(get_incompatible(S"tail1", S"tail2"), Singleton("check")) /\ filter(S"tail1" \/ S"tail2").tee(Singleton("check"))), P"hash1" x S"tail1"))
    p


  def leftJoin(s1: VarMapping, s2: VarMapping): VarMapping =
    // assuming filter = True
    join(s1, s2) \/ difference(s1, s2)

  def hyperFilter(s1: VarMappings, filter: VarMapping => VarMapping): VarMappings =
    s1.iter("h", "varmapping", P"h" x filter(S"varmapping"))

  def hyperLeftJoin(s1: VarMappings, s2: VarMappings, filter: VarMapping => VarMapping = (s => s)): VarMappings =
    hyperFilter(hyperJoin(s1, s2), filter) \/ hyperDifference(s1, s2, filter)

  def filterVarEqualsString(s1: VarMapping, v: String, to_match: String): VarMapping =
    (s1(v) /\ Singleton(to_match)).tee(s1)
  def filterVarEqualsVar(s1: VarMapping, v1: String, v2: String): VarMapping =
    (s1(v1) /\ s1(v2)).tee(s1)
  def filterStringEqualsString(s1: VarMapping, c1: String, c2: String): VarMapping =
    if c1 == c2 then s1 else Space.Empty


  def filterLessThan(s1: VarMapping, v: String, i: Int): VarMapping =
    (s1(v) <| range(f"0.${i.toString}.1")).tee(s1)
  def filterLessThanVars(s1: VarMapping, v1: String, v2: String): VarMapping =
    // TODO use max or min to assert that s1(v1) and s1(v2) only have one element
    (s1(v1) <| s1(v2).iter("i", "_", range("0" x P"i" x "1"))).tee(s1)
  def filterLessThanCons(s1: VarMapping, i1: Int, i2: Int): VarMapping =
    if i1 < i2 then s1 else Space.Empty

  def filterLessOrEqual(s1: VarMapping, v: String, i: Int): VarMapping =
    (s1(v) <| range("0" x s"${(i + 1).toString}" x "1")).tee(s1)
  def filterLessOrEqualVars(s1: VarMapping, v1: String, v2: String): VarMapping =
    // TODO use max or min to assert that s1(v1) and s1(v2) only have one element
    (s1(v1) /\ s1(v2).iter("i", "_", range("0" x P"i" x "1") \/ Singleton(P"i"))).tee(s1)
  def filterLessOrEqualCons(s1: VarMapping, i1: Int, i2: Int): VarMapping =
    if i1 <= i2 then s1 else Space.Empty

  def filterGreaterThan(s1: VarMapping, v: String, i: Int, max: Int = 2000): VarMapping =
    (s1(v) <| range(f"${(i + 1).toString}.${max.toString}.1")).tee(s1)
  def filterGreaterThanVars(s1: VarMapping, v1: String, v2: String): VarMapping =
    filterLessThanVars(s1, v2, v1)
  def filterGreaterThanCons(s1: VarMapping, i1: Int, i2: Int): VarMapping =
    if i1 > i2 then s1 else Space.Empty

  def filterGreaterOrEqual(s1: VarMapping, v: String, i: Int, max: Int = 2000): VarMapping =
    (s1(v) <| range(f"${i.toString}.${max.toString}.1")).tee(s1)
  def filterGreaterOrEqualVars(s1: VarMapping, v1: String, v2: String): VarMapping =
    filterLessOrEqualVars(s1, v2, v1)
  def filterGreaterOrEqualCons(s1: VarMapping, i1: Int, i2: Int): VarMapping =
    if i1 >= i2 then s1 else Space.Empty

//  def hyperFilterGreaterThan(s1: Space, v: String, i: Int, max: Int = 2000): Space =
//    s1.iter("h", "tail", P"h" x filterGreaterThan(S"tail", v, i, max))
//  def hyperFilterGreaterOrEqual(s1: Space, v: String, i: Int, max: Int = 2000): Space =
//    s1.iter("h", "tail", P"h" x filterGreaterOrEqual(S"tail", v, i, max))


//  def hyperFilterLessThan(s1: Space, v: String, i: Int): Space =
//    s1.iter("h", "tail", P"h" x filterLessThan(S"tail", v, i))
//  def hyperFilterLessOrEqual(s1: Space, v: String, i: Int): Space =
//    s1.iter("h", "tail", P"h" x filterLessOrEqual(S"tail", v, i))

  def filterNot(s: VarMapping, f: VarMapping => VarMapping): VarMapping =
    if_empty_do(f(s), s)

  def filterBound(s: VarMapping, v: String): VarMapping =
    s(v)


  test("algebra") {
    val compatible: SpaceContextMap = SpaceContextMap(Map(
      SpaceMention("lhs") -> SpaceValue(
        "person.A",
        "name.Alice",
        "hobby.reading"),
      SpaceMention("rhs") -> SpaceValue(
        "person.A",
        "name.Alice",
        "age.13"
      )))

    val incompatible: SpaceContextMap = SpaceContextMap(Map(
      SpaceMention("lhs") -> SpaceValue(
        "person.B",
        "name.Alice",
        "hobby.reading"),
      SpaceMention("rhs") -> SpaceValue(
        "person.A",
        "name.Alice",
        "age.13"
      )))

    given SpaceContext = compatible

    val get_incompatible_ = S"lhs".iter("v", "os", S"os".iter("o", "_", {
       val v2 = P"v" x S"rhs"(P"v")
       val o2 = P"v" x P"o" x S"rhs"(P"v" x P"o")
       v2 \ o2
    }))

    val get_incompatible2 = (Head(S"lhs") /\ Head(S"rhs")).iter("v", "os", {
      (P"v" x (S"lhs"(P"v") \ S"rhs"(P"v"))) \/ (P"v" x (S"rhs"(P"v") \ S"lhs"(P"v")))
    })


    // assert(eval(get_incompatible_) == eval(get_incompatible(S"lhs", S"rhs")))

    val e = S"lhs" \/ S"lhs".iter("v", "o", S"rhs"(P"v"))

    val e2 = S"lhs".iter("v", "o", S"rhs"(P"v"))

    assert(eval(get_incompatible_) == SpaceValue(Set()))
    assert(eval(get_incompatible(S"lhs", S"rhs")) == SpaceValue(Set()))
    assert(eval(get_incompatible(S"lhs", S"rhs"))(using sc = incompatible) == SpaceValue("person.B"))
    assert(eval(join(S"lhs", S"rhs"))(using sc = compatible) == SpaceValue("age.13", "hobby.reading", "name.Alice", "person.A"))
    assert(eval(join2(S"lhs", S"rhs"))(using sc = compatible) == SpaceValue("age.13", "hobby.reading", "name.Alice", "person.A"))
    assert(eval(join(S"lhs", S"rhs"))(using sc = incompatible) == SpaceValue())
    assert(eval(join2(S"lhs", S"rhs"))(using sc = incompatible) == SpaceValue())
    assert(eval(difference(S"lhs", S"rhs"))(using sc = compatible) == SpaceValue())
    assert(eval(difference(S"lhs", S"rhs"))(using sc = incompatible) == SpaceValue("hobby.reading", "name.Alice", "person.B"))
    assert(eval(leftJoin(S"lhs", S"rhs"))(using sc = compatible) == SpaceValue("age.13", "hobby.reading", "name.Alice", "person.A"))
    assert(eval(leftJoin(S"lhs", S"rhs"))(using sc = incompatible) == SpaceValue("hobby.reading", "name.Alice", "person.B"))
    assert(eval(filterGreaterThan(S"rhs", "age", 10))(using sc = compatible) == SpaceValue("age.13", "name.Alice", "person.A"))
    assert(eval(filterGreaterThan(S"rhs", "age", 15))(using sc = compatible) == SpaceValue())
    assert(eval(filterLessThan(S"rhs", "age", 10))(using sc = compatible) == SpaceValue())
    assert(eval(filterLessThan(S"rhs", "age", 15))(using sc = compatible) == SpaceValue("age.13", "name.Alice", "person.A"))
  }

  test("algebra over hyperspaces") {
    val context: SpaceContextMap = SpaceContextMap(Map(
      SpaceMention("lhs") -> SpaceValue(
        "00.name.Alice",
        "01.name.Mel"),
      SpaceMention("rhs") -> SpaceValue(
        "10.name.Alice",
        "10.give.Lis",
        "10.age.13",
        "11.name.Bob",
        "11.given.Bobbie",
        "11.age.20"
      )))

    given SpaceContext = context
    assert(eval(hyperJoin(S"lhs", S"rhs")) == SpaceValue("R2ec263c.age.13", "R2ec263c.give.Lis", "R2ec263c.name.Alice"))

  }


end AlgebraSPARQL

class TranslateSPARQL extends FunSuite:

  import org.apache.jena.query.ParameterizedSparqlString
  import org.apache.jena.query.Query
  import org.apache.jena.sparql.expr.ExprVisitorBase
  import org.apache.jena.sparql.expr.E_LessThan
  import org.apache.jena.sparql.algebra.Algebra
  import org.apache.jena.sparql.algebra.OpVisitorBase
  import org.apache.jena.sparql.algebra.walker.WalkerVisitor
  import org.apache.jena.sparql.algebra.{OpVisitor, op, Op, OpVisitorByTypeBase, OpVisitorByType}
  import org.apache.jena.sparql.algebra.op.{Op0, Op1, Op2, OpN, OpAssign, OpBGP, OpConditional, OpDatasetNames, OpDiff, OpDisjunction, OpDistinct, OpExtend, OpFilter, OpGroup, OpJoin, OpLabel, OpLateral, OpLeftJoin, OpList, OpMinus, OpNull, OpOrder, OpPath, OpProcedure, OpProject, OpPropFunc, OpQuad, OpQuadBlock, OpQuadPattern, OpReduced, OpSequence, OpService, OpSlice, OpTable, OpTopN, OpTriple, OpUnion}
  import org.apache.jena.graph.{Node_Literal, Node_URI, Node_Variable}

  import Space.*

  val g = Grounded()
  import g.{symbol_concat, hash, spaceout}

  val sparqlAlg = AlgebraSPARQL()
  import sparqlAlg.*

  val sparqlTests = SPARQL()
  import sparqlTests.{tee, Head}


  def spo_to_pso = S"SPO".iter("s", "po", S"po".iter("p", "o", Singleton(P"p" x P"s") x S"o"))

  def spo_to_pos = S"SPO".iter("s", "po", S"po".iter("p", "o", Singleton(P"p") x S"o" x Singleton(P"s")))

  def print_context_permutations(c: SpaceContext): Unit =
    println("PSO: ")
    println(eval(spo_to_pso)(using sc = c).show)
    println("POS: ")
    println(eval(spo_to_pos)(using sc = c).show)


  def prefixHash(space: Space): Space = hash(space) x space

  extension (e: ExprList)
    def to_expression(): Expr =
      e.size() match
        case 0 =>
          println("Not implemented, empty expressionlist")
          ???
        case 1 => e.get(0)
        case _ =>
          val e_list = Range(0, e.size()).map(i => e.get(i))
          e_list.tail.foldLeft(e_list.head)((exp1, exp2) => E_LogicalAnd(exp1, exp2))



  def order_bgp(triple: org.apache.jena.graph.Triple): (IndexedSeq[Int], IndexedSeq[Int]) =
    // spo -> fixed first
    // ?y http://www.w3.org/2001/vcard-rdf/3.0#Family "Smith" -> ((1, 2), (0))
    val trip_list = List(triple.getSubject, triple.getPredicate, triple.getObject)
    Range(0, 3).partition(x => {
      trip_list(x) match
        case i: org.apache.jena.sparql.core.Var => false
        case _ => true})

  def triple_get(triple: org.apache.jena.graph.Triple, i: Int): org.apache.jena.graph.Node =
    val trip_list = List(triple.getSubject, triple.getPredicate, triple.getObject)
    trip_list(i)

  def get_str(n: org.apache.jena.graph.Node): String =
    n match
      case n: Node_Literal => n.getLiteral.getLexicalForm
      case n: Node_URI => n.getLocalName

  def get_space_from_bgp(triple: org.apache.jena.graph.Triple): Space =
    val rotation: (IndexedSeq[Int], IndexedSeq[Int]) = order_bgp(triple)
    val ordered_spo = rotation(0).concat(rotation(1)).map(x => "spo".charAt(x)).fold("")((c1, c2) => s"$c1$c2").toString
    val m: Map[String, Space] = Map("spo" -> S"SPO", "pos" -> S"POS", "pso" -> S"PSO")

    val constant_ids = rotation(0)
    val var_ids = rotation(1)
    constant_ids.length match
      case 0 =>
        val v0 = triple_get(triple, var_ids(0)).getName
        val v1 = triple_get(triple, var_ids(1)).getName
        val v2 = triple_get(triple, var_ids(2)).getName
        m(ordered_spo).iter("v0", "v12s", S"v12s".iter("v1", "v2s", S"v2s".iter("v2", "_", prefixHash(Singleton(v0 x P"v0") \/ Singleton(v1 x P"v1") \/ Singleton(v2 x P"v2")))))
      case 1 =>
        val c0 = get_str(triple_get(triple, constant_ids(0)))
        val v0 = triple_get(triple, var_ids(0)).getName
        val v1 = triple_get(triple, var_ids(1)).getName
        val e = m(ordered_spo)(c0).iter("x", "sy", S"sy".iter("y", "_", {
          prefixHash(Singleton(v0 x P"x") \/ Singleton(v1 x P"y"))
        }))
        e
      case 2 =>
        val c0 = get_str(triple_get(triple, constant_ids(0)))
        val c1 = get_str(triple_get(triple, constant_ids(1)))
        val v0 = triple_get(triple, var_ids(0)).getName
        val e = m(ordered_spo)(c0 x c1).iter("x", "_", {
          prefixHash(v0 x Singleton(P"x"))
        })
        e

      case 3 => ???


  def get_filter_function(ex: Expr): Space => Space =
    // TODO arguments can also both be variables or integers or ... in numerical comparisons
    // assumes first argument is a variable and second argument is an integer
    ex match
      case e: E_LessThan =>
        (e.getArg1, e.getArg2) match
          case (a1, a2) if a1.isVariable & a2.isConstant =>
            s => filterLessThan(s, a1.asVar().getName, a2.getConstant.toString.toInt)
          case (a1, a2) if a1.isConstant & a2.isVariable =>
            assert(a1.getConstant.isInteger)
            s => filterGreaterThan(s, a2.asVar().getName, a1.getConstant.toString.toInt)
          case (a1, a2) if a1.isVariable & a2.isVariable =>
            s => sparqlAlg.filterLessThanVars(s, a1.asVar().getName, a2.asVar().getName)
          case (a1, a2) if a1.isConstant & a2.isConstant =>
            assert(a1.getConstant.isInteger && a2.getConstant.isInteger)
            s => filterLessThanCons(s, a1.getConstant.toString.toInt, a2.getConstant.toString.toInt)
          case (a1, a2) =>
            println(s"unsupported Less Than between $a1 (${a1.getClass.getName}) and $a2 (${a2.getClass.getName})")
            ???
      case e: E_LessThanOrEqual =>
        (e.getArg1, e.getArg2) match
        case (a1, a2) if a1.isVariable & a2.isConstant =>
          s => filterLessOrEqual(s, a1.asVar().getName, a2.getConstant.toString.toInt)
        case (a1, a2) if a1.isConstant & a2.isVariable =>
          assert(a1.getConstant.isInteger)
          s => filterGreaterOrEqual(s, a2.asVar().getName, a1.getConstant.toString.toInt)
        case (a1, a2) if a1.isVariable & a2.isVariable =>
          s => filterLessOrEqualVars(s, a1.asVar().getName, a2.asVar().getName)
        case (a1, a2) if a1.isConstant & a2.isConstant =>
          assert(a1.getConstant.isInteger && a2.getConstant.isInteger)
          s => filterLessOrEqualCons(s, a1.getConstant.toString.toInt, a2.getConstant.toString.toInt)
        case (a1, a2) =>
          println(s"unsupported Less Than between $a1 (${a1.getClass.getName}) and $a2 (${a2.getClass.getName})")
          ???
      case e: E_GreaterThan =>
        (e.getArg1, e.getArg2) match
          case (a1, a2) if a1.isVariable & a2.isConstant =>
            s => filterGreaterThan(s, a1.asVar().getName, a2.getConstant.toString.toInt)
          case (a1, a2) if a1.isConstant & a2.isVariable =>
            assert(a1.getConstant.isInteger)
            s => filterLessThan(s, a2.asVar().getName, a1.getConstant.toString.toInt)
          case (a1, a2) if a1.isVariable & a2.isVariable =>
            // This will compare the strings of the objects attached to the variables
            // Might not work for dates, doubles, ...
            s => filterGreaterThanVars(s, a1.asVar().getName, a2.asVar().getName)
          case (a1, a2) if a1.isConstant & a2.isConstant =>
            s => filterGreaterThanCons(s, a1.getConstant.toString.toInt, a2.getConstant.toString.toInt)
          case (a1, a2) =>
            println(s"unsupported Greater Than between $a1 (${a1.getClass.getName}) and $a2 (${a2.getClass.getName})")
            ???
      case e: E_GreaterThanOrEqual => (e.getArg1, e.getArg2) match
        case (a1, a2) if a1.isVariable & a2.isConstant =>
          s => filterGreaterOrEqual(s, a1.asVar().getName, a2.getConstant.toString.toInt)
        case (a1, a2) if a1.isConstant & a2.isVariable =>
          assert(a1.getConstant.isInteger)
          s => filterLessOrEqual(s, a2.asVar().getName, a1.getConstant.toString.toInt)
        case (a1, a2) if a1.isVariable & a2.isVariable =>
          s => filterGreaterOrEqualVars(s, a1.asVar().getName, a2.asVar().getName)
        case (a1, a2) if a1.isConstant & a2.isConstant =>
          assert(a1.getConstant.isInteger && a2.getConstant.isInteger)
          s => filterGreaterOrEqualCons(s, a1.getConstant.toString.toInt, a2.getConstant.toString.toInt)
        case (a1, a2) =>
          println(s"unsupported Less Than between $a1 (${a1.getClass.getName}) and $a2 (${a2.getClass.getName})")
          ???
      case e: E_Equals =>
        (e.getArg1, e.getArg2) match
          case (a1, a2) if a1.isVariable & a2.isConstant =>
            a2.getConstant match
              case c2 if c2.isString || c2.isInteger || c2.isIRI =>
                (s => filterVarEqualsString(s, a1.asVar().getName, get_str(a2.getConstant.asNode())))
              case c2 =>
                println(s"unsupported equality between variable and $c2 (${c2.getClass.getName})")
                ???
          case (a1, a2) if a1.isConstant & a2.isVariable =>
            a1.getConstant match
              case c1 if c1.isString || c1.isInteger || c1.isIRI => (s => filterVarEqualsString(s, a2.asVar().getName, get_str(a1.getConstant.asNode())))
              case c1 => println(s"unsupported equality between $c1 (${c1.getClass.getName}) and variable")
                ???
          case (a1, a2) if a1.isVariable & a2.isVariable => (s => filterVarEqualsVar(s, a1.asVar().getName, a2.asVar().getName))
          case (a1, a2) if a1.isConstant & a2.isConstant =>
            (a1.getConstant, a2.getConstant) match
              case (c1, c2) if (c1.isString & c2.isString) || (c1.isInteger & c2.isInteger) || (c1.isIRI & c2.isIRI) =>
                (s => filterStringEqualsString(s, get_str(c1.asNode()), get_str(c2.asNode())))
              case (c1, c2) =>
                println(s"unsupported equality between constants $a1 (${a1.getClass.getName}) and $a2 (${a2.getClass.getName})")
                ???
          case (a1, a2) => println(s"unsupported equality between $a1 (${a1.getClass.getName}) and $a2 (${a2.getClass.getName})")
            ???
      case e: E_LogicalOr => (s => get_filter_function(e.getArg1)(s) \/ get_filter_function(e.getArg2)(s))
      case e: E_LogicalAnd => (s => get_filter_function(e.getArg1)(s) /\ get_filter_function(e.getArg2)(s))
      case e: E_LogicalNot => (s => filterNot(s, get_filter_function(e.getArg)))
      case e: E_Bound => (s => s(e.getArg.asVar().getName).tee(s))

      //(s => get_filter_function(e.getExpr)(s))
      case _ => println(s"unsupported filter $ex (${ex.getClass.getName})")
        return ???


  def translate(op: Op): Space = op match
    case op: OpProject =>
      val t = translate(op.getSubOp)
      val varspace = Range(0, op.getVars.size()).map(i => {op.getVars.get(i).getName}).foldLeft(Space.Empty)((s1, p2) => s1 \/ Singleton(p2))

      val e = op.getSubOp match
        case op2: OpOrder =>

          def recursion(s: Space, d: Int): Space =
            if d == 0 then
              s.iter("h", "vv", prefixHash(S"vv" <| varspace))
            else
              s.iter(s"dir$d", s"otail$d", S"otail$d".iter(s"o$d", s"tail$d", P"dir$d" x P"o$d" x recursion(S"tail$d", d - 1)))

          op2.getConditions.size().toString x recursion(t, op2.getConditions.size())

          // t.iter("order", "hvv", S"hvv".iter("h", "vv", P"order" x prefixHash(S"vv" <| varspace)))
        case _ =>
          t.iter("hash", "vv", prefixHash(S"vv" <| varspace))
      e

    case op: OpBGP =>
      val e = Range(1, op.getPattern.size()).map(x => get_space_from_bgp(op.getPattern.get(x))).fold(get_space_from_bgp(op.getPattern.get(0)))((s1, s2) => hyperJoin(s1, s2))
      e

    case op: OpJoin =>
      val e = hyperJoin(translate(op.getLeft), translate(op.getRight))
      e

    case op: OpLeftJoin =>
      op.getExprs match
        case null => hyperLeftJoin(translate(op.getLeft), translate(op.getRight), s => s)
        case ex: ExprList => hyperLeftJoin(translate(op.getLeft), translate(op.getRight), get_filter_function(ex.to_expression()))

    case op: OpFilter =>
      val f = get_filter_function(op.getExprs.to_expression())
      val i1 = hyperFilter(translate(op.getSubOp), f)
      i1

    case op: OpUnion =>
      val e = translate(op.getLeft) \/ translate(op.getRight)
      e


    case op: OpOrder =>
      val prefix_unordered = "0"

      val e = translate(op.getSubOp)
      // TODO what to use as prefix for unordered elements (now 0)
      def get_direction_name(i: Int): String =
        i match
          case 1 => "asc"
          case -1 => "desc"
          case -2 => "asc"
      if op.getConditions.size() == 1 then
        val c1 = op.getConditions.get(0)
        val v = c1.getExpression.asVar().getName
        e.iter("h", "vc",
          S"vc"(v).iter("c", "_",
            get_direction_name(c1.direction) x P"c" x P"h" x S"vc") \/
        if_empty_do(S"vc"(v), get_direction_name(c1.direction) x prefix_unordered x P"h" x S"vc"))

      else if op.getConditions.size() >= 2 then

        def highest(s: Space, backup: PathValue): Path =
          Path.GroundedSP(s, sv => sv.paths.flatMap(_.items.headOption).maxByOption(_.show).fold(backup)(x => PathValue(List(x))))

        e.iter("h", "vc",
          ((0 until op.getConditions.size())
            .map(i => op.getConditions.get(i))
            .map(n => get_direction_name(n.getDirection) x highest(S"vc"(n.getExpression.asVar().getName), prefix_unordered))
            .reduce(_ x _) x P"h") x S"vc"
        )

      else
        ???

    case op: OpSlice =>
      assert (op.getStart < -9E10)  // we assume no start is given; if no start is given, start is a very low number.

      // for SPARQL keyword LIMIT, length will always be an integer
      Limit(op.getLength.toInt, translate(op.getSubOp))



    case op =>
      println(s"unhandled case $op")
      return ???

  test("books example"){
    // example from https://iccl.inf.tu-dresden.de/w/images/e/ee/FSWT-L16-SPARQL-Algebra.pdf
    val books: SpaceContextMap = SpaceContextMap(Map(
      SpaceMention("SPO") -> SpaceValue(
        "Hamlet.author.Shakespeare", "Hamlet.price.10",
        "Macbeth.author.Shakespeare",
        "Tamburlaine.author.Marlowe", "Tamburlaine.price.17",
        "DoctorFaustus.author.Marlowe", "DoctorFaustus.price.12", "DoctorFaustus.title.\"The Tragical History of Doctor Faustus\"",
        "RomeoJulia.author.Brooke", "RomeoJulia.price.9"
      ),
      SpaceMention("PSO") -> SpaceValue(
        "author.DoctorFaustus.Marlowe", "author.Hamlet.Shakespeare", "author.Macbeth.Shakespeare", "author.RomeoJulia.Brooke", "author.Tamburlaine.Marlowe",
        "price.DoctorFaustus.12", "price.Hamlet.10", "price.RomeoJulia.9", "price.Tamburlaine.17",
        "title.DoctorFaustus.\"The Tragical History of Doctor Faustus\""),
      SpaceMention("POS") -> SpaceValue(
        "author.Brooke.RomeoJulia", "author.Marlowe.DoctorFaustus", "author.Marlowe.Tamburlaine", "author.Shakespeare.Hamlet", "author.Shakespeare.Macbeth",
        "price.10.Hamlet", "price.12.DoctorFaustus", "price.17.Tamburlaine", "price.9.RomeoJulia",
        "title.\"The Tragical History of Doctor Faustus\".DoctorFaustus")

    ))


    val q = new ParameterizedSparqlString(
      """PREFIX ex: <http://example.org/ns#>
        |
        |SELECT ?book ?price ?title
        |WHERE {
        |  ?book ex:price ?price .
        |  FILTER (?price < 15) .
        |  OPTIONAL { ?book ex:title ?title } .
        |  {
        |    ?book ex:author ex:Shakespeare
        |  } UNION {
        |    ?book ex:author ex:Marlowe
        |  }
        |}""".stripMargin).asQuery()


    // println(q)
    val aq = Algebra.compile(q)
    // println(aq)
    // println(Algebra.optimize(aq))


    val t_books = translate(aq)
    assert(eval(t_books)(using sc = books) == SpaceValue(
      "R36707057.book.Hamlet", "R36707057.price.10",
      "R5bb27dcc.book.DoctorFaustus", "R5bb27dcc.price.12", "R5bb27dcc.title.\"The Tragical History of Doctor Faustus\""))
  }

  test("jenna tutorial examples"){
    val context: SpaceContextMap = SpaceContextMap(Map(
      SpaceMention("SPO") -> SpaceValue(
        "A.type.Person", "A.name.Alice", "A.FN.AliceFN", "A.age.25", "Alice.Family.Smith", "Alice.Given.Lis", "Alice.Given.Al", "Mel.Family.Smith",
        "B.type.Person", "B.name.Bob", "B.age.12", "Bob.Family.Bouwer", "Bob.Given.Bobbie",
        "C.name.Charlie", "C.FN.CharlieFN",
        "D.type.Person", "D.FN.Dora", "D.age.20"),
      SpaceMention("PSO") -> SpaceValue(
        "age.A.25", "age.B.12",
        "type.A.Person", "type.B.Person",
        "name.A.Alice", "name.B.Bob", "name.C.Charlie",
        "FN.A.AliceFN", "FN.C.CharlieFN",
        "Family.Alice.Smith", "Given.Alice.Lis", "Given.Alice.Al", "Family.Mel.Smith",
        "Family.Bob.Bouwer", "Given.Bob.Bobbie",
        "type.D.Person", "FN.D.Dora", "age.D.20"),
      SpaceMention("POS") -> SpaceValue(
        "age.12.B", "age.25.A",
        "type.Person.A", "type.Person.B",
        "name.Alice.A", "name.Bob.B", "name.Charlie.C",
        "FN.AliceFN.A", "FN.CharlieFN.C",
        "Family.Smith.Alice", "Given.Lis.Alice", "Given.Al.Alice", "Family.Smith.Mel",
        "Family.Bouwer.Bob", "Given.Bob.Bobbie",
        "type.Person.D", "FN.Dora.D", "age.20.D")
    ))

    given SpaceContext = context

    val blindNodes = new ParameterizedSparqlString(
      """PREFIX vcard:  	<http://www.w3.org/2001/vcard-rdf/3.0#>
        |
        |SELECT ?y ?givenName
        |WHERE
        | { ?y vcard:Family "Smith" .
        |   ?y vcard:Given  ?givenName .
        | }
        |""".stripMargin).asQuery()


    val algblind = Algebra.compile(blindNodes)


    val t = translate(algblind)
    // println(t.show)
    assert(eval(t) == SpaceValue("R4f8194bd.givenName.Al", "R4f8194bd.y.Alice", "Re30ef3e3.givenName.Lis", "Re30ef3e3.y.Alice"))

    val optionalQuery = new ParameterizedSparqlString(
      """PREFIX info:	<http://somewhere/peopleInfo#>
        |PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |
        |SELECT ?name ?age
        |WHERE
        |{
        |	?person vcard:name  ?name .
        |	OPTIONAL { ?person info:age ?age }
        |}""".stripMargin).asQuery()

    val algoptional = Algebra.compile(optionalQuery)
    val t2 = translate(algoptional)
    assert(eval(t2) == SpaceValue("R24e793cb.age.25", "R24e793cb.name.Alice", "R29640fc9.age.12", "R29640fc9.name.Bob", "R4a4fbc23.name.Charlie"))

    val dependentOptional = new ParameterizedSparqlString(
      """PREFIX foaf: <http://xmlns.com/foaf/0.1/>
        |PREFIX vCard: <http://www.w3.org/2001/vcard-rdf/3.0#>
        |
        |SELECT ?name
        |WHERE
        |{
        |  ?x a foaf:Person .
        |  OPTIONAL { ?x foaf:name ?name }
        |  OPTIONAL { ?x vCard:FN  ?name }
        |}""".stripMargin).asQuery()
    val algdependent = Algebra.compile(dependentOptional)
    val t3 = translate(algdependent)
    // println(eval(t3).show)

    // Charlie is not labeled as person
    assert(eval(t3) == SpaceValue("R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val filterQuery = new ParameterizedSparqlString(
      """PREFIX info: <http://somewhere/peopleInfo#>
        |
        |SELECT ?resource
        |WHERE
        |{
        |?resource info:age ?age .
        |FILTER (?age >= 24)
        |}""".stripMargin).asQuery()
    val algfilter = Algebra.compile(filterQuery)
    val t4 = translate(algfilter)
    assert(eval(t4) == SpaceValue("R9623531d.resource.A"))


    val optionalFilter = new ParameterizedSparqlString(
      """PREFIX info:    	<http://somewhere/peopleInfo#>
        |PREFIX vcard:  	<http://www.w3.org/2001/vcard-rdf/3.0#>
        |
        |SELECT ?name ?age
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	OPTIONAL { ?person info:age ?age . FILTER ( ?age > 24 ) }
        |}
        |""".stripMargin).asQuery()

    val algOptFilter = Algebra.compile(optionalFilter)
    val t5 = translate(algOptFilter)
    // assert(eval(t5)(using sc = context) == SpaceValue("R252f02a6.name.CharlieFN", "Rb9e3bf8d.age.25", "Rb9e3bf8d.name.AliceFN"))
    assert(eval(t5) == SpaceValue("R252f02a6.name.CharlieFN", "R739c1f7f.name.Dora", "Rb9e3bf8d.age.25", "Rb9e3bf8d.name.AliceFN"))

    val optionalFilter2 = new ParameterizedSparqlString("""PREFIX info:    	<http://somewhere/peopleInfo#>
                                                          |PREFIX vcard:  	<http://www.w3.org/2001/vcard-rdf/3.0#>
                                                          |
                                                          |SELECT ?name ?age
                                                          |WHERE
                                                          |{
                                                          |	?person vcard:FN  ?name .
                                                          |	OPTIONAL { ?person info:age ?age . }
                                                          |	FILTER ( !bound(?age) || ?age > 24 )
                                                          |}
                                                          |""".stripMargin).asQuery()
    val algOpt2Filter = Algebra.compile(optionalFilter2)
    val t6 = translate(algOpt2Filter)
    assert(eval(t6) == SpaceValue("R252f02a6.name.CharlieFN", "Rb9e3bf8d.age.25", "Rb9e3bf8d.name.AliceFN"))

    val unionQuery = new ParameterizedSparqlString("""PREFIX foaf: <http://xmlns.com/foaf/0.1/>
                                                     |PREFIX vCard: <http://www.w3.org/2001/vcard-rdf/3.0#>
                                                     |
                                                     |SELECT ?name
                                                     |WHERE
                                                     |{
                                                     |   { [] foaf:name ?name } UNION { [] vCard:FN ?name }
                                                     |}
                                                     |""".stripMargin).asQuery()

    val algUnion = Algebra.compile(unionQuery)
    val unionMORKL = translate(algUnion)
    assert(eval(unionMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R4a4fbc23.name.Charlie", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora", "Raa5b8e36.name.AliceFN"))

    val twoWaysQuery = new ParameterizedSparqlString("""PREFIX foaf: <http://xmlns.com/foaf/0.1/>
                                                      |PREFIX vCard: <http://www.w3.org/2001/vcard-rdf/3.0#>
                                                      |
                                                      |SELECT ?name
                                                      |WHERE
                                                      |{
                                                      |  [] ?p ?name
                                                      |  FILTER ( ?p = foaf:name || ?p = vCard:FN )
                                                      |}""".stripMargin).asQuery()
    val algTwoWays = Algebra.compile(twoWaysQuery)
    val twoWaysMorkl = translate(algTwoWays)

    assert(eval(twoWaysMorkl) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R4a4fbc23.name.Charlie", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora", "Raa5b8e36.name.AliceFN"))


    val remeberingWhereQuery = new ParameterizedSparqlString("""PREFIX foaf: <http://xmlns.com/foaf/0.1/>
                                                               |PREFIX vCard: <http://www.w3.org/2001/vcard-rdf/3.0#>
                                                               |
                                                               |SELECT ?name1 ?name2
                                                               |WHERE
                                                               |{
                                                               |   { [] foaf:name ?name1 } UNION { [] vCard:FN ?name2 }
                                                               |}""".stripMargin).asQuery()
    val rememberingWhereAlg = Algebra.compile(remeberingWhereQuery)
    val rememberingWhereMorkl = translate(rememberingWhereAlg)

    assert(eval(rememberingWhereMorkl) == SpaceValue("R3f073e44.name2.AliceFN", "R891f221b.name2.CharlieFN", "R8ed45e.name1.Bob", "R957c521b.name1.Alice", "R9ef340ab.name1.Charlie", "Re39e7030.name2.Dora"))

    val optionalAndUnionQuery = new ParameterizedSparqlString("""PREFIX foaf: <http://xmlns.com/foaf/0.1/>
                                                                |PREFIX vCard: <http://www.w3.org/2001/vcard-rdf/3.0#>
                                                                |
                                                                |SELECT ?name1 ?name2
                                                                |WHERE
                                                                |{
                                                                |  ?x a foaf:Person
                                                                |  OPTIONAL { ?x  foaf:name  ?name1 }
                                                                |  OPTIONAL { ?x  vCard:FN   ?name2 }
                                                                |}""".stripMargin).asQuery()
    val optionalAndUnionAlg = Algebra.compile(optionalAndUnionQuery)
    val optionalAndUnionMorkl = translate(optionalAndUnionAlg)
    assert(eval(optionalAndUnionMorkl) == SpaceValue("R8ed45e.name1.Bob", "Rc95260c5.name1.Alice", "Rc95260c5.name2.AliceFN", "Re39e7030.name2.Dora"))


  }

  val context: SpaceContextMap = SpaceContextMap(Map(
    SpaceMention("SPO") -> SpaceValue(
      "A.FN.Alice", "A.age.25", "A.family.Smith",
      "B.FN.Bob", "B.age.28", "B.family.Bouwer",
      "C.FN.CharlieFN", "C.age.51", "C.family.Smith",
      "D.FN.Dora", "D.age.20"),
    SpaceMention("PSO") -> SpaceValue("FN.A.Alice", "FN.B.Bob", "FN.C.CharlieFN", "FN.D.Dora", "age.A.25", "age.B.28", "age.C.51", "age.D.20", "family.A.Smith", "family.B.Bouwer", "family.C.Smith"),
    SpaceMention("POS") -> SpaceValue("FN.Alice.A", "FN.Bob.B", "FN.CharlieFN.C", "FN.Dora.D", "age.20.D", "age.25.A", "age.28.B", "age.51.C", "family.Smith.A", "family.Bouwer.B", "family.Smith.C")
  ))

  test("double filters") {

    given SpaceContext = context

    // print_context_permutations(context)

    val twoFiltersInOptionalQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name ?age
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	OPTIONAL { ?person info:age ?age . FILTER ( ?age > 20 ) . FILTER ( ?age < 30)}
        |}""".stripMargin).asQuery()

    val twoFiltersInOptionalAlg = Algebra.compile(twoFiltersInOptionalQuery)
    val twoFiltersInOptionalMORKL = translate(twoFiltersInOptionalAlg)

    assert(eval(twoFiltersInOptionalMORKL) == SpaceValue("R24e793cb.age.25", "R24e793cb.name.Alice", "R252f02a6.name.CharlieFN", "R739c1f7f.name.Dora", "Ra8769d5b.age.28", "Ra8769d5b.name.Bob"))

    val twoExprsInFilterQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name ?age
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	?person info:age ?age .
        | FILTER ( ?age > 20 )
        | FILTER(?age < 30)
        |}""".stripMargin).asQuery()

    val twoExprsInFilterAlg = Algebra.compile(twoExprsInFilterQuery)
    // println(twoExprsInFilterAlg)
    // (project (?name ?age)
    //  (filter (exprlist (> ?age 20) (< ?age 30))
    //    (bgp
    //      (triple ?person <http://www.w3.org/2001/vcard-rdf/3.0#FN> ?name)
    //      (triple ?person <http://somewhere/peopleInfo#age> ?age)
    //    )))

    val twoExprsInFilterMORKL = translate(twoExprsInFilterAlg)
    assert(eval(twoExprsInFilterMORKL) == SpaceValue("R24e793cb.age.25", "R24e793cb.name.Alice", "Ra8769d5b.age.28", "Ra8769d5b.name.Bob"))
  }

  test("less than filters") {
    given SpaceContext = context

    val filterIntLessThanVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name ?age
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	?person info:age ?age .
        |  FILTER ( 25 < ?age)
        |}""".stripMargin).asQuery()

    val filterIntLessThanVarAlg = Algebra.compile(filterIntLessThanVarQuery)
    val filterIntLessThanVarMORKL = translate(filterIntLessThanVarAlg)

    //println(eval(filterIntLessThanVarMORKL).show)
    assert(eval(filterIntLessThanVarMORKL) == SpaceValue("R6e648a5d.age.51", "R6e648a5d.name.CharlieFN", "Ra8769d5b.age.28", "Ra8769d5b.name.Bob"))

    val filterVarLessThanVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?age1 ?age2
        |WHERE
        |{
        |	?person1 vcard:FN  ?name1 .
        |	?person1 info:age ?age1 .
        | ?person2 vcard:FN  ?name2 .
        |	?person2 info:age ?age2 .
        | FILTER ( ?age1 < ?age2)
        |}""".stripMargin).asQuery()

    val filterVarLessThanVarAlg = Algebra.compile(filterVarLessThanVarQuery)
    val filterVarLessThanVarMORKL = translate(filterVarLessThanVarAlg)

    assert(eval(filterVarLessThanVarMORKL) == SpaceValue("R3a6c1807.age1.25", "R3a6c1807.age2.28", "R561941bb.age1.20", "R561941bb.age2.28", "R71b32826.age1.28", "R71b32826.age2.51", "R966b0251.age1.20", "R966b0251.age2.25", "R99fc5b9a.age1.25", "R99fc5b9a.age2.51", "Rc264a24d.age1.20", "Rc264a24d.age2.51"))

    val filterConsLessThanConsPosQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 1 < 3)
        |}""".stripMargin).asQuery()

    val filterConsLessThanConsPosAlg = Algebra.compile(filterConsLessThanConsPosQuery)
    val filterConsLessThanConsPosMORKL = translate(filterConsLessThanConsPosAlg)

    assert(eval(filterConsLessThanConsPosMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val filterConsLessThanConsNegQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 3 < 1)
        |}""".stripMargin).asQuery()

    val filterConsLessThanConsNegAlg = Algebra.compile(filterConsLessThanConsNegQuery)
    val filterConsLessThanConsNegMORKL = translate(filterConsLessThanConsNegAlg)

    assert(eval(filterConsLessThanConsNegMORKL) == SpaceValue())
  }

  test("less or equal filters") {
    given SpaceContext = context

    val intVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name ?age
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	?person info:age ?age .
        |  FILTER ( 28 <= ?age)
        |}""".stripMargin).asQuery()

    val intVarAlg = Algebra.compile(intVarQuery)
    val intVarMORKL = translate(intVarAlg)

    //println(eval(filterIntLessThanVarMORKL).show)
    assert(eval(intVarMORKL) == SpaceValue("R6e648a5d.age.51", "R6e648a5d.name.CharlieFN", "Ra8769d5b.age.28", "Ra8769d5b.name.Bob"))

    val varVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?age1 ?age2
        |WHERE
        |{
        |	?person1 vcard:FN  ?name1 .
        |	?person1 info:age ?age1 .
        | ?person2 vcard:FN  ?name2 .
        |	?person2 info:age ?age2 .
        | FILTER ( ?age1 <= ?age2)
        |}""".stripMargin).asQuery()

    val varVarAlg = Algebra.compile(varVarQuery)
    val varVarMORKL = translate(varVarAlg)

    // println(eval(varVarMORKL).show)
    assert(eval(varVarMORKL) == SpaceValue("R3a6c1807.age1.25", "R3a6c1807.age2.28", "R561941bb.age1.20", "R561941bb.age2.28", "R5e6c52.age1.28", "R5e6c52.age2.28", "R71b32826.age1.28", "R71b32826.age2.51", "R966b0251.age1.20", "R966b0251.age2.25", "R98a32e95.age1.20", "R98a32e95.age2.20", "R99fc5b9a.age1.25", "R99fc5b9a.age2.51", "Ra901c078.age1.51", "Ra901c078.age2.51", "Rc264a24d.age1.20", "Rc264a24d.age2.51", "Rf9c8df12.age1.25", "Rf9c8df12.age2.25"))

    val consConsPositiveQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 3 <= 3)
        |}""".stripMargin).asQuery()

    val consConsPositiveAlg = Algebra.compile(consConsPositiveQuery)
    val consConsPositiveMORKL = translate(consConsPositiveAlg)

    // println(eval(consConsPositiveMORKL).show)
    assert(eval(consConsPositiveMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val consConsNegativeQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 3 <= 2)
        |}""".stripMargin).asQuery()

    val consConsNegativeAlg = Algebra.compile(consConsNegativeQuery)
    val consConsNegativeMORKL = translate(consConsNegativeAlg)

    assert(eval(consConsNegativeMORKL) == SpaceValue())
  }

  test("greater than filters") {
    given SpaceContext = context

    val filterIntGreaterThanVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name ?age
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	?person info:age ?age .
        |  FILTER ( 25 > ?age)
        |}""".stripMargin).asQuery()

    val filterIntGreaterThanVarAlg = Algebra.compile(filterIntGreaterThanVarQuery)
    val filterIntGreaterThanVarMORKL = translate(filterIntGreaterThanVarAlg)

    // println(eval(filterIntGreaterThanVarMORKL).show)
    assert(eval(filterIntGreaterThanVarMORKL) == SpaceValue("Re15e3a2f.age.20", "Re15e3a2f.name.Dora"))

    val filterVarGreaterThanVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?age1 ?age2
        |WHERE
        |{
        |	?person1 vcard:FN  ?name1 .
        |	?person1 info:age ?age1 .
        | ?person2 vcard:FN  ?name2 .
        |	?person2 info:age ?age2 .
        | FILTER ( ?age2 > ?age1)
        |}""".stripMargin).asQuery()

    val filterVarGreaterThanVarAlg = Algebra.compile(filterVarGreaterThanVarQuery)
    val filterVarGreaterThanVarMORKL = translate(filterVarGreaterThanVarAlg)

    assert(eval(filterVarGreaterThanVarMORKL) == SpaceValue("R3a6c1807.age1.25", "R3a6c1807.age2.28", "R561941bb.age1.20", "R561941bb.age2.28", "R71b32826.age1.28", "R71b32826.age2.51", "R966b0251.age1.20", "R966b0251.age2.25", "R99fc5b9a.age1.25", "R99fc5b9a.age2.51", "Rc264a24d.age1.20", "Rc264a24d.age2.51"))


    val filterConsGreaterThanConsPosQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 3 > 1)
        |}""".stripMargin).asQuery()

    val filterConsGreaterThanConsPosAlg = Algebra.compile(filterConsGreaterThanConsPosQuery)
    val filterConsGreaterThanConsPosMORKL = translate(filterConsGreaterThanConsPosAlg)

    assert(eval(filterConsGreaterThanConsPosMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val filterConsGreaterThanConsNegQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 1 > 3)
        |}""".stripMargin).asQuery()

    val filterConsGreaterThanConsNegAlg = Algebra.compile(filterConsGreaterThanConsNegQuery)
    val filterConsGreaterThanConsNegMORKL = translate(filterConsGreaterThanConsNegAlg)

    assert(eval(filterConsGreaterThanConsNegMORKL) == SpaceValue())
  }

  test("greater or equal filters") {
    given SpaceContext = context

    val intVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name ?age
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	?person info:age ?age .
        |  FILTER ( 20 >= ?age)
        |}""".stripMargin).asQuery()

    val intVarAlg = Algebra.compile(intVarQuery)
    val intVarMORKL = translate(intVarAlg)

    // println(eval(intVarMORKL).show)
    assert(eval(intVarMORKL) == SpaceValue("Re15e3a2f.age.20", "Re15e3a2f.name.Dora"))

    val varVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?age1 ?age2
        |WHERE
        |{
        |	?person1 vcard:FN  ?name1 .
        |	?person1 info:age ?age1 .
        | ?person2 vcard:FN  ?name2 .
        |	?person2 info:age ?age2 .
        | FILTER ( ?age2 >= ?age1)
        |}""".stripMargin).asQuery()

    val varVarAlg = Algebra.compile(varVarQuery)
    val varVarMORKL = translate(varVarAlg)

    assert(eval(varVarMORKL) == SpaceValue("R3a6c1807.age1.25", "R3a6c1807.age2.28", "R561941bb.age1.20", "R561941bb.age2.28", "R5e6c52.age1.28", "R5e6c52.age2.28", "R71b32826.age1.28", "R71b32826.age2.51", "R966b0251.age1.20", "R966b0251.age2.25", "R98a32e95.age1.20", "R98a32e95.age2.20", "R99fc5b9a.age1.25", "R99fc5b9a.age2.51", "Ra901c078.age1.51", "Ra901c078.age2.51", "Rc264a24d.age1.20", "Rc264a24d.age2.51", "Rf9c8df12.age1.25", "Rf9c8df12.age2.25"))


    val consConsPositiveQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 3 >= 3)
        |}""".stripMargin).asQuery()

    val consConsPositiveAlg = Algebra.compile(consConsPositiveQuery)
    val consConsPositiveMORKL = translate(consConsPositiveAlg)

    assert(eval(consConsPositiveMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val consConsNegativeQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 2 >= 3)
        |}""".stripMargin).asQuery()

    val consConsNegativeAlg = Algebra.compile(consConsNegativeQuery)
    val consConsNegativeMORKL = translate(consConsNegativeAlg)

    assert(eval(consConsNegativeMORKL) == SpaceValue())
  }

  test("equal filters"){
    given SpaceContext = context

    val filterVarEqualsStringQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( ?name = "Alice")
        |}""".stripMargin).asQuery()

    val filterVarEqualsStringAlgebra = Algebra.compile(filterVarEqualsStringQuery)
    val filterVarEqualsStringMORKL = translate(filterVarEqualsStringAlgebra)

    // println(eval(filterVarEqualsStringMORKL).show)
    assert(eval(filterVarEqualsStringMORKL) == SpaceValue("R5caa4e81.name.Alice"))

    val filterStringEqualsVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ("Alice" = ?name)
        |}""".stripMargin).asQuery()

    val filterStringEqualsVarAlgebra = Algebra.compile(filterStringEqualsVarQuery)
    val filterStringEqualsVarMORKL = translate(filterStringEqualsVarAlgebra)

    // println(eval(filterVarEqualsStringMORKL).show)
    assert(eval(filterStringEqualsVarMORKL) == SpaceValue("R5caa4e81.name.Alice"))


    val filterVarEqualsIntQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?person
        |WHERE
        |{
        | ?person info:age ?age
        | FILTER ( ?age = 20)
        |}""".stripMargin).asQuery()

    val filterVarEqualsIntAlgebra = Algebra.compile(filterVarEqualsIntQuery)
    val filterVarEqualsIntMORKL = translate(filterVarEqualsIntAlgebra)

    // println(eval(filterVarEqualsIntMORKL).show)
    assert(eval(filterVarEqualsIntMORKL) == SpaceValue("Ra1467c53.person.D"))

    val filterIntEqualsVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?person
        |WHERE
        |{
        | ?person info:age ?age
        | FILTER (20 = ?age)
        |}""".stripMargin).asQuery()

    val filterIntEqualsVarAlgebra = Algebra.compile(filterIntEqualsVarQuery)
    val filterIntEqualsVarMORKL = translate(filterIntEqualsVarAlgebra)

    // println(eval(filterIntEqualsVarMORKL).show)
    assert(eval(filterIntEqualsVarMORKL) == SpaceValue("Ra1467c53.person.D"))


    val filterVarEqualsIRIQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        | ?person ?p ?name
        | FILTER (?p = vcard:FN)
        |}""".stripMargin).asQuery()

    val filterVarEqualsIRIAlgebra = Algebra.compile(filterVarEqualsIRIQuery)
    val filterVarEqualsIRIMORKL = translate(filterVarEqualsIRIAlgebra)

    // println(eval(filterVarEqualsIRIMORKL).show)
    assert(eval(filterVarEqualsIRIMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora")
    )

    val filterIRIEqualsVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        | ?person ?p ?name
        | FILTER (vcard:FN = ?p)
        |}""".stripMargin).asQuery()

    val filterIRIEqualsVarAlgebra = Algebra.compile(filterIRIEqualsVarQuery)
    val filterIRIEqualsVarMORKL = translate(filterIRIEqualsVarAlgebra)

    // println(eval(filterIRIEqualsVarMORKL).show)
    assert(eval(filterIRIEqualsVarMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val filterVarEqualsVarQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?person1 ?person2
        |WHERE
        |{
        | ?person1 info:family ?family1 .
        | ?person2 info:family ?family2 .
        | FILTER (?family1 = ?family2) .
        |}""".stripMargin).asQuery()

    val filterVarEqualsVarAlgebra = Algebra.compile(filterVarEqualsVarQuery)
    val filterVarEqualsVarMORKL = translate(filterVarEqualsVarAlgebra)

    // println(eval(filterVarEqualsVarMORKL).show)
    assert(eval(filterVarEqualsVarMORKL) == SpaceValue("R13c5b67a.person1.A", "R13c5b67a.person2.C", "R2710c9c9.person1.B", "R2710c9c9.person2.B", "R73b91de9.person1.C", "R73b91de9.person2.C", "R861c57a0.person1.C", "R861c57a0.person2.A", "Rd194f6fa.person1.A", "Rd194f6fa.person2.A"))


    val filterStringEqualsStringNegQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( "hello" = "ehllo")
        |}""".stripMargin).asQuery()

    val filterStringEqualsStringNegAlg = Algebra.compile(filterStringEqualsStringNegQuery)
    val filterStringEqualsStringNegMORKL = translate(filterStringEqualsStringNegAlg)

    // println(eval(filterStringEqualsStringNegMORKL).show)
    assert(eval(filterStringEqualsStringNegMORKL) == SpaceValue())

    val filterStringEqualsStringPosQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( "hello" = "hello")
        |}""".stripMargin).asQuery()

    val filterStringEqualsStringPosAlg = Algebra.compile(filterStringEqualsStringPosQuery)
    val filterStringEqualsStringPosMORKL = translate(filterStringEqualsStringPosAlg)

    assert(eval(filterStringEqualsStringPosMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))


    val filterStringEqualsIntPosQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 5 = 5)
        |}""".stripMargin).asQuery()

    val filterStringEqualsIntPosAlg = Algebra.compile(filterStringEqualsIntPosQuery)
    val filterStringEqualsIntPosMORKL = translate(filterStringEqualsIntPosAlg)

    assert(eval(filterStringEqualsIntPosMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val filterStringEqualsIntNegQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( 4 = 5)
        |}""".stripMargin).asQuery()

    val filterStringEqualsIntNegAlg = Algebra.compile(filterStringEqualsIntNegQuery)
    val filterStringEqualsIntNegMORKL = translate(filterStringEqualsIntNegAlg)

    assert(eval(filterStringEqualsIntNegMORKL) == SpaceValue())


    val filterStringEqualsIRIPosQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( vcard:FN = vcard:FN)
        |}""".stripMargin).asQuery()

    val filterStringEqualsIRIPosAlg = Algebra.compile(filterStringEqualsIRIPosQuery)
    val filterStringEqualsIRIPosMORKL = translate(filterStringEqualsIRIPosAlg)

    assert(eval(filterStringEqualsIRIPosMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val filterStringEqualsIRINegQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN ?name .
        | FILTER ( vcard:FN = info:name)
        |}""".stripMargin).asQuery()

    val filterStringEqualsIRINegAlg = Algebra.compile(filterStringEqualsIRINegQuery)
    val filterStringEqualsIRINegMORKL = translate(filterStringEqualsIRINegAlg)

    assert(eval(filterStringEqualsIRINegMORKL) == SpaceValue())

    // val alg = AlgebraSPARQL()
    // val e = S"SPO"("A.age").iter("age", "_", S"SPO"("A.age") <| alg.range(P"age" x "100" x "1"))
    // println(eval(e).show)

    // println(eval(sparqlAlg.range("2.1.1")))
    // println(Range(2, 1, 1))


  }

  test("ordering"){
    val ordering_context: SpaceContextMap = SpaceContextMap(Map(
      SpaceMention("SPO") -> SpaceValue(
        "A.FN.Alice", "A.age.25",
        "B.FN.Bob", "B.age.28",
        "C.FN.Charlie", "C.age.25",
        "D.FN.Dora"),
      SpaceMention("PSO") -> SpaceValue("FN.A.Alice", "FN.B.Bob", "FN.C.Charlie", "FN.D.Dora", "age.A.25", "age.B.28", "age.C.25"),
      SpaceMention("POS") -> SpaceValue("FN.Alice.A", "FN.Bob.B", "FN.Charlie.C", "FN.Dora.D", "age.25.A", "age.28.B", "age.25.C")
    ))


    given SpaceContext = ordering_context

    val orderAgeQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	?person info:age ?age .
        |}
        |ORDER BY ?age""".stripMargin).asQuery()

    val orderAgeAlgebra = Algebra.compile(orderAgeQuery)
    val orderAgeMORKL = translate(orderAgeAlgebra)

    // println(eval(orderAgeMORKL).show)
    // assert(eval(orderAgeMORKL) == SpaceValue("25.R4a4fbc23.name.Charlie", "25.R5caa4e81.name.Alice", "28.R44c6683b.name.Bob"))
    assert(eval(orderAgeMORKL) == SpaceValue("1.asc.25.R4a4fbc23.name.Charlie", "1.asc.25.R5caa4e81.name.Alice", "1.asc.28.R44c6683b.name.Bob"))

    val orderAgeNameQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	OPTIONAL {?person info:age ?age} .
        |}
        |ORDER BY ?age ?name""".stripMargin).asQuery()

    val orderAgeNameAlgebra = Algebra.compile(orderAgeNameQuery)
    val orderAgeNameMORKL = translate(orderAgeNameAlgebra)

    // println(eval(orderAgeNameMORKL).show)
    // assert(eval(orderAgeNameMORKL) == SpaceValue("lr.0.lr.Dora.R739c1f7f.name.Dora", "Symbol(25) Symbol(Alice).R5caa4e81.name.Alice", "Symbol(25) Symbol(Charlie).R4a4fbc23.name.Charlie", "Symbol(28) Symbol(Bob).R44c6683b.name.Bob"))
    assert(eval(orderAgeNameMORKL) == SpaceValue("2.asc.0.asc.Dora.R739c1f7f.name.Dora", "2.asc.25.asc.Alice.R5caa4e81.name.Alice", "2.asc.25.asc.Charlie.R4a4fbc23.name.Charlie", "2.asc.28.asc.Bob.R44c6683b.name.Bob"))

    val orderOptionalQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	OPTIONAL {?person info:age ?age} .
        |}
        |ORDER BY ?age""".stripMargin).asQuery()

    val orderOptionalAlgebra = Algebra.compile(orderOptionalQuery)
    val orderOptionalMORKL = translate(orderOptionalAlgebra)

    // TODO what to use as prefix for unordered elements (like Dora in this example)
    // println(eval(orderOptionalMORKL).show)
    // assert(eval(orderOptionalMORKL) == SpaceValue("0.R739c1f7f.name.Dora", "25.R4a4fbc23.name.Charlie", "25.R5caa4e81.name.Alice", "28.R44c6683b.name.Bob"))
    assert(eval(orderOptionalMORKL) == SpaceValue("1.asc.0.R739c1f7f.name.Dora", "1.asc.25.R4a4fbc23.name.Charlie", "1.asc.25.R5caa4e81.name.Alice", "1.asc.28.R44c6683b.name.Bob"))


    val orderAgeDescNameQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |	OPTIONAL {?person info:age ?age} .
        |}
        |ORDER BY ASC(?age) DESC(?name)""".stripMargin).asQuery()

    val orderAgeDescNameAlgebra = Algebra.compile(orderAgeDescNameQuery)
    val orderAgeDescNameMORKL = translate(orderAgeDescNameAlgebra)

    // println(eval(orderAgeDescNameMORKL).show)
    assert(eval(orderAgeDescNameMORKL) == SpaceValue("2.asc.0.desc.Dora.R739c1f7f.name.Dora", "2.asc.25.desc.Alice.R5caa4e81.name.Alice", "2.asc.25.desc.Charlie.R4a4fbc23.name.Charlie", "2.asc.28.desc.Bob.R44c6683b.name.Bob"))

  }

  test("limit") {
    given SpaceContext = context

    val limitQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |}
        |LIMIT 2""".stripMargin).asQuery()

    val limitAlg = Algebra.compile(limitQuery)
    val limitMORKL = translate(limitAlg)

    // println(eval(limitMORKL).show)
    assert(eval(limitMORKL) == SpaceValue("R252f02a6.name.CharlieFN", "R739c1f7f.name.Dora"))

    val limitAscOrderQuery = new ParameterizedSparqlString(
      """PREFIX vcard:   <http://www.w3.org/2001/vcard-rdf/3.0#>
        |PREFIX info:    <http://somewhere/peopleInfo#>
        |SELECT ?name
        |WHERE
        |{
        |	?person vcard:FN  ?name .
        |}
        |ORDER BY ?name
        |LIMIT 2""".stripMargin).asQuery()

    val limitAscOrderAlg = Algebra.compile(limitAscOrderQuery)
    val limitAscOrderMORKL = translate(limitAscOrderAlg)

    // TODO note: limit does not take the first two of the ordered sequence! (Bob is missing)
    // println(eval(limitAscOrderMORKL).show)
    assert(eval(limitAscOrderMORKL) == SpaceValue("1.asc.Alice.R5caa4e81.name.Alice", "1.asc.CharlieFN.R252f02a6.name.CharlieFN"))


  }





