package morkl

import morkl.Space.Singleton
import munit.FunSuite
import morkl.Syntax.{x, *, given}
import org.apache.jena.sparql.expr.E_GreaterThanOrEqual


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
  def spaceout(space: Space)(using ab: collection.mutable.ArrayBuffer[SpaceValue]): Path = grounded.spaceout(space)(using ab: collection.mutable.ArrayBuffer[SpaceValue])

  def Head(s: Space): Space = s.iter("s", "_", Singleton(P"s"))

  extension (s: Space)
    def tee(run: Space): Space = s.iter("_1", "_2", run)

  def range(path: Path): Space = grounded.range(path)

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
  def Head(space:Space): Space = sparql.Head(space)
  extension (s: Space)
    def tee(run: Space): Space = s.iter("_1", "_2", run)

  val grounded = Grounded()
  def range(path: Path): Space = grounded.range(path)
  def phash(path: Path) = grounded.hash(path)
  def shash(space: Space) = grounded.hash(space)


  def get_incompatible(s1: Space, s2: Space): Space =
    (Head(s1) /\ Head(s2)).iter("v", "_", {
      P"v" x (s1(P"v") \ s2(P"v"))
    })

  def if_empty_do(e: Space, todo: Space): Space =
    (Singleton("tobeempty") \ Head("tobeempty" x e)).tee(todo)

  def join(s1: Space, s2: Space): Space =
    (Singleton("incompatible") \ Head("incompatible" x get_incompatible(s1, s2))).tee(s1 \/ s2)

  def join2(s1: Space, s2: Space): Space =
    if_empty_do(get_incompatible(s1, s2), s1 \/ s2)

  def hyperJoin(s1: Space, s2: Space): Space =
    // s1.iter("h1", "tail1", S"tail1")
    s1.iter("h1", "tail1", s2.iter("h2", "tail2", shash(join2(S"tail1", S"tail2")) x join2(S"tail1", S"tail2")))

  def difference(s1: Space, s2: Space): Space =
    // assuming filter = True
    get_incompatible(s1, s2).tee(s1)

  def hyperDifference(s1: Space, s2: Space): Space =
    // assuming filter = True
    val p1 = s1.iter("hash1", "tail1", if_empty_do(s2.iter("hash2", "tail2", if_empty_do(get_incompatible(S"tail1", S"tail2"), Singleton("compatible"))), P"hash1" x S"tail1"))
    val p2 = s1.iter("hash1", "tail1", if_empty_do(s2.iter("hash2", "tail2", get_incompatible(S"tail1", S"tail2").tee(Singleton("incompatible"))), P"hash1" x S"tail1"))
    p1 \/ p2


  def leftJoin(s1: Space, s2: Space): Space =
    // assuming filter = True
    join(s1, s2) \/ difference(s1, s2)

  def hyperLeftJoin(s1: Space, s2: Space): Space =
    // assuming filter = True
    hyperJoin(s1, s2) \/ hyperDifference(s1, s2)

  def filterBiggerThen(s1: Space, v: String, i: Int, max: Int = 2000): Space =
    (s1(v) <| range(i.toString + "." + max.toString + "." + "1")).tee(s1)

  def hyperFilterBiggerThen(s1: Space, v: String, i: Int, max: Int = 2000): Space =
    s1.iter("hash", "tail", "hash" x filterBiggerThen(S"tail", v, i, max))

  def filterSmallerThen(s1: Space, v: String, i: Int): Space =
    (s1(v) <| range("0." + i.toString + ".1")).tee(s1)

  def hyperFilterLessThen(s1: Space, v: String, i: Int): Space =
    s1.iter("hash", "tail", "hash" x filterSmallerThen(S"tail", v, i))


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
    assert(eval(filterBiggerThen(S"rhs", "age", 10))(using sc = compatible) == SpaceValue("age.13", "name.Alice", "person.A"))
    assert(eval(filterBiggerThen(S"rhs", "age", 15))(using sc = compatible) == SpaceValue())
    assert(eval(filterSmallerThen(S"rhs", "age", 10))(using sc = compatible) == SpaceValue())
    assert(eval(filterSmallerThen(S"rhs", "age", 15))(using sc = compatible) == SpaceValue("age.13", "name.Alice", "person.A"))
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

  def spaceout(space: Space)(using ab: collection.mutable.ArrayBuffer[SpaceValue]): Path =
    Path.GroundedSP(space, sv => {
      ab.addOne(sv);
      PathValue(List(PathItem.Symbol("unit")))
    })

  val g = Grounded()
  def phash(path: Path) = g.hash(path)
  def shash(space: Space) = g.hash(space)

  def prefixHash(space: Space): Space = shash(space) x space


  def Head(s: Space): Space = s.iter("s", "_", Singleton(P"s"))

  extension (s: Space)
    def tee(run: Space): Space = s.iter("_1", "_2", run)

  val sparqlAlg = AlgebraSPARQL()

  def join2(s1: Space, s2: Space): Space = sparqlAlg.join2(s1, s2)
  def hyperJoin(s1: Space, s2: Space): Space = sparqlAlg.hyperJoin(s1, s2)
  def hyperLeftJoin(s1: Space, s2: Space): Space = sparqlAlg.hyperLeftJoin(s1, s2)
  def filterBiggerThen(s1: Space, v: String, i: Int): Space = sparqlAlg.filterBiggerThen(s1, v, i)
  def hyperFilterBiggerThen: (Space, String, Int, Int) => Space = sparqlAlg.hyperFilterBiggerThen
  def filterLessThen(s1: Space, v: String, i: Int): Space = sparqlAlg.filterSmallerThen(s1, v, i)
  def hyperFilterLessThen: (Space, String, Int) => Space = sparqlAlg.hyperFilterLessThen


  val context: SpaceContextMap = SpaceContextMap(Map(
    SpaceMention("SPO") -> SpaceValue(
      "A.type.Person", "A.name.Alice", "A.FN.AliceFN", "A.age.25", "Alice.Family.Smith", "Alice.Given.Lis", "Alice.Given.Al", "Mel.Family.Smith",
      "B.type.Person", "B.name.Bob", "B.age.12", "Bob.Family.Bouwer", "Bob.Given.Bow",
      "C.name.Charlie",
      "D.type.Person", "D.FN.Dora"),
    SpaceMention("PSO") -> SpaceValue(
      "age.A.25", "age.B.12",
      "type.A.Person", "type.B.Person",
      "name.A.Alice", "name.B.Bob", "name.C.Charlie",
      "FN.A.AliceFN",
      "Family.Alice.Smith", "Given.Alice.Lis", "Given.Alice.Al", "Family.Mel.Smith",
      "Family.Bob.Bouwer", "Given.Bob.Bow",
      "type.D.Person", "FN.D.Dora"),
    SpaceMention("POS") -> SpaceValue(
      "age.12.B", "age.25.A",
      "type.Person.A", "type.Person.B",
      "name.Alice.A", "name.Bob.B", "name.Charlie.C",
      "Fn.AliceFN.A",
      "Family.Smith.Alice", "Given.Lis.Alice", "Given.Al.Alice", "Family.Smith.Mel",
      "Family.Bouwer.Bob", "Given.Bob.Bow",
      "type.Person.D", "FN.Dora.D")
  ))

  test("query parsed") {
    val q = new ParameterizedSparqlString(
      """PREFIX ex: <http://example.org/ns#>
        |
        |SELECT ?price ?title
        |WHERE {
        |  ?book ex:price ?price .
        |  FILTER (?price > 15) .
        |  OPTIONAL { ?book ex:title ?title } .
        |  {
        |    ?book ex:author ex:Shakespeare
        |  } UNION {
        |    ?book ex:author ex:Marlowe
        |  }
        |}""".stripMargin).asQuery()

    val blindNodes = new ParameterizedSparqlString(
      """PREFIX vcard:  	<http://www.w3.org/2001/vcard-rdf/3.0#>
        |
        |SELECT ?y ?givenName
        |WHERE
        | { ?y vcard:Family "Smith" .
        |   ?y vcard:Given  ?givenName .
        | }
        |""".stripMargin).asQuery()


    println(q)
    val aq = Algebra.compile(q)
    val algblind = Algebra.compile(blindNodes)

    println(aq)
    println(algblind)
    println(Algebra.optimize(aq))

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
      rotation(0).length match
        case 0 => ???
        case 1 =>
          val c0 = get_str(triple_get(triple, constant_ids(0)))
          val v0 = triple_get(triple, var_ids(0)).getName
          val v1 = triple_get(triple, var_ids(1)).getName
          val e = m(ordered_spo)(c0).iter("x", "sy", S"sy".iter("y", "_", {
            prefixHash(Singleton(v0 x P"x") \/ Singleton(v1 x P"y"))
          }))
          println(eval(e)(using sc = context).show)
          e
        case 2 =>
          val c0 = get_str(triple_get(triple, constant_ids(0)))
          val c1 = get_str(triple_get(triple, constant_ids(1)))
          val v0 = triple_get(triple, var_ids(0)).getName
          val e = m(ordered_spo)(c0 x c1).iter("x", "_", {
            prefixHash(v0 x Singleton(P"x"))
          })
          println(eval(e)(using sc = context).show)
          e

        case 3 => ???


    def translate(op: Op): Space = op match
      case op: OpProject =>
        val t = translate(op.getSubOp)
        val varspace = Range(0, op.getVars.size()).map(i => {op.getVars.get(i).getName}).foldLeft(Space.Empty)((s1, p2) => s1 \/ Singleton(p2))
        val e = t.iter("hash", "vv", prefixHash(S"vv" <| varspace))
        e

      case op: OpBGP =>
        println("bgp")
        val e = Range(1, op.getPattern.size()).map(x => get_space_from_bgp(op.getPattern.get(x))).fold(get_space_from_bgp(op.getPattern.get(0)))((s1, s2) => hyperJoin(s1, s2))
        println(eval(e)(using sc = context))
        e

      case op: OpJoin =>
        println("join")
        translate(op.getLeft)
        translate(op.getRight)
        return ???
      case op: OpLeftJoin =>
        hyperLeftJoin(translate(op.getLeft), translate(op.getRight))

      case op: OpFilter =>
        println("filter")
        translate(op.getSubOp)
        op.getExprs.get(0) match
          case e: E_LessThan =>
            println(s"less than $e")
            println(e.getArg1)
            return hyperFilterLessThen(translate(op.getSubOp), e.getArg1.asVar().getName, e.getArg2.asVar().getName.toInt)

            return ???
          case e: E_GreaterThanOrEqual =>
            println(e.getArg2.getConstant.getInteger)

            return hyperFilterBiggerThen(translate(op.getSubOp), e.getArg1.asVar().getName, e.getArg2.getConstant.toString.toInt, 2000)
            return ???
          case e =>
            println(s"unsupported expr $e (${e.getClass.getName})")
            return ???
      case op: OpUnion =>
        println("Union")
        translate(op.getLeft)
        translate(op.getRight)
        return ???

      case op =>
        println(s"unhandled case $op")
        return ???

    println("------------")

    val t = translate(algblind)
    // println(t.show)
    assert(eval(t)(using sc = context) == SpaceValue("R4f8194bd.givenName.Al", "R4f8194bd.y.Alice", "Re30ef3e3.givenName.Lis", "Re30ef3e3.y.Alice"))

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
    // println(t2.show)
    assert(eval(t2)(using sc = context) == SpaceValue("R24e793cb.age.25", "R24e793cb.name.Alice", "R29640fc9.age.12", "R29640fc9.name.Bob", "R4a4fbc23.name.Charlie"))

    val dependentOptional = new ParameterizedSparqlString("""PREFIX foaf: <http://xmlns.com/foaf/0.1/>
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
    println("eval 3")
    assert(eval(t3)(using sc = context) == SpaceValue("R44c6683b.name.Bob", "R5caa4e81.name.Alice", "R739c1f7f.name.Dora"))

    val filterQuery = new ParameterizedSparqlString("""PREFIX info: <http://somewhere/peopleInfo#>
                                                      |
                                                      |SELECT ?resource
                                                      |WHERE
                                                      |{
                                                      |?resource info:age ?age .
                                                      |FILTER (?age >= 24)
                                                      |}""".stripMargin).asQuery()
    val algfilter = Algebra.compile(filterQuery)
    val t4= translate(algfilter)
    assert(eval(t4)(using sc = context) == SpaceValue("R9623531d.resource.A"))

  }





