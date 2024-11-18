package morkl

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
    println(transpile(scc_routine).show)
    println("optimized")
    println(optimize_sharing(transpile(scc_routine)).show)
    println(prune_redundant(optimize_sharing(transpile(scc_routine))).show)
  }

  test("transpile union iter") {
    println(transpile(union_iter_routine).show)
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

  def spaceout(space: Space)(using ab: collection.mutable.ArrayBuffer[SpaceValue]): Path =
    Path.GroundedSP(space, sv => {
      ab.addOne(sv); PathValue(List(PathItem.Symbol("unit")))
    })

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

  test("loves example") {
    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty

    //val l = S"PSO"("loves").iter("s", "os", S"os".iter("o", "_", Singleton("person1" x P"s") \/ Singleton("person2" x P"o") ))
    val l2 = S"PSO"("loves").iter("s", "o", S"o".iter("o", "_", Singleton(spaceout(Singleton( P"s" x P"o" )))))
    assert(eval(l2)(using PathContext.emptyMap, loves) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("Harry.Taylor"), SpaceValue("Harry.Macbeth"), SpaceValue("Macbeth.Taylor"), SpaceValue("Macbeth.Harry")))
  }



  // (x.X, name.NAME)
  test("basic pattern") {
    // SPO -> PSO
    val spo_to_pso = S"SPO".iter("s", "po", S"po".iter("p", "o", Singleton(P"p" x P"s") x S"o"))
    assert(eval(spo_to_pso)(using PathContext.emptyMap, context) == eval(S"PSO")(using PathContext(), context))

    // SPO -> POS
    val spo_to_pos = S"SPO".iter("s", "po", S"po".iter("p", "o", Singleton(P"p") x S"o" x Singleton(P"s")))
    assert(eval(spo_to_pos)(using PathContext.emptyMap, context) == eval(S"POS")(using PathContext(), context))

    val basic_pattern_person = "person" x S"POS"("isa" x "Person")
    assert(eval(basic_pattern_person)(using PathContext.emptyMap, context) == SpaceValue("person.A", "person.B"))

    val basic_pattern_name = "name" x S"POS"("isa" x "Person").iter("x", "_", S"PSO"("name" x P"x"))
    assert(eval(basic_pattern_name)(using PathContext.emptyMap, context) == SpaceValue("name.Alice", "name.Bob"))

    val basic_pattern = S"POS"("isa" x "Person").iter("x", "_", ("name" x S"PSO"("name" x P"x")) \/ ("person" x Singleton(P"x")))
    assert(eval(basic_pattern)(using PathContext.emptyMap, context) == SpaceValue("person.A", "name.Alice", "person.B", "name.Bob"))


    given ps: collection.mutable.ArrayBuffer[SpaceValue] = collection.mutable.ArrayBuffer.empty
    val basic_pattern_ = S"POS"("isa" x "Person").iter("x", "_", Singleton(spaceout(("name" x S"PSO"("name" x P"x")) \/ ("person" x Singleton(P"x")))))
    assert(eval(basic_pattern_)(using PathContext.emptyMap, context) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("person.A", "name.Alice"), SpaceValue("person.B", "name.Bob")))


    val basic_blank_nodes = S"POS"("family" x "Smith").iter("y", "_", Singleton("y" x P"y") \/ ("given" x S"SPO"(P"y" x "given")))
    assert(eval(basic_blank_nodes)(using PathContext.emptyMap, context) == SpaceValue("given.Lis", "y.Alice"))

    ps.clear()
    val basic_blank_nodes_ = S"POS"("family" x "Smith").iter("y", "_", Singleton(spaceout(Singleton("y" x P"y") \/ ("given" x S"SPO"(P"y" x "given")))))
    assert(eval(basic_blank_nodes_)(using PathContext.emptyMap, context) == SpaceValue("unit"))
    assert(ps.toList == List(SpaceValue("y.Alice", "given.Lis")))

    // val filter_values = S"POS"("age").iter("a", "r", (ifa (P"a" < 25) then "resource" x S"r" else Singleton(P"a")))
    // val filter_values = S"POS"("age").iter("age", "r", "resource" x Singleton(P"age") x S"r")

    // val optionals =


    println(eval(basic_pattern_)(using PathContext.emptyMap, context).show)
    println(ps.toList)

  }

end SPARQL

