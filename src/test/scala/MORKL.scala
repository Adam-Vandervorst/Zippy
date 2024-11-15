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

class SPARQL extends FunSuite:
  import org.apache.jena.query.ParameterizedSparqlString
  import org.apache.jena.query.Query
  import org.apache.jena.sparql.expr.ExprVisitorBase
  import org.apache.jena.sparql.algebra.Algebra
  import org.apache.jena.sparql.algebra.OpVisitorBase
  import org.apache.jena.sparql.algebra.walker.WalkerVisitor
  import org.apache.jena.sparql.algebra.{OpVisitor, op, Op, OpVisitorByTypeBase, OpVisitorByType}
  import org.apache.jena.sparql.algebra.op.{Op0, Op1, Op2, OpN, OpAssign, OpBGP, OpConditional, OpDatasetNames, OpDiff, OpDisjunction, OpDistinct, OpExtend, OpFilter, OpGroup, OpJoin, OpLabel, OpLateral, OpLeftJoin, OpList, OpMinus, OpNull, OpOrder, OpPath, OpProcedure, OpProject, OpPropFunc, OpQuad, OpQuadBlock, OpQuadPattern, OpReduced, OpSequence, OpService, OpSlice, OpTable, OpTopN, OpTriple, OpUnion}
  import Space.*

  extension [K, V](m1: Map[K, V])
    def unionWith(op: (V, V) => V)(m2: Map[K, V]): Map[K, V] =
      val n = collection.mutable.Map.from(m1)
      m2.foreachEntry((k, v) =>
        var required = true
        val v_ = n.getOrElseUpdate(k, {
          required = false;
          v
        })
        if required then n.update(k, op(v, v_))
      )
      n.toMap

  test("query parsed") {
    val q = new ParameterizedSparqlString(
      """PREFIX ex: <http://example.org/ns#>
        |
        |SELECT ?price ?title
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
    println(q)
    val aq = Algebra.compile(q)
    println(aq)
    println(Algebra.optimize(aq))
    case class Frame[A](func: collection.mutable.ArrayBuffer[A] => A, args: collection.mutable.ArrayBuffer[A])
    val stack = collection.mutable.Stack[Frame[(Map[String, Boolean], String)]](Frame(args => {
      assert(args.size == 1); args.last
    }, collection.mutable.ArrayBuffer.empty))
    val before_op = new OpVisitorBase {
      override def visit(opTriple: OpTriple): Unit =
        assert(false)
        stack.push(Frame(cs => {
          Map() -> s"PathOf(${opTriple.getTriple})()"
        }, collection.mutable.ArrayBuffer.empty))

      override def visit(opBGP: OpBGP): Unit =
        stack.push(Frame(cs => {
          assert(opBGP.getPattern.size() == 1)
          val triple = opBGP.getPattern.get(0)
          val (s, p, o) = (triple.getSubject, triple.getPredicate, triple.getObject)
          //          println(s"pattern variables ${Set(s, p, o).filter(_.isVariable).map(_.getName)} ")
          Set(s, p, o).filter(_.isVariable).map(_.getName -> true).toMap -> s"LoopOver(${opBGP.getPattern})()"
        }, collection.mutable.ArrayBuffer.empty))

      override def visit(opProject: OpProject): Unit =
        stack.push(Frame(cs => {
          assert(cs.size == 1)
          val allowed = collection.mutable.Set.empty[String]
          opProject.getVars.iterator().forEachRemaining(x => allowed.addOne(x.getVarName))
          cs.head._1.filter((s, g) => allowed.contains(s)) -> s"Project(${opProject.getVars.toArray.mkString(", ")})(${cs.mkString(", ")})"
        }, collection.mutable.ArrayBuffer.empty))

      override def visit(opUnion: OpUnion): Unit =
        stack.push(Frame(cs => {
          // union is left biased!
          assert(cs.size == 2 && cs(0)._1 == cs(1)._1)
          cs(0)._1 -> s"Union()(${cs.mkString(", ")})"
        }, collection.mutable.ArrayBuffer.empty))

      override def visit(opJoin: OpJoin): Unit =
        stack.push(Frame(cs => {
          assert(cs.size == 2)
          cs(0)._1.unionWith(_ || _)(cs(1)._1) -> s"Join()(${cs.mkString(", ")})"
        }, collection.mutable.ArrayBuffer.empty))

      override def visit(opLeftJoin: OpLeftJoin): Unit =
        stack.push(Frame(cs => {
          cs(0)._1.unionWith((l, r) => l)(cs(1)._1.map((s, g) => (s, false))) -> s"LeftJoin(${opLeftJoin.getExprs})(${cs.mkString(", ")})"
        }, collection.mutable.ArrayBuffer.empty))

      override def visit(opFilter: OpFilter): Unit =
        stack.push(Frame(cs => {
          assert(cs.size == 1)
          cs.head._1 -> s"Filter(${opFilter.getExprs})(${cs.mkString(", ")})"
        }, collection.mutable.ArrayBuffer.empty))
    }
    val on_op = new OpVisitorBase {
    }
    val after_op = new OpVisitorByType {
      def shift(): Unit =
        val Frame(f, args) = stack.pop()
        val v = f(args)
        stack.top.args.addOne(v)

      override def visitN(op: OpN): Unit = shift()

      override def visit2(op: Op2): Unit = shift()

      override def visit1(op: Op1): Unit = shift()

      override def visit0(op: Op0): Unit = shift()

      override def visitFilter(op: OpFilter): Unit = shift()

      override def visitLeftJoin(op: OpLeftJoin): Unit = shift()
    }
    val walker = new WalkerVisitor(on_op, ExprVisitorBase(), before_op, after_op)
    aq.visit(walker)
    val Frame(f, args) = stack.pop()
    println(f(args))

/*    (Map(title -> false, price -> true), Project(? book, ? price, ? title)(
      (Map(title -> false, price -> true, book -> true), Filter([(< ? price
    15
    )] ) (
      (Map(title -> false, price -> true, book -> true), Join()(
        (Map(title -> false, price -> true, book -> false), LeftJoin(null)(
          (Map(book -> true, price -> true), LoopOver((? book ns: price ? price))()),
          (Map(book -> true, title -> true), LoopOver((? book ns: title ? title))()))),
        (Map(book -> true), Union()(
          (Map(book -> true), LoopOver((? book ns: author ns: Shakespeare))()),
          (Map(book -> true), LoopOver((? book ns: author ns: Marlowe))()))))
    ) ) ) ) )*/

    // ($output $o)
    // $o = (superpose ((book 394803), (title "The Night of Seven"), (author ns:Marlowe)))


    // good(book) \b:r OUTPUT(Singleton(book x b) \/ r) where
    //   good = book x content(book) \b:r => demand r(price) > 15 of b x r where
    //     content = book x info(book) \b:r => b x (r \/ relevant(book)(b) where
    //       info = book x prices(book) \b:r => b x (r \/ titles(book)(b)) where
    //         prices = book x (spo \b:r => b x price x r(ns:price))
    //         titles = book x (spo \b:r => b x title x r(ns:title))
    //       relevant = book x (ops(ns:Shakespeare)(ns:author)) \/ ops(ns:Marlowe)(ns:author))

    //   spo <| ((ops(ns:Shakespeare)(ns:author) \/ ops(ns:Marlowe)(ns:author)) x {ns:price x range(15, INT:MAX, 1), ns:title}) \b:r => OUTPUT({book x b, title x r(ns:title), price x r(ns:price)})
  }
end SPARQL

class Imperative extends FunSuite:
  import Space.*

  val aunt_query_routine = routine("aunts", Vector(), Vector("family", "people"),
    "Aunt" x S"people".iter("person", "_",
      P"person" x ((DropHead(S"family"("parent") <| DropHead(S"family"("child") <| S"family"("child" x P"person"))) \ S"family"("child" x P"person")) /\ S"family"("female")))
  )

  test("aunt query pretty") {
//    println(aunt_query_routine.show)
  }

  test("aunt query transpiled") {
//    println(transpile(aunt_query_routine).show)
  }
end Imperative

class Routines extends FunSuite:
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
//
//  test("eval factorial") {
//    function("fact", Vector("n"),
//      F"mul"(P"n", F"fact"(Vector(F"decr"(P"n")), Vector())
//    )
//  }
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
