package morkl

enum Path:
  case Symbol(n: String)
  case Variable(n: String)
  case Concat(l: Path, r: Path)
  def foldMap[A](fs: String => A, fv: String => A, fc: (A, A) => A): A = this match
    case Path.Symbol(n) => fs(n)
    case Path.Variable(n) => fv(n)
    case Path.Concat(l, r) => fc(l.foldMap(fs, fv, fc), r.foldMap(fs, fv, fc))

enum Space:
  case Empty
  case Singleton(p: Path)
  case Union(x: Space, y: Space)
  case Intersection(x: Space, y: Space)
  case Subtraction(x: Space, y: Space)
  case Restriction(x: Space, y: Space)
  case Composition(x: Space, y: Space)
  case Transformation(src: Space, pattern: Path, template: Path)
  case Subspace(src: Space, p: Path)
  case DropHead(src: Space)
  case LeftResidual(x: Space, y: Space) // likely not to be included
  case RightResidual(y: Space, x: Space) // likely not to be included

enum Expr:
  case Read(postfix: Path)
  case Write(postfix: Path, result: Space)

case class Subroutine(read: Path, write: Space, body: Expr)

case class Program(s: List[Subroutine])

object Syntax:
  export Path.*
  export Expr.*
  export Space.*
  import scala.Conversion
  import scala.language.implicitConversions

  extension (x: Space)
    // assignment of operators WIP
    def \/ (y: Space) = Union(x, y)
    def /\ (y: Space) = Intersection(x, y)
    def \ (y: Space) = Subtraction(x, y)
    def <| (y: Space) = Restriction(x, y)
    infix def x (y: Space) = Composition(x, y)
    def apply(p: Path) = Subspace(x, p)
    def tail = DropHead(x)
    infix def transform (lhs_rhs: (Path, Path)): Space = Transformation(x, lhs_rhs._1, lhs_rhs._2)

  extension (st: Space.type)
    def apply(ps: Path*): Space = ps.map(Singleton.apply).reduce(Union.apply)

  given parse: Conversion[String, Path] = _.split('.').map(name => if name.startsWith("$") then Variable(name.tail) else Symbol(name)).reduce(Concat.apply)

def prefixes(s: String): Seq[String] =
  // e.g. Test.Foo.Bar.2 |-> Vector(Test, Test.Foo, Test.Foo.Bar, Test.Foo.Bar.2)
  val cs = s.split('.')
  cs.indices.map(i => cs.slice(0, i + 1).mkString("", ".", ""))

def postfixes(s: String): Seq[String] =
  // e.g. Test.Foo.Bar.2 |-> Vector(Test.Foo.Bar.2, Foo.Bar.2, Bar.2, 2)
  val cs = s.split('.')
  cs.indices.map(cs.slice(_, cs.length).mkString("", ".", ""))

def make_transform(pattern: Path, template: Path): String => Option[String] = // not using bidirectional matching or unification yet
  val pattern_parse: String => Option[Seq[String]] = pattern.foldMap(identity, _ => "(\\w+)", _ + "[.]" + _).r.unapplySeq
  val template_format: Seq[String] => String = template.foldMap(identity, _ => "%s", _ + "." + _).format
  val args_mapping: Seq[String] => Seq[String] = {
    val pl = pattern.foldMap(_ => Nil, _::Nil, _ ++ _)
    val tl = template.foldMap(_ => Nil, _::Nil, _ ++ _)
    val oc = tl.map(pv => pl.zipWithIndex.collectFirst{ case (`pv`, i) => i }.get)
    s => oc.map(s.apply)
  }
  pattern_parse(_).map(args_mapping andThen template_format)

def eval(e: Path): String = e match
  case Path.Symbol(n) => n
  case Path.Variable(n) => "$" concat n
  case Path.Concat(l, r) => eval(l) concat "." concat eval(r)

def eval(e: Space): Set[String] = e match
  case Space.Empty => Set()
  case Space.Singleton(p) => Set(eval(p))
  case Space.Union(x, y) => eval(x) union eval(y)
  case Space.Intersection(x, y) => eval(x) intersect eval(y)
  case Space.Subtraction(x, y) => eval(x) removedAll eval(y)
  case Space.Restriction(x, y) => val ys = eval(y); eval(x).filter(e => ys.exists(e.startsWith))
  case Space.Composition(x, y) => val ys = eval(y); for e1 <- eval(x); e2 <- ys yield e1 + "." + e2
  case Space.Transformation(src, pattern, template) => eval(src).collect(make_transform(pattern, template).unlift)
  case Space.Subspace(src, p) => val ep = eval(p); eval(src).collect{ case e if e.startsWith(ep) && e != ep => e.stripPrefix(ep + ".") }
  case Space.DropHead(src) => eval(src).collect{ case e if e.contains('.') => e.dropWhile(_ != '.').stripPrefix(".") }
  case Space.LeftResidual(x, y) => val ys = eval(y); val xs = eval(x); for e <- xs; r <- prefixes(e); if ys.forall(g => xs.contains(r + "." + g)) yield r
  case Space.RightResidual(y, x) => val ys = eval(y); val xs = eval(x); for e <- xs; r <- postfixes(e); if ys.forall(g => xs.contains(g + "." + r)) yield r

object Examples:
  import Syntax.{*, given}

  object Basic:
    def composition() =
      val prefixed = Composition(Singleton("Foo"), Space("bar", "baz", "cux"))
      val separated = Space("Foo.bar", "Foo.baz", "Foo.cux")
      assert(eval(prefixed) == eval(separated))
      val xyz_ab = Composition(Space("x", "y", "z"), Space("a", "b"))
      val composed = Space("x.a", "y.a", "z.a", "x.b", "y.b", "z.b")
      assert(eval(xyz_ab) == eval(composed))
      val structure = Composition(Space("Foo.Bar", "Foo.Baz"), Space("A.1", "A.2"))
      val composed_structure = Space("Foo.Bar.A.1", "Foo.Bar.A.2", "Foo.Baz.A.1", "Foo.Baz.A.2")
      assert(eval(structure) == eval(composed_structure))

    def union() =
      val separate = Union(Union(Singleton("a"), Singleton("b")), Singleton("c"))
      val unioned = Space("a", "b", "c")
      assert(eval(separate) == eval(unioned))

    def intersection() =
      val abc_ace = Intersection(Space("a", "b", "c"), Space("a", "c", "e"))
      val ac = Space("a", "c")
      assert(eval(abc_ace) == eval(ac))

    def subtraction() =
      val abc_ce = Subtraction(Space("a", "b", "c"), Space("c", "e"))
      val ab = Space("a", "b")
      assert(eval(abc_ce) == eval(ab))

    def restriction() =
      val lhs = Restriction(Composition(Singleton("Foo"), Union(Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C"))),
        Composition(Singleton("Cux"), Space("Red", "Blue")))), Space("Foo.Bar", "Foo.Baz"))
      val rhs = Composition(Singleton("Foo"), Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C"))))
      assert(eval(lhs) == eval(rhs))

    def transformation() =
      val lhs = Transformation(Composition(Singleton("Foo"), Union(Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C"))),
        Composition(Singleton("Cux"), Space("Red", "Blue")))), "$_.Cux.$c", "Result.Color.$c")
      val rhs = Space("Result.Color.Red", "Result.Color.Blue")
      assert(eval(lhs) == eval(rhs))

    def subspace() =
      val lhs = Subspace(Composition(Singleton("Foo"), Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C")))), "Foo.Baz")
      val rhs = Space("A", "B", "C")
      assert(eval(lhs) == eval(rhs))

    def drophead() =
      val lhs = DropHead(Composition(Singleton("Foo"), Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C")))))
      val rhs = Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C")))
      assert(eval(lhs) == eval(rhs))

    def left_residual() =
      // all prefixes we can add to y such prefix.y <= x
      val x = Composition(Singleton("Test.Foo"), Union(Union(
        Composition(Singleton("Bar"), Space("1", "2", "3", "4", "5", "6")),
        Composition(Singleton("Baz"), Space("1", "2", "3", "A", "B", "C"))),
        Composition(Singleton("Cux"), Space("Red", "Blue"))))
      val y = Space("1", "2", "3")
      val lhs = LeftResidual(x, y)
      val rhs = Space("Test.Foo.Bar", "Test.Foo.Baz")
      assert(eval(lhs) == eval(rhs))

    def right_residual() =
      // all postfixes we can add to y such y.postfix <= x
      val x = Composition(Singleton("Test.Foo"), Union(Union(
        Composition(Singleton("Bar"), Space("1", "2", "3", "4", "5", "6")),
        Composition(Singleton("Baz"), Space("1", "2", "3", "A", "B", "C"))),
        Composition(Singleton("Cux"), Space("Red", "Blue"))))
      val y = Space("Test.Foo.Bar", "Test.Foo.Baz")
      val lhs = RightResidual(y, x)
      val rhs = Space("1", "2", "3")
      assert(eval(lhs) == eval(rhs))

  object AuntQuery:
    ???
//  val add_index = 2($"family") ! { 3("parent", $"x", $"y") -> Singleton(3("child", $"y", $"x")) }

//  val parent_query = 2("family", 2("parents", $"people")) ! {
//    $"people" transform $"person" -> Subspace(2("family", 3("child")), $"person")
//  }
//
//  val mother_query = 2("family", 2("mothers", $"people")) ! {
//    $"people" transform $"person" -> Intersection(Subspace(2("family", 3("child")), $"person"), 2("family", 2("female")))
//  }
//
//  val sister_query = 2("family", 2("sisters", $"people")) ! {
//    $"people" transform $"person" -> {
//      Concat($"_", $"siblings") ! Intersection(2("family", 3("child")), Subspace(2("family", 3("parent")), $"person"))
//      Intersection($"siblings", 2("family", 2("female")))
//    }
//  }
//
//  val aunt_query = 2("family", 2("aunts", $"people")) ! {
//    $"people" transform $"person" -> {
//      $"person_parents" ! Subspace(2("family", 3("child")), $"person")
//      Concat($"_1", $"person_grandparents") ! Restriction(2("family", 3("child")), $"person_parents")
//      Concat($"_2", $"person_parent_siblings_incl") ! Restriction(2("family", 3("parent")), $"person_grandparents")
//      $"person_parent_siblings" ! Subtraction($"person_parent_siblings_incl", $"person_parents")
//      Intersection($"person_parent_siblings", 2("family", 2("female")))
//    }
//  }
//
//  val predecessor: Path ?=> Expr = ⚓ + 2("family", 2("predecessors")) ! {
//    $"people" transform $"person" -> {
//      $"pred" ! Subspace(2("family", 3("child")), $"person")
//      $"oldest" ! $"pred"
//      while $"oldest".nonEmpty do // TODO write with recursion
//        $"pred" ! Union($"pred", $"oldest")
//        Concat($"_", $"oldest") ! Restriction(2("family", 3("child")), $"oldest")
//      Composition(Singleton($"person"), $"pred")
//    }
//  }


@main def example =
  Examples.Basic.composition()
  Examples.Basic.union()
  Examples.Basic.intersection()
  Examples.Basic.subtraction()
  Examples.Basic.restriction()
  Examples.Basic.transformation()
  Examples.Basic.subspace()
  Examples.Basic.drophead()
  Examples.Basic.left_residual()
  Examples.Basic.right_residual()
