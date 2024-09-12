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
  case Transformation(src: Space, pattern: Path, templates: Path)
//  case TransformationS(src: Space, pattern: Path, templates: Space)
  case Subspace(src: Space, p: Path)
  case DropUnion(src: Space)
  case DropIntersection(src: Space)
  case LeftResidual(x: Space, y: Space) // likely not to be included
  case RightResidual(y: Space, x: Space) // likely not to be included
  case Sharing(y: Space, x: Space) // likely not to be included
  case GCD(y: Space, x: Space) // likely not to be included
  case Subsumption(x: Space) // likely not to be included
  case Instantiation(x: Space) // likely not to be included

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

  extension (x: Path)
    infix def x (y: Space) = Composition(Singleton(x), y)

  extension (x: Space)
    // assignment of operators WIP
    def \/ (y: Space) = Union(x, y)
    def /\ (y: Space) = Intersection(x, y)
    def \ (y: Space) = Subtraction(x, y)
    def <| (y: Space) = Restriction(x, y)
    infix def x (y: Space) = Composition(x, y)
    def apply(p: Path) = Subspace(x, p)
    def tail = DropUnion(x)
    def common = DropIntersection(x)
    infix def transform (lhs_rhs: (Path, Path)): Space = Transformation(x, lhs_rhs._1, lhs_rhs._2)
    def </(y: Space) = LeftResidual(x, y)
    def />(y: Space) = RightResidual(x, y)
    def <>(y: Space) = GCD(x, y)
//    infix def transformS (lhs_rhs: (Path, Space)): Space = TransformationS(x, lhs_rhs._1, lhs_rhs._2)

  object ^ :
    def apply(x: Space) = Subsumption(x)
  object v :
    def apply(x: Space) = Instantiation(x)


  extension (st: Space.type)
    def apply(ps: Path*): Space = ps.map(Singleton.apply).reduce(Union.apply)

  given parse: Conversion[String, Path] = _.split('.').map(name => if name.startsWith("$") then Variable(name.tail) else Symbol(name)).reduce(Concat.apply)
  given lift2[A, B](using c: Conversion[A, B]): Conversion[(A, A), (B, B)] = (l, r) => (c(l), c(r))

def factor(xs: Set[String]): Space =
  import Syntax.parse
  def rec(xs: Set[String]): Space =
    val l = xs.groupMapReduce(_.takeWhile(_ != '.'))(s => Set(s.dropWhile(_ != '.').tail))(_ union _)
    l.map((pre, space) => if space == Set("") then Space.Singleton(pre) else Space.Composition(Space.Singleton(pre), rec(space)))
      .reduce(Space.Union)
  rec(xs)

def prefixes(s: String): Seq[String] =
  // e.g. Test.Foo.Bar.2 |-> Vector(Test, Test.Foo, Test.Foo.Bar, Test.Foo.Bar.2)
  val cs = s.split('.')
  cs.indices.map(i => cs.slice(0, i + 1).mkString("", ".", ""))

def postfixes(s: String): Seq[String] =
  // e.g. Test.Foo.Bar.2 |-> Vector(Test.Foo.Bar.2, Foo.Bar.2, Bar.2, 2)
  val cs = s.split('.')
  cs.indices.map(cs.slice(_, cs.length).mkString("", ".", ""))

def shared(x: String, y: String): Option[String] =
  if x.takeWhile(_ != '.') != y.takeWhile(_ != '.') then None
  else Some(x.concat(".").zip(y.concat(".")).takeWhile((l, r) => l == r).map(_._1).reverse.dropWhile(_ != '.').tail.reverse.mkString)

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
//  case Space.TransformationS(src, pattern, templates) => eval(src).flatMap(s => templates.flatMap(t => make_transform(pattern, Syntax.parse(t))(s)))
  case Space.Subspace(src, p) => val ep = eval(p); eval(src).collect{ case e if e.startsWith(ep) && e != ep => e.stripPrefix(ep + ".") }
  case Space.DropUnion(src) => eval(src).collect{ case e if e.contains('.') => e.dropWhile(_ != '.').stripPrefix(".") }
  case Space.DropIntersection(src) => eval(src).filter(_.contains('.')).groupMapReduce(_.takeWhile(_ != '.'))(x => Set(x.dropWhile(_ != '.').stripPrefix(".")))(_ union _).values.reduce(_ intersect _)
  case Space.LeftResidual(x, y) => val ys = eval(y); val xs = eval(x); for e <- xs; r <- prefixes(e); if ys.forall(g => xs.contains(r + "." + g)) yield r
  case Space.RightResidual(y, x) => val ys = eval(y); val xs = eval(x); for e <- xs; r <- postfixes(e); if ys.forall(g => xs.contains(g + "." + r)) yield r
  case Space.Sharing(y, x) => val ys = eval(y); val xs = eval(x); for e <- xs; p <- ys; s <- shared(e, p) yield s
  case Space.GCD(y, x) =>
    val ys = eval(y); val xs = eval(x);
    val all = for e <- xs; p <- ys; s <- shared(e, p) yield s
    all.filter(e => all.excl(e).exists(e.startsWith))
  case Space.Subsumption(x) => val xs = eval(x); xs.filter(e => !xs.excl(e).exists(e.startsWith))
  case Space.Instantiation(x) => val xs = eval(x); xs.filter(e => xs.excl(e).exists(e.startsWith))

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

    def dropunion() =
      val lhs = DropUnion(Composition(Singleton("Foo"), Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C")))))
      val rhs = Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C")))
      assert(eval(lhs) == eval(rhs))

    def dropintersection() =
      val lhs = DropIntersection(Union(Union(
        Composition(Singleton("Foo"), Space("A", "2", "C", "4", "5")),
        Composition(Singleton("Bar"), Space("1", "2", "C", "4"))),
        Composition(Singleton("Baz"), Space("A", "2", "3", "4"))))
      val rhs = Space("2", "4")
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

    def gcd() =
      assert(shared("Test.Foo.Bar", "Test.Foo") == Some("Test.Foo"))
      assert(shared("Test.Foo.Bar", "Test.Foo.Baz") == Some("Test.Foo"))
      val x = Space("Test.Cux", "Test.Foo")
      val y = Space("Test.Foo.Bar", "Test.Foo.Baz")
      val lhs = GCD(x, y)
      val rhs = Space("Test.Foo")
      assert(eval(lhs) == eval(rhs))

    def sharing() =
      val x = Space("Test.Cux", "Test.Foo")
      val y = Space("Test.Foo.Bar", "Test.Foo.Baz")
      val lhs = Instantiation(Sharing(x, y))
      val rhs = Space("Test.Foo")
      assert(eval(lhs) == eval(rhs))

    def subsumption() =
      val lhs = Subsumption(Space("Test.Foo.Bar", "Test.Foo.Baz", "Test.Foo", "Test.Cux"))
      val rhs = Space("Test.Foo", "Test.Cux")
      assert(eval(lhs) == eval(rhs))

    def instantiation() =
      val lhs = Instantiation(Space("Test.Foo.Bar", "Test.Foo.Baz", "Test.Foo", "Test.Cux"))
      val rhs = Space("Test.Foo.Bar", "Test.Foo.Baz")
      assert(eval(lhs) == eval(rhs))

    def factor_set() =
      val rhs = Composition(Singleton("Foo"), Union(
        Composition(Singleton("Bar"), Space("1", "2", "3")),
        Composition(Singleton("Baz"), Space("A", "B", "C"))))
      assert(factor(eval(rhs)) == rhs)

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
    val ifamily = Space(
      "parent.Tom.Bob",
      "parent.Pam.Bob",
      "parent.Tom.Liz",
      "parent.Bob.Ann",
      "parent.Bob.Pat",
      "parent.Pat.Jim",
      "female.Pam", "female.Liz", "female.Pat", "female.Ann",
      "male.Tom", "male.Bob", "male.Jim",
    )

    val family = Space(
      "parent.Tom.Bob", "child.Bob.Tom",
      "parent.Pam.Bob", "child.Bob.Pam",
      "parent.Tom.Liz", "child.Liz.Tom",
      "parent.Bob.Ann", "child.Ann.Bob",
      "parent.Bob.Pat", "child.Pat.Bob",
      "parent.Pat.Jim", "child.Jim.Pat",
      "female.Pam", "female.Liz", "female.Pat", "female.Ann",
      "male.Tom", "male.Bob", "male.Jim",
      "person.Tom", "person.Bob", "person.Jim", "person.Pam", "person.Liz", "person.Pat", "person.Ann"
    )

    val people = Space("Tom", "Bob", "Jim", "Pam", "Liz", "Pat", "Ann")
//    val people = Space("Bob", "Tom")

    def add_index() =
      val rhs = ifamily \/ (ifamily transform "parent.$x.$y" -> "child.$y.$x")
                        \/ ("person" x ifamily("female"))
                        \/ ("person" x ifamily("male"))
      assert(eval(family) == eval(rhs))

    def parent_query() =
      val lhs = "Parent" x (family("child") <| people)
      val rhs = Space("Parent.Bob.Tom", "Parent.Pat.Bob", "Parent.Bob.Pam", "Parent.Liz.Tom", "Parent.Ann.Bob", "Parent.Jim.Pat")
      assert(eval(lhs) == eval(rhs))

    def mother_query() =
      for person <- eval(people) do
        val r = (family(Concat("child", person)) /\ family("female"))
        println(s"$person : ${eval(r)}")

    def sister_query() =
      for person <- eval(people) do
        val r = ((family("parent") <| family(Concat("child", person))).tail /\ family("female")) \ Singleton(person)
        println(s"$person : ${eval(r)}")

    def aunt_query() =
      for person <- eval(people) do
        val parents = family(Concat("child", person))
        val grandparents = (family("child") <| parents).tail
        val parent_siblings = (family("parent") <| grandparents).tail \ parents
        val aunts = parent_siblings /\ family("female")
        println(s"$person : ${eval(aunts)}")

    def predecessors() =
      for person <- eval(people) do
        var pred = family(Concat("child", person))
        var oldest = pred
        while eval(oldest).nonEmpty do
          pred = pred \/ oldest
          oldest = (family("child") <| oldest).tail
        println(s"$person : ${eval(pred)}")

@main def example =
  Examples.Basic.composition()
  Examples.Basic.union()
  Examples.Basic.intersection()
  Examples.Basic.subtraction()
  Examples.Basic.restriction()
  Examples.Basic.transformation()
  Examples.Basic.subspace()
  Examples.Basic.dropunion()
  Examples.Basic.dropintersection()
  Examples.Basic.left_residual()
  Examples.Basic.right_residual()
  Examples.Basic.factor_set()
  Examples.Basic.gcd()
  Examples.Basic.sharing()
  Examples.Basic.subsumption()
  Examples.Basic.instantiation()
//  Examples.AuntQuery.add_index()
//  Examples.AuntQuery.parent_query()
  Examples.AuntQuery.mother_query()
  Examples.AuntQuery.sister_query()
//  Examples.AuntQuery.aunt_query()
//  Examples.AuntQuery.predecessors()
