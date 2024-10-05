package morkl

import scala.io.AnsiColor.*
import scala.util.Random
import java.util.Base64


enum PathItem:
  case Symbol(n: String)
  case Variable(n: String)
  case Arity(k: Int)

  def show: String = this match
    case PathItem.Symbol(n) => n
    case PathItem.Variable(n) => s"$$$n"
    case PathItem.Arity(k) => s"[$k]"

case class SymbolConflict(l: String, r: String) extends Exception(s"Symbol conflict $l $r")

enum Path:
  case Deref(pr: String)
  case Constant(pi: PathValue)
  case Concat(l: Path, r: Path)

  def show: String = this match
    case Path.Deref(pr) => s"$$\"$pr\""
    case Path.Constant(pi) => s"\"${pi.show}\""
    case Path.Concat(l, r) => s"${l.show} x ${r.show}"

case class PathValue(items: List[PathItem]):
  def show: String = items.map(_.show).mkString(".")

  def prefixes: Seq[PathValue] =
    // e.g. Test.Foo.Bar.2 |-> Vector(Test, Test.Foo, Test.Foo.Bar, Test.Foo.Bar.2)
    items.indices.map(i => PathValue(items.slice(0, i + 1)))

  def postfixes: Seq[PathValue] =
    // e.g. Test.Foo.Bar.2 |-> Vector(Test.Foo.Bar.2, Foo.Bar.2, Bar.2, 2)
    items.indices.map(i => PathValue(items.slice(i, items.length)))


class PathContext:
  def resolve(pr: String): PathValue = throw RuntimeException(s"$pr path ref not resolved")
  def grown(pv: Map[String, PathValue]): PathContext = throw RuntimeException(s"growing path context not implemented")

case class PathContextMap(m: Map[String, PathValue]) extends PathContext:
  override def resolve(pr: String): PathValue =
    try
      m(pr)
    catch
      case e: java.util.NoSuchElementException =>
        println(s"$pr not in $m")
        throw e
  override def grown(pv: Map[String, PathValue]): PathContext =
    val n = collection.mutable.Map.from(m)
    pv.foreachEntry((k, v) =>
      n.updateWith(k)(mov =>
        mov.foreach(ov => println(f"at $k, $ov was already present when trying to insert $v"))
        Some(v)
      )
    )
    PathContextMap(n.toMap)

object PathContext:
  val emptyMap: PathContextMap = PathContextMap(Map())

  def mixed(seed: Long = 0): PathContext = new PathContext:
    private val rng = Random(seed)
    override def resolve(pr: String): PathValue = PathValue(PathItem.Symbol(pr + "_" + Base64.getEncoder.encodeToString(rng.nextBytes(4)).take(4))::Nil)

def make_transform(pattern: PathValue, template: PathValue): PathValue => Option[PathValue] = // not using bidirectional matching or unification yet
  val pattern_parse: PathValue => Option[Seq[PathItem]] = pv => try Some((pv.items lazyZip pattern.items).collect{
    case (PathItem.Symbol(lhs), PathItem.Symbol(rhs)) if lhs != rhs => throw SymbolConflict(lhs, rhs)
    case (PathItem.Variable(_), rhs) => rhs
    case (lhs, PathItem.Variable(_)) => lhs
  }.toSeq) catch case e: SymbolConflict => None
  val template_format: Seq[PathItem] => PathValue = pis => {
    val pis_it = pis.iterator
    PathValue(template.items.map{ case PathItem.Variable(_) => pis_it.next(); case x => x })
  }
  val args_mapping: Seq[PathItem] => Seq[PathItem] = {
    val pl = pattern.items.collect{ case PathItem.Variable(s) => s }
    val tl = template.items.collect{ case PathItem.Variable(s) => s }
    val oc = tl.map(pv => pl.zipWithIndex.collectFirst{ case (`pv`, i) => i }.get)
    s => oc.map(s.apply)
  }
  pattern_parse(_).map(args_mapping andThen template_format)

def extract(pattern: Path, data: PathValue): Option[Map[String, PathValue]] =
  val it = data.items.iterator
  val mb = Map.newBuilder[String, PathValue]

  def rec(p: Path): Unit = p match
    case Path.Deref(v) => it.nextOption().foreach(o => mb.addOne(v -> PathValue(List(o))))
    case Path.Constant(pi) => (pi.items zip it).foreach {
      case (PathItem.Symbol(lhs), PathItem.Symbol(rhs)) if lhs != rhs => throw SymbolConflict(lhs, rhs)
      case (PathItem.Arity(lhs), PathItem.Arity(rhs)) if lhs != rhs => throw SymbolConflict(lhs.toString, rhs.toString)
      case (PathItem.Variable(v), rhs) => ()
    }
    case Path.Concat(l, r) => rec(l); rec(r)

  try
    rec(pattern)
    Some(mb.result())
  catch
    case e: SymbolConflict => None

def eval(p: Path)(using pc: PathContext): PathValue =
  def rec(x: Path): List[PathItem] = x match
    case Path.Deref(pr) => pc.resolve(pr).items
    case Path.Constant(pi) => pi.items
    case Path.Concat(l, r) => rec(l) ++ rec(r)
  PathValue(rec(p))

class SpaceContext:
  def resolve(pv: PathValue): SpaceValue = throw RuntimeException(s"$pv space ref not resolved")

object SpaceContext:
  val identity: SpaceContext = new SpaceContext:
    override def resolve(pr: PathValue): SpaceValue = SpaceValue(Set(pr))
  def constant(m: Map[String, SpaceValue]): SpaceContext = new SpaceContext:
    val pm = m.map((k, v) => Syntax.parse(k) -> v)
    override def resolve(pr: PathValue): SpaceValue = pm(pr)
  def space(s: SpaceValue): SpaceContext = new SpaceContext:
    override def resolve(pr: PathValue): SpaceValue = // subspace
      SpaceValue(s.paths.collect { case e if e.items.startsWith(pr.items) => PathValue(e.items.drop(pr.items.length)) })

enum Space:
  case Empty
  case Read(postfix: PathValue)
  case Singleton(p: Path)
  case Literal(p: SpaceValue)
  case Union(x: Space, y: Space)
  case Intersection(x: Space, y: Space)
  case Subtraction(x: Space, y: Space)
  case Restriction(x: Space, y: Space)
  case Composition(x: Space, y: Space)
  case Transformation(src: Space, pattern: Path, template: Path)
  case Iteration(src: Space, pattern: Path, templates: Space)
  case Wrap(src: Space, p: Path)
  case Unwrap(src: Space, p: Path)
  case DropHead(src: Space)
  case LeftResidual(x: Space, y: Space) // likely not to be included
  case RightResidual(y: Space, x: Space) // likely not to be included

  def show(using indent: Int = 0): String = this match
    case Space.Empty => "Empty"
    case Space.Read(postfix) => s"R\"${postfix.show}\""
    case Space.Singleton(p) => s"Singleton(${p.show})"
    case Space.Literal(p) => s"Literal(${p.show})"
    case Space.Union(x, y) => s"(${x.show} \\/ ${y.show})"
    case Space.Intersection(x, y) => s"(${x.show} /\\ ${y.show})"
    case Space.Subtraction(x, y) => s"(${x.show} \\ ${y.show})"
    case Space.Restriction(x, y) => s"(${x.show} <| ${y.show})"
    case Space.Composition(x, y) => s"(${x.show} x ${y.show})"
    case Space.Transformation(src, pattern, template) => s"${src.show}.transform(${pattern.show}, ${template.show})"
    case Space.Iteration(src, pattern, templates) => s"${src.show}.iter(${pattern.show}, \n${" ".repeat(indent + 1)}${templates.show(using indent + 1)}\n)"
    case Space.Wrap(src, p) => s"(${p.show} x ${src.show})"
    case Space.Unwrap(src, p) => s"${src.show}(${p.show})"
    case Space.DropHead(src) => s"DropHead(${src.show})"
    case Space.LeftResidual(x, y) => s"(${y.show} /: ${x.show})"
    case Space.RightResidual(y, x) => s"(${y.show} :\\ ${x.show})"


case class SpaceValue(paths: Set[PathValue]):
  def show: String = paths.map(x => '"' + x.show + '"').toSeq.sorted.mkString("SpaceValue(", ", ", ")")
  def pretty: String = paths.map(_.show).toSeq.sorted.mkString("{", ";", "}")
  def prettyLines: String = paths.map(_.show).toSeq.sorted.mkString("", "\n", "")


def eval(s: Space)(using sc: SpaceContext, pc: PathContext): SpaceValue =
  def rec(x: Space): Set[PathValue] = x match
    case Space.Empty => Set()
    case Space.Read(p) => sc.resolve(p).paths
    case Space.Singleton(p) => Set(eval(p))
    case Space.Literal(SpaceValue(ps)) => ps
    case Space.Union(x, y) => rec(x) union rec(y)
    case Space.Intersection(x, y) => rec(x) intersect rec(y)
    case Space.Subtraction(x, y) => rec(x) removedAll rec(y)
    case Space.Restriction(x_e, prefixes_e) => val prefixes = rec(prefixes_e); rec(x_e).filter(x => prefixes.exists(p => x.items.startsWith(p.items)))
    case Space.Composition(x, y) => val ys = rec(y); for e1 <- rec(x); e2 <- ys yield PathValue(e1.items ++ e2.items)
    case Space.Wrap(src_e, p_e) => val p = eval(p_e); rec(src_e).map( sp => PathValue(p.items ++ sp.items))
    case Space.Unwrap(src_e, p_e) => val p = eval(p_e); rec(src_e).collect { case e if e.items.startsWith(p.items) => PathValue(e.items.drop(p.items.length)) }
    case Space.DropHead(src_e) => rec(src_e).collect { case PathValue(_::r) => PathValue(r) }
    case Space.Transformation(src_e, pattern, template) => val transformer = make_transform(eval(pattern), eval(template)).unlift; eval(src_e).paths.collect(transformer)
    case Space.Iteration(src_e, pattern, templates) => for path <- eval(src_e).paths; m <- extract(pattern, path).toSet; p <- eval(templates)(using sc, pc.grown(m)).paths yield p
    case Space.LeftResidual(x_e, y_e) => val ys = eval(y_e); val xs = eval(x_e); for e <- xs.paths; r <- e.prefixes; if ys.paths.forall(g => xs.paths.contains(PathValue(r.items ++ g.items))) yield r
    case Space.RightResidual(y_e, x_e) => val ys = eval(y_e); val xs = eval(x_e); for e <- xs.paths; r <- e.postfixes; if ys.paths.forall(g => xs.paths.contains(PathValue(g.items ++ r.items))) yield r
  SpaceValue(rec(s))

object Syntax:
  import PathItem.*
  import Path.*
  given parse: Conversion[String, PathValue] = s => PathValue(s.split('.').map(name => if name.startsWith("$") then PathItem.Variable(name.tail) else PathItem.Symbol(name)).toList)
  given constant: Conversion[String, Path] = (parse andThen Path.Constant.apply)(_)
  given parse2: Conversion[(String, String), (PathValue, PathValue)] = (x, y) => (parse(x), parse(y))
  given constant2: Conversion[(String, String), (Path, Path)] = (x, y) => (Path.Constant(parse(x)), Path.Constant(parse(y)))
  extension (x: Path)
    infix def x (y: Path) : Path = Concat(x, y)
    infix def x (y: Space) : Space = Space.Wrap(y, x)
  extension (x: Space)
    // assignment of operators WIP
    def \/(y: Space) = Space.Union(x, y)
    def /\(y: Space) = Space.Intersection(x, y)
    def \(y: Space) = Space.Subtraction(x, y)
    def <|(y: Space) = Space.Restriction(x, y)
    infix def x(y: Space) = Space.Composition(x, y)
    def apply(p: Path) = Space.Unwrap(x, p)
    infix def transform(lhs: Path, rhs: Path): Space = Space.Transformation(x, lhs, rhs)
    infix def iter(lhs: Path, rhs: Space): Space = Space.Iteration(x, lhs, rhs)
    def :\(y: Space) = Space.RightResidual(x, y)
    def /:(y: Space) = Space.LeftResidual(x, y)

  extension (st: SpaceValue.type)
    def apply(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)

  extension (inline sc: StringContext)
    inline def R(inline args: Any*): Space =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Space.Read(parse(k))

  extension (inline sc: StringContext)
    inline def $(inline args: Any*): Path =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Path.Deref(k)

