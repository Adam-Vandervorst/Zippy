package morkl

import scala.io.AnsiColor.*
import scala.util.Random
import scala.collection.mutable.ArrayBuffer
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

case class PathRef(s: String)

enum Path:
  case Deref(pr: PathRef)
  case Constant(pi: PathValue)
  case Concat(l: Path, r: Path)
  case GroundedPP(p: Path, f: PathValue => PathValue)
  case GroundedSP(p: Space, f: SpaceValue => PathValue)

  def show: String = this match
    case Path.Deref(pr) => s"P\"${pr.s}\""
    case Path.Constant(pi) => s"\"${pi.show}\""
    case Path.Concat(l, r) => s"${l.show} x ${r.show}"
    case Path.GroundedPP(p, f) => s"${f.hashCode()}PP(${p.show})"
    case Path.GroundedSP(s, f) => s"${f.hashCode()}SP(${s.show})"

  def pretty: String = this match
    case Path.Deref(pr) => pr.s
    case Path.Constant(pi) => pi.show
    case Path.Concat(l, r) => s"${l.pretty}.${r.pretty}"
    case Path.GroundedPP(p, f) => s"${f.hashCode()}PP(${p})"
    case Path.GroundedPP(s, f) => s"${f.hashCode()}SP(${s.show})"

case class PathValue(items: List[PathItem]):
  def show: String = items.map(_.show).mkString(".")

  def prefixes: Seq[PathValue] =
    // e.g. Test.Foo.Bar.2 |-> Vector(Test, Test.Foo, Test.Foo.Bar, Test.Foo.Bar.2)
    items.indices.map(i => PathValue(items.slice(0, i + 1)))

  def postfixes: Seq[PathValue] =
    // e.g. Test.Foo.Bar.2 |-> Vector(Test.Foo.Bar.2, Foo.Bar.2, Bar.2, 2)
    items.indices.map(i => PathValue(items.slice(i, items.length)))


class PathContext:
  def resolve(pr: PathRef): PathValue = throw RuntimeException(s"$pr path ref not resolved")
  def grown(pv: Map[PathRef, PathValue]): PathContext = throw RuntimeException(s"growing path context not implemented")

case class PathContextMap(m: Map[PathRef, PathValue]) extends PathContext:
  override def resolve(pr: PathRef): PathValue =
    try
      m(pr)
    catch
      case e: java.util.NoSuchElementException =>
        println(s"$pr not in $m")
        throw e
  override def grown(pv: Map[PathRef, PathValue]): PathContext =
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
    override def resolve(pr: PathRef): PathValue = PathValue(PathItem.Symbol(pr.s + "_" + Base64.getEncoder.encodeToString(rng.nextBytes(4)).take(4))::Nil)

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

/*def extract(pattern: Path, data: PathValue): Option[Map[String, PathValue]] =
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
    case e: SymbolConflict => None*/

class SpaceContext:
  def resolve(pv: SpaceMention): SpaceValue = throw RuntimeException(s"$pv space mention not resolved")
  def grown(pv: Map[SpaceMention, SpaceValue]): SpaceContext = throw RuntimeException(s"growing space context not implemented")


case class SpaceContextMap(m: Map[SpaceMention, SpaceValue]) extends SpaceContext:
  override def resolve(pr: SpaceMention): SpaceValue =
    try
      m(pr)
    catch
      case e: java.util.NoSuchElementException =>
        println(s"$pr not in $m")
        throw e

  override def grown(pv: Map[SpaceMention, SpaceValue]): SpaceContextMap =
    val n = collection.mutable.Map.from(m)
    pv.foreachEntry((k, v) =>
      n.updateWith(k)(mov =>
        mov.foreach(ov => println(f"at $k, $ov was already present when trying to insert $v"))
        Some(v)
      )
    )
    SpaceContextMap(n.toMap)


object SpaceContext:
//  val identity: SpaceContext = new SpaceContext:
//    override def resolve(pr: PathRef): SpaceValue = SpaceValue(Set(pr))
  def constant(m: Map[SpaceMention, SpaceValue]): SpaceContext = new SpaceContext:
    val pm = m
    override def resolve(pr: SpaceMention): SpaceValue = pm(pr)

case class SpaceMention(s: String)

enum Space:
  case Empty
  case Call(r: RoutinePtr, refs: Vector[Path], mentions: Vector[Space])
  case Mention(variable: SpaceMention)
  case Singleton(p: Path)
  case Literal(p: SpaceValue)
  case Union(x: Space, y: Space)
  case Intersection(x: Space, y: Space)
  case Subtraction(x: Space, y: Space)
  case Restriction(x: Space, y: Space)
  case Composition(x: Space, y: Space)
  case Transformation(src: Space, pattern: Path, template: Path)
  case Iteration(src: Space, symbol: PathRef, rest: SpaceMention, templates: Space)
  case Wrap(src: Space, p: Path)
  case Unwrap(src: Space, p: Path)
  case DropHead(src: Space)
  case LeftResidual(x: Space, y: Space) // likely not to be included
  case RightResidual(y: Space, x: Space) // likely not to be included
  case GroundedPS(p: Path, f: PathValue => SpaceValue)
  case GroundedSS(p: Space, f: SpaceValue => SpaceValue)

  def show(using indent: Int = 0): String = this match
    case Space.Empty => "Empty"
    case Space.Call(r, refs, mentions) => s"${r.s}(${refs.mkString(", ")}; ${mentions.mkString(", ")})"
    case Space.Mention(variable) => s"S\"${variable.s}\""
    case Space.Singleton(p) => s"Singleton(${p.show})"
    case Space.Literal(p) => s"Literal(${p.show})"
    case Space.Union(x, y) => s"(${x.show} \\/ ${y.show})"
    case Space.Intersection(x, y) => s"(${x.show} /\\ ${y.show})"
    case Space.Subtraction(x, y) => s"(${x.show} \\ ${y.show})"
    case Space.Restriction(x, y) => s"(${x.show} <| ${y.show})"
    case Space.Composition(x, y) => s"(${x.show} x ${y.show})"
    case Space.Transformation(src, pattern, template) => s"${src.show}.transform(${pattern.show}, ${template.show})"
    case Space.Iteration(src, symbol, rest, templates) => s"${src.show}.iter(\"${symbol.s}\", \"${rest.s}\", \n${" ".repeat(indent + 1)}${templates.show(using indent + 1)}\n)"
    case Space.Wrap(src, p) => s"(${p.show} x ${src.show})"
    case Space.Unwrap(src, p) => s"${src.show}(${p.show})"
    case Space.DropHead(src) => s"DropHead(${src.show})"
    case Space.LeftResidual(x, y) => s"(${y.show} /: ${x.show})"
    case Space.RightResidual(y, x) => s"(${y.show} :\\ ${x.show})"
    case Space.GroundedPS(p, f) => s"${f.hashCode()}PS(${p.show})"
    case Space.GroundedSS(s, f) => s"${f.hashCode()}SS(${s.show})"


case class SpaceValue(paths: Set[PathValue]):
  def show: String = paths.map(x => '"' + x.show + '"').toSeq.sorted.mkString("SpaceValue(", ", ", ")")
  def pretty: String = paths.map(_.show).toSeq.sorted.mkString("{", ";", "}")
  def prettyLines: String = paths.map(_.show).toSeq.sorted.mkString("", "\n", "")


case class RoutinePtr(s: String)
case class Routine(name: RoutinePtr, refs: Vector[PathRef], mentions: Vector[SpaceMention], body: Space):
  def show = s"routine(\"${name.s}\", Vector(${refs.map("\"" ++ _.s ++ "\"").mkString(", ")}), Vector(${mentions.map("\"" ++ _.s ++ "\"").mkString(", ")}), \n${body.show.split('\n').map("  " + _).mkString("\n")}\n)"

def eval(s: Space)(using pc: PathContext = PathContextMap(Map.empty), sc: SpaceContext = SpaceContextMap(Map.empty), rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): SpaceValue =
  def recp(x: Path): List[PathItem] = x match
    case Path.Deref(pr) => pc.resolve(pr).items
    case Path.Constant(pi) => pi.items
    case Path.Concat(l, r) => recp(l) ++ recp(r)
    case Path.GroundedPP(p, f) => f(PathValue(recp(p))).items
    case Path.GroundedSP(s, f) => f(SpaceValue(recs(s))).items
  def recs(x: Space): Set[PathValue] = x match
    case Space.Empty => Set()
    case Space.Call(rp, refs, mentions) =>
      val refvs = refs.map(p => PathValue(recp(p)))
      val mentionvs = mentions.map(s => SpaceValue(recs(s)))
      val Routine(_, refns, mentionns, body) = rc(rp)
      val pctx = PathContextMap(Map.from(refns zip refvs))
      val sctx = SpaceContextMap(Map.from(mentionns zip mentionvs))
      body match
        case Space.Union(l, Space.Call(`rp`, `refs`, `mentions`)) =>
          if (refs zip refvs).forall((p, pv) => pv == eval(Space.Singleton(p))(using pctx, sctx, rc).paths.head) &&
             (mentions zip mentionvs).forall((s, sv) => sv == eval(s)(using pctx, sctx, rc))
          then eval(l)(using pctx, sctx, rc).paths
          else eval(body)(using pctx, sctx, rc).paths
        case _ => eval(body)(using pctx, sctx, rc).paths
    case Space.Mention(p) => sc.resolve(p).paths
    case Space.Singleton(p) => Set(PathValue(recp(p)))
    case Space.Literal(SpaceValue(ps)) => ps
    case Space.Union(x, y) => recs(x) union recs(y)
    case Space.Intersection(x, y) => recs(x) intersect recs(y)
    case Space.Subtraction(x, y) => recs(x) removedAll recs(y)
    case Space.Restriction(x_e, prefixes_e) => val prefixes = recs(prefixes_e); recs(x_e).filter(x => prefixes.exists(p => x.items.startsWith(p.items)))
    case Space.Composition(x, y) => val ys = recs(y); for e1 <- recs(x); e2 <- ys yield PathValue(e1.items ++ e2.items)
    case Space.Wrap(src_e, p_e) => val p = recp(p_e); recs(src_e).map( sp => PathValue(p ++ sp.items))
    case Space.Unwrap(src_e, p_e) => val p = recp(p_e); recs(src_e).collect { case e if e.items.startsWith(p) => PathValue(e.items.drop(p.length)) }
    case Space.DropHead(src_e) => recs(src_e).collect { case PathValue(_::r) => PathValue(r) }
    case Space.Transformation(src_e, pattern, template) => val transformer = make_transform(PathValue(recp(pattern)), PathValue(recp(template))).unlift; recs(src_e).collect(transformer)
    case Space.Iteration(src_e, symbol, rest, templates) =>
      (for (h, r) <- recs(src_e).groupMap(x => PathValue(x.items.head::Nil))(x => PathValue(x.items.tail));
          p <- eval(templates)(using pc.grown(Map(symbol -> h)), sc.grown(Map(rest -> SpaceValue(r))), rc).paths
      yield p).toSet
    case Space.LeftResidual(x_e, y_e) => val ys = recs(y_e); val xs = recs(x_e); for e <- xs; r <- e.prefixes; if ys.forall(g => xs.contains(PathValue(r.items ++ g.items))) yield r
    case Space.RightResidual(y_e, x_e) => val ys = recs(y_e); val xs = recs(x_e); for e <- xs; r <- e.postfixes; if ys.forall(g => xs.contains(PathValue(g.items ++ r.items))) yield r
    case Space.GroundedPS(p, f) => f(PathValue(recp(p))).paths
    case Space.GroundedSS(s, f) => f(SpaceValue(recs(s))).paths
  SpaceValue(recs(s))

case class Node[R](scope: Path, operation: String, kind: "path" | "space", inputs: Vector[R]):
  def show: String = s"${scope.pretty} $operation(${inputs.mkString(", ")}): $kind"
class OpGraph(val nodes: ArrayBuffer[Node[Int]]):
  def this() = this(ArrayBuffer.empty)
  def show: String = nodes.zipWithIndex.map((n, i) => s"$i ${n.show}").mkString("\n")
  def store(node: Node[Int]): Int = {val i = nodes.length; nodes.addOne(node); i}
  def load(ref: Int): Node[Int] = nodes(ref)
  def update(ref: Int, f: Node[Int] => Node[Int]): Unit = nodes(ref) = f(nodes(ref))

def transpile(r: Routine): OpGraph =
  val g = OpGraph()
  val path_vars: ArrayBuffer[(Int, PathRef, Path)] = ArrayBuffer.from(r.refs.zipWithIndex.map((pr, i) =>
    (g.store(Node(Path.Deref(PathRef("^")), s"ExtractPathRef(${pr.s})", "path", Vector())),
      pr, Path.Deref(PathRef("^")))))
  val space_vars: ArrayBuffer[(Int, SpaceMention, Path)] = ArrayBuffer.from(r.mentions.zipWithIndex.map((sm, i) =>
    (g.store(Node(Path.Deref(PathRef("^")), s"ExtractSpaceMention(${sm.s})", "space", Vector())),
      sm, Path.Deref(PathRef("^")))))

  def recp(x: Path, scope: Path): Int = x match
    case Path.Deref(pr) =>
      path_vars.find((v, name, scp) => pr == name).get._1
    case Path.Constant(pi) =>
      g.store(Node(scope, s"Constant(${pi.show})", "path", Vector()))
    case Path.Concat(l, r) =>
      g.store(Node(scope, s"Concat", "path", Vector(recp(l, scope), recp(r, scope))))
    case Path.GroundedPP(p, f) =>
      throw NotImplementedError("grounded functions WIP")
    case Path.GroundedPP(s, f) =>
      throw NotImplementedError("grounded functions WIP")

  def recs(x: Space, scope: Path): Int =
    x match
      case Space.Empty =>
        g.store(Node(scope, "Empty", "space", Vector()))
      case Space.Call(r, refs, mentions) =>
        val refvs = refs.map(p => recp(p, scope))
        val mentionvs = mentions.map(s => recs(s, scope))
        g.store(Node(scope, r.s, "space", refvs ++ mentionvs))
      case Space.Mention(sm) =>
        space_vars.find((v, name, scp) => sm == name).map(_._1).getOrElse(sm.hashCode())
      case Space.Singleton(p) =>
        val v = recp(p, scope)
        g.store(Node(scope, "Singleton", "space", Vector(v)))
      case Space.Literal(sv) =>
        g.store(Node(scope, s"Literal(${sv.show})", "space", Vector()))
      case Space.Union(x, y) =>
        g.store(Node(scope, "Union", "space", Vector(recs(x, scope), recs(y, scope))))
      case Space.Intersection(x, y) =>
        g.store(Node(scope, "Intersection", "space", Vector(recs(x, scope), recs(y, scope))))
      case Space.Subtraction(x, y) =>
        g.store(Node(scope, "Subtraction", "space", Vector(recs(x, scope), recs(y, scope))))
      case Space.Restriction(x, prefixes) =>
        g.store(Node(scope, "Restriction", "space", Vector(recs(x, scope), recs(prefixes, scope))))
      case Space.Composition(x, y) =>
        g.store(Node(scope, "Composition", "space", Vector(recs(x, scope), recs(y, scope))))
      case Space.Wrap(src, p) =>
        val s = recs(src, scope)
        val v = recp(p, scope)
        g.store(Node(scope, "Wrap", "space", Vector(s, v)))
      case Space.Unwrap(src, p) =>
        val s = recs(src, scope)
        val v = recp(p, scope)
        g.store(Node(scope, "Unwrap", "space", Vector(s, v)))
      case Space.DropHead(src) =>
        g.store(Node(scope, "DropHead", "space", Vector(recs(src, scope))))
      case Space.Transformation(src, pattern, template) =>
        val s = recs(src, scope)
        val pv = recp(pattern, scope)
        val tv = recp(template, scope)
        g.store(Node(scope, "Transformation", "space", Vector(s, pv, tv)))
      case Space.Iteration(src, symbol, rest, templates) =>
        val s = recs(src, scope)
        val new_scope = Path.Concat(scope, Path.Deref(symbol))
        path_vars.addOne((g.store(Node(new_scope, "NextPath", "path", Vector(s))), symbol, new_scope))
        space_vars.addOne((g.store(Node(new_scope, "NextSubspace", "space", Vector(s))), rest, new_scope))
        recs(templates, new_scope)
      case Space.LeftResidual(x, y) =>
        g.store(Node(scope, "LeftResidual", "space", Vector(recs(x, scope), recs(y, scope))))
      case Space.RightResidual(y, x) =>
        g.store(Node(scope, "RightResidual", "space", Vector(recs(y, scope), recs(x, scope))))
      case Space.GroundedPS(p, f) =>
        throw NotImplementedError("grounded functions WIP")
      case Space.GroundedPS(s, f) =>
        throw NotImplementedError("grounded functions WIP")

  recs(r.body, Path.Deref(PathRef("^")))
  g


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
    infix def iter(symbol: String, rest: String, rhs: Space): Space = Space.Iteration(x, PathRef(symbol), SpaceMention(rest), rhs)
    def :\(y: Space) = Space.RightResidual(x, y)
    def /:(y: Space) = Space.LeftResidual(x, y)

  extension (st: SpaceValue.type)
    def apply(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)

  extension (rp: RoutinePtr)
    def apply(refs: Vector[Path], mentions: Vector[Space]) = Space.Call(rp, refs, mentions)

  extension (inline sc: StringContext)
    inline def S(inline args: Any*): Space =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Space.Mention(SpaceMention(k))

  extension (inline sc: StringContext)
    inline def P(inline args: Any*): Path =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Path.Deref(PathRef(k))

  extension (inline sc: StringContext)
    inline def R(inline args: Any*): RoutinePtr =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      RoutinePtr(k)

  def routine(name: String, refs: Vector[String], mentions: Vector[String], space: Space) = Routine(RoutinePtr(name), refs.map(PathRef(_)), mentions.map(SpaceMention(_)), space)