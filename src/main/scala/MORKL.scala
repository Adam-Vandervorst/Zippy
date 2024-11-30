package morkl

import scala.io.AnsiColor.*
import scala.util.Random
import scala.collection.mutable.{ArrayBuffer, LongMap, Stack}
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

  infix def mostSpecific(that: PathValue): Option[PathValue] =
    // Foo.Bar mostSpecific Foo.Bar.Baz == Some(Foo.Bar.Baz)
    if this.prefixes.contains(that) then Some(this)
    else if that.prefixes.contains(this) then Some(that)
    else None

  infix def renameFrom(that: PathValue, bound: Map[String, String] = Map.empty): PathValue =
    // $x.$y.$x renameFrom $a.$b.$a == $a.$b.$a
    // $x.c.$x renameFrom $a.c.$b == $a.c.$a
    // s.$x.$y renameFrom s.$a.$a == s.$a.$y
    // $x.p.$y.$x renameFrom $a.q.$a.$b == $a.p.$y.$a
    (this.items, that.items) match
      case (PathItem.Variable(x)::this_tail, PathItem.Variable(y)::that_tail) =>
        bound.get(x) match
          case Some(y_analog) =>
            val v = PathItem.Variable(y_analog)
            PathValue(v::(PathValue(this_tail).renameFrom(PathValue(that_tail), bound)).items)
          case None =>
            val v = PathItem.Variable(x)
            if bound.exists((_, y_) => y == y_) then
              PathValue(v::(PathValue(this_tail).renameFrom(PathValue(that_tail), bound)).items)
            else
              PathValue(PathItem.Variable(y)::(PathValue(this_tail).renameFrom(PathValue(that_tail), bound + (x -> y))).items)
      case (v::this_tail, _::that_tail) =>
        PathValue(v::(PathValue(this_tail).renameFrom(PathValue(that_tail), bound)).items)
      case (Nil, _) => PathValue(Nil)
      case (rest, Nil) => PathValue(rest.map{ case PathItem.Variable(v) => PathItem.Variable(bound.getOrElse(v, v)); case x => x })


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
  case Limit(i: Int, x: Space)

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
    case Space.Limit(i, z) => s"Limit($i, ${z.show})"


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
    case Space.Limit(i, x) => recs(x).take(i)
  SpaceValue(recs(s))

case class Node[R](operation: String, constant: String, kind: "path" | "space", inputs: Vector[R]):
  def show: String = s"$operation[${constant}](${inputs.mkString(", ")}): $kind"
  def map[S](f: R => S): Node[S] = copy(inputs=inputs.map(f))
class RecursiveOpGraph(var root: Node[(Int, Int)], val parent: Option[RecursiveOpGraph], val nodes: ArrayBuffer[Either[Node[(Int, Int)], RecursiveOpGraph]]):
  def level: Int = parent.fold(0)(_.level + 1)
  def show: String = s"${root.show}\n" + nodes.zipWithIndex.map((n_g, i) => n_g.fold(
    n => s"$i ${n.show}",
    g => s"$i ${g.show.split('\n').head}\n" ++ g.show.split('\n').tail.map(l => s"  $l").mkString("\n")
  )).mkString("\n")
  def store(node: Node[(Int, Int)]): (Int, Int) = {val i = nodes.length; nodes.addOne(Left(node)); level -> i}
  def store(node: RecursiveOpGraph): (Int, Int) = {val i = nodes.length; nodes.addOne(Right(node)); level -> i}
  def lookup(pos: (Int, Int)): Either[Node[(Int, Int)], RecursiveOpGraph] =
    val desired_level = pos._1
    if desired_level == level then nodes(pos._2)
    else if desired_level < level then parent.get.lookup(pos)
    else throw RuntimeException(s"Not in tree $pos")
  def find(pred: Node[(Int, Int)] => Boolean): Option[(Int, Int)] =
    nodes.zipWithIndex.collectFirst{ case (x, i) if x.left.exists(pred) => level -> i } match
      case None => ()
      case Some(p) => return Some(p)
    var curr = this
    while curr.parent.nonEmpty do
      val n = curr.parent.get
      n.nodes.iterator.takeWhile(x => !x.exists(_ eq curr)).zipWithIndex
        .collectFirst{ case (x, i) if x.left.exists(pred) => n.level -> i } match
        case None => curr = n
        case Some(p) => return Some(p)
    None

def transpile(r: Routine, caller: Option[RecursiveOpGraph] = None): RecursiveOpGraph =
  val g = RecursiveOpGraph(Node("Routine", r.name.s, "space", Vector()), caller, ArrayBuffer.empty)
  for (pr, i) <- r.refs.zipWithIndex do
    g.store(Node("ExtractPathRef", pr.s, "path", Vector()))
  for (sm, i) <- r.mentions.zipWithIndex do
    g.store(Node("ExtractSpaceMention", sm.s, "space", Vector()))

  def recp(x: Path): (Int, Int) = x match
    case Path.Deref(pr) =>
      g.find(n => n.operation == s"ExtractPathRef" && n.constant == pr.s).getOrElse(throw RuntimeException(s"$pr not found"))
    case Path.Constant(pi) =>
      g.store(Node("Constant", pi.show, "path", Vector()))
    case Path.Concat(l, r) =>
      g.store(Node("Concat", "", "path", Vector(recp(l), recp(r))))
    case Path.GroundedPP(p, f) =>
      throw NotImplementedError("grounded functions WIP")
    case Path.GroundedPP(s, f) =>
      throw NotImplementedError("grounded functions WIP")

  def recs(x: Space): (Int, Int) =
    x match
      case Space.Empty =>
        g.store(Node("Empty", "", "space", Vector()))
      case Space.Call(r, refs, mentions) =>
        val refvs = refs.map(p => recp(p))
        val mentionvs = mentions.map(s => recs(s))
        g.store(Node("Call", r.s, "space", refvs ++ mentionvs))
      case Space.Mention(sm) =>
        g.find(n => n.operation == "ExtractSpaceMention" && n.constant == sm.s).getOrElse(throw RuntimeException(s"$sm not found"))
      case Space.Singleton(p) =>
        val v = recp(p)
        g.store(Node("Singleton", "", "space", Vector(v)))
      case Space.Literal(sv) =>
        g.store(Node(s"Literal", sv.show, "space", Vector()))
      case Space.Union(x, y) =>
        g.store(Node("Union", "", "space", Vector(recs(x), recs(y))))
      case Space.Intersection(x, y) =>
        g.store(Node("Intersection", "", "space", Vector(recs(x), recs(y))))
      case Space.Subtraction(x, y) =>
        g.store(Node("Subtraction", "", "space", Vector(recs(x), recs(y))))
      case Space.Restriction(x, prefixes) =>
        g.store(Node("Restriction", "", "space", Vector(recs(x), recs(prefixes))))
      case Space.Composition(x, y) =>
        g.store(Node("Composition", "", "space", Vector(recs(x), recs(y))))
      case Space.Wrap(src, p) =>
        val s = recs(src)
        val v = recp(p)
        g.store(Node("Wrap", "", "space", Vector(s, v)))
      case Space.Unwrap(src, p) =>
        val s = recs(src)
        val v = recp(p)
        g.store(Node("Unwrap", "", "space", Vector(s, v)))
      case Space.DropHead(src) =>
        g.store(Node("DropHead", "", "space", Vector(recs(src))))
      case Space.Transformation(src, pattern, template) =>
        val s = recs(src)
        val pv = recp(pattern)
        val tv = recp(template)
        g.store(Node("Transformation", "", "space", Vector(s, pv, tv)))
      case Space.Iteration(src, symbol, rest, templates) =>
        val s = recs(src)
        val rog = transpile(Routine(
          RoutinePtr(r.name.s + "_" + symbol.s),
          Vector(symbol),
          Vector(rest),
          templates
        ), Some(g))
        rog.root = Node("Iteration", "", "space", Vector(s))
        g.store(rog)
      case Space.LeftResidual(x, y) =>
        g.store(Node("LeftResidual", "", "space", Vector(recs(x), recs(y))))
      case Space.RightResidual(y, x) =>
        g.store(Node("RightResidual", "", "space", Vector(recs(y), recs(x))))
      case Space.GroundedPS(p, f) =>
        throw NotImplementedError("grounded functions WIP")
      case Space.GroundedPS(s, f) =>
        throw NotImplementedError("grounded functions WIP")
      case Space.Limit(i, x) =>
        g.store(Node(s"Limit", i.toString, "space", Vector(recs(x))))

  recs(r.body)
  g

def exec(rog: RecursiveOpGraph,
         stack: Stack[Array[PathValue | SpaceValue | Null]]): Unit =
  val l = rog.level
  var c = 0
  val s = stack.top
  inline def pos = (l, c)
  extension (p : (Int, Int)) inline def sget = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[SpaceValue]
  extension (p : (Int, Int)) inline def pget = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[PathValue]
  while c < rog.nodes.length do
    rog.nodes(c) match
      case Left(Node(op, constant, kind, inputs)) => kind match
        case "path" => s(c) = (op match
          case "ExtractPathRef" => pos.pget // stack should already prepared
          case "Constant" => Syntax.parse(constant) // stack should already be prepared
          case "Concat" => PathValue(inputs(0).pget.items ++ inputs(1).pget.items))
        case "space" => s(c) = (op match
          case "Empty" => SpaceValue(Set.empty)
          case "Call" => ??? // todo
          case "ExtractSpaceMention" => pos.sget // stack should already prepared
          case "Singleton" => SpaceValue(Set(inputs(0).pget))
          case "Literal" => ??? // should likely be translated into a union of singletons of constant paths
          case "Union" => eval(Space.Union(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Intersection" => eval(Space.Intersection(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Restriction" => eval(Space.Restriction(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Subtraction" => eval(Space.Subtraction(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Composition" => eval(Space.Composition(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Wrap" => eval(Space.Wrap(Space.Literal(inputs(0).sget), Path.Constant(inputs(1).pget)))
          case "Unwrap" => eval(Space.Unwrap(Space.Literal(inputs(0).sget), Path.Constant(inputs(1).pget)))
          case "DropHead" => eval(Space.DropHead(Space.Literal(inputs(0).sget)))
          case "Transformation" => ??? // we should likely eventually support this
          case "Iteration" => ??? // should've been elided
          case "LeftResidual" => ??? // not worth supporting
          case "RightResidual" => ??? // not worth supporting
          case "Limit" => ???) // todo, mainly should be optimized to be integrated in Iteration
      case Right(sg: RecursiveOpGraph) =>
        val Node(op, constant, kind, inputs) = sg.root
        op match
          case "Routine" => ???
//            assert(l == 0)
//            exec(sg, stack)
          case "Iteration" =>
            s(c) = SpaceValue(Set.empty)
            for (h, r) <- inputs(0).sget.paths.groupMap(x => PathValue(x.items.head :: Nil))(x => PathValue(x.items.tail)) do
              stack.push(new Array(sg.nodes.length))
              stack.top(0) = h
              stack.top(1) = SpaceValue(r)
              exec(sg, stack)
              s(c) = SpaceValue(pos.sget.paths union stack.pop().last.asInstanceOf[SpaceValue].paths)
    c += 1
  end while

def graphviz_table(g: RecursiveOpGraph, path: Vector[Int] = Vector()): Unit =
  if path.length == 0 then
    println("digraph G {")
    println("graph [rankdir = \"LR\"];")
  val label = g.nodes.zipWithIndex.map{
    case (Left(n @ Node(operation, constant, kind, inputs)), i) =>
      inputs.foreach((d, j) => println(s"g${path.take(d).map(_.toString).mkString("_")}:f$j -> g${path.map(_.toString).mkString("_")}:f$i:nw"))
      f"<f$i>" + n.operation
    case (Right(sg), i) =>
      sg.root.inputs.foreach((d, j) => println(s"g${path.take(d).map(_.toString).mkString("_")}:f$j -> g${path.map(_.toString).mkString("_")}:f$i:nw"))
      sg.root.operation match
        case "Iteration" =>
          println(s"g${path.map(_.toString).mkString("_")}:f$i -> g${(path :+ i).map(_.toString).mkString("_")}:f0:nw [style=dotted]")
          println(s"g${path.map(_.toString).mkString("_")}:f$i -> g${(path :+ i).map(_.toString).mkString("_")}:f1:nw [style=dotted]")
      f"<f$i>" + sg.root.operation
  }.mkString(" | ")
  println(s"g${path.map(_.toString).mkString("_")} [label=\"${label}\", shape=\"record\"];")
  g.nodes.zipWithIndex.collect { case (Right(sg), i) =>
    graphviz(sg, path :+ i)
  }
  if path.length == 0 then
    println("}")

def graphviz(g: RecursiveOpGraph, path: Vector[Int] = Vector(), show_label: Boolean = false): Unit =
  if path.length == 0 then { println("digraph G {"); println("graph [rankdir=\"LR\" compound=true];") }
  val indent = "  ".repeat(path.length)
  println(s"${indent}subgraph cluster_${path.map(_.toString).mkString("_")} {")
  println(s"${indent}  label=\"${g.root.operation}[${g.root.constant}]\"")
  g.nodes.zipWithIndex.foreach {
    case (Left(n@Node(operation, constant, kind, inputs)), i) =>
      val shape = if kind == "space" then s" shape=\"box\"" else ""
      println(s"${indent}  g${path.map(_.toString).mkString("_")}_f$i [label=\"${operation}[${constant}]\"$shape]")
      inputs.zipWithIndex.foreach{ case ((d, j), k) => g.lookup((d, j)) match
        case Left(n) =>
          val label = if show_label then s"label=\"${n.kind} ${k}\"" else ""
          println(s"${indent}  g${path.take(d).map(_.toString).mkString("_")}_f$j -> g${path.map(_.toString).mkString("_")}_f$i [$label]")
        case Right(sg) =>
          val label = if show_label then s"label=\"${sg.root.kind} ${k}\"" else ""
          println(s"${indent}  g${(path.take(d) :+ j).map(_.toString).mkString("_")}_f0 -> g${path.map(_.toString).mkString("_")}_f$i [$label ltail=cluster_${(path.take(d) :+ j).map(_.toString).mkString("_")}]")
      }
    case (Right(sg), i) =>
      sg.root.inputs.zipWithIndex.foreach{ case ((d, j), k) => g.lookup((d, j)) match
        case Left(n) =>
          val label = if show_label then s"label=\"${n.kind} ${k}\"" else ""
          println(s"${indent}  g${path.take(d).map(_.toString).mkString("_")}_f$j -> g${(path :+ i).map(_.toString).mkString("_")}_f0 [$label lhead=cluster_${(path :+ i).map(_.toString).mkString("_")}]")
        case Right(sg) =>
          val label = if show_label then s"label=\"${sg.root.kind} ${k}\"" else ""
          println(s"${indent}  g${(path.take(d) :+ j).map(_.toString).mkString("_")}_f0 -> g${(path :+ i).map(_.toString).mkString("_")}_f0 [$label lhead=cluster_${(path :+ i).map(_.toString).mkString("_")} ltail=cluster_${(path.take(d) :+ j).map(_.toString).mkString("_")}]")
      }
  }
  g.nodes.zipWithIndex.collect { case (Right(sg), i) =>
    graphviz(sg, path :+ i, show_label)
  }
  println(s"${indent}}")
  if path.length == 0 then println("}")


def mermaid(g: RecursiveOpGraph, show_label: Boolean = false, vertical: Boolean = true): Unit =
  val ff = ArrayBuffer.empty[String]
  val fg = ArrayBuffer.empty[String]
  val gf = ArrayBuffer.empty[String]
  val gg = ArrayBuffer.empty[String]
  println("flowchart LR")
  def rec(g: RecursiveOpGraph, path: Vector[Int] = Vector()): Unit =
    val indent = "  ".repeat(path.length)
    println(s"${indent}subgraph g${path.map(_.toString).mkString("_")} [\"${g.root.operation}[${g.root.constant}]\"]")
    println(s"${indent}  direction ${if vertical then "TB" else "LR"}")
    g.nodes.zipWithIndex.foreach {
      case (Left(n@Node(operation, constant, kind, inputs)), i) =>
        val shape = if kind == "space" then "rect" else "rounded"
        println(s"${indent}  g${path.map(_.toString).mkString("_")}_f$i@{ shape: $shape, label: \"${operation}[${constant}]\"}")
        inputs.zipWithIndex.foreach{ case ((d, j), k) => g.lookup((d, j)) match
          case Left(n) =>
            val label = if show_label then s"|\"${n.kind} ${k}\"|" else ""
            ff += s"g${path.take(d).map(_.toString).mkString("_")}_f$j ---->$label g${path.map(_.toString).mkString("_")}_f$i %% LL"
          case Right(sg) =>
            val label = if show_label then s"|\"${sg.root.kind} ${k}\"|" else ""
            gf += s"g${(path.take(d) :+ j).map(_.toString).mkString("_")} --->$label g${path.map(_.toString).mkString("_")}_f$i %% LR"
        }
      case (Right(sg), i) =>
        sg.root.inputs.zipWithIndex.foreach{ case ((d, j), k) => g.lookup((d, j)) match
          case Left(n) =>
            val label = if show_label then s"|\"${n.kind} ${k}\"|" else ""
            fg += s"g${path.take(d).map(_.toString).mkString("_")}_f$j --->$label g${(path :+ i).map(_.toString).mkString("_")} %% RL"
          case Right(sg) =>
            val label = if show_label then s"|\"${sg.root.kind} ${k}\"|" else ""
            gg += s"g${(path.take(d) :+ j).map(_.toString).mkString("_")} -->$label g${(path :+ i).map(_.toString).mkString("_")} %% RR"
        }
    }
    g.nodes.zipWithIndex.collect { case (Right(sg), i) =>
      rec(sg, path :+ i)
    }
    println(s"${indent}end")
  rec(g)
  given ordering: Ordering[String] = Ordering.String.on(_.takeWhile(_ != '-'))
  println(ff.sorted.mkString("\n"))
  println(fg.sorted.mkString("\n"))
  println(gf.sorted.mkString("\n"))
  println(gg.sorted.mkString("\n"))


def optimize_sharing(g: RecursiveOpGraph, stack: ArrayBuffer[(LongMap[(Int, Int)], LongMap[(Int, Int)])] = ArrayBuffer.empty): RecursiveOpGraph =
  val r = RecursiveOpGraph(g.root, g.parent, ArrayBuffer.empty)
  val l = g.level
  stack.addOne(LongMap.withDefault[(Int, Int)](x => l -> x.toInt) -> LongMap.withDefault[(Int, Int)](x => l -> x.toInt))
  var c = 0
  for (n, j) <- g.nodes.zipWithIndex do n match
    case Left(n) => g.find(m => m.map((lm, xm) => stack(lm)._1(xm)) == n.map((ln, xn) => stack(ln)._1(xn))) match
      case Some((l2, i)) =>
        if (l, i) == (l2, j) then
          r.store(n.map((l, x) => { val (l_, x_) = stack(l)._1(x); stack(l_)._2(x_) }))
          stack(l2)._2.update(i, l -> c)
          c += 1
        else
          stack.last._1.update(j, l2 -> i)
      case None => ()
    case Right(sg) =>
      r.store(optimize_sharing(sg, stack))
      c += 1
  r


def push_out(g: RecursiveOpGraph, stack: ArrayBuffer[LongMap[(Int, Int)]] = ArrayBuffer.empty): RecursiveOpGraph =
  val r = RecursiveOpGraph(g.root, g.parent, ArrayBuffer.empty)
  val lb = g.level


  def pred(g: RecursiveOpGraph, n: Node[(Int, Int)], pos: (Int, Int), gather: Boolean): Boolean =

    val c = {
    (pos._2 != g.nodes.length - 1) &&
    n.inputs.forall((l, x) => stack(l)(x)._1 < lb) &&
    !n.operation.startsWith("Extract") &&
    !((lb == pos._1) && (lb == 0))}
    println(s"${gather} move ${n.show} from ${pos} to ${lb -> (r.nodes.length - 1)}: $c")
    c
//    !stack(pos._1).get(pos._2).fold(false)((l, x) => l <= lb)

  def gather(g: RecursiveOpGraph, r: RecursiveOpGraph): Unit =
    val lr = g.level
    if lr == stack.length then
      stack.addOne(LongMap.withDefault[(Int, Int)](x => lr -> x.toInt))

    for (n_sg, j) <- g.nodes.zipWithIndex do n_sg match
      case Left(n) =>
        if pred(g, n, lr -> j, true) then
          val value = r.store(n)
//          assert(!stack(lr).contains(j), s"pos: ${lr -> j} current: ${stack(lr)(j)} new: $value node: $n")
          stack(lr)(j) = value
      case Right(sg) =>
        gather(sg, r)

  stack.addOne(LongMap.withDefault[(Int, Int)](x => lb -> x.toInt))
  for (n_sg, j) <- g.nodes.zipWithIndex do n_sg match
    case Left(n) =>
//      if !pred(g, n, lb -> j, false) then
      if !stack(lb).contains(j) then
//        println()
//        assert(!stack(lb).contains(j))
        stack(lb)(j) = r.store(n)
    case Right(sg) =>
      gather(sg, r)
      stack(lb)(j) = r.store(push_out(sg, stack))
  r.nodes.mapInPlace{
    case Left(n) => Left(n.map((l, x) => stack(l)(x)))
    case Right(sg) => Right(RecursiveOpGraph(sg.root.map((l, x) => stack(l)(x)), sg.parent, sg.nodes))
  }
  r


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
