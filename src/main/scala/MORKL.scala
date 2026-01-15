package morkl

import scala.io.AnsiColor.*
import scala.util.Random
import scala.collection.mutable.{ArrayBuffer, LongMap, Stack}
import java.util.Base64
import scala.collection.mutable
import scala.language.implicitConversions


/*
case class BinNode(F: BinNode | Null, T: BinNode | Null)

object Kernels:
  // SIMT
  sealed trait Executor

  case object Sequential extends Executor
  // step through applied kernels in sequence with Chain over AKernels

  case object SIMD extends Executor
  // Step Kernel over Stacked data

  case object MIMD extends Executor
  // Step set of AKernels at once

  

  sealed trait Kernel
  case object Union extends Kernel
  case class Unwrap(path: Vector[Boolean]) extends Kernel
  case class Wrap(path: Vector[Boolean]) extends Kernel
  case object Identity extends Kernel

  sealed trait AppliedKernel
  case class AUnion(x: BinNode | Null, y: BinNode | Null) extends AppliedKernel
  case class AUnwrap(node: BinNode | Null, path: Vector[Boolean]) extends AppliedKernel
  case class AWrap(node: BinNode | Null, path: Vector[Boolean]) extends AppliedKernel
  case class AIdentity(node: BinNode) extends AppliedKernel
  case class AForkJoin(T: AppliedKernel, F: AppliedKernel) extends AppliedKernel
  case class AWQ(todo: Vector[AppliedKernel], done: Vector[AppliedKernel]) extends AppliedKernel


  def exec(akernel: AppliedKernel): AppliedKernel =
    kernel match
      case AUnion(x, y) =>
        if x eq null then AIdentity(y)
        else if y eq null then AIdentity(x)
        else AForkJoin(
          (x.F, y.F) match
            case (null, null) => AIdentity(null)
            case (null, r) => AIdentity(r)
            case (l, null) => AIdentity(l)
            case (l, r) => AUnion(l, r),
          (x.T, y.T) match
            case (null, null) => AIdentity(null)
            case (null, r) => AIdentity(r)
            case (l, null) => AIdentity(l)
            case (l, r) => AUnion(l, r))
      case AUnwrap(node, path) =>
        if node eq null then AIdentity(node)
        if path.length == 0 then AIdentity(node)
        else
          if path.head then AUnwrap(node.T, path.tail)
          else AUnwrap(node.F, path.tail)
      case AWrap(node, path) =>
        if path.length == 0 then AIdentity(node)
        else
          if path.head then AWrap(BinNode(node, null), path.init)
          else AWrap(BinNode(null, node), path.init)
      case AIdentity(n) => AIdentity(n)


infix def intersection(that: BinNode): BinNode =
  BinNode(
    (this.F, that.F) match
      case (null, null) => null
      case (null, r) => null
      case (l, null) => null
      case (l, r) => l intersection r,
    (this.T, that.T) match
      case (null, null) => null
      case (null, r) => null
      case (l, null) => null
      case (l, r) => l intersection r)

  infix def restriction(that: BinNode): BinNode =
    BinNode(
      (this.F, that.F) match
        case (null, null) => null
        case (null, r) => r
        case (l, null) => null
        case (l, r) => l restriction r,
      (this.T, that.T) match
        case (null, null) => null
        case (null, r) => r
        case (l, null) => null
        case (l, r) => l restriction r)
*/


trait Loc:
  def is_path(segment: PathValue): Boolean
  def branches(segment: PathValue): Set[PathItem]
  def descend(segment: PathValue, branch: Int): Loc = this


object Loc:
  case class Const(path: PathValue) extends Loc:
    def is_path(segment: PathValue): Boolean = segment == path
    def branches(segment: PathValue): Set[PathItem] = if segment.items.length < path.items.length then Set(path.items(segment.items.length)) else Set.empty

  case class Repeat(alphabet: Set[PathItem], k: Int) extends Loc:
    def is_path(segment: PathValue): Boolean = segment.items.length == k
    def branches(segment: PathValue): Set[PathItem] = if segment.items.length < k then alphabet else Set.empty

  case class Full(alphabet: Set[PathItem]) extends Loc:
    def is_path(segment: PathValue): Boolean = true
    def branches(segment: PathValue): Set[PathItem] = alphabet

  case object Empty extends Loc:
    def is_path(segment: PathValue): Boolean = false
    def branches(segment: PathValue): Set[PathItem] = Set.empty

  case class Trie(space: SpaceValue) extends Loc:
    def is_path(segment: PathValue): Boolean = space.paths.contains(segment)
    def branches(segment: PathValue): Set[PathItem] = space.paths.collect { case e if e.items.startsWith(segment.items) => e.items(segment.items.length) }

  case class Union(locs: Set[Loc]) extends Loc:
    def is_path(segment: PathValue): Boolean = locs.exists(_.is_path(segment))
    def branches(segment: PathValue): Set[PathItem] = locs.map(_.branches(segment)).reduce(_ union _)

  case class Intersection(locs: Set[Loc]) extends Loc:
    def is_path(segment: PathValue): Boolean = locs.forall(_.is_path(segment))
    def branches(segment: PathValue): Set[PathItem] = locs.map(_.branches(segment)).reduce(_ intersect _)

  case class Subtraction(loc: Loc, neg: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && !neg.is_path(segment)
    def branches(segment: PathValue): Set[PathItem] = loc.branches(segment) removedAll neg.branches(segment)

  case class Restriction(loc: Loc, accepted: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && (0 to segment.items.length).exists(i =>
      accepted.is_path(PathValue(segment.items.take(i))))
    def branches(segment: PathValue): Set[PathItem] = if (0 to segment.items.length).exists(i =>
      accepted.is_path(PathValue(segment.items.take(i)))) then loc.branches(segment) else Set.empty

  case class Raffination(loc: Loc, unaccepted: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = loc.is_path(segment) && !(0 to segment.items.length).exists(i =>
      unaccepted.is_path(PathValue(segment.items.take(i))))
    def branches(segment: PathValue): Set[PathItem] = if !(0 to segment.items.length).exists(i =>
      unaccepted.is_path(PathValue(segment.items.take(i)))) then loc.branches(segment) else Set.empty

  case class Compose(left: Loc, right: Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = (0 to segment.items.length).exists(i =>
      val (l, r) = segment.items.splitAt(i)
      left.is_path(PathValue(l)) && right.is_path(PathValue(r)))
    def branches(segment: PathValue): Set[PathItem] =
      (0 to segment.items.length).filter(i =>
        left.is_path(PathValue(segment.items.take(i)))
      ).flatMap(i => right.branches(PathValue(segment.items.drop(i)))).toSet

  case class Dep(left: Loc, rightf: PathValue => Loc) extends Loc:
    def is_path(segment: PathValue): Boolean = (0 to segment.items.length).exists(i =>
      val (l, r) = segment.items.splitAt(i)
      left.is_path(PathValue(l)) && rightf(PathValue(l)).is_path(PathValue(r)))
    def branches(segment: PathValue): Set[PathItem] =
      (0 to segment.items.length).filter(i =>
        left.is_path(PathValue(segment.items.take(i)))
      ).flatMap(i => rightf(PathValue(segment.items.take(i))).branches(PathValue(segment.items.drop(i)))).toSet


  def uop(src: Loc, pf: PathValue => PathValue) = Dep(src, p => Const(pf(p)))

  def int_to_int(f: Int => Int) = uop(Full((0 to 9).map(k => PathItem.Symbol(k.toString)).toSet),
    p => PathValue(f(p.items.map(_.show).mkString.toInt).toString.map(c => PathItem.Symbol(c.toString)).toList))

  def sqrt = int_to_int(i => Math.sqrt(i.toDouble).toInt)

enum PathItem:
  case Symbol(n: String)
  case Variable(n: String)
  case Arity(k: Int)

  def show: String = this match
    case PathItem.Symbol(n) => n
    case PathItem.Variable(n) => s"$$$n"
    case PathItem.Arity(k) => s"[$k]"

case class SymbolConflict(l: String, r: String) extends Exception(s"Symbol conflict $l $r")

case class PathRef(s: String):
  val lengthHint = -1
  def known(length: Int): PathRef = new PathRef(s) { override val lengthHint = length }

enum Path:
  case Deref(pr: PathRef)
  case Constant(pi: PathValue)
  case Concat(l: Path, r: Path)
  case GroundedPP(p: Path, f: PathValue => PathValue)
  case GroundedSP(p: Space, f: SpaceValue => PathValue)

  def show: String = this match
//    case Path.Deref(pr) => if pr.lengthHint == -1 then s"P\"${pr.s}\"" else s"P\"${pr.s}\"{${pr.lengthHint}}"
    case Path.Deref(pr) => s"P\"${pr.s}\""
    case Path.Constant(pi) => s"\"${pi.show}\""
    case Path.Concat(l, r) => s"${l.show} x ${r.show}"
    case Path.GroundedPP(p, f) => s"PP${f.hashCode()}(${p.show})"
    case Path.GroundedSP(s, f) => s"SP${f.hashCode()}(${s.show})"

  def pretty: String = this match
    case Path.Deref(pr) => pr.s
    case Path.Constant(pi) => pi.show
    case Path.Concat(l, r) => s"${l.pretty}.${r.pretty}"
    case Path.GroundedPP(p, f) => s"PP${f.hashCode()}(${p.pretty})"
    case Path.GroundedSP(s, f) => s"SP${f.hashCode()}(${s.show})"

  def factors: List[Path] = this match
    case Path.Concat(l, r) => l.factors ++ r.factors
    case p => p::Nil

object Path:
  val ZERO = Path.Constant(PathValue(Nil))
  val first: PartialFunction[Path, (Path, List[Path])] =
    case Path.Deref(pr) => Path.Deref(pr) -> Nil
    case Path.Constant(c) => Path.Constant(c) -> Nil
    case c @ Path.Concat(l, r) => c.factors.head -> c.factors.tail
  def fromFactors(ps: Iterable[Path]): Path = if ps.isEmpty then Path.Constant(PathValue(Nil)) else ps.iterator.reduce(Path.Concat(_, _))

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
      if k.s != "_" then n.updateWith(k)(mov =>
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
      if k.s != "_" then n.updateWith(k)(mov =>
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
  case Raffination(x: Space, y: Space)
  case Composition(x: Space, y: Space)
  case Transformation(src: Space, pattern: Path, template: Path)
  case Iteration(src: Space, symbol: PathRef, rest: SpaceMention, templates: Space)
  case Fold(src: Space, initial: Path, acc: PathRef, symbol: PathRef, rest: SpaceMention, templates: Space, update: Path)
  case Wrap(src: Space, p: Path)
  case Unwrap(src: Space, p: Path)
  case TailsUnion(src: Space)
  case TailsIntersection(src: Space)
  case LeftResidual(x: Space, y: Space) // likely not to be included
  case RightResidual(y: Space, x: Space) // likely not to be included
  case GroundedPS(p: Path, f: PathValue => SpaceValue)
  case GroundedSS(p: Space, f: SpaceValue => SpaceValue)
  case First(i: Int, x: Space)
  case Last(i: Int, x: Space)

  def show(using indent: Int = 0): String = this match
    case Space.Empty => "Empty"
    case Space.Call(r, refs, mentions) => s"${r.s}(${refs.map(_.show).mkString(", ")}; ${mentions.map(_.show).mkString(", ")})"
    case Space.Mention(variable) => s"S\"${variable.s}\""
    case Space.Singleton(p) => s"Singleton(${p.show})"
    case Space.Literal(p) => s"Literal(${p.show})"
    case Space.Union(x, y) => s"(${x.show} \\/ ${y.show})"
    case Space.Intersection(x, y) => s"(${x.show} /\\ ${y.show})"
    case Space.Subtraction(x, y) => s"(${x.show} \\ ${y.show})"
    case Space.Restriction(x, y) => s"(${x.show} <| ${y.show})"
    case Space.Composition(x, y) => s"(${x.show} x ${y.show})"
    case Space.Transformation(src, pattern, template) => s"${src.show}.transform(${pattern.show}, ${template.show})"
    case Space.Iteration(src, symbol, rest, templates) => s"${src.show}.iter(P\"${symbol.s}\", S\"${rest.s}\", \n${" ".repeat(indent + 1)}${templates.show(using indent + 1)}\n)"
    case Space.Wrap(src, p) => s"(${p.show} x ${src.show})"
    case Space.Unwrap(src, p) => s"${src.show}(${p.show})"
    case Space.TailsUnion(src) => s"TailsUnion(${src.show})"
    case Space.TailsIntersection(src) => s"TailsIntersection(${src.show})"
    case Space.LeftResidual(x, y) => s"(${y.show} /: ${x.show})"
    case Space.RightResidual(y, x) => s"(${y.show} :\\ ${x.show})"
    case Space.GroundedPS(p, f) => s"PS${f.hashCode()}(${p.show})"
    case Space.GroundedSS(s, f) => s"SS${f.hashCode()}(${s.show})"
    case Space.Raffination(x, y) => s"(${x.show} \\| ${y.show})"
    case Space.First(i, z) => s"First($i, ${z.show})"
    case Space.Last(i, z) => s"Last($i, ${z.show})"


case class SpaceValue(paths: Set[PathValue]):
  def show: String = paths.map(x => '"' + x.show + '"').toSeq.sorted.mkString("SpaceValue(", ", ", ")")
  def pretty: String = paths.map(_.show).toSeq.sorted.mkString("{", ";", "}")
  def prettyLines: String = paths.map(_.show).toSeq.sorted.mkString("", "\n", "")


case class RoutinePtr(s: String)
case class Routine(name: RoutinePtr, refs: Vector[PathRef], mentions: Vector[SpaceMention], body: Space):
  def show = s"routine(\"${name.s}\", Vector(${refs.map("\"" ++ _.s ++ "\"").mkString(", ")}), Vector(${mentions.map("\"" ++ _.s ++ "\"").mkString(", ")}), \n${body.show.split('\n').map("  " + _).mkString("\n")}\n)"
  def optimized(using ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Routine = Routine(name, refs, mentions,
    all_forever(Lower.inline(using new PartialFunction {
      override def apply(f: RoutinePtr): Routine = ctx(f)
      override def isDefinedAt(f: RoutinePtr): Boolean = f != name && ctx.isDefinedAt(f)
//    })(body), List(Lower.ConstantOps, Lower.IterateSingleton_Deref, Lower.LiteralSpaceOps, Lower.SingletonConst_Literal, Lower.ConcatSingleton_Iter, Lower.IterUnion_Indep, Lower.Wrap_Iter, Lower.Iter_Ident, Lower.Concat_Path, Lower.IterateLiteral_Union, Lower.UnwrapConcat_Unwraps, Lower.SingletonComposition_Wrap, Lower.SingletonSpaceOp_PathOp)))
    })(body), List(Lower.IterateSingleton_Deref, Lower.LiteralSpaceOps, Lower.SingletonConst_Literal, Lower.ConcatSingleton_Iter, Lower.IterUnion_Indep, Lower.Wrap_Iter, Lower.Iter_Ident, Lower.Concat_Path, Lower.IterateLiteral_Union, Lower.UnwrapConcat_Unwraps, Lower.SingletonComposition_Wrap, Lower.SingletonSpaceOp_PathOp)))

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
//      println(s"calling ${rp.s}(${pctx.m.map((pr, pv) => pr.s ++ ":" ++ pv.show)}; ${sctx.m.map((pr, pv) => pr.s ++ ":" ++ pv.show)}) >")
      val res = body match
        case Space.Union(l, Space.Call(`rp`, `refs`, `mentions`)) =>
          if (refs zip refvs).forall((p, pv) => pv == eval(Space.Singleton(p))(using pctx, sctx, rc).paths.head) &&
             (mentions zip mentionvs).forall((s, sv) => sv == eval(s)(using pctx, sctx, rc))
          then eval(l)(using pctx, sctx, rc).paths
          else eval(body)(using pctx, sctx, rc).paths
        case _ => eval(body)(using pctx, sctx, rc).paths
//      println(s"called ${rp.s}(${pctx.m.map((pr, pv) => pr.s ++ ":" ++ pv.show).mkString(", ")}; ${sctx.m.map((pr, pv) => pr.s ++ ":" ++ pv.show).mkString(", ")}) = ${SpaceValue(res).show}")
      res
    case Space.Mention(p) => sc.resolve(p).paths
    case Space.Singleton(p) => Set(PathValue(recp(p)))
    case Space.Literal(SpaceValue(ps)) => ps
    case Space.Union(x, y) => recs(x) union recs(y)
    case Space.Intersection(x, y) => recs(x) intersect recs(y)
    case Space.Subtraction(x, y) => recs(x) removedAll recs(y)
    case Space.Restriction(x_e, prefixes_e) => val prefixes = recs(prefixes_e); recs(x_e).filter(x => prefixes.exists(p => x.items.startsWith(p.items)))
    case Space.Composition(x, y) => val ys = recs(y); for e1 <- recs(x); e2 <- ys yield PathValue(e1.items ++ e2.items)
//    case Space.Wrap(src_e, p_e) => val p = recp(p_e); recs(src_e).map( sp => PathValue(p ++ sp.items))
//    case Space.Unwrap(src_e, p_e) => val p = recp(p_e); recs(src_e).collect { case e if e.items.startsWith(p) => PathValue(e.items.drop(p.length)) }

    case Space.Wrap(src_e, p_e) =>
//      val p = recp(p_e); recs(src_e).map( sp => PathValue(p ++ sp.items))
      recs(Space.Composition(Space.Singleton(p_e), src_e))
    case Space.Unwrap(src_e, p_e) =>
      val p = recp(p_e);
      val src = recs(src_e);
      val res = src.collect { case e if e.items.startsWith(p) => PathValue(e.items.drop(p.length)) }
//      println(s"unwrap p=${PathValue(p).show} src=${src.map(_.show)} res=${res.map(_.show)}")
      res
    case Space.TailsUnion(src_e) => recs(src_e).collect { case PathValue(_::r) => PathValue(r) }
    case Space.TailsIntersection(src_e) => recs(src_e).groupMapReduce{ case PathValue(h::_) => h }{ case PathValue(_::t) => Set(PathValue(t)) }(_ union _).values.reduce(_ intersect _)
    case Space.Transformation(src_e, pattern, template) => val transformer = make_transform(PathValue(recp(pattern)), PathValue(recp(template))).unlift; recs(src_e).collect(transformer)
    case Space.Iteration(src_e, symbol, rest, templates) =>
      Set.from(for (h, r) <- recs(src_e).groupMap(x => PathValue(x.items.head::Nil))(x => PathValue(x.items.tail));
          p <- eval(templates)(using pc.grown(Map(symbol -> h)), sc.grown(Map(rest -> SpaceValue(Set.from(r)))), rc).paths
      yield p)
    case Space.LeftResidual(x_e, y_e) => val ys = recs(y_e); val xs = recs(x_e); for e <- xs; r <- e.prefixes; if ys.forall(g => xs.contains(PathValue(r.items ++ g.items))) yield r
    case Space.RightResidual(y_e, x_e) => val ys = recs(y_e); val xs = recs(x_e); for e <- xs; r <- e.postfixes; if ys.forall(g => xs.contains(PathValue(g.items ++ r.items))) yield r
    case Space.Raffination(x_e, y_e) => recs(Space.Subtraction(x_e, Space.Restriction(x_e, y_e)))
    case Space.GroundedPS(p, f) => f(PathValue(recp(p))).paths
    case Space.GroundedSS(s, f) => f(SpaceValue(recs(s))).paths
    case Space.First(i, x) => recs(x).take(i)
    case Space.Last(i, x) => recs(x).takeRight(i)
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
        g.store(Node(s"Literal", sv.paths.map(_.show).mkString("\n"), "space", Vector()))
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
      case Space.TailsUnion(src) =>
        g.store(Node("TailsUnion", "", "space", Vector(recs(src))))
      case Space.TailsIntersection(src) =>
        g.store(Node("TailsIntersection", "", "space", Vector(recs(src))))
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
        rog.root = Node("Iteration", symbol.s, "space", Vector(s))
        g.store(rog)
      case Space.LeftResidual(x, y) =>
        g.store(Node("LeftResidual", "", "space", Vector(recs(x), recs(y))))
      case Space.RightResidual(y, x) =>
        g.store(Node("RightResidual", "", "space", Vector(recs(y), recs(x))))
      case Space.GroundedPS(p, f) =>
        throw NotImplementedError("grounded functions WIP")
      case Space.GroundedPS(s, f) =>
        throw NotImplementedError("grounded functions WIP")
      case Space.First(i, x) =>
        g.store(Node(s"First", i.toString, "space", Vector(recs(x))))
      case Space.Last(i, x) =>
        g.store(Node(s"Last", i.toString, "space", Vector(recs(x))))

  r.body match
//    case Space.Union(x, Space.Call(name, refs, mentions)) if name.s == r.name.s =>
      // r(a) = x(a) \/ r(g(a))  =  r(a) = x(a) \/ x(g(a)) \/ r(g(g(a)))
      // r(a) = x(a) \/ x(g(a)) \/ x(g(g(a))) \/ x(g(g(g((a)))) \/ ...
      // if monotone:  r(a) = y := {}; z := a; loop z := g(z); y' := y \/ x(z) if y' == y break else continue
      // else:         r(a) = y := {}; z := a; loop z' := g(z); if z' == z then break else z := z'; y := y \/ x(z); continue

      // monotone: r(b, a) = x(b, a) \/ r(g(b, a), f(b, a))
      //           r(b, a) = y := {}; b_ = b; a_ := a; loop a' := f(b_, a_); b' := g(b_, a_); if a' == a_ && b' == b_ then break else a_ := a'; b_ = b'; y := y \/ x(b_, a_); continue
      //           r(b, a) = y := {}; b_ = b; a_ := a; loop
      //             y := y \/ switch f(b_, a_)
      //               case `a_` => switch g(b_, a_)
      //                 case `b_` => break
      //                 case b' => x(b_, a_)
      //               case a' => switch g(b_, a_)
      //                 case `b_` => x(b_, a_)
      //                 case b' => x(b_, a_)
      // z' == z is cheap when z' := z \/ f(z)  and free when z' := identity(z)

//      (Singleton("E") \ ("E" x s).iter("h", _, Singleton(P"h"))).iter(_, _, backup)


//      val s = recs(x)
//      val rog = transpile(Routine(
//        RoutinePtr(r.name.s + "_" + name.s + g.nodes.length),
//        refs,
//        mentions,
//        x
//      ), Some(g))
//      rog.root = Node("Fixpoint", "", "space", Vector(s))
//      g.store(rog)
    case n => recs(n)
  g

def exec(rog: RecursiveOpGraph,
         stack: Stack[Array[PathValue | SpaceValue | Null]], index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): Unit =
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
          case "Call" =>
//            println(s"call ${constant} ${inputs}")
            val code = index(constant)
            val cstack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](code.nodes.length))
            for (arg, i) <- inputs.zipWithIndex do cstack.top(i) = stack(stack.length - 1 - arg._1)(arg._2)
            exec(code, cstack, index)
            cstack.top.last.asInstanceOf[SpaceValue]
          case "ExtractSpaceMention" => pos.sget // stack should already prepared
          case "Singleton" => SpaceValue(Set(inputs(0).pget))
          case "Literal" => SpaceValue(constant.linesIterator.map(Syntax.parse(_)).toSet) // should likely be translated into a union of singletons of constant paths
          case "Union" => eval(Space.Union(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Intersection" => eval(Space.Intersection(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Restriction" => eval(Space.Restriction(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Subtraction" => eval(Space.Subtraction(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Composition" => eval(Space.Composition(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Wrap" => eval(Space.Wrap(Space.Literal(inputs(0).sget), Path.Constant(inputs(1).pget)))
          case "Unwrap" => eval(Space.Unwrap(Space.Literal(inputs(0).sget), Path.Constant(inputs(1).pget)))
          case "TailsUnion" => eval(Space.TailsUnion(Space.Literal(inputs(0).sget)))
          case "TailsIntersection" => eval(Space.TailsIntersection(Space.Literal(inputs(0).sget)))
          case "Transformation" => ??? // we should likely eventually support this
          case "Iteration" => ??? // should've been elided
          case "LeftResidual" => ??? // not worth supporting
          case "RightResidual" => ??? // not worth supporting
          case "First" => eval(Space.First(constant.toInt, Space.Literal(inputs(0).sget))) // should be optimized to be integrated in Iteration
          case "Last" => eval(Space.Last(constant.toInt, Space.Literal(inputs(0).sget))) // should be optimized to be integrated in Iteration
          )
      case Right(sg: RecursiveOpGraph) =>
        val Node(op, constant, kind, inputs) = sg.root
        op match
          case "Routine" => ???
//            assert(l == 0)
//            exec(sg, stack)
//          case "FixPoint" =>
//            s(c) = SpaceValue(Set.empty)
//            while {
//              stack.push(new Array(sg.nodes.length))
//              stack.top(0) = h
//              stack.top(1) = SpaceValue(r)
//              exec(sg, stack, index)
//
//              val cstack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](code.nodes.length))
//              for (arg, i) <- inputs.zipWithIndex do cstack.top(i) = stack(stack.length - 1 - arg._1)(arg._2)
//              exec(code, cstack, index)
//              cstack.top.last.asInstanceOf[SpaceValue]
//
//              s(c) = SpaceValue(pos.sget.paths union stack.pop().last.asInstanceOf[SpaceValue].paths)
//            } do ()
          case "Iteration" =>
            s(c) = SpaceValue(Set.empty)
            for (h, r) <- inputs(0).sget.paths.groupMap(x => PathValue(x.items.head :: Nil))(x => PathValue(x.items.tail)) do
              stack.push(new Array(sg.nodes.length))
              stack.top(0) = h
              stack.top(1) = SpaceValue(Set.from(r))
              exec(sg, stack, index)
              s(c) = SpaceValue(pos.sget.paths union stack.pop().last.asInstanceOf[SpaceValue].paths)
    c += 1
  end while


def untranspile(rog: RecursiveOpGraph,
         stack: Stack[Array[Path | Space | Null]], index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): Unit =
  val l = rog.level
  var c = 0
  val s = stack.top

  inline def pos = (l, c)

  extension (p: (Int, Int)) inline def sget = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[Space]
  extension (p: (Int, Int)) inline def pget = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[Path]
  while c < rog.nodes.length do
    rog.nodes(c) match
      case Left(Node(op, constant, kind, inputs)) => kind match
        case "path" => s(c) = (op match
          case "ExtractPathRef" => Path.Deref(PathRef(constant)) // stack should already prepared
          case "Constant" => Path.Constant(Syntax.parse(constant)) // stack should already be prepared
          case "Concat" => Path.Concat(inputs(0).pget, inputs(1).pget))
        case "space" => s(c) = (op match
          case "Empty" => Space.Empty
          case "Call" =>
            //            println(s"call ${constant} ${inputs}")
            //              val code = index(constant)
            //              val cstack = collection.mutable.Stack(new Array[PathValue | SpaceValue | Null](code.nodes.length))
            //              for (arg, i) <- inputs.zipWithIndex do cstack.top(i) = stack(stack.length - 1 - arg._1)(arg._2)
            //              exec(code, cstack, index)
            //              cstack.top.last.asInstanceOf[SpaceValue]
            throw RuntimeException("not implemented call")
          case "ExtractSpaceMention" => Space.Mention(SpaceMention(constant)) // stack should already prepared
          case "Singleton" => Space.Singleton(inputs(0).pget)
          case "Literal" => ??? // should likely be translated into a union of singletons of constant paths
          case "Union" => Space.Union(inputs(0).sget, inputs(1).sget)
          case "Intersection" => Space.Intersection(inputs(0).sget, inputs(1).sget)
          case "Restriction" => Space.Restriction(inputs(0).sget, inputs(1).sget)
          case "Subtraction" => Space.Subtraction(inputs(0).sget, inputs(1).sget)
          case "Composition" => Space.Composition(inputs(0).sget, inputs(1).sget)
          case "Wrap" => Space.Wrap(inputs(0).sget, inputs(1).pget)
          case "Unwrap" => Space.Unwrap(inputs(0).sget, inputs(1).pget)
          case "TailsUnion" => Space.TailsUnion(inputs(0).sget)
          case "TailsIntersection" => Space.TailsIntersection(inputs(0).sget)
          case "Transformation" => ??? // we should likely eventually support this
          case "Iteration" => ??? // should've been elided
          case "LeftResidual" => ??? // not worth supporting
          case "RightResidual" => ??? // not worth supporting
          case "First" => Space.First(constant.toInt, inputs(0).sget) // should be optimized to be integrated in Iteration
          case "Last" => Space.Last(constant.toInt, inputs(0).sget) // should be optimized to be integrated in Iteration
          )
      case Right(sg: RecursiveOpGraph) =>
        val Node(op, constant, kind, inputs) = sg.root
        op match
          case "Routine" => ???
          case "Iteration" =>
//            println(s"constant ${constant} ${kind} ${inputs}")
//            println(s"sg ${sg.nodes} ")
            stack.push(new Array(sg.nodes.length))
            untranspile(sg, stack, index)
            val popped = stack.pop()
            s(c) = Space.Iteration(inputs(0).sget, popped(0).asInstanceOf[Path.Deref].pr, popped(1).asInstanceOf[Space.Mention].variable, popped.last.asInstanceOf[Space])
    c += 1
  end while


def graphviz_table(g: RecursiveOpGraph, path: Vector[Int] = Vector()): Unit =
  if path.isEmpty then
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
  if path.isEmpty then
    println("}")

def graphviz(g: RecursiveOpGraph, path: Vector[Int] = Vector(), show_label: Boolean = false): Unit =
  if path.isEmpty then { println("digraph G {"); println("graph [rankdir=\"LR\" compound=true];") }
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
  if path.isEmpty then println("}")


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
            ff += s"g${path.take(d).map(_.toString).mkString("_")}_f$j ---->$label g${path.map(_.toString).mkString("_")}_f$i"
          case Right(sg) =>
            val label = if show_label then s"|\"${sg.root.kind} ${k}\"|" else ""
            gf += s"g${(path.take(d) :+ j).map(_.toString).mkString("_")} --->$label g${path.map(_.toString).mkString("_")}_f$i"
        }
      case (Right(sg), i) =>
        sg.root.inputs.zipWithIndex.foreach{ case ((d, j), k) => g.lookup((d, j)) match
          case Left(n) =>
            val label = if show_label then s"|\"${n.kind} ${k}\"|" else ""
            fg += s"g${path.take(d).map(_.toString).mkString("_")}_f$j --->$label g${(path :+ i).map(_.toString).mkString("_")}"
          case Right(sg) =>
            val label = if show_label then s"|\"${sg.root.kind} ${k}\"|" else ""
            gg += s"g${(path.take(d) :+ j).map(_.toString).mkString("_")} -->$label g${(path :+ i).map(_.toString).mkString("_")}"
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
    case Left(n) =>
      val (l2, i) = g.find(m => m.map((lm, xm) => stack(lm)._1(xm)) == n.map((ln, xn) => stack(ln)._1(xn))).get
      if (l, i) == (l2, j) then
        r.store(n.map((l, x) => { val (l_, x_) = stack(l)._1(x); stack(l_)._2(x_) }))
        stack(l2)._2.update(i, l -> c)
        c += 1
      else
        stack.last._1.update(j, l2 -> i)
    case Right(sg) => // todo share subgraphs (via meaning propagation and structural hashing)
      r.store(optimize_sharing(sg, stack))
      stack(l)._2.update(j, l -> c)
      c += 1
  r.root = r.root.map((l, x) => { val (l_, x_) = stack(l)._1(x); stack(l_)._2(x_) })
  stack.remove(stack.length - 1)
  r


def push_out(g: RecursiveOpGraph, stack: ArrayBuffer[LongMap[(Int, Int)]] = ArrayBuffer.empty, parent: Option[RecursiveOpGraph] = None): RecursiveOpGraph =
  val r = RecursiveOpGraph(g.root, parent, ArrayBuffer.empty)
  val lb = g.level
  var jb = 0
  var added = 0

  def pred(g: RecursiveOpGraph, n: Node[(Int, Int)], pos: (Int, Int), gather: Boolean): Boolean =
    (pos._2 != g.nodes.length - 1) &&
    n.inputs.forall((l, x) => l < pos._1 && (stack(l)(x)._1 < lb || (stack(l)(x)._1 == lb && stack(l)(x)._2 < jb))) &&
    !n.operation.startsWith("Extract")

  def gather(g: RecursiveOpGraph, r: RecursiveOpGraph): Unit =
    val lr = g.level
    if lr == stack.length then
      stack.addOne(LongMap.withDefault[(Int, Int)](x => lr -> x.toInt))
      added += 1
    assert(lr < stack.length)

    for (n_sg, j) <- g.nodes.zipWithIndex do n_sg match
      case Left(n) =>
        if pred(g, n, lr -> j, true) then
          val value = r.store(n)
//          assert(!stack(lr).contains(j), s"pos: ${lr -> j} current: ${stack(lr)(j)} new: $value node: $n")
          stack(lr)(j) = value
      case Right(sg) =>
        gather(sg, r)
//    if lr == stack.length - 1 then
//      stack.dropRightInPlace(1)

  stack.addOne(LongMap.withDefault[(Int, Int)](x => lb -> x.toInt))
  for (n_sg, j) <- g.nodes.zipWithIndex do n_sg match
    case Left(n) =>
      if !stack(lb).contains(j) then
        stack(lb)(j) = r.store(n)
//      else
//        println(s"not storing ${n.show} because stack($lb)($j)=${stack(lb)(j)}")
    case Right(sg) =>
      jb = j
      added = 0
      gather(sg, r)
      stack(lb)(j) = r.store(push_out(sg, stack, Some(r)))
      stack.dropRightInPlace(added)

  r.nodes.mapInPlace{
    case Left(n) => Left(n.map((l, x) => stack(l)(x)))
    case Right(sg) =>
      sg.root = sg.root.map((l, x) => stack(l)(x))
      Right(sg)
  }
  stack.dropRightInPlace(1)
  r

def all_forever(s: Space, mappings: List[Space => Space] = Nil): Space =
  val s_ = mappings.foldLeft(s)((s, f) => f(s))
  if s.show == s_.show then s
  else all_forever(s_, mappings)

def optimize(g: RecursiveOpGraph): RecursiveOpGraph =
  val g_ = optimize_sharing(push_out(g))
  if g.show == g_.show then g
  else optimize(g_)


object Reflect:
  def code_to_space(s: Space): SpaceValue =
    import Syntax.parse
    def recp(x: Path): Set[PathValue] = x match
      case Path.Deref(pr) => Set[PathValue](f"Deref.${pr.s}")
      case Path.Constant(pi) => Set[PathValue](f"Constant.${pi.show}")
      case Path.Concat(l, r) =>
        (for p <- recp(l) yield PathValue(PathItem.Symbol("Concat")::PathItem.Symbol("lhs")::p.items)) union
        (for p <- recp(r) yield PathValue(PathItem.Symbol("Concat")::PathItem.Symbol("rhs")::p.items))
      case Path.GroundedPP(p, f) => ???
      case Path.GroundedSP(s, f) => ???

    def recs(x: Space): Set[PathValue] = x match
      case Space.Empty => Set("Empty")
      case Space.Call(rp, refs, mentions) =>
        Set[PathValue](f"Call.routine.${rp.s}") union
        (for (pd, i) <- refs.zipWithIndex; pp <- recp(pd) yield PathValue(PathItem.Symbol("Call")::PathItem.Symbol("path")::PathItem.Symbol(i.toString)::pp.items)).toSet union
        (for (sd, i) <- mentions.zipWithIndex; sp <- recs(sd) yield PathValue(PathItem.Symbol("Call")::PathItem.Symbol("space")::PathItem.Symbol(i.toString)::sp.items)).toSet
      case Space.Mention(p) => Set(f"Mention.${p.s}")
      case Space.Singleton(p) => Set(f"Singleton.${p.pretty}")
      case Space.Literal(SpaceValue(ps)) => for pp <- ps yield PathValue(PathItem.Symbol("Literal")::pp.items)
      case Space.Union(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem.Symbol("Union")::pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem.Symbol("Union")::pp.items))
      case Space.Intersection(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem.Symbol("Intersection")::pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem.Symbol("Intersection")::pp.items))
      case Space.Subtraction(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem.Symbol("Subtraction")::PathItem.Symbol("domain")::pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem.Symbol("Subtraction")::PathItem.Symbol("argument")::pp.items))
      case Space.Restriction(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem.Symbol("Restriction") :: PathItem.Symbol("domain") :: pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem.Symbol("Restriction") :: PathItem.Symbol("argument") :: pp.items))
      case Space.Raffination(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem.Symbol("Raffination") :: PathItem.Symbol("domain") :: pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem.Symbol("Raffination") :: PathItem.Symbol("argument") :: pp.items))
      case Space.Composition(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem.Symbol("Composition") :: PathItem.Symbol("domain") :: pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem.Symbol("Composition") :: PathItem.Symbol("argument") :: pp.items))
      case Space.Wrap(x, p_e) =>
        (for pp <- recp(p_e) yield PathValue(PathItem.Symbol("Wrap") :: PathItem.Symbol("prefix") :: pp.items)) union
        (for pp <- recs(x) yield PathValue(PathItem.Symbol("Wrap") :: PathItem.Symbol("domain") :: pp.items))
      case Space.Unwrap(x, p_e) =>
        (for pp <- recp(p_e) yield PathValue(PathItem.Symbol("Unwrap") :: PathItem.Symbol("prefix") :: pp.items)) union
        (for pp <- recs(x) yield PathValue(PathItem.Symbol("Unwrap") :: PathItem.Symbol("domain") :: pp.items))
      case Space.TailsUnion(x) =>
        for pp <- recs(x) yield PathValue(PathItem.Symbol("TailsUnion") :: pp.items)
      case Space.TailsIntersection(x) =>
        for pp <- recs(x) yield PathValue(PathItem.Symbol("TailsIntersection") :: pp.items)
      case Space.Transformation(src_e, pattern, template) => ???
      case Space.Iteration(x, symbol, rest, templates) =>
        Set[PathValue](f"Iteration.head.${symbol.s}", f"Iteration.tail.${rest.s}") union
        (for sp <- recs(x) yield PathValue(PathItem.Symbol("Iteration")::PathItem.Symbol("domain")::sp.items)) union
        (for sp <- recs(templates) yield PathValue(PathItem.Symbol("Iteration")::PathItem.Symbol("templates")::sp.items))
      case Space.LeftResidual(x_e, y_e) => ???
      case Space.RightResidual(y_e, x_e) => ???
      case Space.GroundedPS(p, f) => ???
      case Space.GroundedSS(s, f) => ???
      case Space.First(i, x) => ???
      case Space.Last(i, x) => ???

    SpaceValue(recs(s))

def collect[S, P](s: Space)(spre: PartialFunction[Space, S] = PartialFunction.empty,
                   ppre: PartialFunction[Path, P] = PartialFunction.empty): (Vector[(Space, S)], Vector[(Path, P)]) =
  var ss = Vector.newBuilder[(Space, S)]
  var pp = Vector.newBuilder[(Path, P)]
  def recp(x: Path): Path = x match
    case ppre(p) => pp addOne (x, p); x
    case Path.Deref(pr) => Path.Deref(pr)
    case Path.Constant(pi) => Path.Constant(pi)
    case Path.Concat(l, r) => Path.Concat(recp(l), recp(r))
    case Path.GroundedPP(p, f) => ???
    case Path.GroundedSP(s, f) => ???
    case x => x
  def recs(x: Space): Space = x match
    case spre(s) => ss addOne (x, s); x
    case Space.Empty => Space.Empty
    case Space.Call(rp, refs, mentions) => Space.Call(rp, refs.map(recp), mentions.map(recs))
    case Space.Mention(p) => Space.Mention(p)
    case Space.Singleton(p) => Space.Singleton(recp(p))
    case Space.Literal(sv) => Space.Literal(sv)
    case Space.Union(x, y) => Space.Union(recs(x), recs(y))
    case Space.Intersection(x, y) => Space.Intersection(recs(x), recs(y))
    case Space.Subtraction(x, y) => Space.Subtraction(recs(x), recs(y))
    case Space.Restriction(x_e, prefixes_e) => Space.Restriction(recs(x_e), recs(prefixes_e))
    case Space.Composition(x, y) => Space.Composition(recs(x), recs(y))
    case Space.Wrap(src_e, p_e) =>  Space.Wrap(recs(src_e), recp(p_e))
    case Space.Unwrap(src_e, p_e) => Space.Unwrap(recs(src_e), recp(p_e))
    case Space.TailsUnion(src_e) => Space.TailsUnion(recs(src_e))
    case Space.TailsIntersection(src_e) => Space.TailsIntersection(recs(src_e))
    case Space.Transformation(src_e, pattern, template) => Space.Transformation(recs(src_e), recp(pattern), recp(template))
    case Space.Iteration(src_e, symbol, rest, templates) => Space.Iteration(recs(src_e), symbol, rest, recs(templates))
    case Space.LeftResidual(x_e, y_e) =>  Space.LeftResidual(recs(x_e), recs(y_e))
    case Space.RightResidual(y_e, x_e) => Space.RightResidual(recs(y_e), recs(x_e))
    case Space.GroundedPS(p, f) => ???
    case Space.GroundedSS(s, f) => ???
    case Space.First(i, x) => Space.First(i, recs(x))
    case Space.Last(i, x) => Space.Last(i, recs(x))
    case x => x
  recs(s)
  (ss.result(), pp.result())


def subs(s: Space)(spre: PartialFunction[Space, Space] = PartialFunction.empty,
                   spost: PartialFunction[Space, Space] = PartialFunction.empty,
                   ppre: PartialFunction[Path, Path] = PartialFunction.empty,
                   ppost: PartialFunction[Path, Path] = PartialFunction.empty): Space =
  def recp(x: Path): Path = ppost.applyOrElse(x match
    case ppre(p) => p
    case Path.Deref(pr) => x
    case Path.Constant(pi) => x
    case Path.Concat(l, r) => Path.Concat(recp(l), recp(r))
    case Path.GroundedPP(p, f) => ???
    case Path.GroundedSP(s, f) => ???, x => x)
  def recs(x: Space): Space = spost.applyOrElse(x match
    case spre(s) => s
    case Space.Empty => x
    case Space.Call(rp, refs, mentions) => Space.Call(rp, refs.map(recp), mentions.map(recs))
    case Space.Mention(p) => x
    case Space.Singleton(p) => Space.Singleton(recp(p))
    case Space.Literal(sv) => x
    case Space.Union(x, y) => Space.Union(recs(x), recs(y))
    case Space.Intersection(x, y) => Space.Intersection(recs(x), recs(y))
    case Space.Raffination(x, y) => Space.Raffination(recs(x), recs(y))
    case Space.Subtraction(x, y) => Space.Subtraction(recs(x), recs(y))
    case Space.Restriction(x_e, prefixes_e) => Space.Restriction(recs(x_e), recs(prefixes_e))
    case Space.Composition(x, y) => Space.Composition(recs(x), recs(y))
    case Space.Wrap(src_e, p_e) =>  Space.Wrap(recs(src_e), recp(p_e))
    case Space.Unwrap(src_e, p_e) => Space.Unwrap(recs(src_e), recp(p_e))
    case Space.TailsUnion(src_e) => Space.TailsUnion(recs(src_e))
    case Space.TailsIntersection(src_e) => Space.TailsIntersection(recs(src_e))
    case Space.Transformation(src_e, pattern, template) => Space.Transformation(recs(src_e), recp(pattern), recp(template))
    case Space.Iteration(src_e, symbol, rest, templates) => Space.Iteration(recs(src_e), symbol, rest, recs(templates))
    case Space.LeftResidual(x_e, y_e) =>  Space.LeftResidual(recs(x_e), recs(y_e))
    case Space.RightResidual(y_e, x_e) => Space.RightResidual(recs(y_e), recs(x_e))
    case Space.GroundedPS(p, f) => ???
    case Space.GroundedSS(s, f) => ???
    case Space.First(i, x) => Space.First(i, recs(x))
    case Space.Last(i, x) => Space.Last(i, recs(x)),
    x => x)
  recs(s)

object Lower:
  val TailsUnion_Iteration = subs(_: Space)(PartialFunction.empty, {
    case Space.TailsUnion(src) =>
      val name = SpaceMention("s" + src.hashCode().toHexString)
      Space.Iteration(src, PathRef("_"), name, Space.Mention(name))
  })

  val Literal_ConstantsUnion = subs(_: Space)(PartialFunction.empty, {
    case Space.Literal(SpaceValue(paths)) =>
      paths.map(p => Space.Singleton(Path.Constant(p))).reduce(Space.Union(_, _))
  })

  val IterateLiteral_Union = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(Space.Literal(SpaceValue(paths)), symbol, rest, template) =>
      paths.map(p => subs(template)(spre={ case Space.Mention(`rest`) => Space.Singleton(Path.Constant(PathValue(p.items.tail))) },
                                    ppre={ case Path.Deref(`symbol`) => Path.Constant(PathValue(p.items.head::Nil)) }))
        .reduce(Space.Union(_, _))
  })

  val IterateSingleton_Deref = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(Space.Singleton(Path.first((Path.Deref(spr), rest))), pr, sm, body) if spr.lengthHint == 1 =>
      subs(body)(spost={ case Space.Mention(`sm`) => if rest.isEmpty then Space.Empty else Space.Singleton(Path.fromFactors(rest)) },
                 ppost={ case Path.Deref(`pr`) => Path.Deref(spr) })
    case Space.Iteration(Space.Singleton(Path.first((Path.Constant(PathValue(Nil)), rest))), pr, sm, body) => if rest.isEmpty then Space.Empty else
      Space.Iteration(Space.Singleton(Path.fromFactors(rest)), pr, sm, body)
    case Space.Iteration(Space.Singleton(Path.first((Path.Constant(PathValue(h::tail)), rest))), pr, sm, body) =>
      subs(body)(spost={ case Space.Mention(`sm`) => if tail.isEmpty then (if rest.isEmpty then Space.Empty else Space.Singleton(Path.fromFactors(rest)))
                                                     else Space.Singleton(Path.fromFactors(Path.Constant(PathValue(tail))::rest)) },
                 ppost={ case Path.Deref(`pr`) => Path.Constant(PathValue(h::Nil)) })
  })

  val SingletonConst_Literal = subs(_: Space)(PartialFunction.empty, {
    case Space.Singleton(Path.Constant(p)) => Space.Literal(SpaceValue(Set(p)))
  })

  val LiteralSpaceOps = subs(_: Space)(spost = {
    case op @ Space.Composition(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Union(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Intersection(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Subtraction(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Restriction(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Raffination(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.First(_, Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Last(_, Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.TailsUnion(Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.TailsIntersection(Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Wrap(Space.Literal(_), Path.Constant(_)) => Space.Literal(eval(op))
    case op @ Space.Unwrap(Space.Literal(_), Path.Constant(_)) => Space.Literal(eval(op))
  })

  val ConstantOps = subs(_: Space)(spost = {
    case op if {
      try
        eval(op)
        true
      catch case e => false
    } => Space.Literal(eval(op))
  })

  val Concat_Path = subs(_: Space)(ppost = {
    case Path.Concat(Path.Constant(PathValue(xs)), Path.Constant(PathValue(ys))) =>
      Path.Constant(PathValue(xs ++ ys))
  })

  val IterUnion_Indep = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if {
      val (soc, poc) = collect(lhs)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () })
      soc.isEmpty && poc.isEmpty
    } => Space.Union(Space.Iteration(src, symbol, rest, rhs), lhs)
    case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if {
      val (soc, poc) = collect(rhs)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () })
      soc.isEmpty && poc.isEmpty
    } => Space.Union(Space.Iteration(src, symbol, rest, lhs), rhs)
  })

  val UnwrapConcat_Unwraps = subs(_: Space)(PartialFunction.empty, {
    case Space.Unwrap(src, Path.Concat(l, r)) => Space.Unwrap(Space.Unwrap(src, r), l)
  })

  val SingletonSpaceOp_PathOp = subs(_: Space)(PartialFunction.empty, {
    case Space.Wrap(Space.Singleton(y), x) => Space.Singleton(Path.Concat(x, y))
  })

  val SingletonComposition_Wrap = subs(_: Space)(PartialFunction.empty, {
    case Space.Composition(Space.Singleton(x), y) => Space.Wrap(y, x)
  })

  val ConcatSingleton_Iter = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, symbol, rest, Space.Singleton(Path.Concat(p, q))) if {
      val (soc, poc) = collect(Space.Singleton(p))({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () })
      soc.isEmpty && poc.isEmpty
    } => Space.Wrap(Space.Iteration(src, symbol, rest, Space.Singleton(q)), p)
  })

  val Wrap_Iter = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, symbol, rest, Space.Wrap(s, p)) if {
      val (soc, poc) = collect(Space.Singleton(p))({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () })
      soc.isEmpty && poc.isEmpty
    } => Space.Wrap(Space.Iteration(src, symbol, rest, s), p)
  })

  val Iter_Ident = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, symbol, rest, Space.Wrap(Space.Mention(sm), Path.Deref(pr))) if symbol == pr && sm == rest
    => src
  })

  val inline = (ctx: PartialFunction[RoutinePtr, Routine]) ?=> subs(_: Space)(spost = {
    case Space.Call(ctx(r), refs, mentions) =>
      val refmap = (r.refs zip refs).toMap
      val mentionmap = (r.mentions zip mentions).toMap
      subs(r.body)(PartialFunction.empty,
        spost = { case Space.Mention(mentionmap(rhs)) => rhs },
        ppost = { case Path.Deref(refmap(rhs)) => rhs })
  })
end Lower


def itypes(s: Space): SpaceValue =
  // > Foo*$foos | Bar*Baz*$bars = S
  // $foos = Foo^ * S
  // $bars = (Bar * Baz)^ * S = Baz^ * Bar^ * S
  // > Point3D*(x*f32*$x | y*f32*$y | z*f32*$z) = S
  // $x = f32^ * x^ * Point3D^ * S
  // $y = f32^ * y^ * Point3D^ * S
  // $z = f32^ * z^ * Point3D^ * S
  // >>
  def recp(x: Path): PathValue = x match
    case Path.Deref(pr) => PathValue(PathItem.Variable(pr.s)::Nil)
    case Path.Constant(pi) => pi
    case Path.Concat(l, r) => PathValue(recp(l).items ++ recp(r).items)
    case Path.GroundedPP(p, f) => ???
    case Path.GroundedSP(s, f) => ???

  import Syntax.x
  def recs(x: Space): Set[PathValue] = x match
    case Space.Empty =>  Set.empty
    case Space.Call(r, refs, mentions) =>
      val refts = refs.foldLeft(Set.empty[PathValue])((a, p) => a.incl(recp(p)))
      mentions.foldLeft(refts)((a, s) => a.union(recs(s)))
    case Space.Mention(sm) => Set(PathValue(PathItem.Variable(sm.s)::Nil))
    case Space.Singleton(p) => Set(recp(p))
    case Space.Literal(sv) => Set.empty
    case Space.Union(x, y) => recs(x) union recs(y)
//    case Space.Intersection(x, y) => recs(x) union recs(y)
    case Space.Intersection(x, y) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue(PathItem.Variable("_")::Nil))),
                                                      Space.Literal(SpaceValue(recs(y))) x Space.Singleton(Path.Constant(PathValue(PathItem.Variable("_")::Nil))))).paths
    case Space.Subtraction(x, y) => recs(x) union recs(y)
//    case Space.Restriction(x, prefixes) => recs(x) union recs(prefixes)
    case Space.Restriction(x, prefixes) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue(PathItem.Variable("_")::Nil))),
      Space.Literal(SpaceValue(recs(prefixes))))).paths
    case Space.Composition(x, y) => recs(x) union recs(y)
    case Space.Wrap(src, p) => recs(src) // .incl(recp(p))
    case Space.Unwrap(src, p) => eval(Space.Composition(Space.Literal(SpaceValue(recs(src))), Space.Singleton(Path.Constant(recp(p))))).paths
    case Space.TailsUnion(src) => ???
    case Space.TailsIntersection(src) => ???
    case Space.Transformation(src, pattern, template) => ??? //recs(src) x pattern
    case Space.Iteration(src, symbol, rest, templates) =>
      import Syntax.*
      val srcs = Space.Literal(SpaceValue(recs(src)))
      val sv = PathValue(PathItem.Variable(symbol.s)::Nil)
      val sr = PathValue(PathItem.Variable(rest.s)::Nil)
      val ts = Space.Literal(SpaceValue(recs(templates)))

      println(s"${srcs.show}.iter(${sv.show}:${sr.show} => ${ts.show})")
//      println(s"calc ${eval(srcs x Space.Singleton(Path.Constant(sv)) x ts(Path.Constant(sr))).show}")
      val res = eval(
        (if rest.s != "_" then (srcs x ts(Path.Constant(sv)) x ts(Path.Constant(sr))) else Space.Empty) \/


        (srcs x ts(Path.Constant(sv))) \/
        srcs
        \/ (ts \| Space.Literal(SpaceValue(Set(sv, sr)))))
      println(s"res ${res.show}")
      res.paths
    case Space.LeftResidual(x, y) => recs(x) union recs(y)
    case Space.RightResidual(y, x) => recs(y) union recs(x)
    case Space.GroundedPS(p, f) => ???
    case Space.GroundedSS(s, f) => ???
    case Space.First(i, x) => recs(x)
    case Space.Last(i, x) => recs(x)
  SpaceValue(recs(s))

def otypes(s: Space): SpaceValue =
  def recp(x: Path): PathValue = x match
    case Path.Deref(pr) => PathValue(PathItem.Variable(pr.s)::Nil)
    case Path.Constant(pi) => pi
    case Path.Concat(l, r) => PathValue(recp(l).items ++ recp(r).items)
    case Path.GroundedPP(p, f) => ???
    case Path.GroundedSP(s, f) => ???

  import Syntax.x
  def recs(x: Space): Set[PathValue] = x match
    case Space.Empty =>  Set.empty
    case Space.Call(r, refs, mentions) =>
      val refts = refs.foldLeft(Set.empty[PathValue])((a, p) => a.incl(recp(p)))
      mentions.foldLeft(refts)((a, s) => a.union(recs(s)))
    case Space.Mention(sm) => Set(PathValue(PathItem.Variable(sm.s)::Nil))
    case Space.Singleton(p) => Set(recp(p))
    case Space.Literal(sv) => Set.empty
    case Space.Union(x, y) => recs(x) union recs(y)
//    case Space.Intersection(x, y) => recs(x) union recs(y)
    case Space.Intersection(x, y) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue(PathItem.Variable("_")::Nil))),
                                                      Space.Literal(SpaceValue(recs(y))) x Space.Singleton(Path.Constant(PathValue(PathItem.Variable("_")::Nil))))).paths
    case Space.Subtraction(x, y) => recs(x) union recs(y)
//    case Space.Restriction(x, prefixes) => recs(x) union recs(prefixes)
    case Space.Restriction(x, prefixes) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue(PathItem.Variable("_")::Nil))),
      Space.Literal(SpaceValue(recs(prefixes))))).paths
    case Space.Composition(x, y) => recs(x) union recs(y)
    case Space.Wrap(src, p) => eval(Space.Composition(Space.Singleton(Path.Constant(recp(p))), Space.Literal(SpaceValue(recs(src))))).paths
    case Space.Unwrap(src, p) => recs(src) // .incl(recp(p))
    case Space.TailsUnion(src) => ???
    case Space.TailsIntersection(src) => ???
    case Space.Transformation(src, pattern, template) => ??? //recs(src) x pattern
    case Space.Iteration(src, symbol, rest, templates) =>
      recs(templates)
    case Space.LeftResidual(x, y) => recs(x) union recs(y)
    case Space.RightResidual(y, x) => recs(y) union recs(x)
    case Space.GroundedPS(p, f) => ???
    case Space.GroundedSS(s, f) => ???
    case Space.First(i, x) => recs(x)
    case Space.Last(i, x) => recs(x)
  SpaceValue(recs(s))

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
    def \|(y: Space) = Space.Raffination(x, y)
    infix def x(y: Space) = Space.Composition(x, y)
    def apply(p: Path) = Space.Unwrap(x, p)
    infix def transform(lhs: Path, rhs: Path): Space = Space.Transformation(x, lhs, rhs)
    infix def iter(h: Path.Deref, t: Space.Mention, rhs: Space): Space = Space.Iteration(x, h.pr.known(1), t.variable, subs(rhs)(ppre = { case `h` => Path.Deref(h.pr.known(1)) }))
    infix def iter(h2: (Path.Deref, Path.Deref), t: Space.Mention, rhs: Space): Space =
      val sm = SpaceMention(s"r${h2._2.pr.s}${rhs.hashCode().toHexString}")
      Space.Iteration(x, h2._1.pr.known(1), sm, Space.Iteration(Space.Mention(sm), h2._2.pr.known(1), t.variable,
        subs(rhs)(ppre = { case Path.Deref(pr) if pr == h2._1.pr || pr == h2._2.pr => Path.Deref(pr.known(1)) })))
    infix def iter(h3: (Path.Deref, Path.Deref, Path.Deref), t: Space.Mention, rhs: Space): Space =
      val sm2 = SpaceMention(s"r${h3._2.pr.s}${rhs.hashCode().toHexString}")
      val sm3 = SpaceMention(s"r${h3._3.pr.s}${rhs.hashCode().toHexString}")
      Space.Iteration(x, h3._1.pr.known(1), sm2,
        Space.Iteration(Space.Mention(sm2), h3._2.pr.known(1), sm3,
          Space.Iteration(Space.Mention(sm3), h3._3.pr.known(1), t.variable,
            subs(rhs)(ppre = { case Path.Deref(pr) if pr == h3._1.pr || pr == h3._2.pr || pr == h3._3.pr => Path.Deref(pr.known(1)) }))))
    infix def iter(h4: (Path.Deref, Path.Deref, Path.Deref, Path.Deref), t: Space.Mention, rhs: Space): Space =
      val sm2 = SpaceMention(s"r${h4._2.pr.s}${rhs.hashCode().toHexString}")
      val sm3 = SpaceMention(s"r${h4._3.pr.s}${rhs.hashCode().toHexString}")
      val sm4 = SpaceMention(s"r${h4._4.pr.s}${rhs.hashCode().toHexString}")
      Space.Iteration(x, h4._1.pr.known(1), sm2,
        Space.Iteration(Space.Mention(sm2), h4._2.pr.known(1), sm3,
          Space.Iteration(Space.Mention(sm3), h4._3.pr.known(1), sm4,
            Space.Iteration(Space.Mention(sm4), h4._4.pr.known(1), t.variable,
              subs(rhs)(ppre = { case Path.Deref(pr) if pr == h4._1.pr || pr == h4._2.pr || pr == h4._3.pr || pr == h4._4.pr => Path.Deref(pr.known(1)) })))))
    infix def iterk(k: Int, t: Space.Mention, rhs: Path => Space): Space =
      val rhsh = rhs.hashCode().toHexString
      val prs = Vector.tabulate(k)(i => PathRef(s"${i}h$rhsh").known(1))
      val sms = Vector.tabulate(k)(i => if i != k - 1 then SpaceMention(s"r${i}h$rhsh") else t.variable)
      val ss = Vector.tabulate(k)(i => if i == 0 then x else Space.Mention(sms(i-1)))
      def rec(i: Int): Space =
        if i == k then
          subs(rhs(Path.fromFactors(prs.map(Path.Deref(_): Path.Deref))))(spost = {
            case Space.Mention(sm) if sm.s == t.variable.s && k == 0 => x
          })
        else
          Space.Iteration(ss(i), prs(i), sms(i), rec(i + 1))
      val res = rec(0)
//      if rhs(Path.ZERO) != Space.Empty then println(s"iter${k} wrapper=${Space.Empty.iterk(k, t, {case _ => Space.Empty}).show}")
      res
    infix def fold(initial: Path, acc: String, symbol: String, rest: String, rhs: Space, update: Path): Space =
      Space.Fold(x, initial, PathRef(acc), PathRef(symbol), SpaceMention(rest), rhs, update)
    def :\(y: Space) = Space.RightResidual(x, y)
    def /:(y: Space) = Space.LeftResidual(x, y)
    def iterh(h: Path.Deref, run: Space): Space = x.iter(h, S"_", run)
    def itert(t: Space.Mention, run: Space): Space = x.iter(P"_", t, run)
    def tee(run: Space): Space = x.iter(P"_", S"_", run)
    def on_empty(todo: Space): Space = (ss"tobeempty" \ head(ss"tobeempty" x x)).tee(todo)
    def :=(s: Space) = x match
      case Space.Call(rp, refs, mentions) => Routine(rp, refs.map { case Path.Deref(pr) => pr }, mentions.map { case Space.Mention(sm) => sm }, s)

  extension (st: SpaceValue.type)
    def apply(ps: PathValue*): SpaceValue = SpaceValue(Set.from(ps))

  extension (rp: RoutinePtr)
    def apply() = Space.Call(rp, Vector(), Vector())
    def apply(r0: Path) = Space.Call(rp, Vector(r0), Vector())
    def apply(r0: Path, r1: Path) = Space.Call(rp, Vector(r0, r1), Vector())
    def apply(r0: Path, r1: Path, r2: Path) = Space.Call(rp, Vector(r0, r1, r2), Vector())
    def apply(m0: Space) = Space.Call(rp, Vector(), Vector(m0))
    def apply(m0: Space, m1: Space) = Space.Call(rp, Vector(), Vector(m0, m1))
    def apply(m0: Space, m1: Space, m2: Space) = Space.Call(rp, Vector(), Vector(m0, m1, m2))

    def apply(r0: Path, m0: Space) = Space.Call(rp, Vector(r0), Vector(m0))
    def apply(r0: Path, m0: Space, m1: Space) = Space.Call(rp, Vector(r0), Vector(m0, m1))
    def apply(r0: Path, m0: Space, m1: Space, m2: Space) = Space.Call(rp, Vector(r0), Vector(m0, m1, m2))

    def apply(r0: Path, r1: Path, m0: Space) = Space.Call(rp, Vector(r0, r1), Vector(m0))
    def apply(r0: Path, r1: Path, m0: Space, m1: Space) = Space.Call(rp, Vector(r0, r1), Vector(m0, m1))
    def apply(r0: Path, r1: Path, m0: Space, m1: Space, m2: Space) = Space.Call(rp, Vector(r0, r1), Vector(m0, m1, m2))

    def apply(r0: Path, r1: Path, r2: Path, m0: Space) = Space.Call(rp, Vector(r0, r1, r2), Vector(m0))
    def apply(r0: Path, r1: Path, r2: Path, m0: Space, m1: Space) = Space.Call(rp, Vector(r0, r1, r2), Vector(m0, m1))
    def apply(r0: Path, r1: Path, r2: Path, m0: Space, m1: Space, m2: Space) = Space.Call(rp, Vector(r0, r1, r2), Vector(m0, m1, m2))

  extension (inline sc: StringContext)
    inline def S(inline args: Any*): Space.Mention =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Space.Mention(SpaceMention(k))

  extension (inline sc: StringContext)
    inline def P(inline args: Any*): Path.Deref =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Path.Deref(PathRef(k))

  extension (inline sc: StringContext)
    inline def R(inline args: Any*): RoutinePtr =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      RoutinePtr(k)

  extension (inline sc: StringContext)
    inline def ss(inline args: Any*): Space.Singleton =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Space.Singleton(Path.Constant(parse(k)))

  extension (inline sc: StringContext)
    inline def sP(inline args: Any*): Space.Singleton =
      val k = StringContext.standardInterpolator(identity, args, sc.parts)
      Space.Singleton(Path.Deref(PathRef(k)))

  def s(args: PathValue*): Space = Space.Literal(SpaceValue(Set.from(args)))
  def head(s: Space): Space = s.iterh(P"h", sP"h")
  def \/(s: Space): Space = Space.TailsUnion(s)
  def /\(s: Space): Space = Space.TailsIntersection(s)
  def mod(rs: Routine*): PartialFunction[RoutinePtr, Routine] = ((rp: RoutinePtr) => rs.find(_.name == rp)).unlift
