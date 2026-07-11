import scala.util.{Random, Try}
import scala.collection.mutable.{ArrayBuffer, LongMap, Stack}
import scala.collection.Searching
import java.util.Base64
import java.util.Locale
import java.nio.charset.StandardCharsets
import scala.language.implicitConversions


opaque type PathItem = String

object PathItem:
  def apply(n: String): PathItem = n
  def unapply(item: PathItem): Some[String] = Some(item)
  def variable(n: String): PathItem = "$" + n
  private def variableNameOf(item: PathItem): Option[String] =
    val s: String = item
    if s.startsWith("$") && s.length > 1 then Some(s.tail) else None

  given Conversion[String, PathItem] = apply

  extension (item: PathItem)
    def show: String = item
    def isVariable: Boolean = variableNameOf(item).isDefined
    def variableName: Option[String] = variableNameOf(item)

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
      case (xItem::this_tail, yItem::that_tail) if xItem.variableName.isDefined && yItem.variableName.isDefined =>
        val x = xItem.variableName.get
        val y = yItem.variableName.get
        bound.get(x) match
          case Some(y_analog) =>
            val v = PathItem.variable(y_analog)
            PathValue(v::(PathValue(this_tail).renameFrom(PathValue(that_tail), bound)).items)
          case None =>
            val v = PathItem.variable(x)
            if bound.exists((_, y_) => y == y_) then
              PathValue(v::(PathValue(this_tail).renameFrom(PathValue(that_tail), bound)).items)
            else
              PathValue(PathItem.variable(y)::(PathValue(this_tail).renameFrom(PathValue(that_tail), bound + (x -> y))).items)
      case (v::this_tail, _::that_tail) =>
        PathValue(v::(PathValue(this_tail).renameFrom(PathValue(that_tail), bound)).items)
      case (Nil, _) => PathValue(Nil)
      case (rest, Nil) => PathValue(rest.map(x => x.variableName.fold(x)(v => PathItem.variable(bound.getOrElse(v, v)))))


class PathContext:
  def resolve(pr: PathRef): PathValue = throw RuntimeException(s"$pr path ref not resolved")
  def bind(pr: PathRef, value: PathValue): PathContext =
    if pr.s == "_" then this else PathContextOverlay(this, pr, value)
  def grown(pv: Map[PathRef, PathValue]): PathContext =
    throw RuntimeException("PathContext.grown is unsupported by this context")

case class PathContextMap(m: Map[PathRef, PathValue]) extends PathContext:
  override def resolve(pr: PathRef): PathValue =
    try
      m(pr)
    catch
      case e: java.util.NoSuchElementException =>
//        println(s"$pr not in $m")
        throw e
  override def grown(pv: Map[PathRef, PathValue]): PathContext =
    pv.iterator.foldLeft(this: PathContext)((ctx, kv) => ctx.bind(kv._1, kv._2))

case class PathContextOverlay(parent: PathContext, key: PathRef, value: PathValue) extends PathContext:
  override def resolve(pr: PathRef): PathValue =
    if pr == key then value else parent.resolve(pr)
  override def grown(pv: Map[PathRef, PathValue]): PathContext =
    pv.iterator.foldLeft(this: PathContext)((ctx, kv) => ctx.bind(kv._1, kv._2))

object PathContext:
  val emptyMap: PathContextMap = PathContextMap(Map())

  def mixed(seed: Long = 0): PathContext = new PathContext:
    private val rng = Random(seed)
    override def resolve(pr: PathRef): PathValue = PathValue(PathItem(pr.s + "_" + Base64.getEncoder.encodeToString(rng.nextBytes(4)).take(4))::Nil)

object GraphFoldTags:
  val Body: PathValue = PathValue(PathItem("#fold_body") :: Nil)
  val Update: PathValue = PathValue(PathItem("#fold_update") :: Nil)

class SpaceContext:
  def resolve(pv: SpaceMention): SpaceValue = throw RuntimeException(s"$pv space mention not resolved")
  def bind(sm: SpaceMention, value: SpaceValue): SpaceContext =
    if sm.s == "_" then this else SpaceContextOverlay(this, sm, value)
  def grown(pv: Map[SpaceMention, SpaceValue]): SpaceContext =
    throw RuntimeException("SpaceContext.grown is unsupported by this context")


case class SpaceContextMap(m: Map[SpaceMention, SpaceValue]) extends SpaceContext:
  override def resolve(pr: SpaceMention): SpaceValue =
    try
      m(pr)
    catch
      case e: java.util.NoSuchElementException =>
//        println(s"$pr not in $m")
        throw e

  override def grown(pv: Map[SpaceMention, SpaceValue]): SpaceContext =
    pv.iterator.foldLeft(this: SpaceContext)((ctx, kv) => ctx.bind(kv._1, kv._2))

case class SpaceContextOverlay(parent: SpaceContext, key: SpaceMention, value: SpaceValue) extends SpaceContext:
  override def resolve(pr: SpaceMention): SpaceValue =
    if pr == key then value else parent.resolve(pr)
  override def grown(pv: Map[SpaceMention, SpaceValue]): SpaceContext =
    pv.iterator.foldLeft(this: SpaceContext)((ctx, kv) => ctx.bind(kv._1, kv._2))


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
  case Iteration(src: Space, symbol: PathRef, rest: SpaceMention, templates: Space)
  case Fold(src: Space, initial: Path, acc: PathRef, symbol: PathRef, rest: SpaceMention, templates: Space, update: Path)
  case Fixpoint(initial: Space, variable: SpaceMention, step: Space)
  case Wrap(src: Space, p: Path)
  case Unwrap(src: Space, p: Path)
  case TailsUnion(src: Space)
  case TailsIntersection(src: Space)
  case PrefixClosure(src: Space)
  case SuffixClosure(src: Space)
  case TailsClosure(src: Space)
  case GroundedPS(p: Path, f: PathValue => SpaceValue)
  case GroundedSS(p: Space, f: SpaceValue => SpaceValue)
  case Range(x: Space, start: Int, end: Int)

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
    case Space.Iteration(src, symbol, rest, templates) => s"${src.show}.iter(P\"${symbol.s}\", S\"${rest.s}\", \n${" ".repeat(indent + 1)}${templates.show(using indent + 1)}\n)"
    case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
      s"${src.show}.fold(${initial.show}, P\"${acc.s}\", P\"${symbol.s}\", S\"${rest.s}\", \n${" ".repeat(indent + 1)}${templates.show(using indent + 1)},\n${" ".repeat(indent + 1)}${update.show}\n)"
    case Space.Fixpoint(initial, variable, step) =>
      s"fixpoint(${initial.show}, S\"${variable.s}\", ${step.show})"
    case Space.Wrap(src, p) => s"(${p.show} x ${src.show})"
    case Space.Unwrap(src, p) => s"${src.show}(${p.show})"
    case Space.TailsUnion(src) => s"TailsUnion(${src.show})"
    case Space.TailsIntersection(src) => s"TailsIntersection(${src.show})"
    case Space.PrefixClosure(src) => s"PrefixClosure(${src.show})"
    case Space.SuffixClosure(src) => s"SuffixClosure(${src.show})"
    case Space.TailsClosure(src) => s"TailsClosure(${src.show})"
    case Space.GroundedPS(p, f) => s"PS${f.hashCode()}(${p.show})"
    case Space.GroundedSS(s, f) => s"SS${f.hashCode()}(${s.show})"
    case Space.Raffination(x, y) => s"(${x.show} \\| ${y.show})"
    case Space.Range(z, start, end) => s"Range(${z.show}, $start, $end)"

object RangeBounds:
  def normalize(size: Int, start: Int, end: Int): (Int, Int) =
    def lower(bound: Int): Int =
      if bound == 0 then 0
      else if bound > 0 then bound - 1
      else size + bound
    def upper(bound: Int): Int =
      if bound == 0 then size
      else if start == 0 && bound > 0 then bound
      else if bound > 0 then bound - 1
      else size + bound

    val lo = lower(start).max(0).min(size)
    val hi = upper(end).max(0).min(size)
    if hi <= lo then 0 -> 0 else lo -> hi


case class SpaceValue(paths: Set[PathValue]):
  def show: String = paths.map(x => '"' + x.show + '"').toSeq.sorted.mkString("SpaceValue(", ", ", ")")
  def pretty: String = paths.map(_.show).toSeq.sorted.mkString("{", ";", "}")
  def prettyLines: String = paths.map(_.show).toSeq.sorted.mkString("", "\n", "")

object LiteralCodec:
  private val marker = "lit64:"

  private def encodeText(s: String): String =
    Base64.getEncoder.encodeToString(s.getBytes(StandardCharsets.UTF_8))

  private def decodeText(s: String): String =
    new String(Base64.getDecoder.decode(s), StandardCharsets.UTF_8)

  private def encodeItem(item: PathItem): String =
    "S" + encodeText(item.show)

  private def decodeItem(s: String): PathItem =
    if s.isEmpty then throw IllegalArgumentException("empty encoded path item")
    s.head match
      case 'S' => PathItem(decodeText(s.tail))
      case 'V' => PathItem.variable(decodeText(s.tail))
      case 'A' => PathItem(s"[${s.tail.toInt}]")
      case other => throw IllegalArgumentException(s"unknown encoded path item tag $other")

  private def encodePath(p: PathValue): String =
    marker + p.items.map(encodeItem).mkString(".")

  private def decodePath(line: String): PathValue =
    val body = line.stripPrefix(marker)
    if body.isEmpty then PathValue(Nil)
    else PathValue(body.split("\\.", -1).toList.map(decodeItem))

  def encode(sv: SpaceValue): String =
    sv.paths.toVector.sortBy(_.show).map(encodePath).mkString("\n")

  def decode(constant: String): SpaceValue =
    val paths =
      constant.linesIterator.filter(_.nonEmpty).map { line =>
        if line.startsWith(marker) then decodePath(line)
        else Syntax.parse(line)
      }.toSet
    SpaceValue(paths)


object PathConstantCodec:
  private val emptyMarker = "path64:"

  def encode(path: PathValue): String =
    if path.items.isEmpty then emptyMarker else path.show

  def decode(constant: String): PathValue =
    if constant == emptyMarker then PathValue(Nil) else Syntax.parse(constant)


case class RoutinePtr(s: String)
case class Routine(name: RoutinePtr, refs: Vector[PathRef], mentions: Vector[SpaceMention], body: Space):
  def show = s"routine(\"${name.s}\", Vector(${refs.map("\"" ++ _.s ++ "\"").mkString(", ")}), Vector(${mentions.map("\"" ++ _.s ++ "\"").mkString(", ")}), \n${body.show.split('\n').map("  " + _).mkString("\n")}\n)"
  def optimized(using ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Routine = Routine(name, refs, mentions,
    all_forever(Lower.inline(using new PartialFunction {
      override def apply(f: RoutinePtr): Routine = ctx(f)
      override def isDefinedAt(f: RoutinePtr): Boolean = f != name && ctx.isDefinedAt(f)
    })(body), Supercompiler.defaultSourcePasses.map(_._2).toList))
//    })(body), List(Lower.IterateSingleton_Deref, Lower.LiteralSpaceOps, Lower.SingletonConst_Literal, Lower.ConcatSingleton_Iter, Lower.IterUnion_Indep, Lower.Wrap_Iter, Lower.Iter_Ident, Lower.Concat_Path, Lower.IterateLiteral_Union, Lower.UnwrapConcat_Unwraps, Lower.SingletonComposition_Wrap, Lower.SingletonSpaceOp_PathOp, Lower.SingletonRestriction_Unwrap)))

def eval(s: Space)(using pc: PathContext = PathContextMap(Map.empty), sc: SpaceContext = SpaceContextMap(Map.empty), rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): SpaceValue =
  import PathItemOrder.given

  val staticSpaceMemo = java.util.IdentityHashMap[Space, java.lang.Boolean]()
  val staticValueMemo = java.util.IdentityHashMap[Space, Set[PathValue]]()

  def recp(x: Path): List[PathItem] = x match
    case Path.Deref(pr) => pc.resolve(pr).items
    case Path.Constant(pi) => pi.items
    case Path.Concat(l, r) => recp(l) ++ recp(r)
    case Path.GroundedPP(p, f) => f(PathValue(recp(p))).items
    case Path.GroundedSP(s, f) => f(SpaceValue(recs(s))).items

  def staticPath(p: Path): Boolean = p match
    case Path.Deref(_) => false
    case Path.Constant(_) => true
    case Path.Concat(l, r) => staticPath(l) && staticPath(r)
    case Path.GroundedPP(p, _) => staticPath(p)
    case Path.GroundedSP(s, _) => staticSpace(s)

  def staticSpace(x: Space): Boolean =
    val cached = staticSpaceMemo.get(x)
    if cached != null then cached.booleanValue()
    else
      val res = x match
        case Space.Empty | Space.Literal(_) => true
        case Space.Call(_, _, _) | Space.Mention(_) => false
        case Space.Singleton(p) => staticPath(p)
        case Space.Union(a, b) => staticSpace(a) && staticSpace(b)
        case Space.Intersection(a, b) => staticSpace(a) && staticSpace(b)
        case Space.Subtraction(a, b) => staticSpace(a) && staticSpace(b)
        case Space.Restriction(a, b) => staticSpace(a) && staticSpace(b)
        case Space.Raffination(a, b) => staticSpace(a) && staticSpace(b)
        case Space.Composition(a, b) => staticSpace(a) && staticSpace(b)
        case Space.Iteration(_, _, _, _) | Space.Fold(_, _, _, _, _, _, _) | Space.Fixpoint(_, _, _) => false
        case Space.Wrap(src, p) => staticSpace(src) && staticPath(p)
        case Space.Unwrap(src, p) => staticSpace(src) && staticPath(p)
        case Space.TailsUnion(src) => staticSpace(src)
        case Space.TailsIntersection(src) => staticSpace(src)
        case Space.PrefixClosure(src) => staticSpace(src)
        case Space.SuffixClosure(src) => staticSpace(src)
        case Space.TailsClosure(src) => staticSpace(src)
        case Space.GroundedPS(p, _) => staticPath(p)
        case Space.GroundedSS(src, _) => staticSpace(src)
        case Space.Range(src, _, _) => staticSpace(src)
      staticSpaceMemo.put(x, java.lang.Boolean.valueOf(res))
      res

  def recs(x: Space): Set[PathValue] =
    if staticSpace(x) then
      val cached = staticValueMemo.get(x)
      if cached != null then cached
      else
        val out = recsUncached(x)
        staticValueMemo.put(x, out)
        out
    else recsUncached(x)

  def recsUncached(x: Space): Set[PathValue] = x match
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
    case Space.Composition(x, y) =>
      val xs = recs(x)
      if xs.isEmpty then Set.empty
      else
        val ys = recs(y)
        if ys.isEmpty then Set.empty
        else
          val out = Set.newBuilder[PathValue]
          xs.foreach(e1 => ys.foreach(e2 => out += PathValue(e1.items ++ e2.items)))
          out.result()
//    case Space.Wrap(src_e, p_e) => val p = recp(p_e); recs(src_e).map( sp => PathValue(p ++ sp.items))
//    case Space.Unwrap(src_e, p_e) => val p = recp(p_e); recs(src_e).collect { case e if e.items.startsWith(p) => PathValue(e.items.drop(p.length)) }

    case Space.Wrap(src_e, p_e) =>
      val p = recp(p_e)
      val src = recs(src_e)
      if p.isEmpty then src
      else
        val out = Set.newBuilder[PathValue]
        src.foreach(sp => out += PathValue(p ++ sp.items))
        out.result()
    case Space.Unwrap(src_e, p_e) =>
      val p = recp(p_e)
      val src = recs(src_e)
      if p.isEmpty then src
      else
        val out = Set.newBuilder[PathValue]
        src.foreach { e =>
          if e.items.startsWith(p) then out += PathValue(e.items.drop(p.length))
        }
        out.result()
    case Space.TailsUnion(src_e) => recs(src_e).collect { case PathValue(_::r) => PathValue(r) }
    case Space.TailsIntersection(src_e) =>
      val groups = recs(src_e).collect { case PathValue(h::t) => h -> PathValue(t) }.groupMap(_._1)(_._2)
      if groups.isEmpty then Set.empty
      else groups.valuesIterator.map(_.toSet).reduce(_ intersect _)
    case Space.PrefixClosure(src_e) =>
      recs(src_e).flatMap(_.prefixes)
    case Space.SuffixClosure(src_e) =>
      recs(src_e).flatMap(_.postfixes)
    case Space.TailsClosure(src_e) =>
      recs(src_e).flatMap(p => (0 to p.items.length).map(i => PathValue(p.items.drop(i))))
    case Space.Iteration(src_e, symbol, rest, templates) =>
      val groups = collection.mutable.HashMap.empty[PathValue, collection.mutable.Set[PathValue]]
      recs(src_e).foreach {
        case PathValue(h :: tail) =>
          val key = PathValue(h :: Nil)
          groups.getOrElseUpdate(key, collection.mutable.Set.empty) += PathValue(tail)
        case _ => ()
      }
      val out = Set.newBuilder[PathValue]
      groups.foreach { (h, r) =>
        out ++= eval(templates)(using pc.bind(symbol, h), sc.bind(rest, SpaceValue(r.toSet)), rc).paths
      }
      out.result()
    case Space.Fold(src_e, initial, acc, symbol, rest, templates, update) =>
      var accValue = PathValue(recp(initial))
      val groups = collection.mutable.HashMap.empty[PathValue, collection.mutable.Set[PathValue]]
      recs(src_e).foreach {
        case PathValue(h :: tail) =>
          val key = PathValue(h :: Nil)
          groups.getOrElseUpdate(key, collection.mutable.Set.empty) += PathValue(tail)
        case _ => ()
      }
      val out = Set.newBuilder[PathValue]
      for (h, r) <- groups.toSeq.sortBy(_._1) do
        val pctx = pc.bind(acc, accValue).bind(symbol, h)
        val sctx = sc.bind(rest, SpaceValue(r.toSet))
        out ++= eval(templates)(using pctx, sctx, rc).paths
        accValue = PathValue(eval(Space.Singleton(update))(using pctx, sctx, rc).paths.head.items)
      out.result()
    case Space.Fixpoint(initial, variable, step) =>
      var current = SpaceValue(recs(initial))
      var changed = true
      while changed do
        val stepped = eval(step)(using pc, sc.bind(variable, current), rc)
        val next = SpaceValue(current.paths union stepped.paths)
        changed = next != current
        current = next
      current.paths
    case Space.Raffination(x_e, y_e) => recs(Space.Subtraction(x_e, Space.Restriction(x_e, y_e)))
    case Space.GroundedPS(p, f) => f(PathValue(recp(p))).paths
    case Space.GroundedSS(s, f) => f(SpaceValue(recs(s))).paths
    case Space.Range(x, start, end) =>
      val values = recs(x)
      val (lo, hi) = RangeBounds.normalize(values.size, start, end)
      if hi <= lo then Set.empty
      else if lo == 0 && hi == values.size then values
      else values.toVector.sorted.slice(lo, hi).toSet
  SpaceValue(recs(s))

case class Node[R](operation: String, constant: String, kind: "path" | "space", inputs: Vector[R]):
  def show: String = s"$operation[${constant}](${inputs.mkString(", ")}): $kind"
  def map[S](f: R => S): Node[S] = copy(inputs=inputs.map(f))
class RecursiveOpGraph(var root: Node[(Int, Int)],
                       val parent: Option[RecursiveOpGraph],
                       val nodes: ArrayBuffer[Either[Node[(Int, Int)], RecursiveOpGraph]],
                       sharedLiteralPool: ArrayBuffer[SpaceValue] | Null = null):
  val literalPool: ArrayBuffer[SpaceValue] =
    if sharedLiteralPool != null then sharedLiteralPool
    else parent.map(_.literalPool).getOrElse(ArrayBuffer.empty[SpaceValue])
  private val pathValueCache = collection.mutable.HashMap.empty[String, PathValue]
  private val intPathValueCache = collection.mutable.HashMap.empty[String, List[Int]]
  private val literalValueCache = collection.mutable.HashMap.empty[String, SpaceValue]
  private val literalTrieCache = collection.mutable.HashMap.empty[String, TrieSpace]
  private val literalPoolIndexCache = collection.mutable.HashMap.empty[String, Int]
  private val rangeBoundsCache = collection.mutable.HashMap.empty[String, (Int, Int)]
  def level: Int = parent.fold(0)(_.level + 1)
  def show: String = s"${root.show}\n" + nodes.zipWithIndex.map((n_g, i) => n_g.fold(
    n => s"$i ${n.show}",
    g => s"$i ${g.show.split('\n').head}\n" ++ g.show.split('\n').tail.map(l => s"  $l").mkString("\n")
  )).mkString("\n")
  def storeLiteral(value: SpaceValue): String =
    val id = literalPool.length
    literalPool += value
    s"pool:$id"
  def pathValue(encoded: String): PathValue =
    pathValueCache.getOrElseUpdate(encoded, PathConstantCodec.decode(encoded))
  def intPathValue(encoded: String): List[Int] =
    intPathValueCache.getOrElseUpdate(encoded, TrieSpace.intern(pathValue(encoded)))
  private def literalPoolIndex(encoded: String): Int =
    literalPoolIndexCache.getOrElseUpdate(encoded, encoded.substring("pool:".length).toInt)
  def literalValue(encoded: String): SpaceValue =
    literalValueCache.getOrElseUpdate(encoded,
      if encoded.startsWith("pool:") then literalPool(literalPoolIndex(encoded))
      else LiteralCodec.decode(encoded)
    )
  def literalTrieValue(encoded: String): TrieSpace =
    literalTrieCache.getOrElseUpdate(encoded, TrieSpace.fromSpaceValue(literalValue(encoded)))
  def rangeBounds(encoded: String): (Int, Int) =
    rangeBoundsCache.getOrElseUpdate(encoded, {
      val sep = encoded.indexOf(':')
      if sep < 0 then throw IllegalArgumentException(s"invalid Range payload: $encoded")
      encoded.substring(0, sep).toInt -> encoded.substring(sep + 1).toInt
    })
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

  def ensureSpaceOutput(pos: (Int, Int)): Unit =
    if pos != (g.level -> (g.nodes.length - 1)) then
      g.store(Node("Alias", "", "space", Vector(pos)))

  def recp(x: Path): (Int, Int) = x match
    case Path.Deref(pr) =>
      g.find(n => n.operation == s"ExtractPathRef" && n.constant == pr.s).getOrElse(throw RuntimeException(s"$pr not found"))
    case Path.Constant(pi) =>
      g.store(Node("Constant", PathConstantCodec.encode(pi), "path", Vector()))
    case Path.Concat(l, r) =>
      g.store(Node("Concat", "", "path", Vector(recp(l), recp(r))))
    case Path.GroundedPP(p, f) =>
      throw UnsupportedOperationException("operation-graph backend does not serialize Path.GroundedPP")
    case Path.GroundedSP(s, f) =>
      throw UnsupportedOperationException("operation-graph backend does not serialize Path.GroundedSP")

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
        g.store(Node(s"Literal", g.storeLiteral(sv), "space", Vector()))
      case Space.Union(x, y) =>
        g.store(Node("Union", "", "space", Vector(recs(x), recs(y))))
      case Space.Intersection(x, y) =>
        g.store(Node("Intersection", "", "space", Vector(recs(x), recs(y))))
      case Space.Subtraction(x, y) =>
        g.store(Node("Subtraction", "", "space", Vector(recs(x), recs(y))))
      case Space.Restriction(x, prefixes) =>
        g.store(Node("Restriction", "", "space", Vector(recs(x), recs(prefixes))))
      case Space.Raffination(x, prefixes) =>
        g.store(Node("Raffination", "", "space", Vector(recs(x), recs(prefixes))))
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
      case Space.PrefixClosure(src) =>
        g.store(Node("PrefixClosure", "", "space", Vector(recs(src))))
      case Space.SuffixClosure(src) =>
        g.store(Node("SuffixClosure", "", "space", Vector(recs(src))))
      case Space.TailsClosure(src) =>
        g.store(Node("TailsClosure", "", "space", Vector(recs(src))))
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
      case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
        val s = recs(src)
        val init = recp(initial)
        val packed =
          Space.Union(
            Space.Wrap(templates, Path.Constant(GraphFoldTags.Body)),
            Space.Wrap(Space.Singleton(update), Path.Constant(GraphFoldTags.Update))
          )
        val rog = transpile(Routine(
          RoutinePtr(r.name.s + "_fold_" + symbol.s),
          Vector(acc, symbol),
          Vector(rest),
          packed
        ), Some(g))
        rog.root = Node("Fold", symbol.s, "space", Vector(s, init))
        g.store(rog)
      case Space.Fixpoint(initial, variable, step) =>
        val init = recs(initial)
        val rog = transpile(Routine(
          RoutinePtr(r.name.s + "_fix_" + variable.s),
          Vector.empty,
          Vector(variable),
          step
        ), Some(g))
        rog.root = Node("Fixpoint", variable.s, "space", Vector(init))
        g.store(rog)
      case Space.GroundedPS(p, f) =>
        throw UnsupportedOperationException("operation-graph backend does not serialize Space.GroundedPS")
      case Space.GroundedSS(s, f) =>
        throw UnsupportedOperationException("operation-graph backend does not serialize Space.GroundedSS")
      case Space.Range(x, start, end) =>
        g.store(Node("Range", s"$start:$end", "space", Vector(recs(x))))

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
    case n => ensureSpaceOutput(recs(n))
  g

def exec(rog: RecursiveOpGraph,
         stack: Stack[Array[PathValue | SpaceValue | Null]], index: PartialFunction[String, RecursiveOpGraph] = PartialFunction.empty): Unit =
  val l = rog.level
  var c = 0
  val s = stack.top
  inline def pos = (l, c)
  extension (p : (Int, Int)) inline def sget = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[SpaceValue]
  extension (p : (Int, Int)) inline def pget = stack(stack.length - 1 - p._1)(p._2).asInstanceOf[PathValue]
  def tagged(packed: SpaceValue, tag: PathValue): SpaceValue =
    SpaceValue(packed.paths.collect {
      case PathValue(items) if items.startsWith(tag.items) => PathValue(items.drop(tag.items.length))
    })
  def taggedSingletonPath(packed: SpaceValue, tag: PathValue): PathValue =
    tagged(packed, tag).paths.headOption.getOrElse(throw IllegalStateException(s"Fold subgraph did not produce ${tag.show} update"))
  while c < rog.nodes.length do
    rog.nodes(c) match
      case Left(Node(op, constant, kind, inputs)) => kind match
        case "path" => s(c) = (op match
          case "ExtractPathRef" => pos.pget // stack should already prepared
          case "Constant" => rog.pathValue(constant)
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
          case "Alias" => inputs(0).sget
          case "Singleton" => SpaceValue(Set(inputs(0).pget))
          case "Literal" => rog.literalValue(constant)
          case "Union" => eval(Space.Union(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Intersection" => eval(Space.Intersection(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Restriction" => eval(Space.Restriction(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Raffination" => eval(Space.Raffination(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Subtraction" => eval(Space.Subtraction(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Composition" => eval(Space.Composition(Space.Literal(inputs(0).sget), Space.Literal(inputs(1).sget)))
          case "Wrap" => eval(Space.Wrap(Space.Literal(inputs(0).sget), Path.Constant(inputs(1).pget)))
          case "Unwrap" => eval(Space.Unwrap(Space.Literal(inputs(0).sget), Path.Constant(inputs(1).pget)))
          case "TailsUnion" => eval(Space.TailsUnion(Space.Literal(inputs(0).sget)))
          case "TailsIntersection" => eval(Space.TailsIntersection(Space.Literal(inputs(0).sget)))
          case "PrefixClosure" => eval(Space.PrefixClosure(Space.Literal(inputs(0).sget)))
          case "SuffixClosure" => eval(Space.SuffixClosure(Space.Literal(inputs(0).sget)))
          case "TailsClosure" => eval(Space.TailsClosure(Space.Literal(inputs(0).sget)))
          case "Iteration" => throw IllegalStateException("Iteration should be represented as a recursive subgraph, not a flat operation node")
          case "Range" =>
            val (start, end) = rog.rangeBounds(constant)
            eval(Space.Range(Space.Literal(inputs(0).sget), start, end))
          )
      case Right(sg: RecursiveOpGraph) =>
        val Node(op, constant, kind, inputs) = sg.root
        op match
          case "Routine" => throw IllegalStateException("Nested Routine subgraphs are not executable without an explicit Call node")
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
            var out = SpaceValue(Set.empty)
            for (h, r) <- inputs(0).sget.paths.collect { case PathValue(head :: tail) => PathValue(head :: Nil) -> PathValue(tail) }.groupMap(_._1)(_._2) do
              stack.push(new Array(sg.nodes.length))
              stack.top(0) = h
              stack.top(1) = SpaceValue(Set.from(r))
              exec(sg, stack, index)
              out = SpaceValue(out.paths union stack.pop().last.asInstanceOf[SpaceValue].paths)
            s(c) = out
          case "Fold" =>
            var accValue = inputs(1).pget
            var out = SpaceValue(Set.empty)
            val groups = inputs(0).sget.paths.collect {
              case PathValue(head :: tail) => PathValue(head :: Nil) -> PathValue(tail)
            }.groupMap(_._1)(_._2)
            for (h, r) <- groups.toSeq.sortBy(_._1.show) do
              stack.push(new Array(sg.nodes.length))
              stack.top(0) = accValue
              stack.top(1) = h
              stack.top(2) = SpaceValue(Set.from(r))
              exec(sg, stack, index)
              val packed = stack.pop().last.asInstanceOf[SpaceValue]
              out = SpaceValue(out.paths union tagged(packed, GraphFoldTags.Body).paths)
              accValue = taggedSingletonPath(packed, GraphFoldTags.Update)
            s(c) = out
          case "Fixpoint" =>
            var current = inputs(0).sget
            var changed = true
            while changed do
              stack.push(new Array[PathValue | SpaceValue | Null](sg.nodes.length))
              stack.top(0) = current
              exec(sg, stack, index)
              val stepped = stack.pop().last.asInstanceOf[SpaceValue]
              val next = SpaceValue(current.paths union stepped.paths)
              changed = next != current
              current = next
            s(c) = current
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
  def taggedSpace(packed: Space, tag: PathValue): Option[Space] = packed match
    case Space.Wrap(src, Path.Constant(`tag`)) => Some(src)
    case Space.Union(a, b) => taggedSpace(a, tag).orElse(taggedSpace(b, tag))
    case _ => None
  def taggedSingletonPath(packed: Space, tag: PathValue): Option[Path] =
    taggedSpace(packed, tag).collect { case Space.Singleton(path) => path }
  while c < rog.nodes.length do
    rog.nodes(c) match
      case Left(Node(op, constant, kind, inputs)) => kind match
        case "path" => s(c) = (op match
          case "ExtractPathRef" => Path.Deref(PathRef(constant)) // stack should already prepared
          case "Constant" => Path.Constant(rog.pathValue(constant))
          case "Concat" => Path.Concat(inputs(0).pget, inputs(1).pget))
        case "space" => s(c) = (op match
          case "Empty" => Space.Empty
          case "Call" =>
            throw RuntimeException(s"untranspile cannot reconstruct Call[$constant] without routine signature metadata")
          case "ExtractSpaceMention" => Space.Mention(SpaceMention(constant)) // stack should already prepared
          case "Alias" => inputs(0).sget
          case "Singleton" => Space.Singleton(inputs(0).pget)
          case "Literal" => Space.Literal(rog.literalValue(constant))
          case "Union" => Space.Union(inputs(0).sget, inputs(1).sget)
          case "Intersection" => Space.Intersection(inputs(0).sget, inputs(1).sget)
          case "Restriction" => Space.Restriction(inputs(0).sget, inputs(1).sget)
          case "Raffination" => Space.Raffination(inputs(0).sget, inputs(1).sget)
          case "Subtraction" => Space.Subtraction(inputs(0).sget, inputs(1).sget)
          case "Composition" => Space.Composition(inputs(0).sget, inputs(1).sget)
          case "Wrap" => Space.Wrap(inputs(0).sget, inputs(1).pget)
          case "Unwrap" => Space.Unwrap(inputs(0).sget, inputs(1).pget)
          case "TailsUnion" => Space.TailsUnion(inputs(0).sget)
          case "TailsIntersection" => Space.TailsIntersection(inputs(0).sget)
          case "PrefixClosure" => Space.PrefixClosure(inputs(0).sget)
          case "SuffixClosure" => Space.SuffixClosure(inputs(0).sget)
          case "TailsClosure" => Space.TailsClosure(inputs(0).sget)
          case "Iteration" => throw IllegalStateException("Iteration should be represented as a recursive subgraph, not a flat operation node")
          case "Range" =>
            val (start, end) = rog.rangeBounds(constant)
            Space.Range(inputs(0).sget, start, end)
          )
      case Right(sg: RecursiveOpGraph) =>
        val Node(op, constant, kind, inputs) = sg.root
        op match
          case "Routine" => throw IllegalStateException("Nested Routine subgraphs are not untranspilable without an explicit Call node")
          case "Iteration" =>
//            println(s"constant ${constant} ${kind} ${inputs}")
//            println(s"sg ${sg.nodes} ")
            stack.push(new Array(sg.nodes.length))
            untranspile(sg, stack, index)
            val popped = stack.pop()
            s(c) = Space.Iteration(inputs(0).sget, popped(0).asInstanceOf[Path.Deref].pr, popped(1).asInstanceOf[Space.Mention].variable, popped.last.asInstanceOf[Space])
          case "Fold" =>
            stack.push(new Array(sg.nodes.length))
            untranspile(sg, stack, index)
            val popped = stack.pop()
            val packed = popped.last.asInstanceOf[Space]
            val body = taggedSpace(packed, GraphFoldTags.Body).getOrElse {
              throw IllegalStateException(s"Fold subgraph did not contain ${GraphFoldTags.Body.show} body tag")
            }
            val update = taggedSingletonPath(packed, GraphFoldTags.Update).getOrElse {
              throw IllegalStateException(s"Fold subgraph did not contain ${GraphFoldTags.Update.show} singleton update tag")
            }
            s(c) = Space.Fold(
              inputs(0).sget,
              inputs(1).pget,
              popped(0).asInstanceOf[Path.Deref].pr,
              popped(1).asInstanceOf[Path.Deref].pr,
              popped(2).asInstanceOf[Space.Mention].variable,
              body,
              update
            )
          case "Fixpoint" =>
            stack.push(new Array(sg.nodes.length))
            untranspile(sg, stack, index)
            val popped = stack.pop()
            s(c) = Space.Fixpoint(inputs(0).sget, SpaceMention(constant), popped.last.asInstanceOf[Space])
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


def optimize_sharing(g: RecursiveOpGraph,
                     stack: ArrayBuffer[(LongMap[(Int, Int)], LongMap[(Int, Int)])] = ArrayBuffer.empty,
                     parent: Option[RecursiveOpGraph] = None): RecursiveOpGraph =
  val parent0 = parent.orElse(g.parent)
  val r = RecursiveOpGraph(g.root, parent0, ArrayBuffer.empty, parent0.map(_.literalPool).getOrElse(g.literalPool))
  val l = g.level
  stack.addOne(LongMap.withDefault[(Int, Int)](x => l -> x.toInt) -> LongMap.withDefault[(Int, Int)](x => l -> x.toInt))
  def forward(pos: (Int, Int)): Option[(Int, Int)] =
    val (lm, xm) = pos
    Option.when(lm >= 0 && lm < stack.length)(stack(lm)._1(xm))
  def forwardNode(n: Node[(Int, Int)]): Option[Node[(Int, Int)]] =
    val inputs = n.inputs.map(forward)
    Option.when(inputs.forall(_.isDefined))(n.copy(inputs = inputs.flatten))
  def toOutputNode(n: Node[(Int, Int)]): Node[(Int, Int)] =
    n.map((lm, xm) => stack(lm)._2(xm))
  var c = 0
  for (n, j) <- g.nodes.zipWithIndex do n match
    case Left(n) =>
      val canonical = forwardNode(n).getOrElse(throw RuntimeException(s"cannot remap node ${n.show} at level $l"))
      val (l2, i) = g.find(m => forwardNode(m).contains(canonical)).get
      if (l, i) == (l2, j) then
        r.store(toOutputNode(canonical))
        stack(l2)._2.update(i, l -> c)
        c += 1
      else
        stack.last._1.update(j, l2 -> i)
    case Right(sg) =>
      // Subgraph sharing needs meaning-aware hashing; keep this pass to local node sharing.
      r.store(optimize_sharing(sg, stack, Some(r)))
      stack(l)._2.update(j, l -> c)
      c += 1
  r.root = toOutputNode(forwardNode(r.root).getOrElse(throw RuntimeException(s"cannot remap root ${r.root.show} at level $l")))
  stack.remove(stack.length - 1)
  r


def push_out(g: RecursiveOpGraph, stack: ArrayBuffer[LongMap[(Int, Int)]] = ArrayBuffer.empty, parent: Option[RecursiveOpGraph] = None): RecursiveOpGraph =
  val r = RecursiveOpGraph(g.root, parent, ArrayBuffer.empty, parent.map(_.literalPool).getOrElse(g.literalPool))
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
      case Right(_) => ()
//    if lr == stack.length - 1 then
//      stack.dropRightInPlace(1)

  val localStackEntry = lb == stack.length
  if localStackEntry then
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
  if localStackEntry then
    stack.dropRightInPlace(1)
  r

def hoist_loop_invariant_subgraphs(g: RecursiveOpGraph): RecursiveOpGraph =
  val remaps = ArrayBuffer.empty[collection.mutable.Map[Int, (Int, Int)]]

  def remap(pos: (Int, Int)): (Int, Int) =
    val (level, index) = pos
    if level >= 0 && level < remaps.length then remaps(level).getOrElse(index, pos)
    else pos

  def remapNode(n: Node[(Int, Int)]): Node[(Int, Int)] =
    n.map(remap)

  def rebuild(src: RecursiveOpGraph,
              parent: Option[RecursiveOpGraph],
              hoistInto: Option[RecursiveOpGraph]): RecursiveOpGraph =
    require(src.level == remaps.length,
      s"cannot rebuild graph at level ${src.level} with ${remaps.length} active remap frames")
    val out = RecursiveOpGraph(src.root, parent, ArrayBuffer.empty, parent.map(_.literalPool).getOrElse(src.literalPool))
    val frame = collection.mutable.Map.empty[Int, (Int, Int)]
    remaps += frame

    def loopInvariant(node: Node[(Int, Int)], index: Int): Boolean =
      hoistInto.nonEmpty &&
        index != src.nodes.length - 1 &&
        !node.operation.startsWith("Extract") &&
        node.inputs.forall((level, _) => level < out.level)

    for (entry, index) <- src.nodes.zipWithIndex do entry match
      case Left(node) =>
        val mapped = remapNode(node)
        val target =
          if loopInvariant(mapped, index) then hoistInto.get.store(mapped)
          else out.store(mapped)
        frame(index) = target
      case Right(subgraph) =>
        val rebuilt = rebuild(subgraph, Some(out), Some(out))
        val target = out.store(rebuilt)
        frame(index) = target

    out.root = remapNode(src.root)
    remaps.remove(remaps.length - 1)
    out

  rebuild(g, g.parent, None)

def all_forever(s: Space, mappings: List[Space => Space] = Nil): Space =
  val s_ = mappings.foldLeft(s)((s, f) => f(s))
  if s == s_ then s
  else all_forever(s_, mappings)

def graphReferenceErrors(g: RecursiveOpGraph, path: Vector[Int] = Vector.empty): Vector[String] =
  def graphAtLevel(from: RecursiveOpGraph, target: Int): Option[RecursiveOpGraph] =
    if from.level == target then Some(from)
    else from.parent.flatMap(graphAtLevel(_, target))
  def check(owner: RecursiveOpGraph, from: String, input: (Int, Int), k: Int): Option[String] =
    val (level, index) = input
    val ok = graphAtLevel(owner, level).exists(gg => index >= 0 && index < gg.nodes.length)
    Option.when(!ok)(s"${path.mkString("/")} $from input $k -> ($level,$index)")
  val rootBad = g.root.inputs.zipWithIndex.flatMap((input, k) => check(g, s"root ${g.root.show}", input, k))
  val nodeBad = g.nodes.zipWithIndex.flatMap {
    case (Left(n), j) =>
      n.inputs.zipWithIndex.flatMap((input, k) => check(g, s"node $j ${n.show}", input, k))
    case (Right(sg), j) =>
      graphReferenceErrors(sg, path :+ j)
  }
  (rootBad ++ nodeBad).toVector

def graphStructurallyEqual(a: RecursiveOpGraph, b: RecursiveOpGraph): Boolean =
  a.root == b.root &&
    a.nodes.length == b.nodes.length &&
    a.nodes.iterator.zip(b.nodes.iterator).forall {
      case (Left(x), Left(y)) => x == y
      case (Right(x), Right(y)) => graphStructurallyEqual(x, y)
      case _ => false
    }

def optimize(g: RecursiveOpGraph): RecursiveOpGraph =
  optimizeTimed(g).graph

def optimizeTimed(g: RecursiveOpGraph,
                  deadline: CompileDeadline = CompileBudget.Default.start(),
                  maxRounds: Int = 32): GraphOptimizeResult =
  val start = System.nanoTime()
  var current = g
  var converged = false
  var round = 0
  var timings = Vector.empty[OptimizationTiming]
  def validate(phase: String, graph: RecursiveOpGraph): Unit =
    val errors = graphReferenceErrors(graph)
    if errors.nonEmpty then
      throw RuntimeException(s"$phase produced invalid graph references:\n${errors.mkString("\n")}")
  validate("graph optimizer input", current)
  while !converged && round < maxRounds do
    deadline.check("graph optimization")
    val roundStart = current
    val beforeHoist = Supercompiler.graphStats(current)
    val hoistStart = System.nanoTime()
    val hoisted = hoist_loop_invariant_subgraphs(current)
    val hoistMs = (System.nanoTime() - hoistStart).toDouble / 1_000_000.0
    validate(s"graph hoist_loop_invariant_subgraphs round $round", hoisted)
    val afterHoist = Supercompiler.graphStats(hoisted)
    timings = timings :+ OptimizationTiming("graph", round, "hoist_loop_invariant_subgraphs", hoistMs, !graphStructurallyEqual(hoisted, roundStart), beforeHoist.nodes, afterHoist.nodes)
    deadline.check("graph hoist_loop_invariant_subgraphs")

    val beforePush = afterHoist
    val pushStart = System.nanoTime()
    val pushed = push_out(hoisted)
    val pushMs = (System.nanoTime() - pushStart).toDouble / 1_000_000.0
    validate(s"graph push_out round $round", pushed)
    val afterPush = Supercompiler.graphStats(pushed)
    timings = timings :+ OptimizationTiming("graph", round, "push_out", pushMs, !graphStructurallyEqual(pushed, hoisted), beforePush.nodes, afterPush.nodes)
    deadline.check("graph push_out")

    val sharingStart = System.nanoTime()
    val next = optimize_sharing(pushed)
    val sharingMs = (System.nanoTime() - sharingStart).toDouble / 1_000_000.0
    validate(s"graph optimize_sharing round $round", next)
    val afterSharing = Supercompiler.graphStats(next)
    timings = timings :+ OptimizationTiming("graph", round, "optimize_sharing", sharingMs, !graphStructurallyEqual(next, pushed), afterPush.nodes, afterSharing.nodes)
    current = next
    converged = graphStructurallyEqual(current, roundStart)
    round += 1
    deadline.check("graph optimize_sharing")
  GraphOptimizeResult(current, timings, round, converged, (System.nanoTime() - start).toDouble / 1_000_000.0)


object Reflect:
  def code_to_space(s: Space): SpaceValue =
    import Syntax.parse
    def recp(x: Path): Set[PathValue] = x match
      case Path.Deref(pr) => Set[PathValue](f"Deref.${pr.s}")
      case Path.Constant(pi) => Set[PathValue](f"Constant.${pi.show}")
      case Path.Concat(l, r) =>
        (for p <- recp(l) yield PathValue(PathItem("Concat")::PathItem("lhs")::p.items)) union
        (for p <- recp(r) yield PathValue(PathItem("Concat")::PathItem("rhs")::p.items))
      case Path.GroundedPP(p, f) =>
        for pp <- recp(p) yield PathValue(PathItem("GroundedPP")::pp.items)
      case Path.GroundedSP(s, f) =>
        for sp <- recs(s) yield PathValue(PathItem("GroundedSP")::sp.items)

    def recs(x: Space): Set[PathValue] = x match
      case Space.Empty => Set("Empty")
      case Space.Call(rp, refs, mentions) =>
        Set[PathValue](f"Call.routine.${rp.s}") union
        (for (pd, i) <- refs.zipWithIndex; pp <- recp(pd) yield PathValue(PathItem("Call")::PathItem("path")::PathItem(i.toString)::pp.items)).toSet union
        (for (sd, i) <- mentions.zipWithIndex; sp <- recs(sd) yield PathValue(PathItem("Call")::PathItem("space")::PathItem(i.toString)::sp.items)).toSet
      case Space.Mention(p) => Set(f"Mention.${p.s}")
      case Space.Singleton(p) => Set(f"Singleton.${p.pretty}")
      case Space.Literal(SpaceValue(ps)) => for pp <- ps yield PathValue(PathItem("Literal")::pp.items)
      case Space.Union(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem("Union")::pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem("Union")::pp.items))
      case Space.Intersection(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem("Intersection")::pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem("Intersection")::pp.items))
      case Space.Subtraction(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem("Subtraction")::PathItem("domain")::pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem("Subtraction")::PathItem("argument")::pp.items))
      case Space.Restriction(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem("Restriction") :: PathItem("domain") :: pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem("Restriction") :: PathItem("argument") :: pp.items))
      case Space.Raffination(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem("Raffination") :: PathItem("domain") :: pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem("Raffination") :: PathItem("argument") :: pp.items))
      case Space.Composition(x, y) =>
        (for pp <- recs(x) yield PathValue(PathItem("Composition") :: PathItem("domain") :: pp.items)) union
        (for pp <- recs(y) yield PathValue(PathItem("Composition") :: PathItem("argument") :: pp.items))
      case Space.Wrap(x, p_e) =>
        (for pp <- recp(p_e) yield PathValue(PathItem("Wrap") :: PathItem("prefix") :: pp.items)) union
        (for pp <- recs(x) yield PathValue(PathItem("Wrap") :: PathItem("domain") :: pp.items))
      case Space.Unwrap(x, p_e) =>
        (for pp <- recp(p_e) yield PathValue(PathItem("Unwrap") :: PathItem("prefix") :: pp.items)) union
        (for pp <- recs(x) yield PathValue(PathItem("Unwrap") :: PathItem("domain") :: pp.items))
      case Space.TailsUnion(x) =>
        for pp <- recs(x) yield PathValue(PathItem("TailsUnion") :: pp.items)
      case Space.TailsIntersection(x) =>
        for pp <- recs(x) yield PathValue(PathItem("TailsIntersection") :: pp.items)
      case Space.PrefixClosure(x) =>
        for pp <- recs(x) yield PathValue(PathItem("PrefixClosure") :: pp.items)
      case Space.SuffixClosure(x) =>
        for pp <- recs(x) yield PathValue(PathItem("SuffixClosure") :: pp.items)
      case Space.TailsClosure(x) =>
        for pp <- recs(x) yield PathValue(PathItem("TailsClosure") :: pp.items)
      case Space.Iteration(x, symbol, rest, templates) =>
        Set[PathValue](f"Iteration.head.${symbol.s}", f"Iteration.tail.${rest.s}") union
        (for sp <- recs(x) yield PathValue(PathItem("Iteration")::PathItem("domain")::sp.items)) union
        (for sp <- recs(templates) yield PathValue(PathItem("Iteration")::PathItem("templates")::sp.items))
      case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
        Set[PathValue](f"Fold.acc.${acc.s}", f"Fold.head.${symbol.s}", f"Fold.tail.${rest.s}") union
        (for pp <- recp(initial) yield PathValue(PathItem("Fold")::PathItem("initial")::pp.items)) union
        (for pp <- recp(update) yield PathValue(PathItem("Fold")::PathItem("update")::pp.items)) union
        (for sp <- recs(src) yield PathValue(PathItem("Fold")::PathItem("domain")::sp.items)) union
        (for sp <- recs(templates) yield PathValue(PathItem("Fold")::PathItem("templates")::sp.items))
      case Space.Fixpoint(initial, variable, step) =>
        Set[PathValue](f"Fixpoint.state.${variable.s}") union
        (for sp <- recs(initial) yield PathValue(PathItem("Fixpoint")::PathItem("initial")::sp.items)) union
        (for sp <- recs(step) yield PathValue(PathItem("Fixpoint")::PathItem("step")::sp.items))
      case Space.GroundedPS(p, f) =>
        for pp <- recp(p) yield PathValue(PathItem("GroundedPS")::pp.items)
      case Space.GroundedSS(s, f) =>
        for sp <- recs(s) yield PathValue(PathItem("GroundedSS")::sp.items)
      case Space.Range(x, start, end) =>
        for sp <- recs(x) yield PathValue(PathItem("Range")::PathItem(start.toString)::PathItem(end.toString)::sp.items)

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
    case Path.GroundedPP(p, f) => Path.GroundedPP(recp(p), f)
    case Path.GroundedSP(s, f) => Path.GroundedSP(recs(s), f)
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
    case Space.Raffination(x, y) => Space.Raffination(recs(x), recs(y))
    case Space.Composition(x, y) => Space.Composition(recs(x), recs(y))
    case Space.Wrap(src_e, p_e) =>  Space.Wrap(recs(src_e), recp(p_e))
    case Space.Unwrap(src_e, p_e) => Space.Unwrap(recs(src_e), recp(p_e))
    case Space.TailsUnion(src_e) => Space.TailsUnion(recs(src_e))
    case Space.TailsIntersection(src_e) => Space.TailsIntersection(recs(src_e))
    case Space.PrefixClosure(src_e) => Space.PrefixClosure(recs(src_e))
    case Space.SuffixClosure(src_e) => Space.SuffixClosure(recs(src_e))
    case Space.TailsClosure(src_e) => Space.TailsClosure(recs(src_e))
    case Space.Iteration(src_e, symbol, rest, templates) => Space.Iteration(recs(src_e), symbol, rest, recs(templates))
    case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
      Space.Fold(recs(src), recp(initial), acc, symbol, rest, recs(templates), recp(update))
    case Space.Fixpoint(initial, variable, step) => Space.Fixpoint(recs(initial), variable, recs(step))
    case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p), f)
    case Space.GroundedSS(s, f) => Space.GroundedSS(recs(s), f)
    case Space.Range(x, start, end) => Space.Range(recs(x), start, end)
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
    case Path.GroundedPP(p, f) => Path.GroundedPP(recp(p), f)
    case Path.GroundedSP(s, f) => Path.GroundedSP(recs(s), f), x => x)
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
    case Space.PrefixClosure(src_e) => Space.PrefixClosure(recs(src_e))
    case Space.SuffixClosure(src_e) => Space.SuffixClosure(recs(src_e))
    case Space.TailsClosure(src_e) => Space.TailsClosure(recs(src_e))
    case Space.Iteration(src_e, symbol, rest, templates) => Space.Iteration(recs(src_e), symbol, rest, recs(templates))
    case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
      Space.Fold(recs(src), recp(initial), acc, symbol, rest, recs(templates), recp(update))
    case Space.Fixpoint(initial, variable, step) => Space.Fixpoint(recs(initial), variable, recs(step))
    case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p), f)
    case Space.GroundedSS(s, f) => Space.GroundedSS(recs(s), f)
    case Space.Range(x, start, end) => Space.Range(recs(x), start, end),
    x => x)
  recs(s)

object Lower:
  private def literalOrEmpty(sv: SpaceValue): Space =
    if sv.paths.isEmpty then Space.Empty else Space.Literal(sv)

  private def foldedTrieLiteral(s: Space): Space =
    literalOrEmpty(ConstantFoldEval.timedEvalTrie(evalTrieValue(s)))

  private def usesMention(s: Space, sm: SpaceMention): Boolean =
    collect(s)(spre = { case Space.Mention(`sm`) => () })._1.nonEmpty

  private def usesRef(s: Space, pr: PathRef): Boolean =
    collect(s)(ppre = { case Path.Deref(`pr`) => () })._2.nonEmpty

  private def emptyPath(p: Path): Boolean = p match
    case Path.Constant(PathValue(Nil)) => true
    case _ => false

  private def pathHeaded(p: Path): Boolean = p match
    case Path.Constant(PathValue(items)) => items.nonEmpty
    case Path.Deref(pr) => pr.lengthHint >= 1
    case Path.Concat(l, r) => pathHeaded(l) || pathHeaded(r)
    case _ => false

  private def provablyNonEmpty(s: Space): Boolean = s match
    case Space.Singleton(_) => true
    case Space.Literal(SpaceValue(paths)) => paths.nonEmpty
    case Space.Union(a, b) => provablyNonEmpty(a) || provablyNonEmpty(b)
    case Space.Wrap(src, _) => provablyNonEmpty(src)
    case Space.Composition(a, b) => provablyNonEmpty(a) && provablyNonEmpty(b)
    case _ => false

  private def provablyHeaded(s: Space): Boolean = s match
    case Space.Singleton(p) => pathHeaded(p)
    case Space.Literal(SpaceValue(paths)) => paths.exists(_.items.nonEmpty)
    case Space.Union(a, b) => provablyHeaded(a) || provablyHeaded(b)
    case Space.Wrap(src, p) => if emptyPath(p) then provablyHeaded(src) else provablyNonEmpty(src)
    case _ => false

  private def hasStaticHead(s: Space): Boolean = s match
    case Space.Literal(SpaceValue(paths)) => paths.exists(_.items.nonEmpty)
    case Space.Singleton(Path.Constant(PathValue(_ :: _))) => true
    case Space.Union(a, b) => hasStaticHead(a) || hasStaticHead(b)
    case _ => false

  private def unionTerms(s: Space): Vector[Space] = s match
    case Space.Union(a, b) => unionTerms(a) ++ unionTerms(b)
    case Space.Literal(SpaceValue(paths)) if paths.isEmpty => Vector(Space.Empty)
    case other => Vector(other)

  private def intersectionTerms(s: Space): Vector[Space] = s match
    case Space.Intersection(a, b) => intersectionTerms(a) ++ intersectionTerms(b)
    case Space.Literal(SpaceValue(paths)) if paths.isEmpty => Vector(Space.Empty)
    case other => Vector(other)

  private def syntacticSubsetOf(left: Space, right: Space): Boolean =
    left == Space.Empty || left == right || ((left, right) match
      case (Space.PrefixClosure(src), Space.PrefixClosure(dst)) =>
        syntacticSubsetOf(src, dst)
      case (Space.Subtraction(src, Space.Singleton(Path.Constant(PathValue(Nil)))), Space.PrefixClosure(dst)) =>
        syntacticSubsetOf(src, dst)
      case (Space.Intersection(left, right), Space.PrefixClosure(src)) =>
        syntacticSubsetOf(left, Space.PrefixClosure(src)) || syntacticSubsetOf(right, Space.PrefixClosure(src))
      case (Space.Intersection(left, right), Space.SuffixClosure(src)) =>
        syntacticSubsetOf(left, Space.SuffixClosure(src)) || syntacticSubsetOf(right, Space.SuffixClosure(src))
      case (Space.Intersection(left, right), Space.TailsClosure(src)) =>
        syntacticSubsetOf(left, Space.TailsClosure(src)) || syntacticSubsetOf(right, Space.TailsClosure(src))
      case (Space.Union(left, right), Space.PrefixClosure(src)) =>
        syntacticSubsetOf(left, Space.PrefixClosure(src)) && syntacticSubsetOf(right, Space.PrefixClosure(src))
      case (Space.Union(left, right), Space.SuffixClosure(src)) =>
        syntacticSubsetOf(left, Space.SuffixClosure(src)) && syntacticSubsetOf(right, Space.SuffixClosure(src))
      case (Space.Union(left, right), Space.TailsClosure(src)) =>
        syntacticSubsetOf(left, Space.TailsClosure(src)) && syntacticSubsetOf(right, Space.TailsClosure(src))
      case (Space.Subtraction(src, Space.Singleton(Path.Constant(PathValue(Nil)))), Space.SuffixClosure(dst)) =>
        syntacticSubsetOf(src, dst)
      case (Space.SuffixClosure(src), Space.SuffixClosure(dst)) =>
        syntacticSubsetOf(src, dst)
      case (Space.SuffixClosure(src), Space.TailsClosure(dst)) =>
        syntacticSubsetOf(src, dst)
      case (Space.TailsClosure(src), Space.TailsClosure(dst)) =>
        syntacticSubsetOf(src, dst)
      case (Space.TailsUnion(src), Space.TailsClosure(dst)) =>
        syntacticSubsetOf(src, dst)
      case (_, Space.TailsClosure(src)) =>
        syntacticSubsetOf(left, src)
      case _ => false
    ) || (left match
      case Space.Union(a, b) =>
        syntacticSubsetOf(a, right) && syntacticSubsetOf(b, right)
      case Space.Intersection(a, b) =>
        syntacticSubsetOf(a, right) || syntacticSubsetOf(b, right)
      case Space.Subtraction(src, _) =>
        syntacticSubsetOf(src, right)
      case Space.Restriction(src, _) =>
        syntacticSubsetOf(src, right)
      case Space.Raffination(src, _) =>
        syntacticSubsetOf(src, right)
      case Space.Range(src, _, _) =>
        syntacticSubsetOf(src, right)
      case _ => right match
        case Space.Union(a, b) =>
          syntacticSubsetOf(left, a) || syntacticSubsetOf(left, b)
        case Space.Intersection(a, b) =>
          syntacticSubsetOf(left, a) && syntacticSubsetOf(left, b)
        case _ => false
    )

  private def complementaryRestrictionPartition(left: Space, right: Space): Boolean = (left, right) match
    case (Space.Restriction(src, prefixes), Space.Raffination(src2, prefixes2)) =>
      src == src2 && prefixes == prefixes2
    case (Space.Raffination(src, prefixes), Space.Restriction(src2, prefixes2)) =>
      src == src2 && prefixes == prefixes2
    case _ => false

  private def differenceIntersectionPartition(left: Space, right: Space): Option[Space] =
    def isIntersectionOf(term: Space, a: Space, b: Space): Boolean = term match
      case Space.Intersection(x, y) => (x == a && y == b) || (x == b && y == a)
      case _ => false
    (left, right) match
      case (Space.Subtraction(src, removed), other) if isIntersectionOf(other, src, removed) =>
        Some(src)
      case (other, Space.Subtraction(src, removed)) if isIntersectionOf(other, src, removed) =>
        Some(src)
      case _ => None

  private def syntacticDisjoint(left: Space, right: Space): Boolean =
    left == Space.Empty || right == Space.Empty || complementaryRestrictionPartition(left, right) || ((left, right) match
      case (Space.Union(a, b), other) =>
        syntacticDisjoint(a, other) && syntacticDisjoint(b, other)
      case (other, Space.Union(a, b)) =>
        syntacticDisjoint(other, a) && syntacticDisjoint(other, b)
      case (Space.Intersection(a, b), other) =>
        syntacticDisjoint(a, other) || syntacticDisjoint(b, other)
      case (other, Space.Intersection(a, b)) =>
        syntacticDisjoint(other, a) || syntacticDisjoint(other, b)
      case (Space.Subtraction(_, removed), other) =>
        syntacticSubsetOf(other, removed)
      case (other, Space.Subtraction(_, removed)) =>
        syntacticSubsetOf(other, removed)
      case _ => false
    )

  private def replaceFirstPair(terms: Vector[Space])(rewrite: (Space, Space) => Option[Space]): Option[Vector[Space]] =
    var found: Option[Vector[Space]] = None
    var i = 0
    while i < terms.length && found.isEmpty do
      var j = i + 1
      while j < terms.length && found.isEmpty do
        rewrite(terms(i), terms(j)).foreach { replacement =>
          found = Some(terms.zipWithIndex.collect {
            case (term, k) if k != i && k != j => term
          }.toVector :+ replacement)
        }
        j += 1
      i += 1
    found

  private def commonFactoredUnionOfIntersections(left: Space, right: Space): Option[Space] =
    val leftTerms = intersectionTerms(left).distinct
    val rightTerms = intersectionTerms(right).distinct
    val common = leftTerms.filter(rightTerms.contains)
    if common.isEmpty then None
    else
      val leftRest = leftTerms.filterNot(common.contains)
      val rightRest = rightTerms.filterNot(common.contains)
      val commonTerm = rebuildIntersection(common)
      if leftRest.isEmpty || rightRest.isEmpty then Some(commonTerm)
      else Some(Space.Intersection(commonTerm, Space.Union(rebuildIntersection(leftRest), rebuildIntersection(rightRest))))

  private def commonFactoredIntersectionOfUnions(left: Space, right: Space): Option[Space] =
    val leftTerms = unionTerms(left).filterNot(_ == Space.Empty).distinct
    val rightTerms = unionTerms(right).filterNot(_ == Space.Empty).distinct
    val common = leftTerms.filter(rightTerms.contains)
    if common.isEmpty then None
    else
      val leftRest = leftTerms.filterNot(common.contains)
      val rightRest = rightTerms.filterNot(common.contains)
      val commonTerm = rebuildUnion(common)
      if leftRest.isEmpty || rightRest.isEmpty then Some(commonTerm)
      else Some(Space.Union(commonTerm, Space.Intersection(rebuildUnion(leftRest), rebuildUnion(rightRest))))

  private def rebuildUnion(terms: Vector[Space]): Space =
    if terms.isEmpty then Space.Empty else terms.reduceLeft(Space.Union(_, _))

  private def rebuildIntersection(terms: Vector[Space]): Space =
    if terms.isEmpty then Space.Empty else terms.reduceLeft(Space.Intersection(_, _))

  private def normalizeUnion(s: Space): Space =
    val flat = unionTerms(s).filterNot(_ == Space.Empty)
    replaceFirstPair(flat) {
      case (Space.Restriction(src, leftPrefixes), Space.Restriction(src2, rightPrefixes)) if src == src2 =>
        Some(Space.Restriction(src, Space.Union(leftPrefixes, rightPrefixes)))
      case (Space.Subtraction(src, leftRemoved), Space.Subtraction(src2, rightRemoved)) if src == src2 =>
        Some(Space.Subtraction(src, Space.Intersection(leftRemoved, rightRemoved)))
      case (left, right) =>
        commonFactoredUnionOfIntersections(left, right)
    } match
      case Some(next) =>
        normalizeUnion(rebuildUnion(next))
      case None =>
        val partitions = flat.collect {
          case r @ Space.Restriction(src, prefixes) if flat.exists {
            case Space.Raffination(`src`, `prefixes`) => true
            case _ => false
          } => src
          case r @ Space.Raffination(src, prefixes) if flat.exists {
            case Space.Restriction(`src`, `prefixes`) => true
            case _ => false
          } => src
        }
        val withoutPartitions = flat.filterNot {
          case Space.Restriction(src, prefixes) => partitions.contains(src) && flat.exists {
            case Space.Raffination(`src`, `prefixes`) => true
            case _ => false
          }
          case Space.Raffination(src, prefixes) => partitions.contains(src) && flat.exists {
            case Space.Restriction(`src`, `prefixes`) => true
            case _ => false
          }
          case _ => false
        } ++ partitions
        val withDifferenceComplements = withoutPartitions.map {
          case Space.Subtraction(src, removed) if withoutPartitions.exists(_ == removed) => src
          case other => other
        }
        val usedPartitionTerms = scala.collection.mutable.BitSet.empty
        val recoveredDifferencePartitions = Vector.newBuilder[Space]
        for
          i <- withDifferenceComplements.indices
          j <- (i + 1) until withDifferenceComplements.length
          if !usedPartitionTerms(i) && !usedPartitionTerms(j)
          source <- differenceIntersectionPartition(withDifferenceComplements(i), withDifferenceComplements(j))
        do
          usedPartitionTerms += i
          usedPartitionTerms += j
          recoveredDifferencePartitions += source
        val withRecoveredPartitions =
          withDifferenceComplements.zipWithIndex.collect {
            case (term, i) if !usedPartitionTerms(i) => term
          }.toVector ++ recoveredDifferencePartitions.result()
        val sources = withRecoveredPartitions.toSet
        val absorbedRanges = withRecoveredPartitions.filterNot {
          case Space.Range(src, _, _) if sources(src) => true
          case _ => false
        }
        val absorbedSubsets = absorbedRanges.filterNot { term =>
          absorbedRanges.exists(other => other != term && syntacticSubsetOf(term, other))
        }
        val distinct = absorbedSubsets.distinct.sortBy(_.show)
        rebuildUnion(distinct)

  private def normalizeIntersection(s: Space): Space =
    val flat = intersectionTerms(s)
    if flat.contains(Space.Empty) then Space.Empty
    else if flat.combinations(2).exists {
      case Vector(a, b) => syntacticDisjoint(a, b)
      case _ => false
    } then Space.Empty
    else
      replaceFirstPair(flat) {
        case (Space.Raffination(src, leftPrefixes), Space.Raffination(src2, rightPrefixes)) if src == src2 =>
          Some(Space.Raffination(src, Space.Union(leftPrefixes, rightPrefixes)))
        case (Space.Subtraction(src, leftRemoved), Space.Subtraction(src2, rightRemoved)) if src == src2 =>
          Some(Space.Subtraction(src, Space.Union(leftRemoved, rightRemoved)))
        case (left, right) =>
          commonFactoredIntersectionOfUnions(left, right)
      } match
        case Some(next) =>
          normalizeIntersection(rebuildIntersection(next))
        case None =>
          val absorbedSupersets = flat.filterNot { term =>
            flat.exists(other => other != term && syntacticSubsetOf(other, term))
          }
          rebuildIntersection(absorbedSupersets.distinct.sortBy(_.show))

  private def normalizeSubtraction(s: Space): Space = s match
    case Space.Subtraction(left, right) if syntacticSubsetOf(left, right) =>
      Space.Empty
    case Space.Subtraction(left, right) if syntacticDisjoint(left, right) =>
      left
    case Space.Subtraction(left, Space.Union(a, b)) =>
      Space.Subtraction(Space.Subtraction(left, a), b)
    case Space.Subtraction(Space.Union(a, b), right) if a == right =>
      Space.Subtraction(b, right)
    case Space.Subtraction(Space.Union(a, b), right) if b == right =>
      Space.Subtraction(a, right)
    case Space.Subtraction(Space.Subtraction(src, removed), right) if removed == right =>
      Space.Subtraction(src, removed)
    case Space.Subtraction(src, Space.Intersection(a, b)) if src == a =>
      Space.Subtraction(src, b)
    case Space.Subtraction(src, Space.Intersection(a, b)) if src == b =>
      Space.Subtraction(src, a)
    case Space.Subtraction(src, Space.Subtraction(src2, removed)) if src == src2 =>
      Space.Intersection(src, removed)
    case Space.Subtraction(Space.Union(a, b), Space.Subtraction(src, removed)) if a == src && b == removed =>
      b
    case Space.Subtraction(Space.Union(a, b), Space.Subtraction(src, removed)) if b == src && a == removed =>
      a
    case Space.Subtraction(src, Space.Restriction(src2, prefixes)) if src == src2 =>
      Space.Raffination(src, prefixes)
    case Space.Subtraction(src, Space.Raffination(src2, prefixes)) if src == src2 =>
      Space.Restriction(src, prefixes)
    case other => other

  private def lowerBound(start: Int): Int =
    if start == 0 then 0 else start - 1

  private def upperBound(start: Int, end: Int): Option[Int] =
    if end == 0 then None
    else if start == 0 then Some(end)
    else Some(end - 1)

  private def encodeRange(lo: Int, hi: Option[Int]): Space => Space =
    hi match
      case Some(upper) if upper <= lo => _ => Space.Empty
      case Some(upper) if lo == 0 => src => Space.Range(src, 0, upper)
      case Some(upper) => src => Space.Range(src, lo + 1, upper + 1)
      case None if lo == 0 => src => Space.Range(src, 0, 0)
      case None => src => Space.Range(src, lo + 1, 0)

  private def composeRange(src: Space, start1: Int, end1: Int, start2: Int, end2: Int): Option[Space] =
    if start2 == 0 && end2 == 0 then Some(Space.Range(src, start1, end1))
    else if start1 >= 0 && end1 >= 0 && start2 >= 0 && end2 >= 0 then Some {
      val lo1 = lowerBound(start1)
      val hi1 = upperBound(start1, end1)
      val lo2 = lowerBound(start2)
      val hi2 = upperBound(start2, end2)
      hi1 match
        case Some(upper1) if upper1 <= lo1 => Space.Empty
        case _ =>
          hi2 match
            case Some(upper2) if upper2 <= lo2 => Space.Empty
            case _ =>
              val lo = lo1 + lo2
              val hi =
                hi2 match
                  case Some(upper2) => Some(lo1 + upper2)
                  case None => hi1
              encodeRange(lo, hi)(src)
    }
    else if start1 > 0 && end1 == 0 && start2 >= 0 && end2 >= 0 then Some {
      val lo1 = lowerBound(start1)
      val lo2 = lowerBound(start2)
      val hi2 = upperBound(start2, end2)
      encodeRange(lo1 + lo2, hi2.map(lo1 + _))(src)
    }
    else if start1 < 0 && end1 == 0 && start2 < 0 && end2 == 0 then Some {
      Space.Range(src, math.max(start1, start2), 0)
    }
    else None

  private def closedEvaluable(s: Space): Boolean =
    def recp(p: Path, boundP: Set[String], boundS: Set[String]): Boolean = p match
      case Path.Deref(pr) => boundP(pr.s)
      case Path.Constant(_) => true
      case Path.Concat(l, r) => recp(l, boundP, boundS) && recp(r, boundP, boundS)
      case Path.GroundedPP(p, _) => recp(p, boundP, boundS)
      case Path.GroundedSP(s, _) => recs(s, boundP, boundS)
    def recs(x: Space, boundP: Set[String], boundS: Set[String]): Boolean = x match
      case Space.Empty | Space.Literal(_) => true
      case Space.Call(_, _, _) => false
      case Space.Mention(sm) => boundS(sm.s)
      case Space.Singleton(p) => recp(p, boundP, boundS)
      case Space.Union(a, b) => recs(a, boundP, boundS) && recs(b, boundP, boundS)
      case Space.Intersection(a, b) => recs(a, boundP, boundS) && recs(b, boundP, boundS)
      case Space.Subtraction(a, b) => recs(a, boundP, boundS) && recs(b, boundP, boundS)
      case Space.Restriction(a, b) => recs(a, boundP, boundS) && recs(b, boundP, boundS)
      case Space.Raffination(a, b) => recs(a, boundP, boundS) && recs(b, boundP, boundS)
      case Space.Composition(a, b) => recs(a, boundP, boundS) && recs(b, boundP, boundS)
      case Space.Iteration(src, symbol, rest, templates) =>
        recs(src, boundP, boundS) && recs(templates, boundP + symbol.s, boundS + rest.s)
      case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
        recs(src, boundP, boundS) &&
          recp(initial, boundP, boundS) &&
          recs(templates, boundP + acc.s + symbol.s, boundS + rest.s) &&
          recp(update, boundP + acc.s + symbol.s, boundS)
      case Space.Fixpoint(initial, variable, step) =>
        recs(initial, boundP, boundS) && recs(step, boundP, boundS + variable.s)
      case Space.Wrap(src, p) => recs(src, boundP, boundS) && recp(p, boundP, boundS)
      case Space.Unwrap(src, p) => recs(src, boundP, boundS) && recp(p, boundP, boundS)
      case Space.TailsUnion(src) => recs(src, boundP, boundS)
      case Space.TailsIntersection(src) => recs(src, boundP, boundS)
      case Space.PrefixClosure(src) => recs(src, boundP, boundS)
      case Space.SuffixClosure(src) => recs(src, boundP, boundS)
      case Space.TailsClosure(src) => recs(src, boundP, boundS)
      case Space.GroundedPS(p, _) => recp(p, boundP, boundS)
      case Space.GroundedSS(src, _) => recs(src, boundP, boundS)
      case Space.Range(src, _, _) => recs(src, boundP, boundS)
    recs(s, Set.empty, Set.empty)

  private def containsFixpoint(s: Space): Boolean =
    def recp(p: Path): Boolean = p match
      case Path.Deref(_) | Path.Constant(_) => false
      case Path.Concat(l, r) => recp(l) || recp(r)
      case Path.GroundedPP(p, _) => recp(p)
      case Path.GroundedSP(s, _) => recs(s)
    def recs(x: Space): Boolean = x match
      case Space.Fixpoint(_, _, _) => true
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => false
      case Space.Call(_, refs, mentions) => refs.exists(recp) || mentions.exists(recs)
      case Space.Singleton(p) => recp(p)
      case Space.Union(a, b) => recs(a) || recs(b)
      case Space.Intersection(a, b) => recs(a) || recs(b)
      case Space.Subtraction(a, b) => recs(a) || recs(b)
      case Space.Restriction(a, b) => recs(a) || recs(b)
      case Space.Raffination(a, b) => recs(a) || recs(b)
      case Space.Composition(a, b) => recs(a) || recs(b)
      case Space.Iteration(src, _, _, templates) => recs(src) || recs(templates)
      case Space.Fold(src, initial, _, _, _, templates, update) =>
        recs(src) || recp(initial) || recs(templates) || recp(update)
      case Space.Wrap(src, p) => recs(src) || recp(p)
      case Space.Unwrap(src, p) => recs(src) || recp(p)
      case Space.TailsUnion(src) => recs(src)
      case Space.TailsIntersection(src) => recs(src)
      case Space.PrefixClosure(src) => recs(src)
      case Space.SuffixClosure(src) => recs(src)
      case Space.TailsClosure(src) => recs(src)
      case Space.GroundedPS(p, _) => recp(p)
      case Space.GroundedSS(src, _) => recs(src)
      case Space.Range(src, _, _) => recs(src)
    recs(s)

  private def foldedLiteral(s: Space): Option[Space] =
    if closedEvaluable(s) then
      val folded = ConstantFoldEval.foldValue(s, containsFixpoint(s))
      folded.toOption.map(literalOrEmpty)
    else None

  val TailsUnion_Iteration = subs(_: Space)(PartialFunction.empty, {
    case Space.TailsUnion(src) =>
      val name = SpaceMention("s" + src.hashCode().toHexString)
      Space.Iteration(src, PathRef("_"), name, Space.Mention(name))
  })

  val Literal_ConstantsUnion = subs(_: Space)(PartialFunction.empty, {
    case Space.Literal(SpaceValue(paths)) =>
      paths.map(p => Space.Singleton(Path.Constant(p))).reduceOption(Space.Union(_, _)).getOrElse(Space.Empty)
  })

  val IterateLiteral_Union = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(Space.Literal(SpaceValue(paths)), symbol, rest, template) =>
      paths.collect { case PathValue(h::tail) => h -> PathValue(tail) }
        .groupMap(_._1)(_._2)
        .map { (h, tails) =>
          subs(template)(spre={ case Space.Mention(`rest`) => Space.Literal(SpaceValue(tails.toSet)) },
                         ppre={ case Path.Deref(`symbol`) => Path.Constant(PathValue(h::Nil)) })
        }
        .reduceOption(Space.Union(_, _)).getOrElse(Space.Empty)
  })

  val IterateSingleton_Deref = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(Space.Singleton(Path.first((Path.Deref(spr), rest))), pr, sm, body) if spr.lengthHint == 1 =>
      subs(body)(spost={ case Space.Mention(`sm`) => if rest.isEmpty then Space.Singleton(Path.Constant(PathValue(Nil))) else Space.Singleton(Path.fromFactors(rest)) },
                 ppost={ case Path.Deref(`pr`) => Path.Deref(spr) })
    case Space.Iteration(Space.Singleton(Path.first((Path.Constant(PathValue(Nil)), rest))), pr, sm, body) => if rest.isEmpty then Space.Empty else
      Space.Iteration(Space.Singleton(Path.fromFactors(rest)), pr, sm, body)
    case Space.Iteration(Space.Singleton(Path.first((Path.Constant(PathValue(h::tail)), rest))), pr, sm, body) =>
      subs(body)(spost={ case Space.Mention(`sm`) => if tail.isEmpty then (if rest.isEmpty then Space.Singleton(Path.Constant(PathValue(Nil))) else Space.Singleton(Path.fromFactors(rest)))
                                                     else Space.Singleton(Path.fromFactors(Path.Constant(PathValue(tail))::rest)) },
                 ppost={ case Path.Deref(`pr`) => Path.Constant(PathValue(h::Nil)) })
  })

  val SingletonConst_Literal = subs(_: Space)(PartialFunction.empty, {
    case Space.Singleton(Path.Constant(p)) => Space.Literal(SpaceValue(Set(p)))
  })

  val LiteralSpaceOps = subs(_: Space)(spost = {
    case Space.Literal(SpaceValue(paths)) if paths.isEmpty => Space.Empty
    case op @ Space.Composition(Space.Literal(_), Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.Union(Space.Literal(_), Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.Intersection(Space.Literal(_), Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.Subtraction(Space.Literal(_), Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.Restriction(Space.Literal(_), Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.Raffination(Space.Literal(_), Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.Range(Space.Literal(_), _, _) => foldedTrieLiteral(op)
    case op @ Space.TailsUnion(Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.TailsIntersection(Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.PrefixClosure(Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.SuffixClosure(Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.TailsClosure(Space.Literal(_)) => foldedTrieLiteral(op)
    case op @ Space.Wrap(Space.Literal(_), Path.Constant(_)) => foldedTrieLiteral(op)
    case op @ Space.Unwrap(Space.Literal(_), Path.Constant(_)) => foldedTrieLiteral(op)
  })

  val ConstantOps = subs(_: Space)(spost = {
    case op => foldedLiteral(op).getOrElse(op)
  })

  val Concat_Path = subs(_: Space)(ppost = {
    case Path.Concat(Path.Constant(PathValue(xs)), Path.Constant(PathValue(ys))) =>
      Path.Constant(PathValue(xs ++ ys))
  })

  val IterUnion_Indep = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if provablyHeaded(src) && {
      val (soc, poc) = collect(lhs)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () })
      soc.isEmpty && poc.isEmpty
    } => Space.Union(Space.Iteration(src, symbol, rest, rhs), lhs)
    case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if provablyHeaded(src) && {
      val (soc, poc) = collect(rhs)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () })
      soc.isEmpty && poc.isEmpty
    } => Space.Union(Space.Iteration(src, symbol, rest, lhs), rhs)
  })

  val UnwrapConcat_Unwraps = subs(_: Space)(PartialFunction.empty, {
    case Space.Unwrap(src, Path.Concat(l, r)) => Space.Unwrap(Space.Unwrap(src, l), r)
  })

  val SingletonSpaceOp_PathOp = subs(_: Space)(PartialFunction.empty, {
    case Space.Wrap(Space.Singleton(y), x) => Space.Singleton(Path.Concat(x, y))
  })

  val SingletonComposition_Wrap = subs(_: Space)(PartialFunction.empty, {
    case Space.Composition(Space.Singleton(x), y) => Space.Wrap(y, x)
  })

  val SingletonRestriction_Unwrap = subs(_: Space)(PartialFunction.empty, {
    case Space.Restriction(x, Space.Singleton(y)) => Space.Wrap(Space.Unwrap(x, y), y)
  })

  val AlgebraicIdentities = subs(_: Space)(spost = {
    case Space.Literal(SpaceValue(paths)) if paths.isEmpty => Space.Empty
    case u @ Space.Union(_, _) => normalizeUnion(u)
    case i @ Space.Intersection(_, _) => normalizeIntersection(i)
    case s @ Space.Subtraction(_, _) => normalizeSubtraction(s)
    case Space.Restriction(Space.Empty, _) => Space.Empty
    case Space.Restriction(_, Space.Empty) => Space.Empty
    case Space.Composition(Space.Empty, _) => Space.Empty
    case Space.Composition(_, Space.Empty) => Space.Empty
    case Space.Wrap(Space.Empty, _) => Space.Empty
    case Space.Unwrap(Space.Empty, _) => Space.Empty
    case Space.Raffination(Space.Empty, _) => Space.Empty
    case Space.Raffination(x, Space.Empty) => x
    case Space.TailsUnion(Space.Empty) => Space.Empty
    case Space.TailsIntersection(Space.Empty) => Space.Empty
    case Space.PrefixClosure(Space.Empty) => Space.Empty
    case Space.SuffixClosure(Space.Empty) => Space.Empty
    case Space.TailsClosure(Space.Empty) => Space.Empty
    case Space.PrefixClosure(Space.PrefixClosure(src)) => Space.PrefixClosure(src)
    case Space.SuffixClosure(Space.SuffixClosure(src)) => Space.SuffixClosure(src)
    case Space.TailsClosure(Space.TailsClosure(src)) => Space.TailsClosure(src)
    case Space.Iteration(Space.Empty, _, _, _) => Space.Empty
    case Space.Fold(Space.Empty, _, _, _, _, _, _) => Space.Empty
    case Space.Fold(src, _, acc, symbol, rest, body, _) if !usesRef(body, acc) =>
      Space.Iteration(src, symbol, rest, body)
    case Space.Iteration(src, _, rest, Space.Mention(sm)) if sm == rest => Space.TailsUnion(src)
    case Space.Iteration(src, symbol, rest, body) if hasStaticHead(src) && !usesRef(body, symbol) && !usesMention(body, rest) => body
    case Space.Fixpoint(initial, variable, Space.Mention(sm)) if sm == variable => initial
    case Space.Fixpoint(initial, variable, Space.Union(Space.Mention(sm), static)) if sm == variable && !usesMention(static, variable) =>
      Space.Union(initial, static)
    case Space.Fixpoint(initial, variable, Space.Union(static, Space.Mention(sm))) if sm == variable && !usesMention(static, variable) =>
      Space.Union(initial, static)
    case Space.Fixpoint(initial, variable, Space.TailsUnion(Space.Mention(sm))) if sm == variable =>
      Space.TailsClosure(initial)
    case Space.Fixpoint(initial, variable, Space.Union(Space.TailsUnion(Space.Mention(sm)), static)) if sm == variable && !usesMention(static, variable) =>
      Space.TailsClosure(Space.Union(initial, static))
    case Space.Fixpoint(initial, variable, Space.Union(static, Space.TailsUnion(Space.Mention(sm)))) if sm == variable && !usesMention(static, variable) =>
      Space.TailsClosure(Space.Union(initial, static))
    case Space.Fixpoint(initial, variable, step) if !usesMention(step, variable) =>
      Space.Union(initial, step)
    case Space.Range(src, 0, 0) => src
    case Space.Range(_, start, end) if start != 0 && start == end => Space.Empty
    case Space.Range(_, start, end) if start > 0 && end > 0 && end <= start => Space.Empty
    case Space.Range(_, start, end) if start < 0 && end < 0 && end <= start => Space.Empty
    case Space.Range(Space.Range(src, start1, end1), start2, end2) =>
      composeRange(src, start1, end1, start2, end2).getOrElse(Space.Range(Space.Range(src, start1, end1), start2, end2))
    case Space.Range(Space.Empty, _, _) => Space.Empty
  }, ppost = {
    case Path.Concat(Path.Constant(PathValue(Nil)), x) => x
    case Path.Concat(x, Path.Constant(PathValue(Nil))) => x
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
    => Space.Subtraction(src, Space.Singleton(Path.ZERO))
    case Space.Iteration(src, symbol, rest, Space.Wrap(Space.Mention(sm), Path.Concat(prefix, Path.Deref(pr)))) if symbol == pr && sm == rest && {
      val (soc, poc) = collect(Space.Singleton(prefix))({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () })
      soc.isEmpty && poc.isEmpty
    } => Space.Wrap(Space.Subtraction(src, Space.Singleton(Path.ZERO)), prefix)
    case Space.Iteration(src, symbol, rest, Space.Composition(Space.Singleton(Path.Concat(prefix, Path.Deref(pr))), Space.Mention(sm))) if symbol == pr && sm == rest && {
      val (soc, poc) = collect(Space.Singleton(prefix))({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () })
      soc.isEmpty && poc.isEmpty
    } => Space.Wrap(Space.Subtraction(src, Space.Singleton(Path.ZERO)), prefix)
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

case class SpaceStats(
  spaceNodes: Int,
  pathNodes: Int,
  depth: Int,
  calls: Int,
  mentions: Int,
  pathRefs: Int,
  literals: Int,
  iterations: Int,
  folds: Int,
  grounded: Int
):
  def totalNodes: Int = spaceNodes + pathNodes
  def compact: String =
    s"nodes=$totalNodes space=$spaceNodes path=$pathNodes depth=$depth calls=$calls mentions=$mentions refs=$pathRefs literals=$literals iter=$iterations folds=$folds grounded=$grounded"

object SpaceStats:
  val empty: SpaceStats = SpaceStats(0, 0, 0, 0, 0, 0, 0, 0, 0, 0)

  extension (x: SpaceStats)
    def +(y: SpaceStats): SpaceStats = SpaceStats(
      x.spaceNodes + y.spaceNodes,
      x.pathNodes + y.pathNodes,
      x.depth.max(y.depth),
      x.calls + y.calls,
      x.mentions + y.mentions,
      x.pathRefs + y.pathRefs,
      x.literals + y.literals,
      x.iterations + y.iterations,
      x.folds + y.folds,
      x.grounded + y.grounded
    )

case class CompileBudget(maxMillis: Long = 30_000):
  require(maxMillis > 0, "compile budget must be positive")
  def start(): CompileDeadline =
    val now = System.nanoTime()
    val span =
      if maxMillis > Long.MaxValue / 1_000_000L then Long.MaxValue
      else maxMillis * 1_000_000L
    val deadline =
      if Long.MaxValue - now < span then Long.MaxValue
      else now + span
    CompileDeadline(now, deadline, maxMillis)

case class CompileDeadline(startNanos: Long, deadlineNanos: Long, maxMillis: Long):
  def check(phase: String): Unit =
    if System.nanoTime() > deadlineNanos then
      throw RuntimeException(s"compile time cap ${maxMillis} ms exceeded during $phase")
  def elapsedMs: Double = (System.nanoTime() - startNanos).toDouble / 1_000_000.0

case class ConstantFoldEvalStats(evalCalls: Int,
                                 evalTrieCalls: Int,
                                 evalZCalls: Int,
                                 execTCalls: Int,
                                 evalNanos: Long,
                                 evalTrieNanos: Long,
                                 evalZNanos: Long,
                                 execTNanos: Long):
  def evalMs: Double = evalNanos.toDouble / 1_000_000.0
  def evalTrieMs: Double = evalTrieNanos.toDouble / 1_000_000.0
  def evalZMs: Double = evalZNanos.toDouble / 1_000_000.0
  def execTMs: Double = execTNanos.toDouble / 1_000_000.0
  def totalMs: Double = evalMs + evalTrieMs + evalZMs + execTMs

object ConstantFoldEval:
  enum Backend:
    case Reference, Trie, Zipper, ExecT, Hybrid

  object Backend:
    def parse(name: String): Option[Backend] =
      name.trim.toLowerCase(Locale.ROOT) match
        case "reference" | "eval" | "set" => Some(Reference)
        case "trie" | "evaltrie" => Some(Trie)
        case "zipper" | "evalz" => Some(Zipper)
        case "exect" | "exec-t" | "graph" => Some(ExecT)
        case "hybrid" => Some(Hybrid)
        case _ => None

  private final class Mutable:
    var evalCalls: Int = 0
    var evalTrieCalls: Int = 0
    var evalZCalls: Int = 0
    var execTCalls: Int = 0
    var evalNanos: Long = 0L
    var evalTrieNanos: Long = 0L
    var evalZNanos: Long = 0L
    var execTNanos: Long = 0L

  private val local = ThreadLocal.withInitial(() => Mutable())
  private val backendOverride = ThreadLocal.withInitial[Option[Backend]](() => None)

  def backend: Backend =
    backendOverride.get().orElse(sys.props.get("morkl.constantFoldBackend").flatMap(Backend.parse)).getOrElse(Backend.Reference)

  def withBackend[A](next: Backend)(body: => A): A =
    val prev = backendOverride.get()
    backendOverride.set(Some(next))
    try body
    finally backendOverride.set(prev)

  def reset(): Unit =
    local.set(Mutable())

  def snapshot: ConstantFoldEvalStats =
    val s = local.get()
    ConstantFoldEvalStats(
      s.evalCalls,
      s.evalTrieCalls,
      s.evalZCalls,
      s.execTCalls,
      s.evalNanos,
      s.evalTrieNanos,
      s.evalZNanos,
      s.execTNanos
    )

  def timedEval[A](f: => A): A =
    val s = local.get()
    val start = System.nanoTime()
    try f
    finally
      s.evalCalls += 1
      s.evalNanos += System.nanoTime() - start

  def timedEvalTrie[A](f: => A): A =
    val s = local.get()
    val start = System.nanoTime()
    try f
    finally
      s.evalTrieCalls += 1
      s.evalTrieNanos += System.nanoTime() - start

  def timedEvalZ[A](f: => A): A =
    val s = local.get()
    val start = System.nanoTime()
    try f
    finally
      s.evalZCalls += 1
      s.evalZNanos += System.nanoTime() - start

  def timedExecT[A](f: => A): A =
    val s = local.get()
    val start = System.nanoTime()
    try f
    finally
      s.execTCalls += 1
      s.execTNanos += System.nanoTime() - start

  private def execTValue(s: Space): SpaceValue =
    val graph = transpile(Routine(RoutinePtr("__constant_fold"), Vector.empty, Vector.empty, s))
    val frame = new Array[List[Int] | TrieSpace | Null](graph.nodes.length)
    val stack = collection.mutable.Stack(frame)
    execT(graph, stack)
    frame.last.asInstanceOf[TrieSpace].toSpaceValue

  private def graphFavored(s: Space): Boolean =
    def recp(p: Path): Boolean = p match
      case Path.Deref(_) | Path.Constant(_) => false
      case Path.Concat(l, r) => recp(l) || recp(r)
      case Path.GroundedPP(p, _) => recp(p)
      case Path.GroundedSP(s, _) => recs(s)
    def recs(x: Space): Boolean = x match
      case Space.Fold(_, _, _, _, _, _, _) | Space.Fixpoint(_, _, _) | Space.Range(_, _, _) => true
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => false
      case Space.Call(_, refs, mentions) => refs.exists(recp) || mentions.exists(recs)
      case Space.Singleton(p) => recp(p)
      case Space.Union(a, b) => recs(a) || recs(b)
      case Space.Intersection(a, b) => recs(a) || recs(b)
      case Space.Subtraction(a, b) => recs(a) || recs(b)
      case Space.Restriction(a, b) => recs(a) || recs(b)
      case Space.Raffination(a, b) => recs(a) || recs(b)
      case Space.Composition(a, b) => recs(a) || recs(b)
      case Space.Iteration(src, _, _, templates) => recs(src) || recs(templates)
      case Space.Wrap(src, p) => recs(src) || recp(p)
      case Space.Unwrap(src, p) => recs(src) || recp(p)
      case Space.TailsUnion(src) => recs(src)
      case Space.TailsIntersection(src) => recs(src)
      case Space.PrefixClosure(src) => recs(src)
      case Space.SuffixClosure(src) => recs(src)
      case Space.TailsClosure(src) => recs(src)
      case Space.GroundedPS(p, _) => recp(p)
      case Space.GroundedSS(src, _) => recs(src)
    recs(s)

  private def referenceValue(s: Space, hasFixpoint: Boolean): scala.util.Try[SpaceValue] =
    if hasFixpoint then scala.util.Try(timedEvalTrie(evalTrieValue(s)))
    else scala.util.Try(timedEval(eval(s)))

  def foldValue(s: Space, hasFixpoint: Boolean): scala.util.Try[SpaceValue] =
    backend match
      case Backend.Reference =>
        referenceValue(s, hasFixpoint)
      case Backend.Trie =>
        scala.util.Try(timedEvalTrie(evalTrieValue(s))).orElse(referenceValue(s, hasFixpoint))
      case Backend.Zipper =>
        scala.util.Try(timedEvalZ(evalZValue(s))).orElse(referenceValue(s, hasFixpoint))
      case Backend.ExecT =>
        scala.util.Try(timedExecT(execTValue(s)))
          .orElse(scala.util.Try(timedEvalTrie(evalTrieValue(s))))
          .orElse(referenceValue(s, hasFixpoint))
      case Backend.Hybrid =>
        if graphFavored(s) then
          scala.util.Try(timedExecT(execTValue(s)))
            .orElse(referenceValue(s, hasFixpoint))
        else referenceValue(s, hasFixpoint)

object CompileBudget:
  val Default: CompileBudget = CompileBudget()

case class OptimizationTiming(stage: String,
                              round: Int,
                              pass: String,
                              elapsedMs: Double,
                              changed: Boolean,
                              beforeNodes: Int,
                              afterNodes: Int):
  def compact: String =
    val flag = if changed then "*" else "-"
    f"$stage#$round $pass $flag ${beforeNodes} -> ${afterNodes} in $elapsedMs%.3f ms"

case class SupercompileStep(round: Int, pass: String, before: SpaceStats, after: SpaceStats, elapsedMs: Double = 0.0):
  def compact: String = f"#$round $pass: ${before.totalNodes} -> ${after.totalNodes} in $elapsedMs%.3f ms"

case class GraphStats(nodes: Int, subgraphs: Int, depth: Int):
  def compact: String = s"nodes=$nodes subgraphs=$subgraphs depth=$depth"

case class NormalizeResult(space: Space,
                           steps: Vector[SupercompileStep],
                           timings: Vector[OptimizationTiming],
                           rounds: Int,
                           converged: Boolean)

case class GraphOptimizeResult(graph: RecursiveOpGraph,
                               timings: Vector[OptimizationTiming],
                               rounds: Int,
                               converged: Boolean,
                               elapsedMs: Double)

case class SupercompileReport(
  name: RoutinePtr,
  before: SpaceStats,
  after: SpaceStats,
  steps: Vector[SupercompileStep],
  rounds: Int,
  converged: Boolean,
  graphBefore: Option[GraphStats],
  graphAfter: Option[GraphStats],
  backendUnsupported: Vector[String],
  sourceTimings: Vector[OptimizationTiming] = Vector.empty,
  graphTimings: Vector[OptimizationTiming] = Vector.empty,
  loweringMs: Double = 0.0,
  inlineMs: Double = 0.0,
  graphTranspileMs: Double = 0.0,
  graphOptimizeMs: Double = 0.0,
  constantFoldEvalMs: Double = 0.0,
  constantFoldEvalTrieMs: Double = 0.0,
  constantFoldEvalZMs: Double = 0.0,
  constantFoldExecTMs: Double = 0.0,
  constantFoldEvalCalls: Int = 0,
  constantFoldEvalTrieCalls: Int = 0,
  constantFoldEvalZCalls: Int = 0,
  constantFoldExecTCalls: Int = 0,
  compileMs: Double = 0.0,
  maxCompileMillis: Long = CompileBudget.Default.maxMillis,
  graphError: Option[String] = None
):
  def changed: Boolean = steps.nonEmpty
  def backendCompiled: Boolean = graphAfter.nonEmpty
  def sourceOptimizeMs: Double = sourceTimings.map(_.elapsedMs).sum
  def summary: String =
    val convergence = if converged then s"converged in $rounds rounds" else s"stopped after $rounds rounds"
    val graph = (graphBefore, graphAfter) match
      case (Some(b), Some(a)) => s", graph ${b.nodes} -> ${a.nodes}"
      case (Some(b), None) => s", graph ${b.nodes} -> unavailable after optimization"
      case (None, None) if backendUnsupported.nonEmpty => s", source-only backend gaps: ${backendUnsupported.distinct.sorted.mkString(", ")}"
      case (None, None) if graphError.nonEmpty => s", graph unavailable: ${graphError.get}"
      case _ => ""
    val fold =
      val calls = constantFoldEvalCalls + constantFoldEvalTrieCalls + constantFoldEvalZCalls + constantFoldExecTCalls
      val total = constantFoldEvalMs + constantFoldEvalTrieMs + constantFoldEvalZMs + constantFoldExecTMs
      if calls == 0 then ""
      else f", const-fold eval $total%.3f ms (${constantFoldEvalCalls} eval, ${constantFoldEvalTrieCalls} evalTrie, ${constantFoldEvalZCalls} evalZ, ${constantFoldExecTCalls} execT)"
    f"${name.s}: ${before.totalNodes} -> ${after.totalNodes} AST nodes, ${steps.size} pass changes, $convergence$graph$fold, compile $compileMs%.3f ms / budget ${maxCompileMillis} ms"

case class SupercompiledRoutine(routine: Routine, report: SupercompileReport, graph: Option[RecursiveOpGraph]):
  def semanticEquals(original: Routine)(using pc: PathContext = PathContext.emptyMap,
                                        sc: SpaceContext = SpaceContextMap(Map.empty),
                                        rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Boolean =
    eval(original.body)(using pc, sc, rc) == eval(routine.body)(using pc, sc, rc)

object Supercompiler:
  val defaultSourcePasses: Vector[(String, Space => Space)] = Vector(
    "algebraic-identities" -> Lower.AlgebraicIdentities,
    "constant-paths" -> Lower.Concat_Path,
    "constant-spaces" -> Lower.ConstantOps,
    "singleton-to-literal" -> Lower.SingletonConst_Literal,
    "literal-space-ops" -> Lower.LiteralSpaceOps,
    "literal-iteration" -> Lower.IterateLiteral_Union,
    "singleton-iteration" -> Lower.IterateSingleton_Deref,
    "composition-singleton" -> Lower.SingletonComposition_Wrap,
    "singleton-space-op" -> Lower.SingletonSpaceOp_PathOp,
    "restriction-singleton" -> Lower.SingletonRestriction_Unwrap,
    "unwrap-concat" -> Lower.UnwrapConcat_Unwraps,
    "concat-singleton-iteration" -> Lower.ConcatSingleton_Iter,
    "wrap-iteration" -> Lower.Wrap_Iter,
    "iteration-union-invariant" -> Lower.IterUnion_Indep,
    "iteration-identity" -> Lower.Iter_Ident,
    "algebraic-cleanup" -> Lower.AlgebraicIdentities,
    "literal-cleanup" -> Lower.LiteralSpaceOps
  )

  def stats(s: Space): SpaceStats =
    def bumpSpace(x: SpaceStats, depth: Int): SpaceStats = x.copy(spaceNodes = x.spaceNodes + 1, depth = x.depth.max(depth))
    def bumpPath(x: SpaceStats, depth: Int): SpaceStats = x.copy(pathNodes = x.pathNodes + 1, depth = x.depth.max(depth))

    def recp(p: Path, depth: Int): SpaceStats = p match
      case Path.Deref(_) => bumpPath(SpaceStats.empty.copy(pathRefs = 1), depth)
      case Path.Constant(_) => bumpPath(SpaceStats.empty, depth)
      case Path.Concat(l, r) => bumpPath(recp(l, depth + 1) + recp(r, depth + 1), depth)
      case Path.GroundedPP(p, _) =>
        val child = recp(p, depth + 1)
        bumpPath(child.copy(grounded = child.grounded + 1), depth)
      case Path.GroundedSP(s, _) =>
        val child = recs(s, depth + 1)
        bumpPath(child.copy(grounded = child.grounded + 1), depth)

    def recs(x: Space, depth: Int): SpaceStats = x match
      case Space.Empty => bumpSpace(SpaceStats.empty, depth)
      case Space.Call(_, refs, mentions) =>
        val child = refs.foldLeft(SpaceStats.empty)(_ + recp(_, depth + 1)) +
          mentions.foldLeft(SpaceStats.empty)(_ + recs(_, depth + 1))
        bumpSpace(child.copy(calls = child.calls + 1), depth)
      case Space.Mention(_) => bumpSpace(SpaceStats.empty.copy(mentions = 1), depth)
      case Space.Singleton(p) => bumpSpace(recp(p, depth + 1), depth)
      case Space.Literal(_) => bumpSpace(SpaceStats.empty.copy(literals = 1), depth)
      case Space.Union(x, y) => bumpSpace(recs(x, depth + 1) + recs(y, depth + 1), depth)
      case Space.Intersection(x, y) => bumpSpace(recs(x, depth + 1) + recs(y, depth + 1), depth)
      case Space.Subtraction(x, y) => bumpSpace(recs(x, depth + 1) + recs(y, depth + 1), depth)
      case Space.Restriction(x, y) => bumpSpace(recs(x, depth + 1) + recs(y, depth + 1), depth)
      case Space.Raffination(x, y) => bumpSpace(recs(x, depth + 1) + recs(y, depth + 1), depth)
      case Space.Composition(x, y) => bumpSpace(recs(x, depth + 1) + recs(y, depth + 1), depth)
      case Space.Iteration(src, _, _, templates) =>
        val child = recs(src, depth + 1) + recs(templates, depth + 1)
        bumpSpace(child.copy(iterations = child.iterations + 1), depth)
      case Space.Fold(src, initial, _, _, _, templates, update) =>
        val child = recs(src, depth + 1) + recp(initial, depth + 1) + recs(templates, depth + 1) + recp(update, depth + 1)
        bumpSpace(child.copy(folds = child.folds + 1), depth)
      case Space.Fixpoint(initial, _, step) =>
        val child = recs(initial, depth + 1) + recs(step, depth + 1)
        bumpSpace(child.copy(iterations = child.iterations + 1), depth)
      case Space.Wrap(src, p) => bumpSpace(recs(src, depth + 1) + recp(p, depth + 1), depth)
      case Space.Unwrap(src, p) => bumpSpace(recs(src, depth + 1) + recp(p, depth + 1), depth)
      case Space.TailsUnion(src) => bumpSpace(recs(src, depth + 1), depth)
      case Space.TailsIntersection(src) => bumpSpace(recs(src, depth + 1), depth)
      case Space.PrefixClosure(src) => bumpSpace(recs(src, depth + 1), depth)
      case Space.SuffixClosure(src) => bumpSpace(recs(src, depth + 1), depth)
      case Space.TailsClosure(src) => bumpSpace(recs(src, depth + 1), depth)
      case Space.GroundedPS(p, _) =>
        val child = recp(p, depth + 1)
        bumpSpace(child.copy(grounded = child.grounded + 1), depth)
      case Space.GroundedSS(s, _) =>
        val child = recs(s, depth + 1)
        bumpSpace(child.copy(grounded = child.grounded + 1), depth)
      case Space.Range(x, _, _) => bumpSpace(recs(x, depth + 1), depth)

    recs(s, 1)

  def graphStats(g: RecursiveOpGraph): GraphStats =
    val children = g.nodes.collect { case Right(sg) => graphStats(sg) }
    GraphStats(
      nodes = g.nodes.size + children.map(_.nodes).sum,
      subgraphs = children.size + children.map(_.subgraphs).sum,
      depth = children.map(_.depth + 1).maxOption.getOrElse(1)
    )

  def normalize(s: Space,
                passes: Vector[(String, Space => Space)] = defaultSourcePasses,
                maxRounds: Int = 128,
                deadline: CompileDeadline = CompileBudget.Default.start()): NormalizeResult =
    var current = s
    var currentStats = stats(current)
    val steps = Vector.newBuilder[SupercompileStep]
    val timings = Vector.newBuilder[OptimizationTiming]
    var changed = true
    var round = 0
    while changed && round < maxRounds do
      deadline.check("source normalization")
      changed = false
      for (name, pass) <- passes do
        val before = current
        val beforeStats = currentStats
        val start = System.nanoTime()
        val after = pass(current)
        val elapsed = (System.nanoTime() - start).toDouble / 1_000_000.0
        val changedPass = before != after
        val afterStats =
          if changedPass then stats(after)
          else beforeStats
        timings += OptimizationTiming("source", round, name, elapsed, changedPass, beforeStats.totalNodes, afterStats.totalNodes)
        if changedPass then
          steps += SupercompileStep(round, name, beforeStats, afterStats, elapsed)
          current = after
          currentStats = afterStats
          changed = true
        deadline.check(s"source pass $name")
      round += 1
    NormalizeResult(current, steps.result(), timings.result(), round, !changed)

  def lowerFixpointCalls(s: Space, ctx: PartialFunction[RoutinePtr, Routine]): Space =
    case class RecursiveArc(target: RoutinePtr, arg: Space)
    case class UnionSaturatingShape(variable: SpaceMention, arcs: Vector[RecursiveArc])

    def unionLeaves(x: Space): Vector[Space] = x match
      case Space.Union(a, b) => unionLeaves(a) ++ unionLeaves(b)
      case other => Vector(other)

    def rebuildUnion(terms: Vector[Space]): Space =
      if terms.isEmpty then Space.Empty else terms.reduceLeft(Space.Union(_, _))

    def calledRoutines(x: Space): Set[RoutinePtr] =
      val out = Set.newBuilder[RoutinePtr]
      def recp(p: Path): Unit = p match
        case Path.Deref(_) | Path.Constant(_) => ()
        case Path.Concat(l, r) =>
          recp(l)
          recp(r)
        case Path.GroundedPP(p, _) => recp(p)
        case Path.GroundedSP(s, _) => recs(s)
      def recs(x: Space): Unit = x match
        case Space.Empty | Space.Mention(_) | Space.Literal(_) => ()
        case Space.Call(rp, refs, mentions) =>
          out += rp
          refs.foreach(recp)
          mentions.foreach(recs)
        case Space.Singleton(p) => recp(p)
        case Space.Union(a, b) =>
          recs(a)
          recs(b)
        case Space.Intersection(a, b) =>
          recs(a)
          recs(b)
        case Space.Subtraction(a, b) =>
          recs(a)
          recs(b)
        case Space.Restriction(a, b) =>
          recs(a)
          recs(b)
        case Space.Raffination(a, b) =>
          recs(a)
          recs(b)
        case Space.Composition(a, b) =>
          recs(a)
          recs(b)
        case Space.Iteration(src, _, _, templates) =>
          recs(src)
          recs(templates)
        case Space.Fold(src, initial, _, _, _, templates, update) =>
          recs(src)
          recp(initial)
          recs(templates)
          recp(update)
        case Space.Fixpoint(initial, _, step) =>
          recs(initial)
          recs(step)
        case Space.Wrap(src, p) =>
          recs(src)
          recp(p)
        case Space.Unwrap(src, p) =>
          recs(src)
          recp(p)
        case Space.TailsUnion(src) => recs(src)
        case Space.TailsIntersection(src) => recs(src)
        case Space.PrefixClosure(src) => recs(src)
        case Space.SuffixClosure(src) => recs(src)
        case Space.TailsClosure(src) => recs(src)
        case Space.GroundedPS(p, _) => recp(p)
        case Space.GroundedSS(src, _) => recs(src)
        case Space.Range(src, _, _) => recs(src)
      recs(x)
      out.result()

    def discover(seed: RoutinePtr): Map[RoutinePtr, Routine] =
      val defs = collection.mutable.LinkedHashMap.empty[RoutinePtr, Routine]
      def visit(rp: RoutinePtr): Unit =
        if ctx.isDefinedAt(rp) && !defs.contains(rp) then
          val r = ctx(rp)
          defs += rp -> r
          calledRoutines(r.body).filter(ctx.isDefinedAt).foreach(visit)
      visit(seed)
      defs.toMap

    def reachable(start: RoutinePtr, graph: Map[RoutinePtr, Set[RoutinePtr]]): Set[RoutinePtr] =
      val seen = collection.mutable.Set.empty[RoutinePtr]
      def visit(rp: RoutinePtr): Unit =
        if !seen(rp) then
          seen += rp
          graph.getOrElse(rp, Set.empty).foreach(visit)
      visit(start)
      seen.toSet

    def componentFor(seed: RoutinePtr): Option[(Map[RoutinePtr, Routine], Set[RoutinePtr])] =
      val defs = discover(seed)
      Option.when(defs.contains(seed)) {
        val graph = defs.view.mapValues(r => calledRoutines(r.body).filter(defs.contains)).toMap
        val fromSeed = reachable(seed, graph)
        val component = fromSeed.filter(rp => reachable(rp, graph)(seed))
        defs -> component
      }

    def hasComponentCall(x: Space, component: Set[RoutinePtr]): Boolean =
      calledRoutines(x).exists(component)

    def shapeFor(r: Routine, component: Set[RoutinePtr]): Option[UnionSaturatingShape] =
      r match
        case Routine(_, Vector(), Vector(variable), body) =>
          var sawBase = false
          var valid = true
          val arcs = Vector.newBuilder[RecursiveArc]
          for term <- unionLeaves(body) do
            term match
              case Space.Mention(sm) if sm == variable =>
                sawBase = true
              case Space.Call(target, Vector(), Vector(arg)) if component(target) && !hasComponentCall(arg, component) =>
                arcs += RecursiveArc(target, arg)
              case _ =>
                valid = false
          val result = arcs.result()
          Option.when(valid && sawBase && result.nonEmpty)(UnionSaturatingShape(variable, result))
        case _ => None

    def replaceMention(s: Space, variable: SpaceMention, replacement: Space): Space =
      def recp(p: Path, spaceShadowed: Boolean): Path = p match
        case Path.Deref(_) | Path.Constant(_) => p
        case Path.Concat(l, r) => Path.Concat(recp(l, spaceShadowed), recp(r, spaceShadowed))
        case Path.GroundedPP(p, f) => Path.GroundedPP(recp(p, spaceShadowed), f)
        case Path.GroundedSP(s, f) => Path.GroundedSP(recs(s, spaceShadowed), f)
      def recs(x: Space, shadowed: Boolean): Space = x match
        case Space.Mention(sm) if !shadowed && sm == variable => replacement
        case Space.Empty | Space.Mention(_) | Space.Literal(_) => x
        case Space.Call(rp, refs, mentions) => Space.Call(rp, refs.map(recp(_, shadowed)), mentions.map(recs(_, shadowed)))
        case Space.Singleton(p) => Space.Singleton(recp(p, shadowed))
        case Space.Union(a, b) => Space.Union(recs(a, shadowed), recs(b, shadowed))
        case Space.Intersection(a, b) => Space.Intersection(recs(a, shadowed), recs(b, shadowed))
        case Space.Subtraction(a, b) => Space.Subtraction(recs(a, shadowed), recs(b, shadowed))
        case Space.Restriction(a, b) => Space.Restriction(recs(a, shadowed), recs(b, shadowed))
        case Space.Raffination(a, b) => Space.Raffination(recs(a, shadowed), recs(b, shadowed))
        case Space.Composition(a, b) => Space.Composition(recs(a, shadowed), recs(b, shadowed))
        case Space.Iteration(src, symbol, rest, templates) =>
          Space.Iteration(recs(src, shadowed), symbol, rest, recs(templates, shadowed || rest == variable))
        case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
          val nested = shadowed || rest == variable
          Space.Fold(recs(src, shadowed), recp(initial, shadowed), acc, symbol, rest, recs(templates, nested), recp(update, nested))
        case Space.Fixpoint(initial, bound, step) =>
          Space.Fixpoint(recs(initial, shadowed), bound, recs(step, shadowed || bound == variable))
        case Space.Wrap(src, p) => Space.Wrap(recs(src, shadowed), recp(p, shadowed))
        case Space.Unwrap(src, p) => Space.Unwrap(recs(src, shadowed), recp(p, shadowed))
        case Space.TailsUnion(src) => Space.TailsUnion(recs(src, shadowed))
        case Space.TailsIntersection(src) => Space.TailsIntersection(recs(src, shadowed))
        case Space.PrefixClosure(src) => Space.PrefixClosure(recs(src, shadowed))
        case Space.SuffixClosure(src) => Space.SuffixClosure(recs(src, shadowed))
        case Space.TailsClosure(src) => Space.TailsClosure(recs(src, shadowed))
        case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p, shadowed), f)
        case Space.GroundedSS(src, f) => Space.GroundedSS(recs(src, shadowed), f)
        case Space.Range(src, start, end) => Space.Range(recs(src, shadowed), start, end)
      recs(s, shadowed = false)

    def mentionsIn(component: Iterable[Routine]): Set[String] =
      val out = Set.newBuilder[String]
      def recp(p: Path): Unit = p match
        case Path.Deref(_) | Path.Constant(_) => ()
        case Path.Concat(l, r) =>
          recp(l)
          recp(r)
        case Path.GroundedPP(p, _) => recp(p)
        case Path.GroundedSP(s, _) => recs(s)
      def recs(x: Space): Unit = x match
        case Space.Empty | Space.Literal(_) => ()
        case Space.Mention(sm) => out += sm.s
        case Space.Call(_, refs, mentions) =>
          refs.foreach(recp)
          mentions.foreach(recs)
        case Space.Singleton(p) => recp(p)
        case Space.Union(a, b) =>
          recs(a)
          recs(b)
        case Space.Intersection(a, b) =>
          recs(a)
          recs(b)
        case Space.Subtraction(a, b) =>
          recs(a)
          recs(b)
        case Space.Restriction(a, b) =>
          recs(a)
          recs(b)
        case Space.Raffination(a, b) =>
          recs(a)
          recs(b)
        case Space.Composition(a, b) =>
          recs(a)
          recs(b)
        case Space.Iteration(src, _, rest, templates) =>
          out += rest.s
          recs(src)
          recs(templates)
        case Space.Fold(src, initial, _, _, rest, templates, update) =>
          out += rest.s
          recs(src)
          recp(initial)
          recs(templates)
          recp(update)
        case Space.Fixpoint(initial, variable, step) =>
          out += variable.s
          recs(initial)
          recs(step)
        case Space.Wrap(src, p) =>
          recs(src)
          recp(p)
        case Space.Unwrap(src, p) =>
          recs(src)
          recp(p)
        case Space.TailsUnion(src) => recs(src)
        case Space.TailsIntersection(src) => recs(src)
        case Space.PrefixClosure(src) => recs(src)
        case Space.SuffixClosure(src) => recs(src)
        case Space.TailsClosure(src) => recs(src)
        case Space.GroundedPS(p, _) => recp(p)
        case Space.GroundedSS(src, _) => recs(src)
        case Space.Range(src, _, _) => recs(src)
      component.foreach(r => recs(r.body))
      out.result()

    def freshMention(prefix: String, used: Set[String]): SpaceMention =
      var i = 0
      var candidate = prefix
      while used(candidate) do
        i += 1
        candidate = s"${prefix}_$i"
      SpaceMention(candidate)

    def componentTag(rp: RoutinePtr): Path =
      Path.Constant(PathValue(PathItem("#mutual_fix") :: PathItem(rp.s) :: Nil))

    val guardTag = Path.Constant(PathValue(PathItem("#mutual_fix_guard") :: Nil))

    def whenNonEmpty(src: Space, body: Space): Space =
      Space.Iteration(Space.Wrap(src, guardTag), PathRef("__mutual_fix_guard").known(1), SpaceMention("_"), body)

    def recp(p: Path): Path = p match
      case Path.Deref(_) | Path.Constant(_) => p
      case Path.Concat(l, r) => Path.Concat(recp(l), recp(r))
      case Path.GroundedPP(p, f) => Path.GroundedPP(recp(p), f)
      case Path.GroundedSP(s, f) => Path.GroundedSP(recs(s), f)
    def singleFixpointFor(rp: RoutinePtr, arg: Space): Option[Space] =
      Option.when(ctx.isDefinedAt(rp))(ctx(rp)).collect {
        case Routine(`rp`, Vector(), Vector(variable), Space.Union(Space.Mention(lhs), Space.Call(`rp`, Vector(), Vector(step)))) if lhs == variable =>
          Space.Fixpoint(recs(arg), variable, recs(step))
      }
    def mutualFixpointFor(rp: RoutinePtr, arg: Space): Option[Space] =
      componentFor(rp).flatMap { (defs, component) =>
        if component.size <= 1 then None
        else
          val routines = component.toVector.sortBy(_.s).map(defs)
          val shapes = routines.map(r => r.name -> shapeFor(r, component)).toMap
          Option.when(shapes.values.forall(_.nonEmpty)) {
            val state = freshMention("__mutual_fix_state", mentionsIn(routines))
            val stepTerms = Vector.newBuilder[Space]
            for source <- component.toVector.sortBy(_.s) do
              val shape = shapes(source).get
              val current = Space.Unwrap(Space.Mention(state), componentTag(source))
              for arc <- shape.arcs do
                val nextArg = replaceMention(arc.arg, shape.variable, current)
                stepTerms += whenNonEmpty(current, Space.Wrap(recs(nextArg), componentTag(arc.target)))
            val step = rebuildUnion(stepTerms.result())
            val initial = Space.Wrap(recs(arg), componentTag(rp))
            Space.Unwrap(Space.Fixpoint(initial, state, step), componentTag(rp))
          }
      }
    def fixpointFor(rp: RoutinePtr, arg: Space): Option[Space] =
      singleFixpointFor(rp, arg).orElse(mutualFixpointFor(rp, arg))
    def recs(x: Space): Space = x match
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => x
      case Space.Call(rp, refs, Vector(arg)) if refs.isEmpty =>
        fixpointFor(rp, arg).getOrElse(Space.Call(rp, refs.map(recp), Vector(recs(arg))))
      case Space.Call(rp, refs, mentions) => Space.Call(rp, refs.map(recp), mentions.map(recs))
      case Space.Singleton(p) => Space.Singleton(recp(p))
      case Space.Union(x, y) => Space.Union(recs(x), recs(y))
      case Space.Intersection(x, y) => Space.Intersection(recs(x), recs(y))
      case Space.Subtraction(x, y) => Space.Subtraction(recs(x), recs(y))
      case Space.Restriction(x, y) => Space.Restriction(recs(x), recs(y))
      case Space.Raffination(x, y) => Space.Raffination(recs(x), recs(y))
      case Space.Composition(x, y) => Space.Composition(recs(x), recs(y))
      case Space.Iteration(src, symbol, rest, templates) => Space.Iteration(recs(src), symbol, rest, recs(templates))
      case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
        Space.Fold(recs(src), recp(initial), acc, symbol, rest, recs(templates), recp(update))
      case Space.Fixpoint(initial, variable, step) => Space.Fixpoint(recs(initial), variable, recs(step))
      case Space.Wrap(src, p) => Space.Wrap(recs(src), recp(p))
      case Space.Unwrap(src, p) => Space.Unwrap(recs(src), recp(p))
      case Space.TailsUnion(src) => Space.TailsUnion(recs(src))
      case Space.TailsIntersection(src) => Space.TailsIntersection(recs(src))
      case Space.PrefixClosure(src) => Space.PrefixClosure(recs(src))
      case Space.SuffixClosure(src) => Space.SuffixClosure(recs(src))
      case Space.TailsClosure(src) => Space.TailsClosure(recs(src))
      case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p), f)
      case Space.GroundedSS(src, f) => Space.GroundedSS(recs(src), f)
      case Space.Range(src, start, end) => Space.Range(recs(src), start, end)
    recs(s)

  def backendUnsupported(s: Space): Vector[String] =
    var unsupported = Vector.newBuilder[String]
    def recp(p: Path): Unit = p match
      case Path.Deref(_) | Path.Constant(_) => ()
      case Path.Concat(l, r) =>
        recp(l)
        recp(r)
      case Path.GroundedPP(p, _) =>
        unsupported += "Path.GroundedPP"
        recp(p)
      case Path.GroundedSP(s, _) =>
        unsupported += "Path.GroundedSP"
        recs(s)
    def recs(x: Space): Unit = x match
      case Space.Empty | Space.Mention(_) | Space.Literal(_) => ()
      case Space.Call(_, refs, mentions) =>
        refs.foreach(recp)
        mentions.foreach(recs)
      case Space.Singleton(p) => recp(p)
      case Space.Union(x, y) =>
        recs(x)
        recs(y)
      case Space.Intersection(x, y) =>
        recs(x)
        recs(y)
      case Space.Subtraction(x, y) =>
        recs(x)
        recs(y)
      case Space.Restriction(x, y) =>
        recs(x)
        recs(y)
      case Space.Raffination(x, y) =>
        recs(x)
        recs(y)
      case Space.Composition(x, y) =>
        recs(x)
        recs(y)
      case Space.Iteration(src, _, _, templates) =>
        recs(src)
        recs(templates)
      case Space.Fold(src, initial, _, _, _, templates, update) =>
        recs(src)
        recp(initial)
        recs(templates)
        recp(update)
      case Space.Fixpoint(initial, _, step) =>
        recs(initial)
        recs(step)
      case Space.Wrap(src, p) =>
        recs(src)
        recp(p)
      case Space.Unwrap(src, p) =>
        recs(src)
        recp(p)
      case Space.TailsUnion(src) =>
        recs(src)
      case Space.TailsIntersection(src) =>
        recs(src)
      case Space.PrefixClosure(src) =>
        recs(src)
      case Space.SuffixClosure(src) =>
        recs(src)
      case Space.TailsClosure(src) =>
        recs(src)
      case Space.Range(src, _, _) =>
        recs(src)
      case Space.GroundedPS(p, _) =>
        unsupported += "Space.GroundedPS"
        recp(p)
      case Space.GroundedSS(s, _) =>
        unsupported += "Space.GroundedSS"
        recs(s)
    recs(s)
    unsupported.result().distinct.sorted

  def compile(r: Routine,
              ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
              maxRounds: Int = 128,
              buildGraph: Boolean = true,
              maxCompileMillis: Long = CompileBudget.Default.maxMillis): SupercompiledRoutine =
    val deadline = CompileBudget(maxCompileMillis).start()
    def timed[A](phase: String)(f: => A): (A, Double) =
      deadline.check(phase)
      val start = System.nanoTime()
      val value = f
      val elapsed = (System.nanoTime() - start).toDouble / 1_000_000.0
      deadline.check(phase)
      value -> elapsed
    val fixpointCtx = new PartialFunction[RoutinePtr, Routine]:
      override def isDefinedAt(rp: RoutinePtr): Boolean = rp == r.name || ctx.isDefinedAt(rp)
      override def apply(rp: RoutinePtr): Routine = if rp == r.name then r else ctx(rp)
    val inlineCtx = new PartialFunction[RoutinePtr, Routine]:
      override def isDefinedAt(rp: RoutinePtr): Boolean = rp != r.name && ctx.isDefinedAt(rp)
      override def apply(rp: RoutinePtr): Routine = ctx(rp)
    val (loweredFixpoints, loweringMs) = timed("fixpoint lowering") {
      lowerFixpointCalls(r.body, fixpointCtx)
    }
    val (inlined, inlineMs) = timed("helper inlining") {
      Lower.inline(using inlineCtx)(loweredFixpoints)
    }
    val before = stats(r.body)
    ConstantFoldEval.reset()
    val normalized = normalize(inlined, maxRounds = maxRounds, deadline = deadline)
    val constantFoldEval = ConstantFoldEval.snapshot
    val body = normalized.space
    val out = Routine(r.name, r.refs, r.mentions, body)
    val unsupported = backendUnsupported(out.body)
    val graphBefore = if buildGraph && backendUnsupported(r.body).isEmpty then Try(graphStats(transpile(r))).toOption else None
    var graphTranspileMs = 0.0
    val graphResult =
      if buildGraph && unsupported.isEmpty then
        Try {
          val (rawGraph, transpileMs) = timed("graph transpile") {
            transpile(out)
          }
          graphTranspileMs = transpileMs
          optimizeTimed(rawGraph, deadline = deadline)
        }
      else scala.util.Failure(RuntimeException("graph backend unsupported"))
    val graph = graphResult.toOption.map(_.graph)
    val graphTimings = graphResult.toOption.map(_.timings).getOrElse(Vector.empty)
    val graphOptimizeMs = graphResult.toOption.map(_.elapsedMs).getOrElse(0.0)
    val graphError =
      if buildGraph && unsupported.isEmpty then graphResult.failed.toOption.map(_.getMessage)
      else None
    val report = SupercompileReport(
      r.name,
      before,
      stats(body),
      normalized.steps,
      normalized.rounds,
      normalized.converged,
      graphBefore,
      graph.map(graphStats),
      unsupported,
      normalized.timings,
      graphTimings,
      loweringMs,
      inlineMs,
      graphTranspileMs,
      graphOptimizeMs,
      constantFoldEval.evalMs,
      constantFoldEval.evalTrieMs,
      constantFoldEval.evalZMs,
      constantFoldEval.execTMs,
      constantFoldEval.evalCalls,
      constantFoldEval.evalTrieCalls,
      constantFoldEval.evalZCalls,
      constantFoldEval.execTCalls,
      deadline.elapsedMs,
      maxCompileMillis,
      graphError
    )
    SupercompiledRoutine(out, report, graph)

  def specialize(r: Routine,
                 pathArgs: Map[PathRef, Path] = Map.empty,
                 spaceArgs: Map[SpaceMention, Space] = Map.empty,
                 ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                 maxRounds: Int = 128,
                 buildGraph: Boolean = true,
                 maxCompileMillis: Long = CompileBudget.Default.maxMillis): SupercompiledRoutine =
    val specializedBody = subs(r.body)(
      spost = { case Space.Mention(sm) if spaceArgs.contains(sm) => spaceArgs(sm) },
      ppost = { case Path.Deref(pr) if pathArgs.contains(pr) => pathArgs(pr) }
    )
    compile(r.copy(body = specializedBody), ctx, maxRounds, buildGraph, maxCompileMillis)

  def equivalent(original: Space,
                 compiled: Space)
                (using pc: PathContext = PathContext.emptyMap,
                 sc: SpaceContext = SpaceContextMap(Map.empty),
                 rc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Boolean =
    eval(original) == eval(compiled)

  def supercompile(conf: Space,
                   ctx: PartialFunction[RoutinePtr, Routine],
                   cfg: SC.Config): Residual =
    SC.supercompile(conf, ctx, cfg)

  def supercompile(conf: Space,
                   ctx: PartialFunction[RoutinePtr, Routine]): Residual =
    SC.supercompile(conf, ctx, SC.Config())

  def supercompile(r: Routine,
                   ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                   cfg: SC.Config = SC.Config()): Residual =
    val defs = new PartialFunction[RoutinePtr, Routine]:
      override def isDefinedAt(rp: RoutinePtr): Boolean = rp == r.name || ctx.isDefinedAt(rp)
      override def apply(rp: RoutinePtr): Routine = if rp == r.name then r else ctx(rp)
    SC.supercompile(r, defs, cfg)

  def specializeProgram(r: Routine,
                        pathArgs: Map[PathRef, Path] = Map.empty,
                        spaceArgs: Map[SpaceMention, Space] = Map.empty,
                        ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
                        cfg: SC.Config = SC.Config()): Residual =
    val specializedBody = subs(r.body)(
      spost = { case Space.Mention(sm) if spaceArgs.contains(sm) => spaceArgs(sm) },
      ppost = { case Path.Deref(pr) if pathArgs.contains(pr) => pathArgs(pr) }
    )
    supercompile(r.copy(body = specializedBody), ctx, cfg)


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
    case Path.Deref(pr) => PathValue(PathItem.variable(pr.s)::Nil)
    case Path.Constant(pi) => pi
    case Path.Concat(l, r) => PathValue(recp(l).items ++ recp(r).items)
    case Path.GroundedPP(p, f) => recp(p)
    case Path.GroundedSP(s, f) => PathValue(PathItem.variable("grounded")::Nil)

  import Syntax.x
  def recs(x: Space): Set[PathValue] = x match
    case Space.Empty =>  Set.empty
    case Space.Call(r, refs, mentions) =>
      val refts = refs.foldLeft(Set.empty[PathValue])((a, p) => a.incl(recp(p)))
      mentions.foldLeft(refts)((a, s) => a.union(recs(s)))
    case Space.Mention(sm) => Set(PathValue(PathItem.variable(sm.s)::Nil))
    case Space.Singleton(p) => Set(recp(p))
    case Space.Literal(sv) => Set.empty
    case Space.Union(x, y) => recs(x) union recs(y)
//    case Space.Intersection(x, y) => recs(x) union recs(y)
    case Space.Intersection(x, y) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue(PathItem.variable("_")::Nil))),
                                                      Space.Literal(SpaceValue(recs(y))) x Space.Singleton(Path.Constant(PathValue(PathItem.variable("_")::Nil))))).paths
    case Space.Subtraction(x, y) => recs(x) union recs(y)
//    case Space.Restriction(x, prefixes) => recs(x) union recs(prefixes)
    case Space.Restriction(x, prefixes) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue(PathItem.variable("_")::Nil))),
      Space.Literal(SpaceValue(recs(prefixes))))).paths
    case Space.Composition(x, y) => recs(x) union recs(y)
    case Space.Raffination(x, y) => recs(x) union recs(y)
    case Space.Wrap(src, p) => recs(src) // .incl(recp(p))
    case Space.Unwrap(src, p) => eval(Space.Composition(Space.Literal(SpaceValue(recs(src))), Space.Singleton(Path.Constant(recp(p))))).paths
    case Space.TailsUnion(src) => recs(src)
    case Space.TailsIntersection(src) => recs(src)
    case Space.PrefixClosure(src) => recs(src)
    case Space.SuffixClosure(src) => recs(src)
    case Space.TailsClosure(src) => recs(src)
    case Space.Iteration(src, symbol, rest, templates) =>
      import Syntax.*
      val srcs = Space.Literal(SpaceValue(recs(src)))
      val sv = PathValue(PathItem.variable(symbol.s)::Nil)
      val sr = PathValue(PathItem.variable(rest.s)::Nil)
      val ts = Space.Literal(SpaceValue(recs(templates)))

//      println(s"calc ${eval(srcs x Space.Singleton(Path.Constant(sv)) x ts(Path.Constant(sr))).show}")
      val res = eval(
        (if rest.s != "_" then (srcs x ts(Path.Constant(sv)) x ts(Path.Constant(sr))) else Space.Empty) \/


        (srcs x ts(Path.Constant(sv))) \/
        srcs
        \/ (ts \| Space.Literal(SpaceValue(Set(sv, sr)))))
      res.paths
    case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
      recs(src).incl(recp(initial)).union(recs(templates)).incl(recp(update))
    case Space.Fixpoint(initial, variable, step) => recs(initial) union recs(step)
    case Space.GroundedPS(p, f) => Set(recp(p))
    case Space.GroundedSS(s, f) => recs(s)
    case Space.Range(x, _, _) => recs(x)
  SpaceValue(recs(s))

def otypes(s: Space): SpaceValue =
  def recp(x: Path): PathValue = x match
    case Path.Deref(pr) => PathValue(PathItem.variable(pr.s)::Nil)
    case Path.Constant(pi) => pi
    case Path.Concat(l, r) => PathValue(recp(l).items ++ recp(r).items)
    case Path.GroundedPP(p, f) => recp(p)
    case Path.GroundedSP(s, f) => PathValue(PathItem.variable("grounded")::Nil)

  import Syntax.x
  def recs(x: Space): Set[PathValue] = x match
    case Space.Empty =>  Set.empty
    case Space.Call(r, refs, mentions) =>
      val refts = refs.foldLeft(Set.empty[PathValue])((a, p) => a.incl(recp(p)))
      mentions.foldLeft(refts)((a, s) => a.union(recs(s)))
    case Space.Mention(sm) => Set(PathValue(PathItem.variable(sm.s)::Nil))
    case Space.Singleton(p) => Set(recp(p))
    case Space.Literal(sv) => Set.empty
    case Space.Union(x, y) => recs(x) union recs(y)
//    case Space.Intersection(x, y) => recs(x) union recs(y)
    case Space.Intersection(x, y) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue(PathItem.variable("_")::Nil))),
                                                      Space.Literal(SpaceValue(recs(y))) x Space.Singleton(Path.Constant(PathValue(PathItem.variable("_")::Nil))))).paths
    case Space.Subtraction(x, y) => recs(x) union recs(y)
//    case Space.Restriction(x, prefixes) => recs(x) union recs(prefixes)
    case Space.Restriction(x, prefixes) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue(PathItem.variable("_")::Nil))),
      Space.Literal(SpaceValue(recs(prefixes))))).paths
    case Space.Composition(x, y) => recs(x) union recs(y)
    case Space.Raffination(x, y) => recs(x) union recs(y)
    case Space.Wrap(src, p) => eval(Space.Composition(Space.Singleton(Path.Constant(recp(p))), Space.Literal(SpaceValue(recs(src))))).paths
    case Space.Unwrap(src, p) => recs(src) // .incl(recp(p))
    case Space.TailsUnion(src) => recs(src)
    case Space.TailsIntersection(src) => recs(src)
    case Space.PrefixClosure(src) => recs(src)
    case Space.SuffixClosure(src) => recs(src)
    case Space.TailsClosure(src) => recs(src)
    case Space.Iteration(src, symbol, rest, templates) =>
      recs(templates)
    case Space.Fold(src, initial, acc, symbol, rest, templates, update) =>
      recs(templates).incl(recp(update))
    case Space.Fixpoint(initial, variable, step) => recs(step)
    case Space.GroundedPS(p, f) => Set(recp(p))
    case Space.GroundedSS(s, f) => recs(s)
    case Space.Range(x, _, _) => recs(x)
  SpaceValue(recs(s))

object Syntax:
  import Path.*
  given parse: Conversion[String, PathValue] = s => PathValue(s.split('.').map(PathItem.apply).toList)
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
    def iterh(h: Path.Deref, run: Space): Space = x.iter(h, S"_", run)
    def itert(t: Space.Mention, run: Space): Space = x.iter(P"_", t, run)
    def tee(run: Space): Space = x.iter(P"_", S"_", run)
    def on_empty(ifEmpty: Space): Space = (ss"tobeempty" \ head(ss"tobeempty" x x)).tee(ifEmpty)
    def :=(s: Space) = x match
      case Space.Call(rp, refs, mentions) =>
        val refPtrs = refs.map {
          case Path.Deref(pr) => pr
          case other => throw IllegalArgumentException(s"routine path parameters must be refs, got ${other.show}")
        }
        val mentionPtrs = mentions.map {
          case Space.Mention(sm) => sm
          case other => throw IllegalArgumentException(s"routine space parameters must be mentions, got ${other.show}")
        }
        Routine(rp, refPtrs, mentionPtrs, s)
      case other => throw IllegalArgumentException(s"routine definition must start from a call, got ${other.show}")

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
