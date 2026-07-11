import scala.util.Random
import scala.collection.mutable.{ArrayBuffer, LongMap, Stack}
import scala.collection.Searching
import java.util.Base64
import java.nio.charset.StandardCharsets
import scala.language.implicitConversions


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
  // Persistent binding: ANY context can grow (iteration/fold/fixpoint bodies), so `eval` is total
  // over the language and can serve as the universal reference.  `_` is the throwaway binder.
  def bind(pr: PathRef, value: PathValue): PathContext = if pr.s == "_" then this else PathContextOverlay(this, pr, value)
  def grown(pv: Map[PathRef, PathValue]): PathContext = pv.iterator.foldLeft(this: PathContext)((c, kv) => c.bind(kv._1, kv._2))

case class PathContextOverlay(parent: PathContext, key: PathRef, value: PathValue) extends PathContext:
  override def resolve(pr: PathRef): PathValue = if pr == key then value else parent.resolve(pr)

case class PathContextMap(m: Map[PathRef, PathValue]) extends PathContext:
  override def resolve(pr: PathRef): PathValue =
    try
      m(pr)
    catch
      case e: java.util.NoSuchElementException =>
//        println(s"$pr not in $m")
        throw e
  override def grown(pv: Map[PathRef, PathValue]): PathContext =
    val n = collection.mutable.Map.from(m)
    pv.foreachEntry((k, v) => if k.s != "_" then n.update(k, v))
    PathContextMap(n.toMap)

object PathContext:
  val emptyMap: PathContextMap = PathContextMap(Map())

  def mixed(seed: Long = 0): PathContext = new PathContext:
    private val rng = Random(seed)
    override def resolve(pr: PathRef): PathValue = PathValue(PathItem.Symbol(pr.s + "_" + Base64.getEncoder.encodeToString(rng.nextBytes(4)).take(4))::Nil)



class SpaceContext:
  def resolve(pv: SpaceMention): SpaceValue = throw RuntimeException(s"$pv space mention not resolved")
  def bind(sm: SpaceMention, value: SpaceValue): SpaceContext = if sm.s == "_" then this else SpaceContextOverlay(this, sm, value)
  def grown(pv: Map[SpaceMention, SpaceValue]): SpaceContext = pv.iterator.foldLeft(this: SpaceContext)((c, kv) => c.bind(kv._1, kv._2))

case class SpaceContextOverlay(parent: SpaceContext, key: SpaceMention, value: SpaceValue) extends SpaceContext:
  override def resolve(pr: SpaceMention): SpaceValue = if pr == key then value else parent.resolve(pr)


case class SpaceContextMap(m: Map[SpaceMention, SpaceValue]) extends SpaceContext:
  override def resolve(pr: SpaceMention): SpaceValue =
    try
      m(pr)
    catch
      case e: java.util.NoSuchElementException =>
//        println(s"$pr not in $m")
        throw e

  override def grown(pv: Map[SpaceMention, SpaceValue]): SpaceContextMap =
    val n = collection.mutable.Map.from(m)
    pv.foreachEntry((k, v) => if k.s != "_" then n.update(k, v))
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
  case Iteration(src: Space, symbol: PathRef, rest: SpaceMention, templates: Space)
  /** Union-saturating least fixpoint: bind `rec` to the accumulator, iterate `rec := body` from
   *  `init`, accumulating the union of every iterate, until the argument stabilises.  `rec` binds in
   *  `body`.  Denotes `init ∪ body[init] ∪ body[body[init]] ∪ …` — the value the union-saturating
   *  recursion `r(m) = m \/ r(next(m))` computes (see [[eval]] / SCC lowering). */
  case Fixpoint(init: Space, rec: SpaceMention, body: Space)
  case Fold(src: Space, initial: Path, acc: PathRef, symbol: PathRef, rest: SpaceMention, templates: Space, update: Path)
  case Wrap(src: Space, p: Path)
  case Unwrap(src: Space, p: Path)
  case TailsUnion(src: Space)
  case TailsIntersection(src: Space)
  case GroundedPS(p: Path, f: PathValue => SpaceValue)
  case GroundedSS(p: Space, f: SpaceValue => SpaceValue)
  /** Cardinality window: `x` if `lo <= |x| < hi`, else the empty space.  Subsumes the old
   *  First/Last (a singleton test is `Range(x, 1, 2)`) and expresses exact counts purely
   *  (`|x| == k`  is  `Range(x, k, k+1)`). */
  case Range(x: Space, lo: Int, hi: Int)

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
    case Space.Fixpoint(init, rec, body) => s"${init.show}.fix(S\"${rec.s}\", \n${" ".repeat(indent + 1)}${body.show(using indent + 1)}\n)"
    case Space.Wrap(src, p) => s"(${p.show} x ${src.show})"
    case Space.Unwrap(src, p) => s"${src.show}(${p.show})"
    case Space.TailsUnion(src) => s"TailsUnion(${src.show})"
    case Space.TailsIntersection(src) => s"TailsIntersection(${src.show})"
    case Space.GroundedPS(p, f) => s"PS${f.hashCode()}(${p.show})"
    case Space.GroundedSS(s, f) => s"SS${f.hashCode()}(${s.show})"
    case Space.Raffination(x, y) => s"(${x.show} \\| ${y.show})"
    case Space.Range(z, lo, hi) => s"Range(${z.show}, $lo, $hi)"


case class SpaceValue(paths: Set[PathValue]):
  def show: String = paths.map(x => '"' + x.show + '"').toSeq.sorted.mkString("SpaceValue(", ", ", ")")
  def pretty: String = paths.map(_.show).toSeq.sorted.mkString("{", ";", "}")
  def prettyLines: String = paths.map(_.show).toSeq.sorted.mkString("", "\n", "")


/** Canonical total order on paths — the trie-native order (`pathItemOrdering` on items, with
 *  shorter-is-less on a shared prefix).  Every backend slices `Range` by THIS order, so they agree. */
given pathValueOrdering: Ordering[PathValue] with
  def compare(a: PathValue, b: PathValue): Int =
    val ai = a.items.iterator; val bi = b.items.iterator
    while ai.hasNext && bi.hasNext do
      val c = pathItemOrdering.compare(ai.next(), bi.next())
      if c != 0 then return c
    Integer.compare(a.items.length, b.items.length)

/** Ordered-slice bounds for `Range(x, start, end)` — the fused `First`/`Last`.  `0` start = from
 *  the beginning, `0` end = through the end; a positive bound is a 1-based slice border; a negative
 *  bound counts from the end.  Returns a half-open `[lo, hi)` clamped into `[0, size]`. */
object RangeBounds:
  def normalize(size: Int, start: Int, end: Int): (Int, Int) =
    def lower(b: Int): Int = if b == 0 then 0 else if b > 0 then b - 1 else size + b
    def upper(b: Int): Int = if b == 0 then size else if start == 0 && b > 0 then b else if b > 0 then b - 1 else size + b
    val lo = lower(start).max(0).min(size)
    val hi = upper(end).max(0).min(size)
    if hi <= lo then (0, 0) else (lo, hi)

/** `Range` over a concrete path set: the canonical-order slice `[start, end)`. */
def sliceRange(s: Set[PathValue], start: Int, end: Int): Set[PathValue] =
  val (lo, hi) = RangeBounds.normalize(s.size, start, end)
  if hi <= lo then Set.empty
  else if lo == 0 && hi == s.size then s
  else s.toVector.sorted(using pathValueOrdering).slice(lo, hi).toSet

case class RoutinePtr(s: String)
case class Routine(name: RoutinePtr, refs: Vector[PathRef], mentions: Vector[SpaceMention], body: Space):
  def show = s"routine(\"${name.s}\", Vector(${refs.map("\"" ++ _.s ++ "\"").mkString(", ")}), Vector(${mentions.map("\"" ++ _.s ++ "\"").mkString(", ")}), \n${body.show.split('\n').map("  " + _).mkString("\n")}\n)"
  def optimized(using ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty): Routine = Routine(name, refs, mentions,
    all_forever(Lower.inline(using new PartialFunction {
      override def apply(f: RoutinePtr): Routine = ctx(f)
      override def isDefinedAt(f: RoutinePtr): Boolean = f != name && ctx.isDefinedAt(f)
    })(body), List(Lower.ConstantOps, Lower.IterateSingleton_Deref, Lower.LiteralSpaceOps, Lower.SingletonConst_Literal, Lower.ConcatSingleton_Iter, Lower.IterUnion_Indep, Lower.Wrap_Iter, Lower.Iter_Ident, Lower.Concat_Path, Lower.IterateLiteral_Union, Lower.UnwrapConcat_Unwraps, Lower.SingletonComposition_Wrap, Lower.SingletonSpaceOp_PathOp, Lower.SingletonRestriction_Unwrap)))
//    })(body), List(Lower.IterateSingleton_Deref, Lower.LiteralSpaceOps, Lower.SingletonConst_Literal, Lower.ConcatSingleton_Iter, Lower.IterUnion_Indep, Lower.Wrap_Iter, Lower.Iter_Ident, Lower.Concat_Path, Lower.IterateLiteral_Union, Lower.UnwrapConcat_Unwraps, Lower.SingletonComposition_Wrap, Lower.SingletonSpaceOp_PathOp, Lower.SingletonRestriction_Unwrap)))

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
    case Space.TailsIntersection(src_e) => // total: empty input or only-empty-paths -> empty space
      val groups = recs(src_e).collect { case PathValue(h::t) => h -> PathValue(t) }.groupMap(_._1)(_._2)
      if groups.isEmpty then Set.empty else groups.valuesIterator.map(_.toSet).reduce(_ intersect _)
    case Space.Iteration(src_e, symbol, rest, templates) => // total: headless (empty) paths are skipped
      val groups = recs(src_e).collect { case PathValue(h::tail) => PathValue(h::Nil) -> PathValue(tail) }.groupMap(_._1)(_._2)
      Set.from(for (h, r) <- groups;
          p <- eval(templates)(using pc.grown(Map(symbol -> h)), sc.grown(Map(rest -> SpaceValue(Set.from(r)))), rc).paths
      yield p)
    case Space.Fixpoint(init, rec, body) => // union-saturating least fixpoint (the datalog shape)
      var cur = recs(init)
      var acc = cur
      var stop = false
      while !stop do
        val nxt = eval(body)(using pc, sc.grown(Map(rec -> SpaceValue(cur))), rc).paths
        if nxt == cur then stop = true else { acc = acc union nxt; cur = nxt }
      acc
    case Space.Fold(src_e, initial, acc, symbol, rest, templates, update) => // deterministic left fold over head-groups
      var accValue = PathValue(recp(initial))
      val groups = recs(src_e).collect { case PathValue(h::tail) => PathValue(h::Nil) -> PathValue(tail) }.groupMap(_._1)(_._2)
      val out = Set.newBuilder[PathValue]
      for (h, r) <- groups.toSeq.sortBy(_._1.show) do
        val pctx = pc.grown(Map(acc -> accValue, symbol -> h))
        val sctx = sc.grown(Map(rest -> SpaceValue(Set.from(r))))
        out ++= eval(templates)(using pctx, sctx, rc).paths
        accValue = PathValue(eval(Space.Singleton(update))(using pctx, sctx, rc).paths.head.items)
      out.result()
    case Space.Raffination(x_e, y_e) => recs(Space.Subtraction(x_e, Space.Restriction(x_e, y_e)))
    case Space.GroundedPS(p, f) => f(PathValue(recp(p))).paths
    case Space.GroundedSS(s, f) => f(SpaceValue(recs(s))).paths
    case Space.Range(x, lo, hi) => sliceRange(recs(x), lo, hi)  // ordered trie-slice (canonical path order)
  SpaceValue(recs(s))

/** Lossless textual codec for the `Literal` constant carried by operation-graph nodes.
 *  The previous encoding (newline-joined `PathValue.show`) was ambiguous: an empty space and
 *  a space containing the empty path both rendered as "", and a symbol containing a "." was
 *  indistinguishable from a multi-item path.  This base64-per-item codec round-trips empty
 *  spaces, epsilon paths, symbols, variables and arity items unambiguously, while staying
 *  backward-compatible with plain `Syntax.parse`-able lines. */
object LiteralCodec:
  private val marker = "lit64:"
  private def encodeText(s: String): String = Base64.getEncoder.encodeToString(s.getBytes(StandardCharsets.UTF_8))
  private def decodeText(s: String): String = new String(Base64.getDecoder.decode(s), StandardCharsets.UTF_8)
  private def encodeItem(item: PathItem): String = item match
    case PathItem.Symbol(n) => "S" + encodeText(n)
    case PathItem.Variable(n) => "V" + encodeText(n)
    case PathItem.Arity(k) => "A" + k.toString
  private def decodeItem(s: String): PathItem =
    if s.isEmpty then throw IllegalArgumentException("empty encoded path item")
    s.head match
      case 'S' => PathItem.Symbol(decodeText(s.tail))
      case 'V' => PathItem.Variable(decodeText(s.tail))
      case 'A' => PathItem.Arity(s.tail.toInt)
      case other => throw IllegalArgumentException(s"unknown encoded path item tag $other")
  private def encodePath(p: PathValue): String = marker + p.items.map(encodeItem).mkString(".")
  private def decodePath(line: String): PathValue =
    val body = line.stripPrefix(marker)
    if body.isEmpty then PathValue(Nil) else PathValue(body.split("\\.", -1).toList.map(decodeItem))
  def encode(sv: SpaceValue): String = sv.paths.toVector.sortBy(_.show).map(encodePath).mkString("\n")
  def decode(constant: String): SpaceValue =
    SpaceValue(constant.linesIterator.filter(_.nonEmpty).map(line =>
      if line.startsWith(marker) then decodePath(line) else Syntax.parse(line)).toSet)

  /** Lossless encoding of a single Constant path: keep the readable `show` form when it
   *  round-trips through `Syntax.parse` (the common symbol-path case, so op-graph dumps stay
   *  legible), otherwise escape with the base64 marker.  The plain `show`/`parse` round-trip is
   *  LOSSY for the empty path (`"".split('.')` -> `[Symbol("")]`), Arity items (`[k]`), and
   *  symbols containing a dot — these must be escaped or the op-graph mis-evaluates. */
  def encodeConst(p: PathValue): String =
    val s = p.show
    if Syntax.parse(s) == p then s else encodePath(p)
  // memoized: `exec` decodes a Constant node's string on every evaluation (per head inside an
  // iteration body), where a raw `Syntax.parse` per call made exec slower than eval (which holds the
  // PathValue inline).  Decoding is a pure function of the (stable) string, so cache it.
  private val decodeConstCache = new java.util.concurrent.ConcurrentHashMap[String, PathValue]()
  def decodeConst(c: String): PathValue =
    decodeConstCache.computeIfAbsent(c, cc => if cc.startsWith(marker) then decodePath(cc) else Syntax.parse(cc))

/** In-process `Space.Literal` payloads carried BY REFERENCE.  Serializing a large literal to a
 *  base64 string at transpile time (and the optimizer re-hashing that multi-MB constant on every
 *  CSE pass) dominated compile time for big literals — e.g. the 16384-cell temperature grid took
 *  ~226 ms just to transpile.  Instead we intern the live `SpaceValue` to a stable, value-keyed id
 *  and store only `"lit#<id>"` in the node: O(1) transpile, O(1) CSE hashing, and equal literals
 *  (value-equal Sets) share an id so structural sharing / CSE still merge them.  The lossless
 *  `LiteralCodec` string form is still produced on demand, and any non-`lit#` constant (e.g. a
 *  graph deserialized from text) decodes through `LiteralCodec` exactly as before. */
/** Ablation/benchmark toggles, default ON (the optimized path).  Each flips ONE perf change off so
 *  its contribution can be isolated (e.g. `-Dmorkl.literalByRef=false`).  Read once at class-load, so
 *  the branch is monomorphic and free after JIT.  Production never sets these. */
object Tuning:
  private def on(k: String): Boolean = !sys.props.get(k).contains("false")
  val literalByRef: Boolean = on("morkl.literalByRef")  // Space.Literal carried by reference, not serialized
  val patriciaOps:  Boolean = on("morkl.patriciaOps")   // IntMap-native ring ops + eq short-circuits

object LiteralStore:
  private val byValue = new java.util.concurrent.ConcurrentHashMap[SpaceValue, Integer]()
  private val byId = new java.util.ArrayList[SpaceValue]()
  private val prefix = "lit#"
  def ref(sv: SpaceValue): String =
    val hit = byValue.get(sv)
    val id = if hit != null then hit.intValue else synchronized {
      val again = byValue.get(sv)
      if again != null then again.intValue
      else { val i = byId.size; byId.add(sv); byValue.put(sv, Integer.valueOf(i)); i }
    }
    prefix + id
  def isRef(c: String): Boolean = c.startsWith(prefix)
  /** the SpaceValue for a Literal node constant (a by-ref id, or a legacy encoded string) */
  def resolve(c: String): SpaceValue =
    if isRef(c) then byId.get(Integer.parseInt(c.substring(prefix.length))) else LiteralCodec.decode(c)

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
      g.store(Node("Constant", LiteralCodec.encodeConst(pi), "path", Vector()))
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
        g.store(Node(s"Literal", if Tuning.literalByRef then LiteralStore.ref(sv) else LiteralCodec.encode(sv), "space", Vector()))
      case Space.Union(x, y) =>
        g.store(Node("Union", "", "space", Vector(recs(x), recs(y))))
      case Space.Intersection(x, y) =>
        g.store(Node("Intersection", "", "space", Vector(recs(x), recs(y))))
      case Space.Subtraction(x, y) =>
        g.store(Node("Subtraction", "", "space", Vector(recs(x), recs(y))))
      case Space.Raffination(x, y) =>
        g.store(Node("Raffination", "", "space", Vector(recs(x), recs(y))))
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
      case Space.Fixpoint(init, rec, body) =>
        // a Fixpoint subgraph: slot 0 = ExtractSpaceMention(rec) (the accumulator `cur`), the body
        // computes the next iterate; the executor saturates the union (see exec/execT "Fixpoint").
        val s = recs(init)
        val rog = transpile(Routine(RoutinePtr(r.name.s + "_fix"), Vector.empty, Vector(rec), body), Some(g))
        rog.root = Node("Fixpoint", rec.s, "space", Vector(s))
        g.store(rog)
      case Space.GroundedPS(p, f) =>
        throw NotImplementedError("grounded functions WIP")
      case Space.GroundedPS(s, f) =>
        throw NotImplementedError("grounded functions WIP")
      case Space.Range(x, lo, hi) =>
        g.store(Node("Range", s"$lo,$hi", "space", Vector(recs(x))))

  val resultCoord = r.body match
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

    // Convenience: a raw single-mention union-saturating self-recursion `r(m) = m \/ r(next(m))`
    // transpiles directly (without first running the SCC lowerer) by rewriting it to the first-class
    // `Space.Fixpoint` and lowering that.  General recursion recognition lives in [[lowerCalls]].
    case Space.Union(Space.Mention(bm), Space.Call(rp, refs2, mentions2))
        if rp == r.name && r.refs.isEmpty && refs2.isEmpty
        && r.mentions.length == 1 && mentions2.length == 1 && bm == r.mentions(0) =>
      recs(Space.Fixpoint(Space.Mention(r.mentions(0)), r.mentions(0), mentions2(0)))
    case n => recs(n)
  // Invariant: a scope's RESULT must be its LAST node (executors read `stack.top.last`).  A body that
  // is a bare `Mention` resolves to an EXISTING coordinate — an ancestor mention, or this scope's own
  // `rest` — WITHOUT storing a node, which would otherwise leave some other node last and make the
  // executor return the wrong slot.  When the result isn't already last, materialize it with a
  // pass-through (`Union(res, res) == res`).  No-op for the usual case (the body stored a final node).
  if resultCoord != (g.level, g.nodes.length - 1) then
    g.store(Node("Union", "", "space", Vector(resultCoord, resultCoord)))
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
          case "Constant" => LiteralCodec.decodeConst(constant)
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
          case "Literal" => LiteralStore.resolve(constant) // by-ref id (fast) or legacy encoded string
          // direct SpaceValue ops (NO per-node `eval(Space.Op(Literal,..))` wrapping — that was strictly
          // more work than `eval` itself; these mirror eval's `recs` exactly, with empty short-circuits).
          case "Union" => SpaceValue(inputs(0).sget.paths union inputs(1).sget.paths)
          case "Intersection" => val a = inputs(0).sget.paths; if a.isEmpty then SpaceValue(Set.empty) else SpaceValue(a intersect inputs(1).sget.paths)
          case "Subtraction" => val a = inputs(0).sget.paths; if a.isEmpty then SpaceValue(Set.empty) else SpaceValue(a removedAll inputs(1).sget.paths)
          case "Restriction" => val a = inputs(0).sget.paths; if a.isEmpty then SpaceValue(Set.empty) else { val pre = inputs(1).sget.paths; SpaceValue(a.filter(x => pre.exists(p => x.items.startsWith(p.items)))) }
          case "Raffination" => val a = inputs(0).sget.paths; if a.isEmpty then SpaceValue(Set.empty) else { val pre = inputs(1).sget.paths; SpaceValue(a removedAll a.filter(x => pre.exists(p => x.items.startsWith(p.items)))) }
          case "Composition" => val a = inputs(0).sget.paths; if a.isEmpty then SpaceValue(Set.empty) else { val b = inputs(1).sget.paths; SpaceValue(for e1 <- a; e2 <- b yield PathValue(e1.items ++ e2.items)) }
          case "Wrap" => val a = inputs(0).sget.paths; if a.isEmpty then SpaceValue(Set.empty) else { val p = inputs(1).pget.items; SpaceValue(a.map(sp => PathValue(p ++ sp.items))) }
          case "Unwrap" => val a = inputs(0).sget.paths; if a.isEmpty then SpaceValue(Set.empty) else { val p = inputs(1).pget.items; SpaceValue(a.collect { case e if e.items.startsWith(p) => PathValue(e.items.drop(p.length)) }) }
          case "TailsUnion" => SpaceValue(inputs(0).sget.paths.collect { case PathValue(_ :: r) => PathValue(r) })
          case "TailsIntersection" => val gs = inputs(0).sget.paths.collect { case PathValue(h :: t) => h -> PathValue(t) }.groupMap(_._1)(_._2); SpaceValue(if gs.isEmpty then Set.empty else gs.valuesIterator.map(_.toSet).reduce(_ intersect _))
          case "Range" => val Array(lo, hi) = constant.split(",", 2).map(_.toInt); SpaceValue(sliceRange(inputs(0).sget.paths, lo, hi))
          case "Iteration" => throw IllegalStateException("Iteration should be a recursive subgraph, not a flat node")
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
            // reuse ONE body frame across all head-groups (exec overwrites every slot it reads), so a
            // deep/nested iteration does not allocate an Array per head — matching execT.
            val src = inputs(0).sget
            val frame = new Array[PathValue | SpaceValue | Null](sg.nodes.length)
            val last = sg.nodes.length - 1
            stack.push(frame)
            var acc = Set.empty[PathValue]
            for (h, r) <- src.paths.collect { case PathValue(head :: tail) => PathValue(head :: Nil) -> PathValue(tail) }.groupMap(_._1)(_._2) do
              frame(0) = h; frame(1) = SpaceValue(Set.from(r))
              exec(sg, stack, index)
              acc = acc union frame(last).asInstanceOf[SpaceValue].paths
            stack.pop()
            s(c) = SpaceValue(acc)
          case "Fixpoint" =>
            // union-saturating recursion `r(m) = m ∪ r(next(m))`: union `m` over every iterate and
            // stop when the argument stabilises — faithful to eval for any `next`, not only extensive.
            // ONE reused frame across iterations (no per-step Array allocation).
            var cur = inputs(0).sget
            var acc = cur
            val frame = new Array[PathValue | SpaceValue | Null](sg.nodes.length)
            val last = sg.nodes.length - 1
            stack.push(frame)
            var done = false
            while !done do
              frame(0) = cur
              exec(sg, stack, index)
              val nxt = frame(last).asInstanceOf[SpaceValue]
              if nxt.paths == cur.paths then done = true else { cur = nxt; acc = SpaceValue(acc.paths union nxt.paths) }
            stack.pop()
            s(c) = acc
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
          case "Constant" => Path.Constant(LiteralCodec.decodeConst(constant))
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
          case "Literal" => Space.Literal(LiteralStore.resolve(constant))
          case "Union" => Space.Union(inputs(0).sget, inputs(1).sget)
          case "Intersection" => Space.Intersection(inputs(0).sget, inputs(1).sget)
          case "Restriction" => Space.Restriction(inputs(0).sget, inputs(1).sget)
          case "Subtraction" => Space.Subtraction(inputs(0).sget, inputs(1).sget)
          case "Raffination" => Space.Raffination(inputs(0).sget, inputs(1).sget)
          case "Composition" => Space.Composition(inputs(0).sget, inputs(1).sget)
          case "Wrap" => Space.Wrap(inputs(0).sget, inputs(1).pget)
          case "Unwrap" => Space.Unwrap(inputs(0).sget, inputs(1).pget)
          case "TailsUnion" => Space.TailsUnion(inputs(0).sget)
          case "TailsIntersection" => Space.TailsIntersection(inputs(0).sget)
          case "Iteration" => throw IllegalStateException("Iteration should be a recursive subgraph, not a flat node")
          case "Range" => val Array(lo, hi) = constant.split(",", 2).map(_.toInt); Space.Range(inputs(0).sget, lo, hi)
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
          case "Fixpoint" =>   // inverse of transpile's Fixpoint lowering: slot 0 = ExtractSpaceMention(rec)
            stack.push(new Array(sg.nodes.length))
            untranspile(sg, stack, index)
            val popped = stack.pop()
            s(c) = Space.Fixpoint(inputs(0).sget, popped(0).asInstanceOf[Space.Mention].variable, popped.last.asInstanceOf[Space])
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


/** optimize_sharing — global common-subexpression elimination by value numbering (hash-consing),
 *  for both flat nodes AND whole iteration subgraphs.
 *
 *  Each node is assigned a value number (VN) — an Int interned from an EXACT structural key
 *  `op|constant|kind|<input VNs>` (constants matter; lossy hashing is unsound for CSE, since a
 *  collision would merge two *different* values).  A node whose key was already produced by a
 *  VISIBLE node (an ancestor scope, or an earlier node in the same scope — never a sibling, which
 *  would be an out-of-scope coordinate) is dropped and its references redirected to that node.
 *
 *  Subgraphs share too: a subgraph's key is `SG|rootOp|rootConstant|<root input VNs>|<body VNs>`.
 *  Because identical body nodes intern to identical VNs (the table is global), two structurally
 *  identical iterations get the same key and the later one is deduplicated.  The result node of
 *  every scope is PINNED (always emitted, never redirected away) so the executor's `.last` remains
 *  the true output even when the result happens to duplicate an earlier node. */
def optimize_sharing(g: RecursiveOpGraph): RecursiveOpGraph =
  import scala.collection.mutable.{HashMap => MMap, ArrayBuffer => MBuf}
  val interns = MMap.empty[String, Int]
  def intern(key: String): Int = interns.getOrElseUpdate(key, interns.size)
  final class Frame(val oldToNew: MMap[Int, (Int, Int)], val oldToVN: MMap[Int, Int], val seen: MMap[String, (Int, Int)])
  val frames = MMap.empty[Int, Frame]   // level -> the current scope's frame on the active chain

  // returns (rebuilt scope, VNs of its kept nodes in order — the scope's structural shape)
  def process(scope: RecursiveOpGraph, parent: Option[RecursiveOpGraph]): (RecursiveOpGraph, Vector[Int]) =
    val lvl = scope.level
    val r = RecursiveOpGraph(scope.root, parent, MBuf.empty)
    val fr = Frame(MMap.empty, MMap.empty, MMap.empty)
    frames(lvl) = fr
    val keptVNs = MBuf.empty[Int]
    def vnAt(c: (Int, Int)): Int = frames(c._1).oldToVN(c._2)
    def newAt(c: (Int, Int)): (Int, Int) = frames(c._1).oldToNew(c._2)
    def lookup(key: String): Option[(Int, Int)] =
      var l = lvl
      while l >= 0 do { frames.get(l).flatMap(_.seen.get(key)) match { case s @ Some(_) => return s; case None => () }; l -= 1 }
      None
    val lastIdx = scope.nodes.length - 1
    for (ng, j) <- scope.nodes.zipWithIndex do
      val isResult = j == lastIdx
      ng match
        case Left(n) =>
          // An Extract is a *binding* (a scope's input slot), not a recomputable value: an
          // ExtractSpaceMention("edges") inside a Fixpoint/Iteration body is the loop variable — a
          // DIFFERENT value from an ancestor's ExtractSpaceMention("edges").  Discriminating its key
          // by scope level keeps the two distinct (so `next(cur)` is never merged into `next(init)`),
          // while same-level Extracts of structurally identical sibling subgraphs still share a VN
          // (so those subgraphs keep deduplicating).  Extracts are never redirected.  The constant is
          // length-prefixed so a space inside it can't be confused with a field boundary (injective).
          val isExtract = n.operation.startsWith("Extract")
          val key = (if isExtract then s"$lvl@" else "") +
            s"${n.operation} ${n.kind} ${n.inputs.map(vnAt).mkString(",")} ${n.constant.length}:${n.constant}"
          val vn = intern(key)
          lookup(key) match
            case Some(nc) if !isResult && !isExtract => fr.oldToNew(j) = nc; fr.oldToVN(j) = vn
            case _ =>
              val nc = r.store(Node(n.operation, n.constant, n.kind, n.inputs.map(newAt)))
              if !isResult && !isExtract then fr.seen.getOrElseUpdate(key, nc)
              fr.oldToNew(j) = nc; fr.oldToVN(j) = vn; keptVNs += vn
        case Right(sg) =>
          val (newSg, bodyVNs) = process(sg, Some(r))
          val key = s"SG ${sg.root.operation} ${sg.root.inputs.map(vnAt).mkString(",")} ${bodyVNs.mkString(",")} ${sg.root.constant.length}:${sg.root.constant}"
          val vn = intern(key)
          lookup(key) match
            case Some(nc) if !isResult => fr.oldToNew(j) = nc; fr.oldToVN(j) = vn
            case _ =>
              newSg.root = Node(sg.root.operation, sg.root.constant, sg.root.kind, sg.root.inputs.map(newAt))
              val nc = r.store(newSg)
              if !isResult then fr.seen.getOrElseUpdate(key, nc)
              fr.oldToNew(j) = nc; fr.oldToVN(j) = vn; keptVNs += vn
    frames.remove(lvl)
    (r, keptVNs.toVector)
  process(g, g.parent)._1


/** push_out — loop-invariant code motion (LICM) over the iteration-subgraph tree, for both flat
 *  nodes AND whole loop-invariant subgraphs.
 *
 *  Coordinate-free until the very end: every node gets a stable global id; inputs are resolved to
 *  ids.  A node's **earliest legal scope** is the deepest scope among its dependencies' placements
 *  (an Extract or a scope's result node is pinned to its own scope; a node with no deps goes to the
 *  root).  For a flat node the dependencies are its inputs.  For a SUBGRAPH the dependencies are its
 *  source plus every reference its *entire subtree* makes to nodes OUTSIDE that subtree — so a
 *  subgraph is hoisted exactly to just inside the innermost loop any part of it actually needs.
 *  Because a scope's external refs subsume its whole subtree's, a scope is never hoisted above an
 *  extract a descendant uses, so the move is always sound (a hoist or a stay, never a sink).  We
 *  then re-derive the scope tree from the subgraph placements (a hoisted subgraph re-parents its
 *  child scope), recompute levels, and lay each scope out as [pinned Extracts at their original
 *  slots] ++ [interior nodes, topologically] ++ [result last] with fresh coordinates.  Well-formed
 *  by construction, at any depth.  `hoistSubgraphs=false` pins subgraphs (node-only LICM) — kept for
 *  A/B measurement of the subgraph-hoisting win. */
def push_out(g: RecursiveOpGraph, hoistSubgraphs: Boolean = true): RecursiveOpGraph =
  import scala.collection.mutable.{HashMap => MMap, ArrayBuffer => MBuf, Set => MSet}
  // ---- node entries (Left ops, and Right subgraphs as a node in their parent scope) ----
  final class Ent(val id: Int, val isSub: Boolean, val op: String, val constant: String,
                  val kind: "path" | "space", val inputIds: Array[Int],
                  val homeScope: Int, val childScope: Int, val pinned: Boolean)
  val ents = MBuf.empty[Ent]
  // scope metadata (scopeLevel is the ORIGINAL depth — a stable chain-depth order for "deepest")
  val scopeLevel = MBuf.empty[Int]
  val scopeParent = MBuf.empty[Int]
  val scopeRoot = MBuf.empty[Node[(Int, Int)]]
  val scopeResultIdx = MBuf.empty[Int]
  val scopeNodeIds = MBuf.empty[MBuf[Int]]
  val scopeOwner = MBuf.empty[Int]               // ent id of the subgraph node introducing the scope (-1 = root)

  // ---- pass 1: collect, resolving every input coordinate to a global id ----
  def collect(node: RecursiveOpGraph, chain: Vector[Int], owner: Int): Int =
    val sid = scopeLevel.length
    scopeLevel.addOne(node.level); scopeParent.addOne(if chain.isEmpty then -1 else chain.last)
    scopeRoot.addOne(node.root); scopeResultIdx.addOne(node.nodes.length - 1); scopeOwner.addOne(owner)
    scopeNodeIds.addOne(MBuf.fill(node.nodes.length)(-1))
    val chain2 = chain :+ sid
    def resolve(coord: (Int, Int)): Int = scopeNodeIds(chain2(coord._1))(coord._2)
    for (ng, j) <- node.nodes.zipWithIndex do
      val id = ents.length
      scopeNodeIds(sid)(j) = id
      val isResult = j == node.nodes.length - 1
      ng match
        case Left(n) =>
          val pinned = n.operation.startsWith("Extract") || isResult
          ents.addOne(Ent(id, false, n.operation, n.constant, n.kind, n.inputs.map(resolve).toArray, sid, -1, pinned))
        case Right(sg) =>
          // a subgraph may HOIST (move its whole child scope up) unless it is this scope's result
          // node (its output must stay) or hoisting is disabled.
          val pinned = isResult || !hoistSubgraphs
          ents.addOne(Ent(id, true, sg.root.operation, sg.root.constant, "space", sg.root.inputs.map(resolve).toArray, sid, -1, pinned))
          val childSid = collect(sg, chain2, id)
          val e = ents(id); ents(id) = Ent(e.id, true, e.op, e.constant, e.kind, e.inputIds, e.homeScope, childSid, e.pinned)
    sid
  val rootScope = collect(g, Vector.empty, -1)
  val nScopes = scopeLevel.length

  // ---- structural sets over the ORIGINAL tree: per scope, every id its subtree references
  // (allRefs) and every id homed in its subtree (subtreeIds).  Computed bottom-up. ----
  val entsByHome = Array.fill(nScopes)(MBuf.empty[Int]); for e <- ents do entsByHome(e.homeScope).addOne(e.id)
  val allRefs = Array.fill(nScopes)(MSet.empty[Int])
  val subtreeIds = Array.fill(nScopes)(MSet.empty[Int])
  for sid <- (nScopes - 1) to 0 by -1 do
    for id <- entsByHome(sid) do { allRefs(sid) ++= ents(id).inputIds; subtreeIds(sid).addOne(id) }
    if scopeParent(sid) >= 0 then { allRefs(scopeParent(sid)) ++= allRefs(sid); subtreeIds(scopeParent(sid)) ++= subtreeIds(sid) }
  /** A subgraph's external dependencies: its source inputs + every reference its whole subtree makes
   *  to nodes OUTSIDE that subtree.  These determine how far it can hoist. */
  def subgraphDeps(e: Ent): Array[Int] =
    (allRefs(e.childScope).iterator.filterNot(subtreeIds(e.childScope)) ++ e.inputIds.iterator).toArray

  // ---- pass 2: earliest-legal placement scope per node id (deepest dependency, memoized) ----
  val placement = Array.fill(ents.length)(-1)
  def place(id: Int): Int =
    if placement(id) >= 0 then return placement(id)
    val e = ents(id)
    val deps = if e.pinned then Array.empty[Int] else if e.isSub then subgraphDeps(e) else e.inputIds
    val p = if e.pinned then e.homeScope
            else if deps.isEmpty then rootScope
            else deps.iterator.map(place).maxBy(scopeLevel)   // deepest (innermost original loop) dep
    placement(id) = p; p
  for id <- ents.indices do place(id)

  // ---- re-derive the scope tree from subgraph placements, then its levels ----
  val newParent = Array.fill(nScopes)(-1)
  for sid <- 0 until nScopes if sid != rootScope do newParent(sid) = place(scopeOwner(sid))
  val newLevel = Array.fill(nScopes)(-1)
  def nlevel(sid: Int): Int =
    if newLevel(sid) >= 0 then newLevel(sid)
    else { val l = if sid == rootScope then 0 else nlevel(newParent(sid)) + 1; newLevel(sid) = l; l }
  for sid <- 0 until nScopes do nlevel(sid)

  // ---- pass 3: rebuild over the NEW tree, assigning fresh coordinates ----
  val nodesByScope = Array.fill(nScopes)(MBuf.empty[Int])
  for id <- ents.indices do nodesByScope(place(id)).addOne(id)
  val coord = new Array[(Int, Int)](ents.length)

  // intra-scope ordering: a subgraph runs as a unit, so it depends on every node its subtree
  // references (not just its source); order those first.
  def subtreeRefs(id: Int): scala.collection.Set[Int] =
    val e = ents(id); if e.isSub then allRefs(e.childScope) ++ e.inputIds else e.inputIds.toSet
  def topo(ids: Seq[Int]): Vector[Int] =
    val inScope = ids.toSet; val seen = MMap.empty[Int, Boolean]; val order = MBuf.empty[Int]
    def visit(id: Int): Unit =
      if !seen.getOrElse(id, false) then
        seen(id) = false
        for in <- subtreeRefs(id) if inScope(in) && in != id do visit(in)
        seen(id) = true; order.addOne(id)
    for id <- ids do visit(id)
    order.toVector

  def build(sid: Int, parent: Option[RecursiveOpGraph]): RecursiveOpGraph =
    val lvl = newLevel(sid)
    val r = RecursiveOpGraph(scopeRoot(sid), parent, MBuf.empty)
    val here = nodesByScope(sid)
    val resultId = scopeNodeIds(sid)(scopeResultIdx(sid))
    val extracts = here.filter(id => ents(id).op.startsWith("Extract") && id != resultId)
      .sortBy(id => scopeNodeIds(sid).indexOf(id))      // keep original slot order (0,1,..)
    val interior = here.filter(id => !ents(id).op.startsWith("Extract") && id != resultId)
    val ordered = extracts.toVector ++ topo(interior.toVector) :+ resultId
    for (id, idx) <- ordered.zipWithIndex do coord(id) = (lvl, idx)
    for id <- ordered do
      val e = ents(id)
      if e.isSub then
        val childRoot = Node(e.op, e.constant, "space", e.inputIds.toVector.map(coord(_)))
        val child = build(e.childScope, Some(r)); child.root = childRoot; r.store(child)
      else
        r.store(Node(e.op, e.constant, e.kind, e.inputIds.toVector.map(coord(_))))
    r
  build(rootScope, None)

// ============================================================================================
//  Compile-time budgeting and profiling.
//
//  A supercompiler/optimizer trades COMPILE time for RUN time; that trade is only worth making if
//  compilation is bounded.  `Deadline` is a wall-clock bound that fixed-point passes poll so they
//  stop GRACEFULLY (every pass here is semantics-preserving, so the best graph reached so far is a
//  correct answer — an early stop only forgoes further optimization).  `Profiler` accounts the time
//  each named pass spends, so compile cost is reported separately from run cost.
// ============================================================================================

/** Wall-clock bound on compile-time work; `Deadline.never` is unbounded.  Poll with [[expired]]. */
final class Deadline(val endNanos: Long):
  def expired: Boolean = endNanos != Long.MaxValue && System.nanoTime() >= endNanos
object Deadline:
  val never: Deadline = new Deadline(Long.MaxValue)
  /** A deadline `ms` milliseconds from now.  Only an infinite/NaN budget means "never"; a budget of
   *  0 (or negative) yields an already-expired deadline (immediate stop), not an unbounded one. */
  def inMillis(ms: Double): Deadline =
    if ms.isInfinite || ms.isNaN then never else new Deadline(System.nanoTime() + (math.max(0.0, ms) * 1e6).toLong)

/** Accumulates wall-clock time per named compilation pass.  `Profiler.off` is a shared sink that
 *  records nothing, so un-instrumented call sites pay only a boolean check. */
final class Profiler(recording: Boolean):
  private val acc = scala.collection.mutable.LinkedHashMap.empty[String, Long]   // label -> nanos
  private val cnt = scala.collection.mutable.LinkedHashMap.empty[String, Long]   // label -> accumulated count
  def timed[A](label: String)(body: => A): A =
    if !recording then body else
      val t0 = System.nanoTime()
      try body finally acc.updateWith(label)(o => Some(o.getOrElse(0L) + (System.nanoTime() - t0)))
  /** Accumulate an integer measure for a pass — e.g. its IMPROVEMENT (nodes removed). */
  def count(label: String, n: Long): Unit = if recording then cnt.updateWith(label)(o => Some(o.getOrElse(0L) + n))
  def millis: Map[String, Double] = acc.view.mapValues(_ / 1e6).toMap
  def counts: Map[String, Long] = cnt.toMap
  def totalMillis: Double = acc.valuesIterator.sum / 1e6
object Profiler:
  val off: Profiler = new Profiler(false)
  def on: Profiler = new Profiler(true)

/** Total node count (flat ops + subgraph roots, recursively) — a size measure for reporting how
 *  much each optimizer pass shrank the graph. */
def nodeCount(g: RecursiveOpGraph): Int =
  1 + g.nodes.iterator.map { case Left(_) => 1; case Right(sg) => nodeCount(sg) }.sum

/** Nodes that live INSIDE a loop (any iteration/fixpoint subgraph), recursively — push_out's job is
 *  to shrink this by hoisting loop-invariant nodes out, so the drop is its real improvement (those
 *  nodes now run once per outer entry instead of once per iteration). */
def loopNodes(g: RecursiveOpGraph): Int =
  g.nodes.iterator.map { case Left(_) => 0; case Right(sg) => nodeCount(sg) }.sum

def all_forever(s: Space, mappings: List[Space => Space] = Nil, budget: Deadline = Deadline.never): Space =
  val s_ = mappings.foldLeft(s)((s, f) => f(s))
  if s == s_ || budget.expired then s   // structural equality (Space is a case-class tree) — no `show` strings
  else all_forever(s_, mappings, budget)

/** Inline every `Call` whose target is in `index` by splicing the callee's body (with arguments
 *  substituted for its parameters), to a fixed point.  This is the source-level realisation of
 *  "expand functions into the graph": after inlining, `transpile` produces a single Call-free
 *  op-graph and the executor needs no Call dispatch.  Because inlining a body that contains nested
 *  Calls exposes them for the next round, `all_forever` repeats until stable — so `index` MUST
 *  contain only non-(mutually-)recursive routines, else it diverges.  Self-recursive,
 *  union-saturating routines are not inlined but *lowered* (a fixpoint loop); see [[transpile]]. */
def inlineCalls(s: Space, index: PartialFunction[RoutinePtr, Routine], budget: Deadline = Deadline.never): Space =
  all_forever(s, List(Lower.inline(using index)), budget)

/** The routines a Space directly Calls. */
def callees(s: Space): Set[RoutinePtr] = collect(s)({ case Space.Call(rp, _, _) => rp })._1.map(_._2).toSet

/** Recognize a union-saturating self-recursion and rewrite it to the first-class [[Space.Fixpoint]],
 *  removing the self-call (so the routine becomes acyclic and inlinable).  Pattern:
 *  `r(refs; mentions) = m_c \/ r(refs; …)` where every path-ref and every space-mention EXCEPT one
 *  is passed through unchanged, and the union's left arm is exactly that one changing mention `m_c`
 *  (an identity base).  This is the datalog shape — covering single-mention `transitive` and
 *  multi-parameter `reachable` (edges/mask pass through, reach saturates). */
def asFixpoint(r: Routine): Option[Routine] = r.body match
  case Space.Union(base, Space.Call(rp, argRefs, argMentions))
      if rp == r.name && argRefs.length == r.refs.length && argMentions.length == r.mentions.length
      && r.refs.lazyZip(argRefs).forall((pr, a) => a == Path.Deref(pr)) =>
    r.mentions.indices.filter(i => argMentions(i) != Space.Mention(r.mentions(i))) match
      case Seq(ci) if base == Space.Mention(r.mentions(ci)) =>
        Some(r.copy(body = Space.Fixpoint(Space.Mention(r.mentions(ci)), r.mentions(ci), argMentions(ci))))
      case _ => None
  case _ => None

/** Lower a mutually-recursive SCC (≥2 routines) of union-saturating set definitions to a single
 *  [[Space.Fixpoint]] via the tagged-union encoding: combine the SCC relations into one tagged
 *  relation `S = ⋃_i (tag_i · r_i)`, replace every (parameter-passthrough) SCC-call `r_j(…)` by
 *  `Unwrap(S, tag_j)`, take the least fixpoint of the combined body, and project each routine as
 *  `r_i(params) = Unwrap(fixpoint, tag_i)` (now NON-recursive, hence inlinable).  Returns `None`
 *  (so the SCC stays an HONEST residual) unless the preconditions hold: every routine shares the
 *  same (refs, mentions) signature; every SCC-call passes the parameters through unchanged; and the
 *  combined body is STRUCTURALLY MONOTONE in the SCC-calls (no recursive call under a Subtraction/
 *  Raffination subtrahend, Range, Fold, residual, or grounded node) — so the ascending Kleene chain
 *  from ∅ reaches a least fixpoint.  Arg-changing mutual recursion fails the passthrough test and
 *  stays residual (defunctionalizing it is out of scope). */
def lowerMutualPassthrough(scc: Vector[RoutinePtr], lowered: Map[RoutinePtr, Routine]): Option[Map[RoutinePtr, Routine]] =
  if scc.size < 2 then return None
  val sccSet = scc.toSet
  val rs = scc.map(lowered)
  val sig = rs.head
  if !rs.forall(r => r.refs == sig.refs && r.mentions == sig.mentions) then return None
  val passRefs = sig.refs.map(Path.Deref(_))
  val passMentions = sig.mentions.map(Space.Mention(_))
  def sccCalls(s: Space): Vector[Space.Call] =
    collect(s)({ case c: Space.Call if sccSet(c.r) => c })._1.map(_._2.asInstanceOf[Space.Call])
  if !rs.forall(r => sccCalls(r.body).forall(c => c.refs == passRefs && c.mentions == passMentions)) then return None
  def refersScc(s: Space): Boolean = callees(s).exists(sccSet)
  def mono(s: Space): Boolean = s match           // SCC-calls only in ⊑-monotone positions
    case _: Space.Call => true
    case Space.Union(a, b) => mono(a) && mono(b)
    case Space.Intersection(a, b) => mono(a) && mono(b)
    case Space.Composition(a, b) => mono(a) && mono(b)
    case Space.Restriction(a, b) => mono(a) && mono(b)
    case Space.Wrap(a, _) => mono(a)
    case Space.Unwrap(a, _) => mono(a)
    case Space.TailsUnion(a) => mono(a)
    case Space.TailsIntersection(a) => mono(a)
    case Space.Iteration(src, _, _, b) => mono(src) && mono(b)
    case Space.Fixpoint(i, _, b) => mono(i) && mono(b)
    case Space.Subtraction(a, b) => mono(a) && !refersScc(b)   // b (subtrahend) is anti-monotone
    case Space.Raffination(a, b) => mono(a) && !refersScc(b)
    case Space.Empty | _: Space.Mention | _: Space.Literal | _: Space.Singleton => true
    case other => !refersScc(other)               // Range/Fold/residual/grounded: no SCC-call allowed
  if !rs.forall(r => mono(r.body)) then return None
  val recVar = SpaceMention("#fixscc#" + scc.map(_.s).sorted.mkString("+"))
  def tag(rp: RoutinePtr): Path = Path.Constant(PathValue(List(PathItem.Symbol("#scc#" + rp.s))))
  def substCalls(s: Space): Space = subs(s)(spost = { case c: Space.Call if sccSet(c.r) => Space.Unwrap(Space.Mention(recVar), tag(c.r)) })
  val combined = rs.map(r => Space.Wrap(substCalls(r.body), tag(r.name))).reduce(Space.Union(_, _))
  val fix = Space.Fixpoint(Space.Empty, recVar, combined)
  Some(scc.map(rp => rp -> lowered(rp).copy(body = Space.Unwrap(fix, tag(rp)))).toMap)

/** Lower a self-recursion `r(refs; mentions) = BASE ∪ r(refs; one mention transformed by T)` for an
 *  ARBITRARY base (not just the identity base [[asFixpoint]] requires) and arbitrary transform `T`,
 *  via a TWO-TAGGED-STATE [[Space.Fixpoint]]: the state carries `#arg#·(current argument)` and
 *  `#out#·(accumulated output)`; each step reads the current argument `cur`, advances it by `T[cm:=cur]`
 *  (into `#arg#`) and emits `BASE[cm:=cur]` (into `#out#`).  The least fixpoint's `#out#` projection is
 *  `⋃ₖ BASE(Tᵏ(arg))`, exactly the recursion's meaning under the iterate-and-accumulate Fixpoint
 *  semantics.  Gated by structural monotonicity of BASE and T in the changing mention.  None ⇒ shape
 *  not handled (multiple/zero changing mentions, ref-change, wrapped self-call, non-monotone). */
def asFixpointGeneral(self: RoutinePtr, refs: Vector[PathRef], mentions: Vector[SpaceMention], body: Space): Option[Space] =
  def unionTerms(s: Space): List[Space] = s match
    case Space.Union(a, b) => unionTerms(a) ++ unionTerms(b)
    case other => List(other)
  def uses(t: Space, m: SpaceMention): Boolean = collect(t)({ case Space.Mention(`m`) => () })._1.nonEmpty
  def monoIn(s: Space, m: SpaceMention): Boolean = s match    // m only in ⊑-monotone positions
    case Space.Union(a, b) => monoIn(a, m) && monoIn(b, m)
    case Space.Intersection(a, b) => monoIn(a, m) && monoIn(b, m)
    case Space.Composition(a, b) => monoIn(a, m) && monoIn(b, m)
    case Space.Restriction(a, b) => monoIn(a, m) && monoIn(b, m)
    case Space.Wrap(a, _) => monoIn(a, m)
    case Space.Unwrap(a, _) => monoIn(a, m)
    case Space.TailsUnion(a) => monoIn(a, m)
    case Space.TailsIntersection(a) => monoIn(a, m)
    case Space.Iteration(src, _, _, b) => monoIn(src, m) && monoIn(b, m)
    case Space.Fixpoint(i, _, b) => monoIn(i, m) && monoIn(b, m)
    case Space.Subtraction(a, b) => monoIn(a, m) && !uses(b, m)
    case Space.Raffination(a, b) => monoIn(a, m) && !uses(b, m)
    case Space.Empty | _: Space.Mention | _: Space.Literal | _: Space.Singleton => true
    case other => !uses(other, m)                              // Call/Range/Fold/residual/grounded: forbid m
  val terms = unionTerms(body)
  terms.collect { case c: Space.Call if c.r == self => c } match
    case List(call) if call.refs == refs.map(Path.Deref(_)) && call.mentions.length == mentions.length =>
      mentions.indices.filter(i => call.mentions(i) != Space.Mention(mentions(i))) match
        case Seq(ci) =>
          val cm = mentions(ci)
          val base = terms.filterNot(_ eq call).reduceOption(Space.Union(_, _)).getOrElse(Space.Empty)
          if !(monoIn(base, cm) && monoIn(call.mentions(ci), cm)) then None
          else
            val state = SpaceMention("#fixarg#" + self.s)
            val argTag = Path.Constant(PathValue(List(PathItem.Symbol("#arg#"))))
            val outTag = Path.Constant(PathValue(List(PathItem.Symbol("#out#"))))
            val cur = Space.Unwrap(Space.Mention(state), argTag)
            def sub(e: Space): Space = subs(e)(spost = { case Space.Mention(`cm`) => cur })
            val step = Space.Union(Space.Wrap(sub(call.mentions(ci)), argTag), Space.Wrap(sub(base), outTag))
            Some(Space.Unwrap(Space.Fixpoint(Space.Wrap(Space.Mention(cm), argTag), state, step), outTag))
        case _ => None
    case _ => None

/** Lower a 2-routine arg-changing mutual SCC by Gaussian elimination: unfold one routine into the
 *  other (one-shot, requires the unfolded routine to not self-call) to obtain a single self-recursion,
 *  then lower that with [[asFixpointGeneral]].  None ⇒ shape not handled (left an honest residual). */
def lowerMutualByElimination(scc: Vector[RoutinePtr], lowered: Map[RoutinePtr, Routine]): Option[Map[RoutinePtr, Routine]] =
  if scc.size != 2 then None
  else
    val pair = scc.sortBy(_.s)
    Seq((pair(0), pair(1)), (pair(1), pair(0))).iterator.flatMap { (keep, drop) =>
      val keepR = lowered(keep); val dropR = lowered(drop)
      if callees(dropR.body).contains(drop) then None                       // drop self-calls ⇒ unfold loops
      else
        val unfolded = inlineCalls(keepR.body, { case `drop` => dropR })
        if callees(unfolded).contains(drop) then None                       // not fully unfolded
        else asFixpointGeneral(keep, keepR.refs, keepR.mentions, unfolded).map(lb =>
          Map(keep -> keepR.copy(body = lb), drop -> dropR))               // keep now non-recursive; drop calls it
    }.nextOption()

/** Lower a mutually-recursive SCC: the tagged-union encoding for parameter-passthrough SCCs, else
 *  Gaussian elimination for arg-changing 2-cycles.  None ⇒ leave the SCC as an honest residual. */
def lowerMutualSCC(scc: Vector[RoutinePtr], lowered: Map[RoutinePtr, Routine]): Option[Map[RoutinePtr, Routine]] =
  lowerMutualPassthrough(scc, lowered).orElse(lowerMutualByElimination(scc, lowered))

/** SCC-aware inliner/lowerer — the source-level "link" step.  (1) Rewrites every recognized
 *  union-saturating self-recursion to a `Space.Fixpoint` (via [[asFixpoint]]), and every lowerable
 *  mutually-recursive SCC to a single tagged `Space.Fixpoint` (via [[lowerMutualSCC]]); both leave
 *  the call cycle.  (2) Recomputes which routines remain in a cycle.  (3) INLINES every (now-)acyclic
 *  routine — into `main`'s body and into each surviving recursive routine's body — leaving genuinely
 *  un-lowerable recursion as HONEST residual `Call`s.  Returns the lowered top body together with the
 *  residual routines it still calls, so the result is self-contained and directly evaluable. */
def lowerCalls(main: Routine, ctx: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty,
          budget: Deadline = Deadline.never): (Space, Map[RoutinePtr, Routine]) =
  val seen = scala.collection.mutable.Map.empty[RoutinePtr, Routine]
  def gather(s: Space): Unit =
    for rp <- callees(s) if ctx.isDefinedAt(rp) && !seen.contains(rp) do
      val d = ctx(rp); seen(rp) = d; gather(d.body)
  gather(main.body)
  val lowered = (seen.toMap + (main.name -> main)).view.mapValues(r => asFixpoint(r).getOrElse(r)).toMap
  def edgesOf(m: Map[RoutinePtr, Routine]): Map[RoutinePtr, Set[RoutinePtr]] =
    m.view.mapValues(r => callees(r.body).filter(m.contains)).toMap
  def isCyclic(es: Map[RoutinePtr, Set[RoutinePtr]], start: RoutinePtr): Boolean =
    val stack = scala.collection.mutable.Stack.from(es(start)); val vis = scala.collection.mutable.Set.empty[RoutinePtr]
    while stack.nonEmpty do
      val x = stack.pop()
      if x == start then return true
      if vis.add(x) then es(x).foreach(stack.push)
    false
  def reach(es: Map[RoutinePtr, Set[RoutinePtr]], start: RoutinePtr): Set[RoutinePtr] =
    val out = scala.collection.mutable.Set.empty[RoutinePtr]; val stack = scala.collection.mutable.Stack.from(es(start))
    while stack.nonEmpty do { val x = stack.pop(); if out.add(x) then es(x).foreach(stack.push) }
    out.toSet
  val edges = edgesOf(lowered)
  val recursive = lowered.keySet.filter(isCyclic(edges, _))
  val reaches = recursive.iterator.map(rp => rp -> reach(edges, rp)).toMap   // group into mutual-reachability SCCs
  val sccs = recursive.map(rp => recursive.filter(o => o == rp || (reaches(rp).contains(o) && reaches(o).contains(rp))))
  var lowered2 = lowered
  for scc <- sccs if scc.size >= 2 do
    lowerMutualSCC(scc.toVector.sortBy(_.s), lowered).foreach(rw => lowered2 = lowered2 ++ rw)
  val edges2 = edgesOf(lowered2)
  val recursive2 = lowered2.keySet.filter(isCyclic(edges2, _))
  val acyclic = lowered2.filter((rp, _) => !recursive2(rp))
  def inl(b: Space): Space = inlineCalls(b, acyclic, budget)
  val topBody = inl(lowered2(main.name).body)
  val residual = recursive2.iterator.map(rp => rp -> lowered2(rp).copy(body = inl(lowered2(rp).body))).toMap
  (topBody, residual)

/** Every node-input coordinate (l, x) must reference an in-range slot of an ancestor-or-self
 *  graph: 0 <= l <= the node's depth, and x within that level's node count.  A malformed
 *  (e.g. downward) coordinate means a graph-rewrite produced garbage.  Used by tests/assertions —
 *  `optimize` no longer swallows ill-formed output (that would hide real bugs); the passes are
 *  correct by construction and a violation should surface, not be silently reverted. */
def wellFormed(g: RecursiveOpGraph): Boolean =
  def chk(node: RecursiveOpGraph, chain: Vector[RecursiveOpGraph]): Boolean =
    val ch = chain :+ node
    def ok(l: Int, x: Int): Boolean = l >= 0 && l < ch.length && x >= 0 && x < ch(l).nodes.length
    node.nodes.forall {
      case Left(n) => n.inputs.forall(ok)
      case Right(sg) => sg.root.inputs.forall(ok) && chk(sg, ch)
    }
  chk(g, Vector.empty)

/** A 64-bit structural fingerprint of a graph (ops, constants, kinds, input coordinates, nesting).
 *  Identical structure ⇒ identical hash; used for fixed-point convergence in [[optimize]] instead of
 *  the expensive `show`-string equality.  A (vanishingly unlikely) collision only makes `optimize`
 *  stop a round early — sound, since every pass is semantics-preserving. */
def structuralHash(g: RecursiveOpGraph): Long =
  var h = 1125899906842597L
  inline def mix(x: Long): Unit = h = h * 1000003L + x
  def node(n: Node[(Int, Int)]): Unit =
    mix(n.operation.hashCode); mix(n.constant.hashCode); mix(n.kind.hashCode); mix(n.inputs.length)
    n.inputs.foreach((l, x) => { mix(l); mix(x) })
  def go(g: RecursiveOpGraph): Unit =
    node(g.root); mix(g.nodes.length)
    g.nodes.foreach { case Left(n) => mix(2); node(n); case Right(sg) => mix(3); go(sg) }
  go(g); h

/** push_out (LICM) + optimize_sharing (CSE) to a fixed point.  Both passes are well-formed by
 *  construction (push_out is coordinate-free until linearization; optimize_sharing value-numbers).
 *  No exceptions are swallowed and no output is silently reverted — a malformed graph is a bug to
 *  fix, not to hide.  `budget` bounds the fixpoint (returning the best graph so far, sound since
 *  every pass preserves semantics); `prof` accounts time per pass. */
def optimize(g: RecursiveOpGraph, budget: Deadline = Deadline.never, prof: Profiler = Profiler.off,
             hoistSubgraphs: Boolean = true): RecursiveOpGraph =
  def loop(g: RecursiveOpGraph, hg: Long): RecursiveOpGraph =
    if budget.expired then g
    else
      prof.count("opt_iters", 1)
      val loops0 = loopNodes(g)
      val g1 = prof.timed("push_out")(push_out(g, hoistSubgraphs)); prof.count("push_out", (loops0 - loopNodes(g1)).toLong)  // nodes hoisted out of loops
      val n1 = nodeCount(g1)
      val g2 = prof.timed("optimize_sharing")(optimize_sharing(g1)); prof.count("optimize_sharing", (n1 - nodeCount(g2)).toLong)  // duplicates removed
      val hg2 = structuralHash(g2)
      if hg == hg2 then g else loop(g2, hg2)   // structural fixpoint (hash carried across iterations — one traversal per round, not two)
  loop(g, structuralHash(g))

/** True when the optimized graph has been "optimized away" to a constant — its result needs no
 *  inputs (no Extract reachable), i.e. compilation fully evaluated the program to a Literal/Empty.
 *  Reported so a fully compile-time-evaluated program is called out explicitly. */
def optimizedAway(g: RecursiveOpGraph): Boolean =
  def hasExtract(x: RecursiveOpGraph): Boolean =
    x.nodes.exists { case Left(n) => n.operation.startsWith("Extract"); case Right(sg) => hasExtract(sg) }
  // the program is a closed constant iff it reads no inputs and its result op is a Literal/Empty
  !hasExtract(g) && (g.nodes.lastOption match
    case Some(Left(n)) => n.operation == "Literal" || n.operation == "Empty"
    case _ => false)


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
      case Space.Iteration(x, symbol, rest, templates) =>
        Set[PathValue](f"Iteration.head.${symbol.s}", f"Iteration.tail.${rest.s}") union
        (for sp <- recs(x) yield PathValue(PathItem.Symbol("Iteration")::PathItem.Symbol("domain")::sp.items)) union
        (for sp <- recs(templates) yield PathValue(PathItem.Symbol("Iteration")::PathItem.Symbol("templates")::sp.items))
      case Space.Fixpoint(init, rec, body) =>
        Set[PathValue](f"Fixpoint.rec.${rec.s}") union
        (for sp <- recs(init) yield PathValue(PathItem.Symbol("Fixpoint")::PathItem.Symbol("init")::sp.items)) union
        (for sp <- recs(body) yield PathValue(PathItem.Symbol("Fixpoint")::PathItem.Symbol("body")::sp.items))
      case Space.GroundedPS(p, f) => ???
      case Space.GroundedSS(s, f) => ???
      case Space.Range(x, lo, hi) =>
        Set[PathValue](f"Range.lo.$lo", f"Range.hi.$hi") union
        (for sp <- recs(x) yield PathValue(PathItem.Symbol("Range")::sp.items))

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
    case Space.Iteration(src_e, symbol, rest, templates) => Space.Iteration(recs(src_e), symbol, rest, recs(templates))
    case Space.Fixpoint(init, rec, body) => Space.Fixpoint(recs(init), rec, recs(body))
    case Space.Fold(src_e, init, acc, symbol, rest, templates, update) => Space.Fold(recs(src_e), recp(init), acc, symbol, rest, recs(templates), recp(update))
    case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p), f)
    case Space.GroundedSS(s, f) => Space.GroundedSS(recs(s), f)
    case Space.Range(x, lo, hi) => Space.Range(recs(x), lo, hi)
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
    case Space.Iteration(src_e, symbol, rest, templates) => Space.Iteration(recs(src_e), symbol, rest, recs(templates))
    case Space.Fixpoint(init, rec, body) => Space.Fixpoint(recs(init), rec, recs(body))
    case Space.Fold(src_e, init, acc, symbol, rest, templates, update) => Space.Fold(recs(src_e), recp(init), acc, symbol, rest, recs(templates), recp(update))
    case Space.GroundedPS(p, f) => Space.GroundedPS(recp(p), f)
    case Space.GroundedSS(s, f) => Space.GroundedSS(recs(s), f)
    case Space.Range(x, lo, hi) => Space.Range(recs(x), lo, hi),
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
      val heads = paths.filter(_.items.nonEmpty)   // the empty path ε has no head ⇒ contributes nothing (matches eval)
      if heads.isEmpty then Space.Empty
      else heads.map(p => subs(template)(spre={ case Space.Mention(`rest`) => Space.Singleton(Path.Constant(PathValue(p.items.tail))) },
                                         ppre={ case Path.Deref(`symbol`) => Path.Constant(PathValue(p.items.head::Nil)) }))
        .reduce(Space.Union(_, _))
  })

  val IterateSingleton_Deref = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(Space.Singleton(Path.first((Path.Deref(spr), rest))), pr, sm, body) if spr.lengthHint == 1 =>
      // iterating a single-item path leaves the tail-set {ε} (NOT ∅): the head is consumed, nothing remains.
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
    case op @ Space.Composition(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Union(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Intersection(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Subtraction(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Restriction(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Raffination(Space.Literal(x), Space.Literal(y)) => Space.Literal(eval(op))
    case op @ Space.Range(Space.Literal(y), _, _) => Space.Literal(eval(op))
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

  private def emptyPath(p: Path): Boolean = p match { case Path.Constant(PathValue(Nil)) => true; case _ => false }
  /** Conservative static "this space has at least one path" / "…at least one path with a head" tests.
   *  Both only ever return true when CERTAIN, so the IterUnion hoist below stays sound. */
  def provablyNonEmpty(s: Space): Boolean = s match
    case Space.Singleton(_) => true
    case Space.Literal(SpaceValue(ps)) => ps.nonEmpty
    case Space.Union(a, b) => provablyNonEmpty(a) || provablyNonEmpty(b)
    case Space.Wrap(a, _) => provablyNonEmpty(a)
    case Space.Composition(a, b) => provablyNonEmpty(a) && provablyNonEmpty(b)
    case _ => false
  private def pathHeaded(p: Path): Boolean = p match
    case Path.Constant(PathValue(items)) => items.nonEmpty
    case Path.Deref(pr) => pr.lengthHint >= 1
    case Path.Concat(l, r) => pathHeaded(l) || pathHeaded(r)   // ≥1 item on either side ⇒ the concat has a head
    case _ => false
  def provablyHeaded(s: Space): Boolean = s match
    case Space.Singleton(p) => pathHeaded(p)
    case Space.Literal(SpaceValue(ps)) => ps.exists(_.items.nonEmpty)
    case Space.Union(a, b) => provablyHeaded(a) || provablyHeaded(b)
    case Space.Wrap(a, p) => if emptyPath(p) then provablyHeaded(a) else provablyNonEmpty(a)
    case _ => false

  /** Hoist a loop-INVARIANT union branch OUT of the iteration — the strongest way to whack products:
   *  the invariant branch is computed ONCE instead of once per head, with no re-iteration of src.
   *  Sound ONLY when src provably has ≥1 head (`iter(src, l∪r) = l ∪ iter(src, r)` needs the union over
   *  heads to be non-empty; over a headless source iter is ∅, so the bare hoist would leak l — the old
   *  unsoundness, egglog: formal.egg IterUnion checks).  When src is not provably headed we DON'T rewrite
   *  (no bloat, no regression); the op-graph push_out still performs sound loop-invariant motion at run
   *  time for the symbolic case. */
  val IterUnion_Indep = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if provablyHeaded(src) && {
      val (soc, poc) = collect(lhs)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () }); soc.isEmpty && poc.isEmpty
    } => Space.Union(Space.Iteration(src, symbol, rest, rhs), lhs)
    case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if provablyHeaded(src) && {
      val (soc, poc) = collect(rhs)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () }); soc.isEmpty && poc.isEmpty
    } => Space.Union(Space.Iteration(src, symbol, rest, lhs), rhs)
  })

  val UnwrapConcat_Unwraps = subs(_: Space)(PartialFunction.empty, {
    case Space.Unwrap(src, Path.Concat(l, r)) => Space.Unwrap(Space.Unwrap(src, l), r)
  })

  /** Merge adjacent CONSTANT unwraps into one (egglog-checked).  Constant-only so it cannot oscillate
   *  with UnwrapConcat_Unwraps (which splits CONCAT-prefix unwraps): the merged prefix is a single
   *  Constant, never a Concat, so the splitter never fires on it. */
  val Unwrap_Merge = subs(_: Space)(PartialFunction.empty, {
    case Space.Unwrap(Space.Unwrap(s, Path.Constant(a)), Path.Constant(b)) =>
      Space.Unwrap(s, Path.Constant(PathValue(a.items ++ b.items)))
  })

  val SingletonSpaceOp_PathOp = subs(_: Space)(PartialFunction.empty, {
    case Space.Wrap(Space.Singleton(y), x) => Space.Singleton(Path.Concat(x, y))
  })

  val SingletonComposition_Wrap = subs(_: Space)(PartialFunction.empty, {
    case Space.Composition(Space.Singleton(x), y) => Space.Wrap(y, x)
  })

  val SingletonRestriction_Unwrap = subs(_: Space)(PartialFunction.empty, {
    // Restriction keeps whole paths INCLUDING the matched prefix; Unwrap only projects the
    // tails.  The canonical law (formal.egg: Restriction x (Singleton p) = Wrap p (Unwrap x p))
    // re-wraps the prefix.  Dropping it (the old `Unwrap(x, y)`) was unsound.
    case Space.Restriction(x, Space.Singleton(y)) => Space.Wrap(Space.Unwrap(x, y), y)
  })

  /** Cheap structural identities (Empty absorption/units, epsilon concat).  These keep the
   *  reducer total and shrink open terms that driving constantly produces (e.g. an Empty
   *  branch from an exhausted search level). */
  val AlgebraicIdentities = subs(_: Space)(spost = {
    case Space.Literal(SpaceValue(ps)) if ps.isEmpty => Space.Empty          // empty literal IS Empty (so absorption fires)
    case Space.Union(Space.Empty, x) => x
    case Space.Union(x, Space.Empty) => x
    case Space.Union(x, y) if x == y => x                                     // idempotence (egglog: (Union x x) x)
    case Space.Intersection(Space.Empty, _) => Space.Empty
    case Space.Intersection(_, Space.Empty) => Space.Empty
    case Space.Intersection(x, y) if x == y => x                             // idempotence
    case Space.Subtraction(Space.Empty, _) => Space.Empty
    case Space.Subtraction(x, Space.Empty) => x
    case Space.Subtraction(x, y) if x == y => Space.Empty
    case Space.Restriction(Space.Empty, _) => Space.Empty
    case Space.Restriction(_, Space.Empty) => Space.Empty
    case Space.Restriction(x, y) if x == y => x                             // every path of x has itself (∈x) as a prefix
    case Space.Composition(Space.Empty, _) => Space.Empty
    case Space.Composition(_, Space.Empty) => Space.Empty
    case Space.Wrap(Space.Empty, _) => Space.Empty
    case Space.Wrap(s, Path.Constant(PathValue(Nil))) => s                   // wrap with the empty path = identity
    case Space.Unwrap(Space.Empty, _) => Space.Empty
    case Space.Unwrap(s, Path.Constant(PathValue(Nil))) => s                 // unwrap the empty path = identity
    case Space.Raffination(Space.Empty, _) => Space.Empty
    case Space.Raffination(x, Space.Empty) => x
    case Space.Raffination(x, y) if x == y => Space.Empty                    // x \ (x<|x) = x \ x = ∅
    case Space.TailsUnion(Space.Empty) => Space.Empty
    case Space.TailsIntersection(Space.Empty) => Space.Empty
    case Space.Range(Space.Empty, _, _) => Space.Empty
    case Space.Iteration(Space.Empty, _, _, _) => Space.Empty                // iter over ∅ has no heads = ∅
    case Space.Iteration(_, _, _, Space.Empty) => Space.Empty                // iter with ∅ body = ⋃∅ = ∅
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
    => src
  })

  /** the body is exactly the rest-mention: the iteration unions the tail-sets over all heads = TailsUnion(src). */
  val Iter_Tails = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, _, rest, Space.Mention(sm)) if sm == rest => Space.TailsUnion(src)
  })

  /** TailsUnion of a singleton drops its (statically-known) first item; a length-1 path leaves ε,
   *  the empty path leaves nothing (Empty). */
  val TailsUnion_Singleton = subs(_: Space)(PartialFunction.empty, {
    case Space.TailsUnion(Space.Singleton(Path.Constant(PathValue(Nil)))) => Space.Empty
    case Space.TailsUnion(Space.Singleton(Path.Constant(PathValue(_ :: t)))) => Space.Singleton(Path.Constant(PathValue(t)))
    case Space.TailsUnion(Space.Singleton(Path.Deref(spr))) if spr.lengthHint == 1 => Space.Singleton(Path.Constant(PathValue(Nil)))
    case Space.TailsUnion(Space.Singleton(Path.Concat(Path.Deref(spr), r))) if spr.lengthHint == 1 => Space.Singleton(r)
    case Space.TailsUnion(Space.Singleton(Path.Concat(Path.Constant(PathValue(_ :: Nil)), r))) => Space.Singleton(r)
    case Space.TailsUnion(Space.Singleton(Path.Concat(Path.Constant(PathValue(_ :: t)), r))) => Space.Singleton(Path.Concat(Path.Constant(PathValue(t)), r))
  })

  /** a singleton is a 1-element set, so an ordered-slice Range keeps it iff index 0 ∈ [lo,hi). */
  val Range_Singleton = subs(_: Space)(PartialFunction.empty, {
    case Space.Range(Space.Singleton(p), lo, hi) =>     // ordered-slice of a 1-element set: kept iff index 0 ∈ [lo,hi)
      val (l, h) = RangeBounds.normalize(1, lo, hi); if l < h then Space.Singleton(p) else Space.Empty
  })

  /** unwrap a just-wrapped prefix (egglog-checked): equal prefix cancels; a constant prefix that is
   *  a prefix of / extended by the other re-wraps or strips the rest; otherwise (incomparable) Empty. */
  val Unwrap_Wrap = subs(_: Space)(PartialFunction.empty, {
    case Space.Unwrap(Space.Wrap(s, p), q) if p == q => s
    case Space.Unwrap(Space.Wrap(s, Path.Constant(PathValue(ps))), Path.Constant(PathValue(qs))) =>
      if ps.startsWith(qs) then Space.Wrap(s, Path.Constant(PathValue(ps.drop(qs.length))))
      else if qs.startsWith(ps) then Space.Unwrap(s, Path.Constant(PathValue(qs.drop(ps.length))))
      else Space.Empty
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
    case Space.Fixpoint(init, rec, body) => ??? // itypes: fixpoint type inference WIP
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
    case Space.GroundedPS(p, f) => ???
    case Space.GroundedSS(s, f) => ???
    case Space.Range(x, _, _) => recs(x)
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
    case Space.Iteration(src, symbol, rest, templates) =>
      recs(templates)
    case Space.Fixpoint(init, rec, body) => recs(init) union recs(body)
    case Space.GroundedPS(p, f) => ???
    case Space.GroundedSS(s, f) => ???
    case Space.Range(x, _, _) => recs(x)
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
