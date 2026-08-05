package morkl

import scala.util.Random
import scala.collection.mutable.{ArrayBuffer, LongMap, Stack}
import scala.collection.Searching
import java.util.Base64
import java.nio.charset.StandardCharsets
import scala.language.implicitConversions


/** A path item is just its text: no arity/variable kinds, one alias to keep the domain vocabulary. */
type PathItem = String

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
  def show: String = items.mkString(".")

  def prefixes: Seq[PathValue] =
    // e.g. Test.Foo.Bar.2 |-> Vector(Test, Test.Foo, Test.Foo.Bar, Test.Foo.Bar.2)
    items.indices.map(i => PathValue(items.slice(0, i + 1)))

  infix def mostSpecific(that: PathValue): Option[PathValue] =
    // Foo.Bar mostSpecific Foo.Bar.Baz == Some(Foo.Bar.Baz)
    if this.prefixes.contains(that) then Some(this)
    else if that.prefixes.contains(this) then Some(that)
    else None


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
    override def resolve(pr: PathRef): PathValue = PathValue((pr.s + "_" + Base64.getEncoder.encodeToString(rng.nextBytes(4)).take(4))::Nil)



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

/** `sizeHint`, like [[PathRef.lengthHint]], is an out-of-equality annotation: the author's
 *  contract that this mention is only ever bound to spaces of exactly that many paths.
 *  Trusted by the size analysis (a wrong hint yields wrong bounds, like a wrong lengthHint). */
case class SpaceMention(s: String):
  val sizeHint = -1L
  def known(size: Long): SpaceMention = new SpaceMention(s) { override val sizeHint = size }

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


/** Canonical total order on paths — the trie-native order (`String` order on items, with
 *  shorter-is-less on a shared prefix).  Every backend slices `Range` by THIS order, so they agree. */
given pathValueOrdering: Ordering[PathValue] with
  def compare(a: PathValue, b: PathValue): Int =
    val ai = a.items.iterator; val bi = b.items.iterator
    while ai.hasNext && bi.hasNext do
      val c = ai.next().compareTo(bi.next())
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
    })(body), List(Lower.ConstantOps, Lower.SizeEmpty, Lower.IterateSingleton_Deref, Lower.LiteralSpaceOps, Lower.SingletonConst_Literal, Lower.ConcatSingleton_Iter, Lower.IterUnion_Indep, Lower.IterComposition_Indep, Lower.EpsGuard_Wrap, Lower.IterWitness_TransposeSemiJoin, Lower.IterWitness_HeadNarrow, Lower.UnwrapPush, Lower.WrapMerge, Lower.RestrictionPush, Lower.CompWrapAssoc, Lower.CompAssocRight, Lower.CompLitWraps, Lower.Unwrap_Merge, Lower.SingletonConstPrefix_Wrap, Lower.RaffinationPush, Lower.RaffRestrictAlgebra, Lower.RestrictRaffWrapBoth, Lower.IterSetOpMerge, Lower.Wrap_Iter, Lower.Iter_Ident, Lower.Concat_Path, Lower.IterateLiteral_Union, Lower.UnwrapConcat_Unwraps, Lower.SingletonComposition_Wrap, Lower.SingletonSpaceOp_PathOp, Lower.SingletonRestriction_Unwrap)))
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
 *  a space containing the empty path both rendered as "", and an item containing a "." was
 *  indistinguishable from a multi-item path.  This base64-per-item codec round-trips empty
 *  spaces, epsilon paths and arbitrary items unambiguously, while staying
 *  backward-compatible with plain `Syntax.parse`-able lines. */
object LiteralCodec:
  private val marker = "lit64:"
  private def encodeItem(item: PathItem): String = Base64.getEncoder.encodeToString(item.getBytes(StandardCharsets.UTF_8))
  private def decodeItem(s: String): PathItem = new String(Base64.getDecoder.decode(s), StandardCharsets.UTF_8)
  private def encodePath(p: PathValue): String = marker + p.items.map(encodeItem).mkString(".")
  private def decodePath(line: String): PathValue =
    val body = line.stripPrefix(marker)
    if body.isEmpty then PathValue(Nil) else PathValue(body.split("\\.", -1).toList.map(decodeItem))
  def encode(sv: SpaceValue): String = sv.paths.toVector.sortBy(_.show).map(encodePath).mkString("\n")
  def decode(constant: String): SpaceValue =
    SpaceValue(constant.linesIterator.filter(_.nonEmpty).map(line =>
      if line.startsWith(marker) then decodePath(line) else Syntax.parse(line)).toSet)

  /** Lossless encoding of a single Constant path: keep the readable `show` form when it
   *  round-trips through `Syntax.parse` (the common case, so op-graph dumps stay
   *  legible), otherwise escape with the base64 marker.  The plain `show`/`parse` round-trip is
   *  LOSSY for the empty path (`"".split('.')` -> `[""]`) and
   *  items containing a dot — these must be escaped or the op-graph mis-evaluates. */
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
            // an Iteration binder always binds a single head item — restore the length-1 tag lost by encoding
            s(c) = Space.Iteration(inputs(0).sget, popped(0).asInstanceOf[Path.Deref].pr.known(1), popped(1).asInstanceOf[Space.Mention].variable, popped.last.asInstanceOf[Space])
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
          // by scope level keeps the two distinct (so `next(cur)` is never merged into `next(init)`).
          // The key is POSITIONAL (slot index), not the binder's name: a binding is identified by
          // where it sits, so α-equivalent sibling subgraphs (same shape, different binder names)
          // get identical VN sequences and deduplicate (see the SG key below).  Extracts are never
          // redirected.  Non-extract constants are length-prefixed so a space inside one can't be
          // confused with a field boundary (injective).
          val isExtract = n.operation.startsWith("Extract")
          // idempotence peephole: an interior pass-through `Union(x, x)` IS x — drop the node and
          // alias it to its operand (the union splits in push_out leave these behind; collapsing
          // them normalizes bodies so α-equivalent loops keep merging).  A scope RESULT stays
          // materialized (executors read the last slot).
          if !isResult && n.operation == "Union" && n.inputs.length == 2 && vnAt(n.inputs(0)) == vnAt(n.inputs(1)) then
            fr.oldToNew(j) = newAt(n.inputs(0)); fr.oldToVN(j) = vnAt(n.inputs(0))
          else
            val key = if isExtract then s"$lvl@${n.operation} ${n.kind} @$j"
              else s"${n.operation} ${n.kind} ${n.inputs.map(vnAt).mkString(",")} ${n.constant.length}:${n.constant}"
            val vn = intern(key)
            lookup(key) match
              case Some(nc) if !isResult && !isExtract => fr.oldToNew(j) = nc; fr.oldToVN(j) = vn
              case _ =>
                val nc = r.store(Node(n.operation, n.constant, n.kind, n.inputs.map(newAt)))
                if !isResult && !isExtract then fr.seen.getOrElseUpdate(key, nc)
                fr.oldToNew(j) = nc; fr.oldToVN(j) = vn; keptVNs += vn
        case Right(sg) =>
          val (newSg, bodyVNs) = process(sg, Some(r))
          // Iteration/Fixpoint root constants are binder NAMES (display only — execution binds by
          // slot), so they are dropped from the key: α-equivalent loops over the same source merge.
          val rootConst = if sg.root.operation == "Iteration" || sg.root.operation == "Fixpoint" then "" else sg.root.constant
          val key = s"SG ${sg.root.operation} ${sg.root.inputs.map(vnAt).mkString(",")} ${bodyVNs.mkString(",")} ${rootConst.length}:$rootConst"
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
def push_out(g: RecursiveOpGraph, hoistSubgraphs: Boolean = true, splitUnions: Boolean = true): RecursiveOpGraph =
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
  def nScopes = scopeLevel.length
  val resultIds = MBuf.tabulate(nScopes)(sid => scopeNodeIds(sid)(scopeResultIdx(sid)))

  // ---- structural sets: per scope, every id its subtree references (allRefs) and every id homed
  // in its subtree (subtreeIds), bottom-up — RECOMPUTABLE because the union split below mutates
  // the id graph. ----
  var entsByHome: Array[MBuf[Int]] = null
  var allRefs: Array[MSet[Int]] = null
  var subtreeIds: Array[MSet[Int]] = null
  var placement: Array[Int] = null
  /** A subgraph's external dependencies: its source inputs + every reference its whole subtree makes
   *  to nodes OUTSIDE that subtree.  These determine how far it can hoist. */
  def subgraphDeps(e: Ent): Array[Int] =
    (allRefs(e.childScope).iterator.filterNot(subtreeIds(e.childScope)) ++ e.inputIds.iterator).toArray
  // earliest-legal placement scope per node id (deepest dependency, memoized)
  def place(id: Int): Int =
    if placement(id) >= 0 then return placement(id)
    val e = ents(id)
    val deps = if e.pinned then Array.empty[Int] else if e.isSub then subgraphDeps(e) else e.inputIds
    val p = if e.pinned then e.homeScope
            else if deps.isEmpty then rootScope
            else deps.iterator.map(place).maxBy(scopeLevel)   // deepest (innermost original loop) dep
    placement(id) = p; p
  def recompute(): Unit =
    entsByHome = Array.fill(nScopes)(MBuf.empty[Int]); for e <- ents do entsByHome(e.homeScope).addOne(e.id)
    allRefs = Array.fill(nScopes)(MSet.empty[Int])
    subtreeIds = Array.fill(nScopes)(MSet.empty[Int])
    for sid <- (nScopes - 1) to 0 by -1 do
      for id <- entsByHome(sid) do { allRefs(sid) ++= ents(id).inputIds; subtreeIds(sid).addOne(id) }
      if scopeParent(sid) >= 0 then { allRefs(scopeParent(sid)) ++= allRefs(sid); subtreeIds(scopeParent(sid)) ++= subtreeIds(sid) }
    placement = Array.fill(ents.length)(-1)
    for id <- ents.indices do place(id)
  recompute()

  // ---- union split (the drain-chain step): an Iteration whose RESULT is `Union(a, b)` with one
  // operand placed OUTSIDE the loop (loop-invariant by construction) splits into
  //   Union(iter{a}, Composition(headedGuard(src), b))
  // in the parent scope.  The guard `Range(src,-1,0).iter(_,_,{ε})` is {ε} iff src has ≥1 head
  // (ε sorts first, so the LAST path is headed iff any is) — O(one path) — so the hoisted operand
  // is emitted exactly when the loop would have run, and ∅-sources stay ∅.  This is what lets a
  // whole inner loop hoist out of an enclosing product loop: the next optimize() round sees the
  // parent's Union and splits/hoists again.  One split per pass; optimize() iterates to fixpoint. */
  /** the loop's result behind any pass-through `Union(x, x)` chain (splits below leave those) */
  def effectiveResult(sid: Int): Int =
    var rid = resultIds(sid)
    while { val e = ents(rid); !e.isSub && e.op == "Union" && e.inputIds.length == 2 && e.inputIds(0) == e.inputIds(1) } do
      rid = ents(rid).inputIds(0)
    rid
  /** redirect every consumer of the loop `ownerId` to `newId`, retargeting the parent's result and
   *  unpinning the loop (it is no longer its scope's result, so it may hoist like any subgraph) */
  def rewireLoop(ownerId: Int, parentSid: Int, newId: Int): Unit =
    for i <- ents.indices if i != newId do
      val e = ents(i)
      if e.inputIds.contains(ownerId) then
        ents(i) = Ent(e.id, e.isSub, e.op, e.constant, e.kind, e.inputIds.map(x => if x == ownerId then newId else x), e.homeScope, e.childScope, e.pinned)
    if resultIds(parentSid) == ownerId then
      resultIds(parentSid) = newId
      val u = ents(newId)
      ents(newId) = Ent(u.id, u.isSub, u.op, u.constant, u.kind, u.inputIds, u.homeScope, u.childScope, true)
    val oe = ents(ownerId)
    ents(ownerId) = Ent(ownerId, true, oe.op, oe.constant, oe.kind, oe.inputIds, oe.homeScope, oe.childScope, !hoistSubgraphs)

  def trySplit(): Boolean =
    var sid = 0
    while sid < nScopes do
      val ownerId = scopeOwner(sid)
      if ownerId >= 0 && ents(ownerId).op == "Iteration" then
        val parentSid = scopeParent(sid)
        val rid = effectiveResult(sid)
        val r = ents(rid)
        if !r.isSub && placement(rid) == sid && r.inputIds.length == 2 then
          val a = r.inputIds(0); val b = r.inputIds(1)
          if r.op == "Union" && a != b then
            val hoisted = if placement(b) != sid then b else if placement(a) != sid then a else -1
            if hoisted >= 0 then
              val kept = if hoisted == b then a else b
              // in-scope result becomes a pass-through of the kept operand (no index shifts)
              ents(rid) = Ent(rid, false, "Union", "", "space", Array(kept, kept), r.homeScope, -1, r.pinned)
              // headed-guard subgraph: Range(src,-1,0).iter(_, _, {ε}) — {ε} iff the loop runs
              val srcId = ents(ownerId).inputIds(0)
              val rangeId = ents.length
              ents.addOne(Ent(rangeId, false, "Range", "-1,0", "space", Array(srcId), parentSid, -1, false))
              val guardId = ents.length
              val gsid = nScopes
              ents.addOne(Ent(guardId, true, "Iteration", "_", "space", Array(rangeId), parentSid, gsid, !hoistSubgraphs))
              val e0 = ents.length; ents.addOne(Ent(e0, false, "ExtractPathRef", "_", "path", Array(), gsid, -1, true))
              val e1 = ents.length; ents.addOne(Ent(e1, false, "ExtractSpaceMention", "_", "space", Array(), gsid, -1, true))
              val e2 = ents.length; ents.addOne(Ent(e2, false, "Constant", LiteralCodec.encodeConst(PathValue(Nil)), "path", Array(), gsid, -1, false))
              val e3 = ents.length; ents.addOne(Ent(e3, false, "Singleton", "", "space", Array(e2), gsid, -1, true))
              scopeLevel.addOne(scopeLevel(sid)); scopeParent.addOne(parentSid)
              scopeRoot.addOne(Node("Iteration", "_", "space", Vector()))
              scopeResultIdx.addOne(3); scopeOwner.addOne(guardId)
              scopeNodeIds.addOne(MBuf(e0, e1, e2, e3)); resultIds.addOne(e3)
              val compId = ents.length
              ents.addOne(Ent(compId, false, "Composition", "", "space", Array(guardId, hoisted), parentSid, -1, false))
              val unionId = ents.length
              ents.addOne(Ent(unionId, false, "Union", "", "space", Array(ownerId, compId), parentSid, -1, false))
              rewireLoop(ownerId, parentSid, unionId)
              return true
          else if r.op == "Composition" then
            // iter{g · s} with g loop-invariant = g · iter{s} (and symmetrically) — sound with NO
            // guard: composition distributes over the union of iterates, and ∅ annihilates it.
            val outside = if placement(a) != sid then a else if placement(b) != sid then b else -1
            if outside >= 0 && !(placement(a) != sid && placement(b) != sid) then
              val kept = if outside == a then b else a
              ents(rid) = Ent(rid, false, "Union", "", "space", Array(kept, kept), r.homeScope, -1, r.pinned)
              val compId = ents.length
              val inputs = if outside == a then Array(outside, ownerId) else Array(ownerId, outside)
              ents.addOne(Ent(compId, false, "Composition", "", "space", inputs, parentSid, -1, false))
              rewireLoop(ownerId, parentSid, compId)
              return true
      sid += 1
    false
  if splitUnions && trySplit() then recompute()

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
    val resultId = resultIds(sid)
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
  def tag(rp: RoutinePtr): Path = Path.Constant(PathValue(List(("#scc#" + rp.s))))
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
            val argTag = Path.Constant(PathValue(List("#arg#")))
            val outTag = Path.Constant(PathValue(List("#out#")))
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
      val g1 = prof.timed("push_out")(push_out(g, hoistSubgraphs, splitUnions = hoistSubgraphs)); prof.count("push_out", (loops0 - loopNodes(g1)).toLong)  // nodes hoisted out of loops
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
        (for p <- recp(l) yield PathValue("Concat"::"lhs"::p.items)) union
        (for p <- recp(r) yield PathValue("Concat"::"rhs"::p.items))
      case Path.GroundedPP(p, f) => ???
      case Path.GroundedSP(s, f) => ???

    def recs(x: Space): Set[PathValue] = x match
      case Space.Empty => Set("Empty")
      case Space.Call(rp, refs, mentions) =>
        Set[PathValue](f"Call.routine.${rp.s}") union
        (for (pd, i) <- refs.zipWithIndex; pp <- recp(pd) yield PathValue("Call"::"path"::i.toString::pp.items)).toSet union
        (for (sd, i) <- mentions.zipWithIndex; sp <- recs(sd) yield PathValue("Call"::"space"::i.toString::sp.items)).toSet
      case Space.Mention(p) => Set(f"Mention.${p.s}")
      case Space.Singleton(p) => Set(f"Singleton.${p.pretty}")
      case Space.Literal(SpaceValue(ps)) => for pp <- ps yield PathValue("Literal"::pp.items)
      case Space.Union(x, y) =>
        (for pp <- recs(x) yield PathValue("Union"::pp.items)) union
        (for pp <- recs(y) yield PathValue("Union"::pp.items))
      case Space.Intersection(x, y) =>
        (for pp <- recs(x) yield PathValue("Intersection"::pp.items)) union
        (for pp <- recs(y) yield PathValue("Intersection"::pp.items))
      case Space.Subtraction(x, y) =>
        (for pp <- recs(x) yield PathValue("Subtraction"::"domain"::pp.items)) union
        (for pp <- recs(y) yield PathValue("Subtraction"::"argument"::pp.items))
      case Space.Restriction(x, y) =>
        (for pp <- recs(x) yield PathValue("Restriction" :: "domain" :: pp.items)) union
        (for pp <- recs(y) yield PathValue("Restriction" :: "argument" :: pp.items))
      case Space.Raffination(x, y) =>
        (for pp <- recs(x) yield PathValue("Raffination" :: "domain" :: pp.items)) union
        (for pp <- recs(y) yield PathValue("Raffination" :: "argument" :: pp.items))
      case Space.Composition(x, y) =>
        (for pp <- recs(x) yield PathValue("Composition" :: "domain" :: pp.items)) union
        (for pp <- recs(y) yield PathValue("Composition" :: "argument" :: pp.items))
      case Space.Wrap(x, p_e) =>
        (for pp <- recp(p_e) yield PathValue("Wrap" :: "prefix" :: pp.items)) union
        (for pp <- recs(x) yield PathValue("Wrap" :: "domain" :: pp.items))
      case Space.Unwrap(x, p_e) =>
        (for pp <- recp(p_e) yield PathValue("Unwrap" :: "prefix" :: pp.items)) union
        (for pp <- recs(x) yield PathValue("Unwrap" :: "domain" :: pp.items))
      case Space.TailsUnion(x) =>
        for pp <- recs(x) yield PathValue("TailsUnion" :: pp.items)
      case Space.TailsIntersection(x) =>
        for pp <- recs(x) yield PathValue("TailsIntersection" :: pp.items)
      case Space.Iteration(x, symbol, rest, templates) =>
        Set[PathValue](f"Iteration.head.${symbol.s}", f"Iteration.tail.${rest.s}") union
        (for sp <- recs(x) yield PathValue("Iteration"::"domain"::sp.items)) union
        (for sp <- recs(templates) yield PathValue("Iteration"::"templates"::sp.items))
      case Space.Fixpoint(init, rec, body) =>
        Set[PathValue](f"Fixpoint.rec.${rec.s}") union
        (for sp <- recs(init) yield PathValue("Fixpoint"::"init"::sp.items)) union
        (for sp <- recs(body) yield PathValue("Fixpoint"::"body"::sp.items))
      case Space.GroundedPS(p, f) => ???
      case Space.GroundedSS(s, f) => ???
      case Space.Range(x, lo, hi) =>
        Set[PathValue](f"Range.lo.$lo", f"Range.hi.$hi") union
        (for sp <- recs(x) yield PathValue("Range"::sp.items))

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
      Space.Iteration(src, PathRef("_").known(1), name, Space.Mention(name))
  })

  val Literal_ConstantsUnion = subs(_: Space)(PartialFunction.empty, {
    case Space.Literal(SpaceValue(paths)) =>
      paths.map(p => Space.Singleton(Path.Constant(p))).reduce(Space.Union(_, _))
  })

  val IterateLiteral_Union = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(Space.Literal(SpaceValue(paths)), symbol, rest, template) =>
      // one copy per DISTINCT head, with the rest-mention bound to the whole group's tail-set —
      // exactly eval's groupMap.  (Unrolling per PATH handed a body a partial rest-set: wrong for
      // anything non-monotone in `rest` — Range, tails-∩, right-hand subtraction… — the corpus law
      // gate caught it on a two-paths-one-head literal under Range(rest, 2, 4).)  ε has no head
      // and contributes nothing (matches eval).
      val groups = paths.filter(_.items.nonEmpty).groupMap(_.items.head)(p => PathValue(p.items.tail))
      if groups.isEmpty then Space.Empty
      else groups.toList.sortBy(_._1).map((h, tails) =>
        subs(template)(spre = { case Space.Mention(`rest`) => Space.Literal(SpaceValue(tails)) },
                       ppre = { case Path.Deref(`symbol`) => Path.Constant(PathValue(h :: Nil)) }))
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

  private[morkl] def pathHeaded(p: Path): Boolean = p match
    case Path.Constant(PathValue(items)) => items.nonEmpty
    case Path.Deref(pr) => pr.lengthHint >= 1
    case Path.Concat(l, r) => pathHeaded(l) || pathHeaded(r)   // ≥1 item on either side ⇒ the concat has a head
    case _ => false

  // ---- abstract result-size analysis ------------------------------------------
  /** Interval abstraction of a space's SIZE: `lo ≤ |eval(s)| ≤ hi`, plus `loHeaded ≤ |{p ∈
   *  eval(s) : p ≠ ε}|` — the lower bound on HEADED paths, i.e. on the groups an iteration over
   *  the space runs (0 ≤ loHeaded ≤ lo ≤ hi).  Unknowns (mentions, calls, grounded, unwraps of
   *  unknowns) widen to `[0, ∞)`; arithmetic saturates at [[SizeBounds.INF]].
   *
   *  The transfer functions (each an exact set-cardinality law):
   *    union         [max(lo), l+r]        a headed path of either side survives: loHeaded = max
   *    intersection  [0, min(hi)]
   *    subtraction   [relu(lo_l − hi_r), hi_l]      (and likewise for loHeaded)
   *    restriction   [0, hi_l]  (∅ prefixes ⇒ ∅)
   *    raffination   [lo_l if r provably ∅ else 0, hi_l]
   *    composition   [max(lo) if both ≥ 1 else 0, hi_l·hi_r] — for a FIXED element of one side,
   *                  concatenation is injective in the other, so max is a sound lower bound
   *                  (the naive lo_l·lo_r overcounts when splits collide, e.g. {a,aa}·{a,aa});
   *                  a concat is headed when either part is
   *    wrap          size-preserving (bijective); a headed prefix makes every path headed
   *    unwrap/tails  [0, hi_src]
   *    range         window (0,k) / (−k,0) slices exactly min(size, k) paths
   *    iteration     [lo_body if the source provably RUNS (loHeaded_src ≥ 1) else 0,
   *                   hi_src·hi_body] — group bodies may overlap, so the lower bound takes ONE
   *                  group's body, never a product
   *    fixpoint      accumulates a union from init: [lo_init, ∞)
   *
   *  This subsumes the old syntactic `provablyNonEmpty`/`provablyHeaded` (now defined by it) and
   *  powers [[SizeEmpty]] (`hi == 0` IS the empty space) and the guard decision in
   *  [[IterUnion_Indep]] (a provably-running source hoists bare, with no runtime factor). */
  final case class SizeBounds(lo: Long, loHeaded: Long, hi: Long)
  object SizeBounds:
    val INF: Long = Long.MaxValue
    val unknown: SizeBounds = SizeBounds(0, 0, INF)
  import SizeBounds.INF
  private def satAdd(a: Long, b: Long): Long = if a == INF || b == INF then INF else { val s = a + b; if s < 0 then INF else s }
  private def satMul(a: Long, b: Long): Long = if a == 0 || b == 0 then 0 else if a == INF || b == INF || a > INF / b then INF else a * b
  private def relu(a: Long): Long = if a < 0 then 0 else a

  def sizeBounds(s: Space): SizeBounds = sizeBounds(s, Map.empty)
  /** `env` refines binder mentions: an iteration's rest-set is ONE head-group of its source, so
   *  `|rest| ≤ ⌈src⌉` — without it every nested rest-iteration widens to [0, ∞).  Binders named
   *  `_` are never bound (contexts ignore the throwaway binder), and a Fixpoint's rec stays
   *  unknown (its iterates are unbounded). */
  private def sizeBounds(s: Space, env: Map[SpaceMention, SizeBounds]): SizeBounds = s match
    case Space.Empty => SizeBounds(0, 0, 0)
    case Space.Singleton(p) => SizeBounds(1, if pathHeaded(p) then 1 else 0, 1)
    case Space.Literal(SpaceValue(ps)) => SizeBounds(ps.size, ps.count(_.items.nonEmpty), ps.size)
    case Space.Union(a, b) =>
      val x = sizeBounds(a, env); val y = sizeBounds(b, env)
      SizeBounds(x.lo max y.lo, x.loHeaded max y.loHeaded, satAdd(x.hi, y.hi))
    case Space.Intersection(a, b) =>
      SizeBounds(0, 0, sizeBounds(a, env).hi min sizeBounds(b, env).hi)
    case Space.Subtraction(a, b) =>
      val x = sizeBounds(a, env); val y = sizeBounds(b, env)
      SizeBounds(relu(x.lo - y.hi), relu(x.loHeaded - y.hi), x.hi)
    case Space.Restriction(a, b) =>
      val x = sizeBounds(a, env)
      SizeBounds(0, 0, if sizeBounds(b, env).hi == 0 then 0 else x.hi)
    case Space.Raffination(a, b) =>
      val x = sizeBounds(a, env); val y = sizeBounds(b, env)
      if y.hi == 0 then x else SizeBounds(0, 0, x.hi)
    case Space.Composition(a, b) =>
      val x = sizeBounds(a, env); val y = sizeBounds(b, env)
      val lo = if x.lo >= 1 && y.lo >= 1 then x.lo max y.lo else 0
      val loH = (if y.lo >= 1 then x.loHeaded else 0) max (if x.lo >= 1 then y.loHeaded else 0)
      SizeBounds(lo, loH, satMul(x.hi, y.hi))
    case Space.Wrap(src, p) =>
      val x = sizeBounds(src, env)
      SizeBounds(x.lo, if pathHeaded(p) then x.lo else x.loHeaded, x.hi)
    case Space.Unwrap(src, _) => SizeBounds(0, 0, sizeBounds(src, env).hi)
    case Space.TailsUnion(src) => SizeBounds(0, 0, sizeBounds(src, env).hi)
    case Space.TailsIntersection(src) => SizeBounds(0, 0, sizeBounds(src, env).hi)
    case Space.Range(x, a, b) =>
      val sub = sizeBounds(x, env)
      if a == 0 && b == 0 then sub                                        // the whole space
      else
        val window = if a == 0 && b > 0 then Some(b.toLong) else if b == 0 && a < 0 then Some(-a.toLong) else None
        window match
          case Some(w) => SizeBounds(sub.lo min w, 0, sub.hi min w)        // exactly min(size, w) paths
          case None =>
            // same-sign slice: at most b − a paths (Range(count, k, k+1) — the exactly-k idiom)
            val width = if (a > 0 && b >= a) || (a < 0 && b <= 0 && b >= a) then (b - a).toLong else INF
            SizeBounds(0, 0, sub.hi min width)
    case Space.Iteration(src, _, rest, body) =>
      val sb = sizeBounds(src, env)
      val benv = if rest.s == "_" then env else env.updated(rest, SizeBounds(0, 0, sb.hi))
      val bb = sizeBounds(body, benv)                                     // one head-group: |rest| ≤ ⌈src⌉
      val runs = sb.loHeaded >= 1                                         // ≥1 head-group ⇒ the body's union has ≥1 term
      SizeBounds(if runs then bb.lo else 0, if runs then bb.loHeaded else 0, satMul(sb.hi, bb.hi))
    case Space.Fixpoint(init, _, _) =>
      val ib = sizeBounds(init, env)                                           // the accumulator only grows from init
      SizeBounds(ib.lo, ib.loHeaded, INF)
    case Space.Fold(src, _, _, _, rest, body, _) =>
      val sb = sizeBounds(src, env)
      val benv = if rest.s == "_" then env else env.updated(rest, SizeBounds(0, 0, sb.hi))
      SizeBounds(0, 0, satMul(sb.hi, sizeBounds(body, benv).hi))
    case Space.Mention(m) =>
      // a sizeHint is the author's exact-cardinality contract; at most one path is ε, so ≥ k−1
      // are headed.  Intersect with the binder refinement (both are true facts when the hint is).
      val b = env.getOrElse(m, SizeBounds.unknown)
      if m.sizeHint < 0 then b
      else SizeBounds(b.lo max m.sizeHint, b.loHeaded max relu(m.sizeHint - 1), b.hi min m.sizeHint)
    case Space.Call(_, _, _) | Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => SizeBounds.unknown

  /** "this space has at least one path" / "…at least one path with a head" — via [[sizeBounds]];
   *  only ever true when CERTAIN, so the IterUnion hoist below stays sound. */
  def provablyNonEmpty(s: Space): Boolean = sizeBounds(s).lo >= 1
  def provablyHeaded(s: Space): Boolean = sizeBounds(s).loHeaded >= 1

  /** a size interval of [0,0] IS the empty space — the analysis-level Empty propagation
   *  (subsumes chains of syntactic absorptions in one step, e.g. a restriction by a
   *  provably-empty prefix set under a wrap under a union operand). */
  val SizeEmpty = subs(_: Space)(spost = {
    case sp if sp != Space.Empty && sizeBounds(sp).hi == 0 => Space.Empty
  })

  // ---- constant-time emptiness factors --------------------------------------
  /** `{ε}` iff `x` is non-empty, else `∅` — O(one path).  `x ∩ {ε}` covers an ε-only `x`
   *  (Range's slice starts at the smallest path, which may be ε and contribute no head);
   *  the Range(0,1) probe iterates the FIRST path only. */
  def nonEmptyGuard(x: Space): Space =
    Space.Union(Space.Intersection(x, Space.Singleton(Path.ZERO)),
                Space.Iteration(Space.Range(x, 0, 1), PathRef("_").known(1), SpaceMention("_"), Space.Singleton(Path.ZERO)))
  /** `{ε}` iff `x` has ≥1 HEADED path (i.e. an iteration over `x` runs), else `∅` — O(one path).
   *  This is the factor an iteration hoist needs, NOT [[nonEmptyGuard]]: `x == {ε}` is non-empty
   *  but runs zero iterations, so the nonEmpty factor would leak the hoisted branch.  ε sorts
   *  FIRST in the canonical path order, so the LAST path (`Range(x, -1, 0)`) is headed iff any
   *  path is. */
  def headedGuard(x: Space): Space =
    Space.Iteration(Space.Range(x, -1, 0), PathRef("_").known(1), SpaceMention("_"), Space.Singleton(Path.ZERO))

  /** Conservative "every path of `s` is ε", i.e. `s ⊆ {ε}` — true for the guards above and their
   *  compositions.  Lets a guard factor commute with Wrap (see [[EpsGuard_Wrap]]): a ⊆{ε} factor
   *  only selects between `∅` and identity, so it cannot contribute items in front of a prefix. */
  def provablyEpsSubset(s: Space): Boolean = s match
    case Space.Empty => true
    case Space.Singleton(Path.Constant(PathValue(Nil))) => true
    case Space.Literal(SpaceValue(ps)) => ps.forall(_.items.isEmpty)
    case Space.Union(a, b) => provablyEpsSubset(a) && provablyEpsSubset(b)
    case Space.Intersection(a, b) => provablyEpsSubset(a) || provablyEpsSubset(b)
    case Space.Subtraction(a, _) => provablyEpsSubset(a)
    case Space.Restriction(a, _) => provablyEpsSubset(a)
    case Space.Raffination(a, _) => provablyEpsSubset(a)
    case Space.Composition(a, b) => provablyEpsSubset(a) && provablyEpsSubset(b)
    case Space.Range(x, _, _) => provablyEpsSubset(x)
    case Space.Iteration(_, _, _, body) => provablyEpsSubset(body)   // a union of ⊆{ε} bodies stays ⊆ {ε}
    case _ => false

  /** Hoist a loop-INVARIANT union branch OUT of the iteration — the strongest way to whack products:
   *  the invariant branch is computed ONCE instead of once per head, with no re-iteration of src.
   *  The bare hoist `iter(src, l∪r) = l ∪ iter(src, r)` needs the union over heads to be non-empty
   *  (over a headless source iter is ∅, so it would leak l — the old unsoundness, egglog: formal.egg
   *  IterUnion checks).  When src provably has ≥1 head we hoist bare; otherwise we attach the
   *  constant-time [[headedGuard]] factor: `iter(src, l∪r) = (headed(src) · l) ∪ iter(src, r)` —
   *  sound for EVERY src, and the ⊆{ε} factor later commutes/fuses (EpsGuard_Wrap, WrapMerge). */
  val IterUnion_Indep = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if {
      val (soc, poc) = collect(lhs)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () }); soc.isEmpty && poc.isEmpty
    } =>
      val hoisted = if provablyHeaded(src) then lhs else Space.Composition(headedGuard(src), lhs)
      Space.Union(Space.Iteration(src, symbol, rest, rhs), hoisted)
    case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if {
      val (soc, poc) = collect(rhs)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () }); soc.isEmpty && poc.isEmpty
    } =>
      val hoisted = if provablyHeaded(src) then rhs else Space.Composition(headedGuard(src), rhs)
      Space.Union(Space.Iteration(src, symbol, rest, lhs), hoisted)
  })

  /** Hoist a loop-INVARIANT composition factor out of an iteration.  Sound WITHOUT any guard:
   *  composition distributes over the union of iterates (⋃_h (g·s_h) = g·⋃_h s_h), and with zero
   *  iterates both sides are ∅. */
  val IterComposition_Indep = subs(_: Space)(PartialFunction.empty, {
    case Space.Iteration(src, symbol, rest, Space.Composition(g, s)) if {
      val (soc, poc) = collect(g)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () }); soc.isEmpty && poc.isEmpty
    } => Space.Composition(g, Space.Iteration(src, symbol, rest, s))
    case Space.Iteration(src, symbol, rest, Space.Composition(s, g)) if {
      val (soc, poc) = collect(g)({ case Space.Mention(`rest`) => () }, { case Path.Deref(`symbol`) => () }); soc.isEmpty && poc.isEmpty
    } => Space.Composition(Space.Iteration(src, symbol, rest, s), g)
  })

  /** A ⊆{ε} factor commutes into a Wrap: `g · (p × s) = p × (g · s)` when g ⊆ {ε} (g only selects
   *  between ∅ and identity, so it cannot put items in front of the prefix p).  Moves guards out
   *  of the way so common prefixes become adjacent and factorable. */
  val EpsGuard_Wrap = subs(_: Space)(PartialFunction.empty, {
    case Space.Composition(g, Space.Wrap(s, p)) if provablyEpsSubset(g) => Space.Wrap(Space.Composition(g, s), p)
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
    // merge only when FULLY CONSTANT (folds onward to a literal); the deref-bearing cases are the
    // domain of SingletonConstPrefix_Wrap below (the split direction — hoistable constant prefix),
    // and unconditional merge would ping-pong with it
    case Space.Wrap(Space.Singleton(y), x) if constPath(x) && constPath(y) => Space.Singleton(Path.Concat(x, y))
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

  // ================================================================================================
  // INVERSE-INDEX SEMIJOIN (iter-transpose-semijoin).
  //
  // A (rest-chained) k-nested iteration binding single-item symbols z1..zk whose innermost body is
  // STRICT in a witness unwrap  Unwrap(E, z1·…·zk·c)  — E constant-rooted (loop-invariant) and c
  // of statically-known item length — evaluates a body frame for EVERY source group and lets the
  // witness veto it.  This law makes the loop OUTPUT-SENSITIVE: it materializes the (k,ℓ)-
  // TRANSPOSE index of E (loop-invariant, so CSE/push-out hoist and evaluate it once),
  //     TR = { w1…wℓ·u1…uk | u1…uk·w1…wℓ is a (k+ℓ)-item prefix of an E-path },
  // takes the candidate set  P = Unwrap(TR, c) = { z⃗ | z⃗·c prefixes an E-path }, and narrows the
  // iteration source to  Restriction(S, P).
  //
  // UNCONDITIONALLY SOUND, with no shape assumptions on S or E: a dropped group's witness is ∅ and
  // the body is strict in it, so the group contributed ∅; a kept group keeps its ENTIRE subtree
  // (P's elements are exactly k items, so the prefix restriction cannot split a group's tails);
  // E-paths deeper than k+ℓ are still indexed by their prefix (the transpose nest binds prefix
  // groups), and shorter ones can never satisfy the witness.  Certificates:
  // proofs/laws/law_iter_transpose_semijoin.smt2 + proofs/laws/law_transpose_spec.smt2 (k=ℓ=1
  // instances; k,ℓ>1 repeat the same level-wise argument — SCHEMATIC in the registry).
  // ================================================================================================
  /** does the term contain any generated name with this reserved prefix?  The semijoin guards
   *  are SHAPE-based, not value-based: the other laws keep rewriting a freshly-planted narrower
   *  (splitting its unwraps, fusing its concats), so an equality guard re-fires forever — but the
   *  generated tj/hn-prefixed binder names survive every rewrite. */
  private def hasGenTag(s: Space, tag: String): Boolean =
    var found = false
    subs(s)(spre = { case it @ Space.Iteration(_, sy, re, _) if sy.s.startsWith(tag) || re.s.startsWith(tag) =>
                       found = true; it },
            ppre = { case d @ Path.Deref(pr) if pr.s.startsWith(tag) => found = true; d })
    found

  private def unwrapSpine(s: Space): (Space, List[Path]) = s match
    case Space.Unwrap(inner, q) => val (b, qs) = unwrapSpine(inner); (b, qs :+ q)
    case other => (other, Nil)

  /** statically-known ITEM length of a path expression (constants; single-item binders). */
  private[morkl] def pathItemLen(p: Path): Option[Int] = p match
    case Path.Constant(pv) => Some(pv.items.length)
    case Path.Deref(pr) if pr.lengthHint == 1 => Some(1)
    case Path.Concat(l, r) => for a <- pathItemLen(l); b <- pathItemLen(r) yield a + b
    case _ => None

  private def cleanSpace(sp: Space, prs: Set[String], sms: Set[String]): Boolean =
    val (so, po) = collect(sp)({ case Space.Mention(m) if sms(m.s) => () },
                              { case Path.Deref(pr) if prs(pr.s) => () })
    so.isEmpty && po.isEmpty
  private def cleanPath(p: Path, prs: Set[String], sms: Set[String]): Boolean =
    cleanSpace(Space.Singleton(p), prs, sms)
  private[morkl] def constPath(p: Path): Boolean = p match
    case Path.Constant(_) => true
    case Path.Concat(l, r) => constPath(l) && constPath(r)
    case _ => false

  /** find, in a STRICT position of `body` (∅ there forces the whole body result to ∅), an unwrap
   *  spine base·pre·(Deref z1)…(Deref zk)·post with base a foreign mention and pre CONSTANT (so E
   *  hoists above z1, and the law only fires at the OUTERMOST nest level — an inner level would
   *  see outer binders in pre).  Returns (E, cs): E = base unwrapped by pre; cs = the longest
   *  clean, statically-sized prefix of post (a shorter c only narrows less — still sound). */
  private def findWitness(body: Space, zs: Vector[String], sms: Set[String]): Option[(Space, List[Path])] =
    val zset = zs.toSet
    def trySpine(x: Space): Option[(Space, List[Path])] =
      val (base, qs) = unwrapSpine(x)
      if qs.isEmpty then None
      else
        val idx = qs.indexWhere { case Path.Deref(pr) => pr.s == zs.head; case _ => false }
        if idx < 0 then None
        else
          val run = qs.slice(idx, idx + zs.length)
          val runOk = run.length == zs.length &&
            run.zip(zs).forall { case (Path.Deref(pr), n) => pr.s == n; case _ => false }
          val pre = qs.take(idx)
          val post = qs.drop(idx + zs.length)
          if !runOk || !pre.forall(constPath) then None
          else base match
            case Space.Mention(m) if !sms(m.s) =>
              val cs = post.takeWhile(p => cleanPath(p, zset, sms) && pathItemLen(p).isDefined)
              if cs.isEmpty then None else Some((pre.foldLeft(base)(Space.Unwrap.apply), cs))
            case _ => None
    def search(s: Space): Option[(Space, List[Path])] = s match
      case u: Space.Unwrap => trySpine(u)
      case Space.Composition(a, b) => search(a).orElse(search(b))
      case Space.Intersection(a, b) => search(a).orElse(search(b))
      case Space.Subtraction(a, _) => search(a)
      case Space.Restriction(a, b) => search(a).orElse(search(b))
      case Space.Raffination(a, _) => search(a)
      case Space.Wrap(src, _) => search(src)
      case Space.TailsUnion(src) => search(src)
      case Space.TailsIntersection(src) => search(src)
      case Space.Iteration(src, _, _, _) => search(src)   // iteration of an ∅ source is ∅ (strict)
      case _ => None
    search(body)

  private def transposeSemiJoinRewrite(it: Space): Option[Space] = it match
    case Space.Iteration(src0, z1, m1, b1) if z1.lengthHint == 1 =>
      // peel the rest-chained nest (up to 3 single-item levels)
      def peel(zsAcc: Vector[PathRef], msAcc: Vector[SpaceMention], b: Space): (Vector[PathRef], Vector[SpaceMention], Space) = b match
        case Space.Iteration(Space.Mention(sm), z, m, bi) if sm == msAcc.last && z.lengthHint == 1 && zsAcc.length < 3 =>
          peel(zsAcc :+ z, msAcc :+ m, bi)
        case _ => (zsAcc, msAcc, b)
      val (zs, ms, innerBody) = peel(Vector(z1), Vector(m1), b1)
      val smNames = ms.map(_.s).toSet
      findWitness(innerBody, zs.map(_.s), smNames).flatMap { (e, cs) =>
        val k = zs.length
        val lw = cs.map(pathItemLen(_).get).sum
        val tag = s"tj${Integer.toHexString(e.hashCode ^ (k * 31 + lw))}"
        val us = Vector.tabulate(k)(i => PathRef(s"${tag}u$i").known(1))
        val ws = Vector.tabulate(lw)(i => PathRef(s"${tag}w$i").known(1))
        val binders = us ++ ws
        val rests = Vector.tabulate(binders.length)(i => SpaceMention(s"${tag}r$i"))
        val trBodyPath = (ws.map(Path.Deref(_): Path) ++ us.map(Path.Deref(_): Path)).reduceRight(Path.Concat.apply)
        val tr = binders.zip(rests).zipWithIndex.foldRight(Space.Singleton(trBodyPath): Space) {
          case (((bnd, rst), i), acc) =>
            val srcI: Space = if i == 0 then e else Space.Mention(rests(i - 1))
            Space.Iteration(srcI, bnd, rst, acc)
        }
        val c = cs.reduceRight(Path.Concat.apply)
        val p = Space.Unwrap(tr, c)
        // guard on the WHOLE Restriction chain AND by generated-name tag: the other laws keep
        // rewriting a planted narrower (unwrap splits, concat fusion), so value equality would
        // re-fire forever; one transpose narrowing per node is the fixpoint
        if hasGenTag(src0, "tj") then None
        else Some(Space.Iteration(Space.Restriction(src0, p), z1, m1, b1))
      }
    case _ => None

  val IterWitness_TransposeSemiJoin = subs(_: Space)(spre = {
    case it: Space.Iteration if transposeSemiJoinRewrite(it).isDefined => transposeSemiJoinRewrite(it).get
  })

  // ================================================================================================
  // LEVEL-WISE HEAD SEMIJOIN (iter-witness-head-narrow) — NEST-TOP FORM.
  //
  // A rest-chained nest binding z1..zk whose innermost body is STRICT in a witness unwrap
  //     Unwrap(E, z1·…·zk)            (the binder run is the SUFFIX of the spine)
  // with E clean of the nest's own binders — and GENUINELY VARYING (containing at least one
  // Deref: an outer binder or a parameter; a fully-constant E has a static, typically dense head
  // set whose narrowing costs a head-iteration per frame and prunes nothing) — evaluates a leaf
  // frame for every source group and lets the witness veto it.  Narrow EVERY level i to
  //     Restriction(src_i, Head(E·z1·…·z_{i-1}))
  // (Head as the canonical head-iteration).  Unconditionally sound per level (certificate:
  // proofs/laws/law_iter_head_narrow.smt2 — dropped groups have an ∅ witness and the body is
  // strict in it; kept groups keep whole subtrees); the DEEPEST level's narrowing is exact, so
  // leaf frames run only for witness-passing groups.  When an invariant statically-sized suffix
  // follows the run, iter-transpose-semijoin narrows exactly instead and this law defers.
  // ================================================================================================
  private def headEnc(e: Space): Space =
    val tag = s"hn${Integer.toHexString(e.hashCode)}"
    val hw = PathRef(s"${tag}h").known(1)
    Space.Iteration(e, hw, SpaceMention(s"${tag}r"), Space.Singleton(Path.Deref(hw)))

  /** find, in a STRICT position of `body`, an unwrap spine base·pre·(Deref z1)…(Deref zk)·post
   *  with base a foreign mention, pre clean of the nest (outer binders allowed) and containing a
   *  Deref (the varying-witness profitability condition), and post NOT an invariant sized suffix
   *  (that case belongs to the transpose law).  Returns E = base unwrapped by pre. */
  private def findHeadNestWitness(body: Space, zs: Vector[String], sms: Set[String]): Option[Space] =
    val zset = zs.toSet
    def trySpine(x: Space): Option[Space] =
      val (base, qs) = unwrapSpine(x)
      val idx = qs.indexWhere { case Path.Deref(pr) => pr.s == zs.head; case _ => false }
      if idx < 0 then None
      else
        val run = qs.slice(idx, idx + zs.length)
        val runOk = run.length == zs.length &&
          run.zip(zs).forall { case (Path.Deref(pr), n) => pr.s == n; case _ => false }
        val pre = qs.take(idx)
        val post = qs.drop(idx + zs.length)
        val hasSuffix = post.headOption.exists(p => cleanPath(p, zset, sms) && pathItemLen(p).isDefined)
        val varies = pre.exists(!constPath(_))
        base match
          case Space.Mention(m) if runOk && !sms(m.s) && !hasSuffix && varies &&
               pre.forall(cleanPath(_, zset, sms)) =>
            Some(pre.foldLeft(base: Space)(Space.Unwrap.apply))
          case _ => None
    def search(s: Space): Option[Space] = s match
      case u: Space.Unwrap => trySpine(u)
      case Space.Composition(a, b) => search(a).orElse(search(b))
      case Space.Intersection(a, b) => search(a).orElse(search(b))
      case Space.Subtraction(a, _) => search(a)
      case Space.Restriction(a, b) => search(a).orElse(search(b))
      case Space.Raffination(a, _) => search(a)
      case Space.Wrap(src, _) => search(src)
      case Space.TailsUnion(src) => search(src)
      case Space.TailsIntersection(src) => search(src)
      case Space.Iteration(src, _, _, _) => search(src)   // iteration of an ∅ source is ∅ (strict)
      case _ => None
    search(body)

  private def headNarrowRewrite(it: Space): Option[Space] = it match
    case Space.Iteration(src0, z1, m1, b1) if z1.lengthHint == 1 &&
         !hasGenTag(src0, "hn") =>
      def peel(zsAcc: Vector[PathRef], msAcc: Vector[SpaceMention], b: Space): (Vector[PathRef], Vector[SpaceMention], Space) = b match
        case Space.Iteration(Space.Mention(sm), z, m, bi) if sm == msAcc.last && z.lengthHint == 1 && zsAcc.length < 3 =>
          peel(zsAcc :+ z, msAcc :+ m, bi)
        case _ => (zsAcc, msAcc, b)
      val (zs, ms, innerBody) = peel(Vector(z1), Vector(m1), b1)
      findHeadNestWitness(innerBody, zs.map(_.s), ms.map(_.s).toSet).map { e =>
        def chainE(i: Int): Space = zs.take(i).foldLeft(e)((acc, z) => Space.Unwrap(acc, Path.Deref(z)))
        def rebuild(i: Int): Space =
          val orig: Space = if i == 0 then src0 else Space.Mention(ms(i - 1))
          val src = Space.Restriction(orig, headEnc(chainE(i)))
          Space.Iteration(src, zs(i), ms(i), if i == zs.length - 1 then innerBody else rebuild(i + 1))
        rebuild(0)
      }
    case _ => None

  val IterWitness_HeadNarrow = subs(_: Space)(spre = {
    case it: Space.Iteration if headNarrowRewrite(it).isDefined => headNarrowRewrite(it).get
  })

  // ================================================================================================
  // MINED COMPOSITION LAWS (scripts/mine_laws.py): every candidate stated denotationally and
  // adjudicated by the provers — 18 PROVED, 4 REFUTED with machine-verified countermodels
  // (proofs/laws/MINED.tsv).  The profitable PROVED ones below; certificates in proofs/laws/.
  // ================================================================================================

  /** unwrap pushed through the set operations (certificate: laws/law_unwrap_push.smt2) —
   *  membership at w·p distributes pointwise; pushing exposes deeper Wrap/literal reductions. */
  val UnwrapPush = subs(_: Space)(spost = {
    case Space.Unwrap(Space.Union(a, b), w) => Space.Union(Space.Unwrap(a, w), Space.Unwrap(b, w))
    case Space.Unwrap(Space.Intersection(a, b), w) => Space.Intersection(Space.Unwrap(a, w), Space.Unwrap(b, w))
    case Space.Unwrap(Space.Subtraction(a, b), w) => Space.Subtraction(Space.Unwrap(a, w), Space.Unwrap(b, w))
  })

  private def incomparableConsts(p: Path, q: Path): Boolean = (p, q) match
    case (Path.Constant(a), Path.Constant(b)) =>
      a.items.nonEmpty && b.items.nonEmpty && a.items.head != b.items.head   // certified form: heads differ
    case _ => false

  /** set operations over equal-prefix wraps merge under the wrap (subsuming the common-prefix
   *  union factoring `(p×a) ∪ (p×b) = p×(a∪b)`); incomparable constant prefixes are disjoint
   *  cylinders (certificates: laws/law_wrap_merge.smt2, laws/law_wrap_disjoint.smt2). */
  val WrapMerge = subs(_: Space)(spost = {
    case Space.Union(Space.Wrap(a, p), Space.Wrap(b, q)) if p == q => Space.Wrap(Space.Union(a, b), p)
    case Space.Intersection(Space.Wrap(a, p), Space.Wrap(b, q)) if p == q => Space.Wrap(Space.Intersection(a, b), p)
    case Space.Subtraction(Space.Wrap(a, p), Space.Wrap(b, q)) if p == q => Space.Wrap(Space.Subtraction(a, b), p)
    case Space.Intersection(Space.Wrap(_, p), Space.Wrap(_, q)) if incomparableConsts(p, q) => Space.Empty
    case Space.Subtraction(w1 @ Space.Wrap(_, p), Space.Wrap(_, q)) if incomparableConsts(p, q) => w1
  })

  /** restriction pushed through the subject's set operations, and split over a union of prefix
   *  sets (certificate: laws/law_restrict_push.smt2).  The ∩/\ forms restrict ONE side only. */
  val RestrictionPush = subs(_: Space)(spost = {
    case Space.Restriction(Space.Union(a, b), pr) => Space.Union(Space.Restriction(a, pr), Space.Restriction(b, pr))
    case Space.Restriction(Space.Intersection(a, b), pr) => Space.Intersection(Space.Restriction(a, pr), b)
    case Space.Restriction(Space.Subtraction(a, b), pr) => Space.Subtraction(Space.Restriction(a, pr), b)
    case Space.Restriction(a, Space.Union(p1, p2)) => Space.Union(Space.Restriction(a, p1), Space.Restriction(a, p2))
  })

  /** a left wrap slides out of a composition: Wrap(w,a)·b = Wrap(w, a·b)
   *  (certificate: laws/law_comp_wrap_assoc.smt2 — wrap-as-composition + associativity). */
  val CompWrapAssoc = subs(_: Space)(spost = {
    case Space.Composition(Space.Wrap(a, w), b) => Space.Wrap(Space.Composition(a, b), w)
  })

  /** composition canonicalizes RIGHT-associated (certificate: laws/law_comp_assoc.smt2), exposing
   *  left factors to CompWrapAssoc / CompLitWraps; strictly reduces left-spine depth. */
  val CompAssocRight = subs(_: Space)(spost = {
    case Space.Composition(Space.Composition(a, b), c) => Space.Composition(a, Space.Composition(b, c))
  })

  /** a SMALL literal on the left of a composition becomes a union of wraps — compositions traded
   *  for unions (certificate: laws/law_comp_lit_wraps.smt2 for the 2-path instance; n<=4 is the
   *  same argument via comp-over-union-left + wrap-as-comp, level-wise).  Bounded to avoid blowup. */
  val CompLitWraps = subs(_: Space)(spost = {
    case Space.Composition(Space.Literal(v), b) if v.paths.nonEmpty && v.paths.size <= 4 =>
      v.paths.toList.sortBy(_.show).map(pv => Space.Wrap(b, Path.Constant(pv)): Space).reduceLeft(Space.Union.apply)
  })

  private def pathFactors(p: Path): List[Path] = p match
    case Path.Concat(l, r) => pathFactors(l) ++ pathFactors(r)
    case other => List(other)
  private def refactor(fs: List[Path]): Path = fs.reduceRight(Path.Concat.apply)

  /** a singleton whose path has a CONSTANT PREFIX followed by deref-bearing factors splits into
   *  Wrap(Singleton(varying), constPrefix) — the constant-prefix wrap is loop-invariant and
   *  hoistable (Wrap_Iter / WrapMerge / graph push_out); the merge direction is gated to fully-
   *  constant paths so the pair cannot ping-pong.  Certificate: laws/law_wrap_set.smt2
   *  (the singleton-fusion case, read right-to-left). */
  val SingletonConstPrefix_Wrap = subs(_: Space)(spost = {
    case Space.Singleton(p @ Path.Concat(_, _))
        if { val fs = pathFactors(p); fs.head.isInstanceOf[Path.Constant] && fs.exists(f => !constPath(f)) } =>
      val fs = pathFactors(p)
      val (cs, rest) = fs.span(constPath)
      val prefix = Path.Constant(PathValue(cs.flatMap { case Path.Constant(v) => v.items; case _ => Nil }))
      Space.Wrap(Space.Singleton(refactor(rest)), prefix)
  })

  /** an iteration-invariant RIGHT composition factor hoists out of the iteration's union of
   *  groups: ∪_h (B_h · c) = (∪_h B_h) · c  (certificate: laws/law_iter_comp_right_hoist.smt2).
   *  Subsumed by [[IterComposition_Indep]] in the default pipeline; kept as the certified name
   *  the supercompiler's reducer registers. */
  val IterCompRight_Hoist = subs(_: Space)(spost = {
    case Space.Iteration(src, h, r, Space.Composition(b, cc))
        if cleanSpace(cc, Set(h.s), Set(r.s)) =>
      Space.Composition(Space.Iteration(src, h, r, b), cc)
  })

  /** raffination pushed through the subject's set operations and split over prefix unions —
   *  raffination is POINTWISE (x∧¬pref), so it distributes exactly like restriction
   *  (certificate: laws/law_raff_push.smt2). */
  val RaffinationPush = subs(_: Space)(spost = {
    case Space.Raffination(Space.Union(a, b), pr) => Space.Union(Space.Raffination(a, pr), Space.Raffination(b, pr))
    case Space.Raffination(Space.Intersection(a, b), pr) => Space.Intersection(Space.Raffination(a, pr), b)
    case Space.Raffination(Space.Subtraction(a, b), pr) => Space.Subtraction(Space.Raffination(a, pr), b)
    case Space.Raffination(a, Space.Union(p1, p2)) => Space.Raffination(Space.Raffination(a, p1), p2)
  })

  /** the raffination/restriction PARTITION collapses: opposite composition annihilates, repeated
   *  application is idempotent, and the two halves reunite to the subject
   *  (certificate: laws/law_raff_restrict_algebra.smt2). */
  val RaffRestrictAlgebra = subs(_: Space)(spost = {
    case Space.Restriction(Space.Raffination(x, y), y2) if y == y2 => Space.Empty
    case Space.Raffination(Space.Restriction(x, y), y2) if y == y2 => Space.Empty
    case Space.Raffination(r @ Space.Raffination(x, y), y2) if y == y2 => r
    case Space.Restriction(r @ Space.Restriction(x, y), y2) if y == y2 => r
    case Space.Union(Space.Raffination(x, y), Space.Restriction(x2, y2)) if x == x2 && y == y2 => x
    case Space.Union(Space.Restriction(x, y), Space.Raffination(x2, y2)) if x == x2 && y == y2 => x
  })

  /** restriction and raffination under a COMMON wrap prefix descend below it
   *  (certificates: laws/law_restrict_wrap_both.smt2, laws/law_raff_wrap_both.smt2). */
  val RestrictRaffWrapBoth = subs(_: Space)(spost = {
    case Space.Restriction(Space.Wrap(a, w), Space.Wrap(pr, w2)) if w == w2 =>
      Space.Wrap(Space.Restriction(a, pr), w)
    case Space.Raffination(Space.Wrap(a, w), Space.Wrap(pr, w2)) if w == w2 =>
      Space.Wrap(Space.Raffination(a, pr), w)
  })

  /** is the body's output GUARANTEED to start with the group key h?  (The "independent" guard:
   *  keyed bodies make groups pairwise DISJOINT across keys, licensing ∩/\ to move through
   *  same-source iterations.)  Syntactic under-approximation, sound by construction. */
  private def keyedBy(b: Space, h: PathRef): Boolean =
    def headIsH(p: Path): Boolean = pathFactors(p).headOption match
      case Some(Path.Deref(pr)) => pr.s == h.s
      case _ => false
    b match
      case Space.Wrap(_, p) => headIsH(p)
      case Space.Singleton(p) => headIsH(p)
      case Space.Union(x, y) => keyedBy(x, h) && keyedBy(y, h)
      case Space.Composition(Space.Singleton(p), _) => headIsH(p)
      case _ => false

  /** n-ary UNION CHAINS re-associate/commute NATIVELY through the engine: ∪ᵢAᵢ =
   *  TailsUnion(⋃ᵢ ~uᵢ~·Aᵢ) with distinct synthetic constant tags — NO new construct, so every
   *  law/optimization applies wherever the pattern lands; the executor's TailsUnion then merges
   *  the branches BALANCED with empty branches filtered (ITrie.joinAll), instead of a left-nested
   *  pairwise chain that re-walks its growing accumulator.  Fires on chains of ≥ 4 operands not
   *  already tagged.  CERTIFIED BUT NOT IN THE DEFAULT PIPELINE: measured on the workload
   *  profiles, the per-evaluation tag-wrap + strip overhead EXCEEDS the balanced-merge gain at
   *  the applications' branch sizes (puzzle15 2136->2954 ticks, gol 10204->12539) — it pays only
   *  for large overlapping branches, so it is available for explicit use, not default.  (The ∩
   *  analogue needs a sentinel construction — ⋃ᵢtᵢ·(Aᵢ∪{σ}) then \{σ}, else an EMPTY operand
   *  silently drops out of the meet; its head-group lemmas prove but the final tails-∩ goal
   *  resists both provers and NO ≥3-ary ∩ chain occurs in the applications, so it stays a
   *  documented design, not a rewrite.)
   *  Certificate: laws/law_union_chain_tailsu.smt2 (3-ary; n-ary is the same argument per tag). */
  private def unionOps(s: Space): List[Space] = s match
    case Space.Union(a, b) => unionOps(a) ++ unionOps(b)
    case other => List(other)
  private def isUTag(s: Space): Boolean = s match
    case Space.Wrap(_, Path.Constant(PathValue(n :: Nil))) => n.startsWith("~u")
    case _ => false
  val UnionChain_TailsU = subs(_: Space)(spost = {
    case u: Space.Union if { val ops = unionOps(u); ops.length >= 4 && !ops.exists(isUTag) } =>
      val ops = unionOps(u)
      Space.TailsUnion(ops.zipWithIndex.map((a, i) =>
        Space.Wrap(a, Path.Constant(PathValue(List(s"~u$i~")))): Space).reduceLeft(Space.Union.apply))
  })

  /** SAME-SOURCE iteration merges.  ∪ merges FREELY (certificate: laws/law_iter_merge.smt2, the
   *  union conjunct) — gated away from loop-INVARIANT bodies, which belong to IterUnion_Indep's
   *  hoist (the two would ping-pong).  ∩ and \ merge only under the KEYED guard on both bodies
   *  (same certificate, keyed conjuncts; the unguarded ∩ is REFUTED — countermodel in the law
   *  mining log — so the guard is necessary, not defensive). */
  val IterSetOpMerge = subs(_: Space)(spost = {
    case Space.Union(Space.Iteration(s1, h1, r1, b1), Space.Iteration(s2, h2, r2, b2))
        if s1 == s2 && h1.s == h2.s && r1.s == r2.s &&
           !cleanSpace(b1, Set(h1.s), Set(r1.s)) && !cleanSpace(b2, Set(h1.s), Set(r1.s)) =>
      Space.Iteration(s1, h1, r1, Space.Union(b1, b2))
    case Space.Intersection(Space.Iteration(s1, h1, r1, b1), Space.Iteration(s2, h2, r2, b2))
        if s1 == s2 && h1.s == h2.s && r1.s == r2.s && keyedBy(b1, h1) && keyedBy(b2, h1) =>
      Space.Iteration(s1, h1, r1, Space.Intersection(b1, b2))
    case Space.Subtraction(Space.Iteration(s1, h1, r1, b1), Space.Iteration(s2, h2, r2, b2))
        if s1 == s2 && h1.s == h2.s && r1.s == r2.s && keyedBy(b1, h1) && keyedBy(b2, h1) =>
      Space.Iteration(s1, h1, r1, Space.Subtraction(b1, b2))
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
    case Path.Deref(pr) => PathValue(("$" + pr.s)::Nil)
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
    case Space.Mention(sm) => Set(PathValue(("$" + sm.s)::Nil))
    case Space.Singleton(p) => Set(recp(p))
    case Space.Literal(sv) => Set.empty
    case Space.Union(x, y) => recs(x) union recs(y)
//    case Space.Intersection(x, y) => recs(x) union recs(y)
    case Space.Intersection(x, y) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue("$_"::Nil))),
                                                      Space.Literal(SpaceValue(recs(y))) x Space.Singleton(Path.Constant(PathValue("$_"::Nil))))).paths
    case Space.Subtraction(x, y) => recs(x) union recs(y)
//    case Space.Restriction(x, prefixes) => recs(x) union recs(prefixes)
    case Space.Restriction(x, prefixes) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue("$_"::Nil))),
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
      val sv = PathValue(("$" + symbol.s)::Nil)
      val sr = PathValue(("$" + rest.s)::Nil)
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
    case Path.Deref(pr) => PathValue(("$" + pr.s)::Nil)
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
    case Space.Mention(sm) => Set(PathValue(("$" + sm.s)::Nil))
    case Space.Singleton(p) => Set(recp(p))
    case Space.Literal(sv) => Set.empty
    case Space.Union(x, y) => recs(x) union recs(y)
//    case Space.Intersection(x, y) => recs(x) union recs(y)
    case Space.Intersection(x, y) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue("$_"::Nil))),
                                                      Space.Literal(SpaceValue(recs(y))) x Space.Singleton(Path.Constant(PathValue("$_"::Nil))))).paths
    case Space.Subtraction(x, y) => recs(x) union recs(y)
//    case Space.Restriction(x, prefixes) => recs(x) union recs(prefixes)
    case Space.Restriction(x, prefixes) => eval(Space.Union(Space.Literal(SpaceValue(recs(x))) x Space.Singleton(Path.Constant(PathValue("$_"::Nil))),
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
  import Path.*
  given parse: Conversion[String, PathValue] = s => PathValue(s.split('.').toList)
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
      Space.Fold(x, initial, PathRef(acc), PathRef(symbol).known(1), SpaceMention(rest), rhs, update)
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
