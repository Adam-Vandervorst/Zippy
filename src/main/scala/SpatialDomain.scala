package morkl

import scala.collection.immutable.SortedMap
import scala.collection.mutable
import Lower.LenBounds

/** ==================================================================================================
 *  THE TWO-TIER CORRELATED SPATIAL DOMAIN.
 *
 *  ==WHAT IT REPLACES==
 *  The cost analysis used to project every operand to independent scalars — a size interval, a length
 *  interval, a head count — before pricing an operation, and the relationships that decide operational
 *  cost (which keys two operands share, how many DISTINCT objects an n-ary operation sees, whether a
 *  result IS an operand, where a path sits in the order, how many paths lie under one prefix) were gone
 *  by the time a transfer ran.  `puzzle15`'s astronomical bound was that loss compounding over fifteen
 *  compositions (build.log, 1B.5).
 *
 *  ==THE CARRIER: ONE HASH-CONSED DAG, TWO TIERS==
 *  An abstract value is a node of a per-analysis [[Arena]]:
 *
 *    [[XTrie]]   (terminal, children)  — an EXACT trie node: ε is present iff `terminal`, the head set
 *                is exactly `children.keys`, and the tail set under `k` is described by `children(k)`;
 *    [[XChoice]] (alternatives)        — FINITELY MANY ALTERNATIVES for the subtrie at this prefix
 *                (a BDD-like decision node: the decision is which alternative, taken independently at
 *                each prefix where a choice appears);
 *    [[XSumm]]   (SpatialType)          — the SUMMARIZED tier: the existing reduced product of the
 *                bounded shape and the length histogram, with its own certified transfers.
 *
 *  The EXACT tier is everything above the first `XSumm`; the SUMMARIZED tier is `XSumm` alone.  Both
 *  live in one structure so that a value can be exact where the analysis can afford it and summarized
 *  below — "a deliberate composition of the two" — and so that prefix disjointness and order extrema
 *  decided in the exact tier are never lost to the shape domain's depth and width caps (`Shape.MaxDepth`,
 *  `Shape.MaxHeads` never apply above an `XSumm`).
 *
 *  Nodes are HASH-CONSED per arena: structurally equal nodes are one object, a shared subtrie is one
 *  node, and comparison inside an analysis is a pointer test.  Identity is a VALUE: [[XNode.key]] is
 *  the structural fingerprint, `equals`/`hashCode` are structural, and two analyses in one JVM (or in
 *  two) produce equal values — arena ids never leave the arena.  Nothing is process-wide.
 *
 *  ==γ, ORDER, JOIN, MEET, PROJECTION, WIDENING== — [[Domain]] below, both tiers:
 *    γ(XTrie)   = { V : ε∈V ⇔ terminal, heads V = keys, ∀k. tails_k V ∈ γ(children k) }
 *    γ(XChoice) = ⋃ γ(alternative)             γ(XSumm t) = the product γ (`SpatialTyping.accepts`)
 *    ⊑          = γ-inclusion, decided structurally (exact ⊑ exact), by `SpatialType.leq` (summ ⊑ summ),
 *                 through the projection (exact ⊑ summ); never the other way (sound, incomplete)
 *    ⊔          = the choice of the two when it fits the ALTERNATIVES BUDGET, else the projection's lub
 *                 (a WIDENING, named `alternatives-budget`)
 *    ⊓          = exact ⊓ exact structurally (a disagreement on ε, a head set or a child is ⊥);
 *                 exact ⊓ summ filters the enumerable alternatives by γ (or keeps the exact operand);
 *                 summ ⊓ summ is `SpatialType.meet`
 *    projection = [[Domain.summary]]: the exact tier through the CERTIFIED summarized transfers (a trie
 *                 node is `ε ∪ ⋃ k·child`, so `Wrap`/`Union`'s own transfers build it), memoised
 *    widening   = [[Domain.widen]]: join, then `SpatialRecursion.widenType` past the budget (named
 *                 `iteration-widening`)
 *
 *  ==CORRELATIONS THE TRANSFERS MAY READ== ([[DomainFacts]])
 *  cardinality and length per prefix (fibres), the exact head set and per-prefix fan-out, order
 *  extrema (`Range(x,0,1)` / `Range(x,-1,0)` are exact on the exact tier and `Shape.orderMin/Max` on the
 *  summarized one), disjointness of two head sets, DISTINCT LIVE OPERANDS of an n-ary operation
 *  (must/may), MUST/MAY ALIASING of two operands (the alias channel: an abstract value that IS the
 *  object bound to an input mention says so, and an operation whose result is an operand by the
 *  executors' identity cases propagates it — PROVEN REUSE), and pointer-preserving sharing (a shared
 *  subtrie is one node).
 *
 *  ==EVERY LOSS OF PRECISION IS IN THE CERTIFICATE==
 *  A budget crossing returns a named [[Widening]] with the before and after facts; it may lose
 *  precision but may not change a must fact or a growth class — the after value is always ⊒ the before
 *  value (checked at the crossing).  [[Domain.certificate]] is the immutable record: the widenings, the
 *  budget, and nothing that depends on process history.
 *
 *  ==PROVENANCE== ([[Cause]])  every node records how it arose — an input, an operation over operand
 *  nodes, an alternative of a join, a round of a fixpoint, a widening — so the same DAG serves the
 *  denotational reading (γ) and the resource reading (what was computed from what) without conflating
 *  them: a node's meaning is its structure; its cause is a separate table indexed by the node.
 *
 *  ==NO EVALUATION==  nothing here calls an executor.  The exact tier is a symbolic value; where it is
 *  a single concrete trie it is because the term was closed, and that is derivation, not evaluation.
 *  ================================================================================================== */

// ==================================================================================================
// THE CARRIER
// ==================================================================================================

/** how a node arose — the operational provenance DAG, indexed by the node */
enum Cause:
  case Input(mention: SpaceMention)
  case Literal
  case Op(kind: String, operands: Vector[Int])
  case Alternative(of: Vector[Int])
  case Round(system: String, round: Int, from: Int)
  case Widened(reason: String, from: Vector[Int])
  case Summarised(from: Int)
  def show: String = this match
    case Input(m) => s"input ${m.s}"
    case Literal => "literal"
    case Op(k, os) => s"$k(${os.mkString(",")})"
    case Alternative(of) => s"alt{${of.mkString(",")}}"
    case Round(sy, n, from) => s"round $n of $sy from #$from"
    case Widened(r, from) => s"widened[$r] from ${from.mkString(",")}"
    case Summarised(from) => s"summarised #$from"

sealed trait XNode:
  /** arena-local, never part of equality */
  def id: Int
  /** THE STRUCTURAL FINGERPRINT — identity as a value */
  def key: XNode.Key
  override def hashCode: Int = key.hashCode
  override def equals(o: Any): Boolean = o match
    case n: XNode => (this eq n) || key == n.key
    case _ => false
  def show: String

object XNode:
  /** the structural key: a nested value with no ids in it */
  sealed trait Key
  final case class TrieKey(terminal: Boolean, children: Vector[(PathItem, Key)]) extends Key
  final case class ChoiceKey(alts: Vector[Key]) extends Key
  final case class SummKey(t: SpatialType) extends Key

/** an exact trie node */
final class XTrie(val id: Int, val terminal: Boolean, val children: SortedMap[PathItem, XNode]) extends XNode:
  val key: XNode.Key = XNode.TrieKey(terminal, children.iterator.map((k, c) => k -> c.key).toVector)
  def isEmptyNode: Boolean = !terminal && children.isEmpty
  def show: String =
    if isEmptyNode then "∅" else
      (if terminal then "ε" else "") + children.iterator.map((k, c) => s"${k}·${c.show}").mkString("{", ",", "}")

/** finitely many alternatives for the subtrie at this prefix */
final class XChoice(val id: Int, val alts: Vector[XNode]) extends XNode:
  val key: XNode.Key = XNode.ChoiceKey(alts.map(_.key).sortBy(_.hashCode))
  def show: String = alts.map(_.show).mkString("⟨", " | ", "⟩")

/** the summarized tier */
final class XSumm(val id: Int, val t: SpatialType) extends XNode:
  val key: XNode.Key = XNode.SummKey(t)
  def show: String = s"≈${t.show}"

/** THE ALIAS CHANNEL: which object an abstract value denotes, when that is known */
enum Alias:
  /** the value IS the object bound to this input mention (by pointer) */
  case Is(m: SpaceMention)
  /** a fresh object of this analysis' making (an operation that built a node) */
  case Fresh
  /** nothing is known about which object it is */
  case Unknown
  def show: String = this match
    case Is(m) => s"=${m.s}"
    case Fresh => "fresh"
    case Unknown => "?"

/** an abstract value: a node and its alias channel */
final case class Abs(node: XNode, alias: Alias = Alias.Unknown):
  def show: String = node.show + (if alias == Alias.Unknown then "" else s"[${alias.show}]")

/** one named loss of precision, with the facts before and after */
final case class Widening(reason: String, before: String, after: String, beforeSize: Ivl, afterSize: Ivl,
                          beforeLen: LenBounds, afterLen: LenBounds):
  def show: String = s"$reason: $before → $after  (size ${beforeSize.show}→${afterSize.show}, len [${beforeLen.lo},${beforeLen.hi}]→[${afterLen.lo},${afterLen.hi}])"

/** the budgets a domain instance runs under */
final case class DomainBudget(alternatives: Int = 16, depth: Int = 64, enumerate: Int = 512)

/** THE IMMUTABLE CERTIFICATE of one analysis: every widening, the budget it ran under */
final case class DomainCert(budget: DomainBudget, widenings: Vector[Widening]):
  def exact: Boolean = widenings.isEmpty
  def show: String =
    if widenings.isEmpty then s"exact (no widening; budget $budget)"
    else s"${widenings.length} widening(s) under $budget:\n" + widenings.map("  " + _.show).mkString("\n")

// ==================================================================================================
// THE ARENA
// ==================================================================================================

/** per-analysis hash-consing store.  Structurally equal nodes are one object; the cause table is the
 *  provenance DAG.  Never shared between analyses. */
final class Arena:
  private val tries = mutable.HashMap.empty[(Boolean, Vector[(PathItem, Int)]), XTrie]
  private val choices = mutable.HashMap.empty[Vector[Int], XChoice]
  private val summs = mutable.HashMap.empty[SpatialType, XSumm]
  private val causes = mutable.ArrayBuffer.empty[Cause]
  private var next = 0
  def size: Int = next
  def cause(id: Int): Cause = causes(id)
  private def mint(c: Cause): Int = { val i = next; next += 1; causes += c; i }

  def trie(terminal: Boolean, children: SortedMap[PathItem, XNode], c: Cause): XTrie =
    val k = (terminal, children.iterator.map((h, n) => h -> n.id).toVector)
    tries.getOrElseUpdate(k, new XTrie(mint(c), terminal, children))
  def summ(t: SpatialType, c: Cause): XSumm =
    summs.getOrElseUpdate(t, new XSumm(mint(c), t))
  /** alternatives are flattened, deduplicated by node, and a single survivor IS the node */
  def choice(alts0: Vector[XNode], c: Cause): XNode =
    val flat = alts0.flatMap { case ch: XChoice => ch.alts; case n => Vector(n) }
    val seen = mutable.LinkedHashMap.empty[Int, XNode]
    for a <- flat do seen.getOrElseUpdate(a.id, a)
    val alts = seen.values.toVector.sortBy(_.id)
    if alts.length == 1 then alts.head
    else choices.getOrElseUpdate(alts.map(_.id), new XChoice(mint(c), alts))

  val empty: XTrie = trie(false, SortedMap.empty, Cause.Literal)
  val epsilon: XTrie = trie(true, SortedMap.empty, Cause.Literal)

// ==================================================================================================
// THE DOMAIN
// ==================================================================================================

/** ONE ANALYSIS' DOMAIN INSTANCE: an arena, a budget, and the widening log the certificate is made of. */
final class Domain(val budget: DomainBudget = DomainBudget()):
  val arena = new Arena
  private val widenings = mutable.ArrayBuffer.empty[Widening]
  private val summaries = mutable.HashMap.empty[Int, SpatialType]
  private val sizes = mutable.HashMap.empty[Int, Ivl]
  private val lens = mutable.HashMap.empty[Int, LenBounds]

  def certificate: DomainCert = DomainCert(budget, widenings.toVector)

  // ---- α --------------------------------------------------------------------------------------------
  /** the exact node of a concrete value */
  def alpha(v: SpaceValue, c: Cause = Cause.Literal): XTrie =
    def go(paths: Set[List[PathItem]]): XTrie =
      val term = paths.contains(Nil)
      val groups = paths.iterator.collect { case h :: t => h -> t }.toVector.groupMap(_._1)(_._2)
      arena.trie(term, SortedMap.from(groups.iterator.map((h, ts) => h -> (go(ts.toSet): XNode))), c)
    go(v.paths.map(_.items))
  def input(m: SpaceMention, v: SpaceValue): Abs = Abs(alpha(v, Cause.Input(m)), Alias.Is(m))
  def inputSummary(m: SpaceMention, t: SpatialType): Abs = Abs(arena.summ(t, Cause.Input(m)), Alias.Is(m))
  def literal(v: SpaceValue): Abs = Abs(alpha(v), Alias.Fresh)
  def empty: Abs = Abs(arena.empty, Alias.Fresh)

  // ---- γ --------------------------------------------------------------------------------------------
  def member(x: XNode, v: SpaceValue): Boolean = x match
    case t: XTrie =>
      val hasEps = v.paths.contains(PathValue(Nil))
      val groups = v.paths.iterator.collect { case PathValue(h :: tl) => h -> PathValue(tl) }.toVector.groupMap(_._1)(_._2)
      hasEps == t.terminal && groups.keySet == t.children.keySet &&
        t.children.forall((k, c) => member(c, SpaceValue(groups(k).toSet)))
    case ch: XChoice => ch.alts.exists(member(_, v))
    case s: XSumm => SpatialType.accepts(s.t, v)
  def member(a: Abs, v: SpaceValue): Boolean = member(a.node, v)

  /** the concrete alternatives of an exact value, when there are at most `budget.enumerate` */
  def enumerate(x: XNode): Option[Vector[SpaceValue]] =
    def go(n: XNode): Option[Vector[Set[PathValue]]] = n match
      case t: XTrie =>
        val base: Option[Vector[Set[PathValue]]] = Some(Vector(if t.terminal then Set(PathValue(Nil)) else Set.empty))
        t.children.foldLeft(base) { case (acc, (k, c)) =>
          for as <- acc; cs <- go(c)
              if as.length.toLong * cs.length <= budget.enumerate
          yield for a <- as; cv <- cs yield a ++ cv.map(p => PathValue(k :: p.items)) }
      case ch: XChoice =>
        ch.alts.foldLeft(Option(Vector.empty[Set[PathValue]])) { (acc, a) =>
          for as <- acc; bs <- go(a) if as.length + bs.length <= budget.enumerate yield as ++ bs }
      case _: XSumm => None
    go(x).map(_.distinct.map(SpaceValue(_)))

  // ---- projections ------------------------------------------------------------------------------------
  /** THE SUMMARIZED READING of any node, through the certified transfers: a trie node is
   *  `ε ∪ ⋃_k k·child_k`, and `Wrap`/`Union`'s own transfers build its type */
  def summary(x: XNode): SpatialType = summaries.getOrElseUpdate(x.id, x match
    case s: XSumm => s.t
    case ch: XChoice => ch.alts.map(summary).reduce(SpatialGamma.lub)
    case t: XTrie =>
      if t.isEmptyNode then SpatialType.empty
      else
        val names = t.children.keys.toVector.zipWithIndex.map((k, i) => k -> SpaceMention(s"#c$i")).toMap
        val parts = t.children.iterator.map((k, c) => Space.Wrap(Space.Mention(names(k)), Path.Constant(PathValue(List(k))))).toVector ++
          (if t.terminal then Vector(Space.Literal(SpaceValue(Set(PathValue(Nil))))) else Vector.empty)
        val term = parts.reduce(Space.Union(_, _))
        val env = SpatialTyping.Env(spaces = t.children.iterator.map((k, c) => names(k) -> summary(c)).toMap)
        SpatialType.reduce(SpatialTyping.infer(term, env)))

  def size(x: XNode): Ivl = sizes.getOrElseUpdate(x.id, x match
    case t: XTrie =>
      var lo = if t.terminal then 1L else 0L; var hi = lo
      for (_, c) <- t.children do { val s = size(c); lo = Ivl.add(lo, s.lo); hi = Ivl.add(hi, s.hi) }
      Ivl(lo, hi)
    case ch: XChoice => ch.alts.map(size).reduce((a, b) => Ivl(a.lo min b.lo, a.hi max b.hi))
    case s: XSumm => val sz = s.t.size; Ivl(sz.lo, sz.hi))

  def len(x: XNode): LenBounds = lens.getOrElseUpdate(x.id, x match
    case t: XTrie =>
      if t.isEmptyNode then LenBounds.empty
      else
        var lo = if t.terminal then 0L else LenBounds.INF; var hi = if t.terminal then 0L else -1L
        for (_, c) <- t.children do
          val l = len(c)
          if !l.isEmpty then { lo = lo min (l.lo + 1); hi = if l.hi >= LenBounds.INF then LenBounds.INF else hi max (l.hi + 1) }
        if hi < 0 then LenBounds.empty else LenBounds(lo, hi)
    case ch: XChoice =>
      val ls = ch.alts.map(len).filterNot(_.isEmpty)
      if ls.isEmpty then LenBounds.empty else LenBounds(ls.map(_.lo).min, ls.map(_.hi).max)
    case s: XSumm => s.t.len)

  def mustEmpty(x: XNode): Boolean = x match
    case t: XTrie => t.isEmptyNode
    case ch: XChoice => ch.alts.forall(mustEmpty)
    case s: XSumm => s.t.isProvablyEmpty
  def mayEmpty(x: XNode): Boolean = x match
    case t: XTrie => t.isEmptyNode
    case ch: XChoice => ch.alts.exists(mayEmpty)
    case s: XSumm => s.t.size.lo == 0
  def exact(x: XNode): Boolean = x match
    case t: XTrie => t.children.values.forall(exact)
    case _ => false

  // ---- order -------------------------------------------------------------------------------------------
  /** γ(a) ⊆ γ(b), decided soundly (a `false` is "not proved") */
  def leq(a: XNode, b: XNode): Boolean =
    if a eq b then true
    else (a, b) match
      case (x: XTrie, y: XTrie) =>
        x.terminal == y.terminal && x.children.keySet == y.children.keySet &&
          x.children.forall((k, c) => leq(c, y.children(k)))
      case (ch: XChoice, _) => ch.alts.forall(leq(_, b))
      case (_, ch: XChoice) => ch.alts.exists(leq(a, _))
      case (_: XSumm, _: XTrie) => false
      case (_, y: XSumm) => SpatialType.leq(summary(a), y.t)

  // ---- join, meet, widening ------------------------------------------------------------------------------
  private def altCount(x: XNode): Int = x match
    case ch: XChoice => ch.alts.length
    case _ => 1

  private def record(reason: String, before: Vector[XNode], after: XNode): Unit =
    if Mutation.active("no-widening-record") then return   // E1 mutation site: the precision loss goes unrecorded
    val bs = before.map(size).reduce((a, b) => Ivl(a.lo min b.lo, a.hi max b.hi))
    val bl = before.map(len).filterNot(_.isEmpty)
    val blen = if bl.isEmpty then LenBounds.empty else LenBounds(bl.map(_.lo).min, bl.map(_.hi).max)
    val w = Widening(reason, before.map(_.show).mkString(" ⊔ ").take(200), after.show.take(200), bs, size(after), blen, len(after))
    // a widening may lose precision but may not change a must fact or a growth class: it is ⊒ each input
    require(before.forall(b => leq(b, after)), s"widening `$reason` is not an upper bound: ${w.show}")
    widenings += w

  /** ⊔: the choice when it fits the budget, else the summarized lub (a named widening) */
  def join(a: XNode, b: XNode): XNode =
    if a eq b then a
    else if leq(a, b) then b
    else if leq(b, a) then a
    else (a, b) match
      case (_: XSumm, _) | (_, _: XSumm) =>
        val out = arena.summ(SpatialGamma.lub(summary(a), summary(b)), Cause.Op("lub", Vector(a.id, b.id)))
        record("summarized-join", Vector(a, b), out)
        out
      case _ =>
        if altCount(a) + altCount(b) <= budget.alternatives then arena.choice(Vector(a, b), Cause.Alternative(Vector(a.id, b.id)))
        else
          val out = arena.summ(SpatialGamma.lub(summary(a), summary(b)), Cause.Widened("alternatives-budget", Vector(a.id, b.id)))
          record("alternatives-budget", Vector(a, b), out)
          out

  /** ⊓: `None` is ⊥ (no concrete value satisfies both) */
  def meet(a: XNode, b: XNode): Option[XNode] =
    if a eq b then Some(a)
    else (a, b) match
      case (x: XTrie, y: XTrie) =>
        if x.terminal != y.terminal || x.children.keySet != y.children.keySet then None
        else
          val kids = x.children.iterator.map((k, c) => meet(c, y.children(k)).map(k -> _)).toVector
          if kids.exists(_.isEmpty) then None
          else Some(arena.trie(x.terminal, SortedMap.from(kids.flatten), Cause.Op("meet", Vector(a.id, b.id))))
      case (ch: XChoice, _) =>
        val ms = ch.alts.flatMap(meet(_, b))
        if ms.isEmpty then None else Some(arena.choice(ms, Cause.Op("meet", Vector(a.id, b.id))))
      case (_, ch: XChoice) =>
        val ms = ch.alts.flatMap(meet(a, _))
        if ms.isEmpty then None else Some(arena.choice(ms, Cause.Op("meet", Vector(a.id, b.id))))
      case (x: XSumm, y: XSumm) =>
        val m = SpatialType.meet(x.t, y.t)
        if m.uninhabited then None else Some(arena.summ(m, Cause.Op("meet", Vector(a.id, b.id))))
      case (_: XSumm, _) => meet(b, a)
      case (_, y: XSumm) =>
        // filter the enumerable alternatives by γ; otherwise the exact operand (⊒ the meet) stands
        if leq(a, b) then Some(a)
        else enumerate(a) match
          case Some(vs) =>
            val ok = vs.filter(v => SpatialType.accepts(y.t, v))
            if ok.isEmpty then None
            else Some(arena.choice(ok.map(v => alpha(v, Cause.Op("meet", Vector(a.id, b.id)))), Cause.Op("meet", Vector(a.id, b.id))))
          case None => Some(a)

  /** the iteration widening: join, then open the summarized counts past the budget */
  def widen(prev: XNode, next: XNode): XNode =
    val j = join(prev, next)
    j match
      case s: XSumm if !(prev eq j) =>
        val w = arena.summ(SpatialRecursion.widenType(s.t), Cause.Widened("iteration-widening", Vector(prev.id, next.id)))
        record("iteration-widening", Vector(prev, next), w)
        w
      case other => other

  // ---- the operations ---------------------------------------------------------------------------------------
  /** A RESULT CONTAINED IN AN OPERAND HAS AT MOST ITS PATHS.  The certified transfers count per depth
   *  and per shape region; past the shape caps they can only sum fibres (tails of a one-path source
   *  become "at most 16 paths", and 16^5 after five levels).  The containment fact is exact and
   *  independent of the caps, so it is met into the summary. */
  private def capSize(t: SpatialType, hi: Long): SpatialType =
    if hi >= Ivl.INF || t.size.hi <= hi then t
    else
      val m = SpatialType.meet(t, SpatialType(Shape.top, SpaceType.bounded(t.len, hi)))
      if m.uninhabited then SpatialType.empty else m
  private def sizeCap(kind: String, a: XNode, b: Option[XNode]): Long = kind match
    case "inter" => b.map(y => math.min(size(a).hi, size(y).hi)).getOrElse(size(a).hi)
    case "sub" | "restrict" | "raff" | "tails-union" | "tails-inter" | "unwrap" | "range" => size(a).hi
    case _ => Ivl.INF
  private def summOp(kind: String, term: (Space, Space) => Space, a: XNode, b: XNode): XSumm =
    val (ma, mb) = (SpaceMention("#a"), SpaceMention("#b"))
    val env = SpatialTyping.Env(spaces = Map(ma -> summary(a), mb -> summary(b)))
    arena.summ(capSize(SpatialType.reduce(SpatialTyping.infer(term(Space.Mention(ma), Space.Mention(mb)), env)), sizeCap(kind, a, Some(b))), Cause.Op(kind, Vector(a.id, b.id)))
  private def summOp1(kind: String, term: Space => Space, a: XNode): XSumm =
    val ma = SpaceMention("#a")
    val env = SpatialTyping.Env(spaces = Map(ma -> summary(a)))
    arena.summ(capSize(SpatialType.reduce(SpatialTyping.infer(term(Space.Mention(ma)), env)), sizeCap(kind, a, None)), Cause.Op(kind, Vector(a.id)))

  /** distribute a binary operation over the alternatives, within the budget */
  private def binary(kind: String, a: XNode, b: XNode, term: (Space, Space) => Space)
                    (onTries: (XTrie, XTrie) => XNode): XNode =
    (a, b) match
      case (x: XTrie, y: XTrie) => onTries(x, y)
      case (_: XSumm, _) | (_, _: XSumm) => summOp(kind, term, a, b)
      case _ =>
        val as = a match { case ch: XChoice => ch.alts; case n => Vector(n) }
        val bs = b match { case ch: XChoice => ch.alts; case n => Vector(n) }
        if as.length.toLong * bs.length <= budget.alternatives then
          arena.choice(for x <- as; y <- bs yield binary(kind, x, y, term)(onTries), Cause.Op(kind, Vector(a.id, b.id)))
        else
          val out = summOp(kind, term, a, b)
          // the widening is from THE CHOICE OF THE RESULTS to the summary: the before values are the
          // operation's results on the alternatives (an operand is not below a comp/inter/sub result), computed
          // for the certificate when there are few enough pairs to enumerate
          val before = if as.length.toLong * bs.length <= 4096 then (for x <- as; y <- bs yield binary(kind, x, y, term)(onTries)) else Vector(out)
          record(s"alternatives-budget($kind)", before, out)
          out
  private def unary(kind: String, a: XNode, term: Space => Space)(onTrie: XTrie => XNode): XNode = a match
    case x: XTrie => onTrie(x)
    case _: XSumm => summOp1(kind, term, a)
    case ch: XChoice => arena.choice(ch.alts.map(unary(kind, _, term)(onTrie)), Cause.Op(kind, Vector(a.id)))

  private def dropEmpty(kids: Iterable[(PathItem, XNode)]): SortedMap[PathItem, XNode] =
    SortedMap.from(kids.filterNot((_, c) => mustEmpty(c)))

  /** `a eq b` is an IDENTITY OF ABSTRACT VALUES; it is a concrete identity only when the node denotes
   *  one value (`exact`).  Two inputs with the same summary are the same node and DIFFERENT objects —
   *  object identity is the alias channel's business (`unionA` etc.), never the node's. */
  private def sameValue(a: XNode, b: XNode): Boolean = (a eq b) && exact(a)

  def union(a: XNode, b: XNode): XNode =
    if sameValue(a, b) then a
    else if mustEmpty(a) then b else if mustEmpty(b) then a
    else binary("union", a, b, Space.Union.apply) { (x, y) =>
      val keys = x.children.keySet ++ y.children.keySet
      arena.trie(x.terminal || y.terminal,
        SortedMap.from(keys.iterator.map(k => k -> ((x.children.get(k), y.children.get(k)) match
          case (Some(c), Some(d)) => union(c, d)
          case (Some(c), None) => c
          case (None, Some(d)) => d
          case _ => arena.empty))), Cause.Op("union", Vector(a.id, b.id))) }

  def inter(a: XNode, b: XNode): XNode =
    if sameValue(a, b) then a
    else if mustEmpty(a) || mustEmpty(b) then arena.empty
    else binary("inter", a, b, Space.Intersection.apply) { (x, y) =>
      val keys = x.children.keySet intersect y.children.keySet
      arena.trie(x.terminal && y.terminal, dropEmpty(keys.iterator.map(k => k -> inter(x.children(k), y.children(k))).toVector),
                 Cause.Op("inter", Vector(a.id, b.id))) }

  def sub(a: XNode, b: XNode): XNode =
    if sameValue(a, b) then arena.empty
    else if mustEmpty(a) then arena.empty else if mustEmpty(b) then a
    else binary("sub", a, b, Space.Subtraction.apply) { (x, y) =>
      arena.trie(x.terminal && !y.terminal,
        dropEmpty(x.children.iterator.map((k, c) => k -> (y.children.get(k) match
          case Some(d) => sub(c, d)
          case None => c)).toVector), Cause.Op("sub", Vector(a.id, b.id))) }

  def restrict(x0: XNode, p0: XNode): XNode =
    if mustEmpty(x0) || mustEmpty(p0) then arena.empty
    else binary("restrict", x0, p0, Space.Restriction.apply) { (x, p) =>
      if p.terminal then x
      else
        val keys = x.children.keySet intersect p.children.keySet
        arena.trie(false, dropEmpty(keys.iterator.map(k => k -> restrict(x.children(k), p.children(k))).toVector),
                   Cause.Op("restrict", Vector(x0.id, p0.id))) }

  def raff(x0: XNode, y0: XNode): XNode =
    if mustEmpty(x0) then arena.empty else if mustEmpty(y0) then x0
    else binary("raff", x0, y0, Space.Raffination.apply) { (x, y) =>
      if y.terminal then arena.empty
      else arena.trie(x.terminal,
        dropEmpty(x.children.iterator.map((k, c) => k -> (y.children.get(k) match
          case Some(d) => raff(c, d)
          case None => c)).toVector), Cause.Op("raff", Vector(x0.id, y0.id))) }

  def comp(a: XNode, b: XNode): XNode =
    if mustEmpty(a) || mustEmpty(b) then arena.empty
    else binary("comp", a, b, Space.Composition.apply) { (x, y) =>
      if y.terminal && y.children.isEmpty then x
      else if x.terminal && x.children.isEmpty then y
      else
        val mapped = arena.trie(false, dropEmpty(x.children.iterator.map((k, c) => k -> comp(c, b)).toVector), Cause.Op("comp", Vector(a.id, b.id)))
        if x.terminal then union(mapped, y) else mapped }

  def wrap(items: List[PathItem], s: XNode): XNode =
    if mustEmpty(s) then arena.empty
    else items.foldRight(s)((k, acc) => arena.trie(false, SortedMap(k -> acc), Cause.Op("wrap", Vector(s.id))))
  def unwrap(s: XNode, items: List[PathItem]): XNode = items match
    case Nil => s
    case k :: rest => unary("unwrap", s, x => Space.Unwrap(x, Path.Constant(PathValue(items)))) { t =>
      t.children.get(k) match { case Some(c) => unwrap(c, rest); case None => arena.empty } }
  /** THE PER-PREFIX FIBRE, as a lub over the heads: `⊔_h (x under h)` — what ONE head's tails can be
   *  (an `Unwrap` by an unknown one-item prefix, a loop's `rest`), against `tailsUnion`, which is the
   *  UNION of all fibres (Σ over heads).  For a board of 16 cells with one tile each the lub has one
   *  path where the union has sixteen; through fifteen compositions that is the difference between a
   *  bound and `inf`.  Falls back to `tailsUnion` when the heads are not all tracked. */
  def fibreLub(s: XNode): XNode = headSet(s) match
    case Some(hs) if hs.nonEmpty =>
      hs.toVector.sortBy(_.toString).map(h => under(s, h)).reduce(join)
    case Some(_) => arena.empty
    case None => tailsUnion(s)
  def tailsUnion(s: XNode): XNode = unary("tails-union", s, Space.TailsUnion.apply) { t =>
    if t.children.isEmpty then arena.empty else t.children.values.reduce(union) }
  def tailsInter(s: XNode): XNode = unary("tails-inter", s, Space.TailsIntersection.apply) { t =>
    if t.children.isEmpty then arena.empty else t.children.values.reduce(inter) }

  /** the canonical-order slice; exact on an exact node, `Shape.rangeAt` on a summary */
  def range(x: XNode, lo: Int, hi: Int): XNode = x match
    case ch: XChoice => arena.choice(ch.alts.map(range(_, lo, hi)), Cause.Op("range", Vector(x.id)))
    case _: XSumm => summOp1("range", y => Space.Range(y, lo, hi), x)
    case t: XTrie =>
      enumerate(t) match
        case Some(Vector(v)) => alpha(SpaceValue(sliceRange(v.paths, lo, hi)), Cause.Op("range", Vector(x.id)))
        case Some(vs) => arena.choice(vs.map(v => alpha(SpaceValue(sliceRange(v.paths, lo, hi)), Cause.Op("range", Vector(x.id)))), Cause.Op("range", Vector(x.id)))
        case None => summOp1("range", y => Space.Range(y, lo, hi), x)

  // ---- the same over `Abs`, with the alias channel and the executors' identity cases ------------------------
  /** the result IS the left operand (by pointer) exactly when the executors' identity case fires */
  def unionA(a: Abs, b: Abs): Abs =
    if DomainFacts.mustAlias(a, b) then return a
    val r = union(a.node, b.node)
    val alias = if (r eq a.node) then a.alias else if (r eq b.node) then b.alias else Alias.Fresh
    Abs(r, alias)
  def interA(a: Abs, b: Abs): Abs =
    if DomainFacts.mustAlias(a, b) then return a
    val r = inter(a.node, b.node)
    Abs(r, if r eq a.node then a.alias else if r eq b.node then b.alias else Alias.Fresh)
  def subA(a: Abs, b: Abs): Abs =
    if DomainFacts.mustAlias(a, b) then return Abs(arena.empty, Alias.Fresh)
    val r = sub(a.node, b.node); Abs(r, if r eq a.node then a.alias else Alias.Fresh)
  def restrictA(x: Abs, p: Abs): Abs =
    if DomainFacts.mustAlias(x, p) then return x
    val r = restrict(x.node, p.node); Abs(r, if r eq x.node then x.alias else Alias.Fresh)
  def raffA(x: Abs, y: Abs): Abs =
    if DomainFacts.mustAlias(x, y) then return Abs(arena.empty, Alias.Fresh)
    val r = raff(x.node, y.node); Abs(r, if r eq x.node then x.alias else Alias.Fresh)
  def compA(a: Abs, b: Abs): Abs =
    val r = comp(a.node, b.node)
    Abs(r, if r eq a.node then a.alias else if r eq b.node then b.alias else Alias.Fresh)
  def wrapA(items: List[PathItem], s: Abs): Abs = Abs(wrap(items, s.node), if items.isEmpty then s.alias else Alias.Fresh)
  /** an unwrap navigates INTO the operand's object: the result is a sub-object, never the object */
  def unwrapA(s: Abs, items: List[PathItem]): Abs = Abs(unwrap(s.node, items), if items.isEmpty then s.alias else Alias.Unknown)
  def tailsUnionA(s: Abs): Abs = Abs(tailsUnion(s.node), Alias.Unknown)
  def tailsInterA(s: Abs): Abs = Abs(tailsInter(s.node), Alias.Unknown)
  def rangeA(x: Abs, lo: Int, hi: Int): Abs =
    val r = range(x.node, lo, hi); Abs(r, if r eq x.node then x.alias else Alias.Fresh)
  def joinA(a: Abs, b: Abs): Abs =
    val r = join(a.node, b.node); Abs(r, if a.alias == b.alias then a.alias else Alias.Unknown)

  // ---- fibres: what the loop transfers read ----------------------------------------------------------------------
  /** the tail set under head `k` — the value an `Iteration` binds `rest` to */
  def under(x: XNode, k: PathItem): XNode = x match
    case t: XTrie => t.children.getOrElse(k, arena.empty)
    case ch: XChoice => arena.choice(ch.alts.map(under(_, k)), Cause.Op("under", Vector(x.id)))
    case s: XSumm => summOp1("under", y => Space.Unwrap(y, Path.Constant(PathValue(List(k)))), s)

  /** the head set when it is closed */
  def headSet(x: XNode): Option[Set[PathItem]] = x match
    case t: XTrie => Some(t.children.keySet.toSet)
    case ch: XChoice => ch.alts.map(headSet).reduce((a, b) => for p <- a; q <- b yield p union q)
    case s: XSumm => s.t.shape.possibleHeads
  /** the heads that are PRESENT in every alternative */
  def mustHeads(x: XNode): Set[PathItem] = x match
    case t: XTrie => t.children.iterator.filterNot((_, c) => mayEmpty(c)).map(_._1).toSet
    case ch: XChoice => ch.alts.map(mustHeads).reduce(_ intersect _)
    case s: XSumm => s.t.shape.heads.keySet.filter(s.t.shape.mustHaveHead).toSet
end Domain

// ==================================================================================================
// THE FACTS
// ==================================================================================================

/** the correlated facts a resource transfer may read.  All are sound with respect to γ. */
object DomainFacts:
  /** how many distinct heads: [must, may] */
  def fanOut(d: Domain, x: XNode): Ivl =
    (d.headSet(x), d.mustHeads(x)) match
      case (Some(all), must) => Ivl(must.size.toLong, all.size.toLong)
      case (None, must) =>
        // a summary's head count past the shape caps is unbounded, but every head carries at least one
        // path: the path count bounds the fan-out
        val t = d.summary(x)
        Ivl(must.size.toLong, math.min(t.headCount.hi, t.size.hi))
  /** the cardinality of the fibre under a prefix */
  def fibre(d: Domain, x: XNode, prefix: List[PathItem]): Ivl = d.size(prefix.foldLeft(x)((n, k) => d.under(n, k)))
  /** the least and greatest paths, when determined — what `Range(x, 0, 1)` / `Range(x, -1, 0)` select */
  def orderMin(d: Domain, x: XNode): Option[PathValue] = x match
    case s: XSumm => s.t.shape.orderMin
    case _ => d.enumerate(x).flatMap { vs =>
      val mins = vs.map(v => if v.paths.isEmpty then None else Some(v.paths.min(using pathValueOrdering))).distinct
      if mins.length == 1 then mins.head else None }
  def orderMax(d: Domain, x: XNode): Option[PathValue] = x match
    case s: XSumm => s.t.shape.orderMax
    case _ => d.enumerate(x).flatMap { vs =>
      val maxs = vs.map(v => if v.paths.isEmpty then None else Some(v.paths.max(using pathValueOrdering))).distinct
      if maxs.length == 1 then maxs.head else None }
  /** the rank of a path in the canonical order, when every alternative agrees */
  def rank(d: Domain, x: XNode, p: PathValue): Option[Int] =
    d.enumerate(x).flatMap { vs =>
      val rs = vs.map(v => v.paths.count(q => pathValueOrdering.compare(q, p) < 0)).distinct
      if rs.length == 1 then Some(rs.head) else None }
  /** provably disjoint head sets (so a merge rejects at the root) */
  def headDisjoint(d: Domain, a: XNode, b: XNode): Boolean =
    (d.headSet(a), d.headSet(b)) match
      case (Some(x), Some(y)) => (x intersect y).isEmpty
      case _ => false
  /** MUST alias: the same object by construction */
  def mustAlias(a: Abs, b: Abs): Boolean = (a.alias, b.alias) match
    case (Alias.Is(m), Alias.Is(n)) => m == n
    case _ => false
  /** MAY alias: not provably different objects.  Two fresh results of two operations are different
   *  objects; two inputs may be the same object only when they are the same mention. */
  def mayAlias(a: Abs, b: Abs): Boolean = (a.alias, b.alias) match
    case (Alias.Is(m), Alias.Is(n)) => m == n
    case (Alias.Fresh, Alias.Fresh) => false
    case (Alias.Fresh, Alias.Is(_)) | (Alias.Is(_), Alias.Fresh) => false
    case _ => true
  /** the number of DISTINCT LIVE (non-empty, non-aliased) operands an n-ary operation sees: [must, may] */
  def distinctLive(d: Domain, ops: Vector[Abs]): Ivl =
    val live = ops.filterNot(o => d.mustEmpty(o.node))
    val mayLive = live
    val mustLive = live.filterNot(o => d.mayEmpty(o.node))
    // distinct by must-alias groups (a must-aliased pair is one operand)
    def groups(v: Vector[Abs]): Int =
      var n = 0
      val seen = mutable.ArrayBuffer.empty[Abs]
      for o <- v do
        if !seen.exists(s => mustAlias(s, o)) then { seen += o; n += 1 }
      n
    // may-distinct: every may-alias-free operand counts; must-distinct: the must-live ones that are
    // pairwise provably different objects
    val mustDistinct = mustLive.foldLeft(Vector.empty[Abs]) { (acc, o) =>
      if acc.exists(p => mayAlias(p, o)) then acc else acc :+ o }.length
    Ivl(mustDistinct.toLong, groups(mayLive).toLong)
  /** the result IS the `i`-th operand (proven reuse) */
  def provenReuse(result: Abs, ops: Vector[Abs]): Option[Int] =
    ops.indexWhere(o => (o.node eq result.node) && o.alias != Alias.Unknown && o.alias == result.alias) match
      case -1 => None
      case i => Some(i)
