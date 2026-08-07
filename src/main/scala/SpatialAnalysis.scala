package morkl

import scala.collection.immutable.SortedMap

/** THE ONE ANALYSIS CONFIGURATION (review.md 6).
 *
 *  Every budget the spatial subsystem spends used to be a constant in whichever object happened to
 *  need it — `Shape.MaxDepth`/`MaxHeads`, the `200000` node budget and the `48` depth cap inside
 *  `SpatialTyping`, `SpatialCost.FactBudget`/`MaxInline`/`MaxDepth`, `SpatialRecursion.Limits`.  A
 *  caller who wanted a cheaper or a sharper analysis had to know all of them.  They are collected
 *  here, one value, with the defaults being exactly the numbers those constants had.
 *
 *  WHAT CONSUMES IT TODAY — three different degrees, and the difference matters to a caller:
 *
 *   - PER CALL, honoured: [[SpatialAnalysis]] (every field it names), `SpatialTyping`
 *     (`nodeBudget`, `termDepth`, `fixpointRounds`, `fixpointWiden`) and `SpatialType.reduce`
 *     (`reduceRounds`) all take a `SpatialConfig` argument, so a non-default value really does change
 *     what those runs do.
 *   - GLOBAL DEFAULT ONLY: `Shape.MaxDepth`/`MaxHeads` are `val`s initialised from
 *     `SpatialConfig.default.shapeDepth`/`shapeWidth`.  Passing a config with a different
 *     `shapeDepth` to [[SpatialAnalysis.of]] does NOT narrow the trie — the carrier's caps are still
 *     process-wide constants, merely named in one place now.  Treat those two fields as
 *     documentation of the caps, not as knobs.
 *   - DECLARED BUT UNCONSUMED: `histQueries`, `inline`, `summaryKeys`, `unroll` mirror
 *     `SpatialCost.FactBudget`/`MaxInline` and `SpatialRecursion.Limits`, which still read their own
 *     constants.  They exist so there is one place to change them when those files adopt the config;
 *     setting them today changes nothing outside [[SpatialAnalysis]].
 *
 *  So review.md 6's "one configuration value for all analysis stages" is PARTIAL, by exactly this
 *  list.  `SpatialConfig.cheap` is honest about it: the fields it sets are the ones that are read. */
final case class SpatialConfig(
  /** [[Shape.MaxDepth]] — trie levels kept before collapsing to an untracked-head count */
  shapeDepth: Int = 4,
  /** [[Shape.MaxHeads]] — tracked heads per level before spilling into `others`/`otherTail` */
  shapeWidth: Int = 12,
  /** transfers the shape traversal may run before degrading to ⊤ */
  nodeBudget: Int = 200000,
  /** lexical depth after which the traversal degrades to ⊤ */
  termDepth: Int = 48,
  /** Kleene rounds in the `Fixpoint` shape transfer, and the round at which it starts widening */
  fixpointRounds: Int = 8,
  fixpointWiden: Int = 4,
  /** rounds of [[SpatialType.reduce]]; the reducer stops early at its fixed point */
  reduceRounds: Int = 4,
  /** nodes [[SpatialAnalysis]] will decorate before it stops recording (the analysis itself carries
   *  on — a missing node means "ask `infer`", never a wrong answer) */
  maxNodes: Int = 20000,
  /** DIRECT histogram queries the decorated traversal may make for the operators whose count
   *  transfer is not compositional (`Iteration`, `Fold`, `Fixpoint`) plus the root.  This is the
   *  budget `SpatialCost.FactBudget` spends per NODE; here it is spent per BINDER. */
  histQueries: Int = 2000,
  /** `SpatialCost.MaxInline` */
  inline: Int = 6,
  /** `SpatialRecursion.Limits.maxKeys` */
  summaryKeys: Int = 512,
  /** `SpatialRecursion.Limits.maxUnroll` */
  unroll: Int = 32,
):
  require(shapeDepth >= 1 && shapeWidth >= 1 && reduceRounds >= 1)

object SpatialConfig:
  val default: SpatialConfig = SpatialConfig()
  /** the cheap setting: no direct histogram queries, no reduction rounds beyond the first */
  val cheap: SpatialConfig = SpatialConfig(reduceRounds = 1, histQueries = 0, maxNodes = 2000)

/** THE LEXICAL IDENTITY of one occurrence: the child-index path from the root of the analysed term.
 *  `Vector()` is the root, `Vector(0, 1)` the second child of the first child.  Two structurally
 *  identical subterms in different positions therefore have DIFFERENT ids, which is the whole point
 *  (review.md 4): `Fact.from(SpatialTyping.infer(subterm))` cannot tell them apart, and an optimizer
 *  rewriting one of them must not consume the other's facts.
 *
 *  Child indices follow the AST field order, and are exactly the order the shape transfer visits its
 *  operands in ([[SpatialAnalysis.childrenOf]]).  A binder's body has ONE id even though it is
 *  analysed once per head group / fixpoint round: those are separate OBSERVATIONS of the same
 *  occurrence, kept individually on the node. */
final case class NodeId(position: Vector[Int]):
  def child(i: Int): NodeId = NodeId(position :+ i)
  def parent: Option[NodeId] = if position.isEmpty then None else Some(NodeId(position.dropRight(1)))
  def depth: Int = position.size
  def show: String = if position.isEmpty then "/" else position.mkString("/", "/", "")

/** ONE OBSERVATION of one occurrence: the environment it was analysed in and what came out.  A loop
 *  body observed under three head groups has three observations, and each keeps ITS OWN bindings —
 *  the head item it was analysed with and the tail-set `rest` was bound to.  `cause` names why this
 *  observation exists (`head=a`, `untracked-heads`, `fixpoint-round=2`, `child`, `root`, `budget`). */
final case class SpatialObservation(cause: String, bindings: SpatialTyping.Env, result: SpatialType):
  /** the histogram-domain view of the same bindings (what `SpatialTypes`/`SpatialCost` consume) */
  def lengthBindings: SpatialEnv = bindings.lengths
  def show: String = s"$cause :: ${result.show}"

/** ONE DECORATED NODE.  `result` is the JOINED summary over every observation (the lattice join, so
 *  it admits each observation's concrete values); `bindings` are the FIRST observation's, kept
 *  because a single-observation node — every non-binder-body node — is the common case and a consumer
 *  should not have to unwrap a vector to get at it. */
final case class NodeAnalysis(id: NodeId,
                              expression: Space,
                              result: SpatialType,
                              bindings: SpatialTyping.Env,
                              observations: Vector[SpatialObservation],
                              facts: Vector[Fact]):
  def isJoined: Boolean = observations.size > 1
  def show: String = s"${id.show} ${expression.show.take(60)} :: ${result.show}"

/** THE DECORATED ANALYSIS — one traversal, per-node results with lexical provenance (review.md 4).
 *
 *  ==WHY==
 *  `SpatialCost` used to call `SpatialTypes.infer` / `SpatialTyping.infer` again at every subterm
 *  (through `histAt`/`shapeAt`/`provablyEmpty`/`typeAt`), which is quadratic — a ceiling on the
 *  duplicate work is not an architecture — and, worse, a freshly inferred subterm type cannot answer
 *  "what does this OCCURRENCE denote under the binders it sits inside".  A loop body analysed under
 *  three head groups has three answers and a root query has none of them.
 *
 *  ==THE SHAPE OF THE RESULT==
 *  {{{
 *  val a = SpatialAnalysis.of(term, env)
 *  a.root                      // the same SpatialType `SpatialTyping.infer` returns, meet-refined
 *  a.at(NodeId(Vector(0, 1)))  // that occurrence, under its own bindings — O(1)
 *  a.factsAt(id)               // validated propositions for that occurrence — a PROJECTION
 *  a.nodes                     // every decorated node, parents before children
 *  }}}
 *
 *  ==HOW ONE TRAVERSAL DOES BOTH COMPONENTS==
 *  The SHAPE half is the traversal `SpatialTyping.infer` already ran: this file installs a
 *  [[SpatialTyping.ShapeVisitor]] on it, so there is one shape traversal in the tree, not two, and
 *  the decorated node's shape is by construction the shape `infer` computes.  The visitor returns the
 *  REDUCED shape, so the parent transfer consumes the tightened child ([[SpatialType.reduce]], the
 *  bidirectional reducer).
 *
 *  The HISTOGRAM half is computed COMPOSITIONALLY, and this is the part that stops being quadratic:
 *  for each node the analysis rebuilds JUST THAT NODE over stub mentions bound to the children's
 *  already-computed histograms, and hands the one-node term to `SpatialTypes.infer` — the single
 *  owner of the count transfers.  The stub term has size `1 + arity`, so one transfer per node.
 *  Sound because a child's concrete value is in γ of the child's own inferred type and the `Mention`
 *  transfer is sound for every value in γ of a declared type.  Two honest costs:
 *
 *    - the sibling-relational rules (`x ∖ x = ∅`, `x ∩ x = x`, `x <| x = x`) survive only because
 *      STRUCTURALLY EQUAL children get the SAME stub mention, which keeps `SpatialTypes.subsumes`'
 *      reflexive cases firing; the nested ones (`subsumes(x, x ∩ y)`) do not survive;
 *    - `Iteration`/`Fold`/`Fixpoint` are genuinely NOT compositional in the count domain (the
 *      rest-chain head-partition law reads the real body, and the fixpoint re-analyses its body
 *      against the accumulated type), so for those the analysis also makes ONE direct
 *      `SpatialTypes.infer` call and MEETS the two answers.  That is `O(#binders)` direct queries
 *      instead of `O(#nodes)`, under [[SpatialConfig.histQueries]].
 *
 *  ==NO EVALUATION==
 *  Nothing here calls `eval`/`evalI`/`evalT`/`exec*`.  Every number comes from the transfers, the
 *  declared input types and the term's syntax; grounded functions stay ⊤. */
final case class SpatialAnalysis(root: SpatialType,
                                 nodes: Vector[NodeAnalysis],
                                 config: SpatialConfig,
                                 notes: Vector[String]):
  /** the index review.md 4 asks for: O(1) per lookup instead of a fresh inference */
  val index: Map[NodeId, NodeAnalysis] = nodes.iterator.map(n => n.id -> n).toMap
  def at(id: NodeId): Option[NodeAnalysis] = index.get(id)
  def rootNode: Option[NodeAnalysis] = at(NodeId(Vector.empty))
  /** facts as a PROJECTION of the decorated analysis (review.md 4), not a second inference */
  def factsAt(id: NodeId): Vector[Fact] = index.get(id).map(_.facts).getOrElse(Vector.empty)
  def rootFacts: Vector[Fact] = rootNode.map(_.facts).getOrElse(Fact.from(root))
  /** every occurrence of a subterm, by position — two identical subterms come back separately */
  def occurrencesOf(s: Space): Vector[NodeAnalysis] = nodes.filter(_.expression == s)
  /** the nodes the analysis PROVED empty: the elimination candidates, with their positions */
  def provablyEmpty: Vector[NodeAnalysis] = nodes.filter(_.result.isProvablyEmpty)
  def show: String =
    (s"root ${root.show}" +: nodes.map(n => "  " + n.show) ++: notes.map("  ! " + _)).mkString("\n")

object SpatialAnalysis:
  import Lower.LenBounds

  /** the operands of a node, in the order the shape transfer visits them — the order [[NodeId]]'s
   *  child indices refer to.  A `Call`'s operands are its mention arguments; the callee's body is a
   *  different routine's tree and is deliberately NOT a child here (see `SpatialTyping.goShape`). */
  def childrenOf(s: Space): Vector[Space] = s match
    case Space.Empty | Space.Literal(_) | Space.Singleton(_) | Space.Mention(_) |
         Space.GroundedPS(_, _) => Vector.empty
    case Space.GroundedSS(_, _) => Vector.empty
    case Space.Union(a, b) => Vector(a, b)
    case Space.Intersection(a, b) => Vector(a, b)
    case Space.Subtraction(a, b) => Vector(a, b)
    case Space.Restriction(a, b) => Vector(a, b)
    case Space.Raffination(a, b) => Vector(a, b)
    case Space.Composition(a, b) => Vector(a, b)
    case Space.Wrap(a, _) => Vector(a)
    case Space.Unwrap(a, _) => Vector(a)
    case Space.TailsUnion(a) => Vector(a)
    case Space.TailsIntersection(a) => Vector(a)
    case Space.Range(a, _, _) => Vector(a)
    case Space.Iteration(src, _, _, body) => Vector(src, body)
    case Space.Fold(src, _, _, _, _, body, _) => Vector(src, body)
    case Space.Fixpoint(init, _, body) => Vector(init, body)
    case Space.Call(_, _, mentions) => mentions

  /** rebuild a node over new operands — the stub term the histogram transfer is applied to */
  private def rebuild(s: Space, kids: Vector[Space]): Space = s match
    case Space.Union(_, _) => Space.Union(kids(0), kids(1))
    case Space.Intersection(_, _) => Space.Intersection(kids(0), kids(1))
    case Space.Subtraction(_, _) => Space.Subtraction(kids(0), kids(1))
    case Space.Restriction(_, _) => Space.Restriction(kids(0), kids(1))
    case Space.Raffination(_, _) => Space.Raffination(kids(0), kids(1))
    case Space.Composition(_, _) => Space.Composition(kids(0), kids(1))
    case Space.Wrap(_, p) => Space.Wrap(kids(0), p)
    case Space.Unwrap(_, p) => Space.Unwrap(kids(0), p)
    case Space.TailsUnion(_) => Space.TailsUnion(kids(0))
    case Space.TailsIntersection(_) => Space.TailsIntersection(kids(0))
    case Space.Range(_, lo, hi) => Space.Range(kids(0), lo, hi)
    case Space.Iteration(_, sym, rest, _) => Space.Iteration(kids(0), sym, rest, kids(1))
    case Space.Fold(_, init, acc, sym, rest, _, upd) => Space.Fold(kids(0), init, acc, sym, rest, kids(1), upd)
    case Space.Fixpoint(_, recm, _) => Space.Fixpoint(kids(0), recm, kids(1))
    case Space.Call(r, refs, _) => Space.Call(r, refs, kids)
    case leaf => leaf

  /** the CONSTANT PATHS the term itself mentions — the finite, useful set of prefixes to run the
   *  prefix query on, so `Fact.PrefixAbsent` becomes a fact somebody actually obtains (review.md 6). */
  def constantPrefixes(s: Space): Vector[List[PathItem]] =
    val out = Vector.newBuilder[List[PathItem]]
    def pathOf(p: Path): Unit = p match
      case Path.Constant(pv) if pv.items.nonEmpty => out += pv.items
      case Path.Concat(l, r) => pathOf(l); pathOf(r)
      case _ => ()
    def go(x: Space): Unit =
      x match
        case Space.Wrap(_, p) => pathOf(p)
        case Space.Unwrap(_, p) => pathOf(p)
        case Space.Singleton(p) => pathOf(p)
        case Space.Literal(v) => v.paths.iterator.filter(_.items.nonEmpty).take(4).foreach(out += _.items)
        case _ => ()
      childrenOf(x).foreach(go)
    go(s)
    out.result().distinct.take(32)

  /** the reserved stub-mention prefix.  A term containing a free mention with this prefix would
   *  shadow a stub, so the analysis refuses to stub in that case and falls back to a direct query. */
  private val StubPrefix = "#sa#"

  def of(s: Space): SpatialAnalysis = of(s, SpatialTyping.Env(), SpatialConfig.default)
  def of(s: Space, env: SpatialTyping.Env): SpatialAnalysis = of(s, env, SpatialConfig.default)

  /** THE decorated analysis. */
  def of(s: Space, env: SpatialTyping.Env, cfg: SpatialConfig): SpatialAnalysis =
    val rec = new Recorder(cfg, constantPrefixes(s))
    val rootShape = SpatialTyping.shapeWith(s, env, cfg, rec)
    // the ROOT additionally meets the authoritative histogram — the one `SpatialTyping.infer` uses —
    // so `root` is never weaker than `infer` no matter how the compositional path fared.  Both are
    // sound approximations of the same value, so the meet is sound; a BOTTOM here would mean the two
    // contradict each other, which `SpatialAnalysisCheck` gates against on the corpus.
    val authoritative = SpatialType.reduce(SpatialType(rootShape, SpatialTypes.infer(s, env.lengths)), cfg)
    val rootId = NodeId(Vector.empty)
    val composed = rec.result(rootId).map(_.result).getOrElse(authoritative)
    val root = SpatialType.meet(composed, authoritative)
    val contradiction =
      if root.uninhabited then
        Vector("the compositional per-node result and the root query CONTRADICT each other: the " +
               "annotations are unsatisfiable, or one of the two transfers is unsound")
      else Vector.empty
    val nodes = rec.nodes(root)
    SpatialAnalysis(root, nodes, cfg, contradiction ++ rec.noteList)

  /** facts for one occurrence, straight out of the decorated analysis */
  def factsAt(s: Space, env: SpatialTyping.Env, id: NodeId): Vector[Fact] = of(s, env).factsAt(id)

  // ------------------------------------------------------------------------------------------------
  // the recorder: the ShapeVisitor that turns the one shape traversal into a decorated analysis
  // ------------------------------------------------------------------------------------------------
  private final class Recorder(cfg: SpatialConfig, probes: Vector[List[PathItem]])
      extends SpatialTyping.ShapeVisitor:
    private val obs = collection.mutable.LinkedHashMap.empty[Vector[Int], Vector[SpatialObservation]]
    private val exprs = collection.mutable.HashMap.empty[Vector[Int], Space]
    private var queries = cfg.histQueries
    private var dropped = 0
    private val notes = collection.mutable.LinkedHashSet.empty[String]
    /** `nodes` may add a note, so read this AFTER it */
    def noteList: Vector[String] = notes.toVector

    def result(id: NodeId): Option[NodeAnalysis] = node(id.position)

    /** POST-ORDER: children are visited before their parent, so their histograms are already here. */
    def visit(pos: Vector[Int], s: Space, env: SpatialTyping.Env, sh: Shape, cause: String): Shape =
      val lens = histOf(pos, s, env)
      val reduced = SpatialType.reduce(SpatialType(sh, lens), cfg)
      if obs.size >= cfg.maxNodes && !obs.contains(pos) then
        dropped += 1
        reduced.shape
      else
        exprs(pos) = s
        obs(pos) = obs.getOrElse(pos, Vector.empty) :+ SpatialObservation(cause, env, reduced)
        // the TIGHTENED child is what the parent transfer sees — the part a root-only reduction
        // cannot do (review.md 5)
        reduced.shape

    /** the compositional histogram for one node, plus a direct query where composition is weak */
    private def histOf(pos: Vector[Int], s: Space, env: SpatialTyping.Env): SpaceType =
      val kids = childrenOf(s)
      val direct = s match
        case Space.Iteration(_, _, _, _) | Space.Fold(_, _, _, _, _, _, _) | Space.Fixpoint(_, _, _) =>
          if queries > 0 then { queries -= 1; Some(SpatialTypes.infer(s, env.lengths)) }
          else { notes += s"direct histogram queries exhausted (${cfg.histQueries}); binder nodes " +
                          "past that point use the compositional bound only"; None }
        case _ => None
      val stub = stubHist(pos, s, kids, env)
      (stub, direct) match
        case (Some(a), Some(b)) => SpatialGamma.meetSpace(a, b).getOrElse(a)
        case (Some(a), None) => a
        case (None, Some(b)) => b
        // a leaf, or a child whose record was dropped: ask the transfer directly on the node itself
        case (None, None) =>
          if kids.isEmpty then SpatialTypes.infer(s, env.lengths)
          else if queries > 0 then { queries -= 1; SpatialTypes.infer(s, env.lengths) }
          else SpaceType.unknown

    /** rebuild the node over stub mentions bound to the children's histograms, and let
     *  `SpatialTypes` — the owner of the count transfers — run the transfer on the one-node term.
     *  STRUCTURALLY EQUAL children share a stub so `subsumes`' reflexive rules still fire.
     *
     *  When a node is observed SEVERAL times (a loop body, once per head group), the child lookup
     *  returns the JOIN of the observations recorded so far, not that observation's own child.  That
     *  is sound — the join admits every group's value — and costs a little precision on the second and
     *  later groups; the SHAPE half, which is where head-group precision actually lives, is per
     *  observation because the traversal itself re-runs the transfer under each group's bindings. */
    private def stubHist(pos: Vector[Int], s: Space, kids: Vector[Space],
                         env: SpatialTyping.Env): Option[SpaceType] =
      if kids.isEmpty then None
      else
        val childTypes = kids.indices.map(i => node(pos :+ i).map(_.result.lens))
        if childTypes.exists(_.isEmpty) then None
        else
          var names = Map.empty[Space, SpaceMention]
          var bind = Map.empty[SpaceMention, SpaceType]
          val stubs = kids.indices.toVector.map { i =>
            val k = kids(i)
            names.get(k) match
              case Some(m) => Space.Mention(m)
              case None =>
                val m = SpaceMention(s"$StubPrefix${pos.mkString(".")}#$i")
                names = names.updated(k, m)
                bind = bind.updated(m, childTypes(i).get)
                Space.Mention(m)
          }
          val lenv = env.lengths
          if lenv.spaces.keysIterator.exists(_.s.startsWith(StubPrefix)) then None
          else Some(SpatialTypes.infer(rebuild(s, stubs), lenv.copy(spaces = lenv.spaces ++ bind)))

    private def node(pos: Vector[Int]): Option[NodeAnalysis] =
      for
        vs <- obs.get(pos)
        e <- exprs.get(pos)
      yield
        val joined = vs.map(_.result).reduce(SpatialType.join)
        NodeAnalysis(NodeId(pos), e, joined, vs.head.bindings, vs, Fact.from(joined, probes))

    /** every decorated node, parents before children.  The ROOT is replaced by the meet-refined root
     *  the analysis publishes, so `at(root)` and `.root` cannot disagree. */
    def nodes(root: SpatialType): Vector[NodeAnalysis] =
      if dropped > 0 then
        notes += s"node budget (${cfg.maxNodes}) reached: $dropped further occurrences were analysed " +
                 "but not recorded — `at` returns None for them, never a wrong answer"
      val all = obs.keysIterator.toVector.sortBy(p => (p.size, p.mkString(".")))
      all.flatMap(p => node(p)).map { n =>
        if n.id.position.isEmpty then n.copy(result = root, facts = Fact.from(root, probes)) else n
      }
end SpatialAnalysis
