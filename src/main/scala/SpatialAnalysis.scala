package morkl

import scala.collection.immutable.SortedMap

/** THE ONE ANALYSIS CONFIGURATION.
 *
 *  Every budget the spatial subsystem spends used to be a constant in whichever object happened to
 *  need it — `Shape.MaxDepth`/`MaxHeads`, the `200000` node budget and the `48` depth cap inside
 *  `SpatialTyping`, `SpatialCost.FactBudget`/`MaxInline`/`MaxDepth`, `SpatialRecursion.Limits`.  A
 *  caller who wanted a cheaper or a sharper analysis had to know all of them.  They are collected
 *  here, one value, with the defaults being exactly the numbers those constants had.
 *
 *  WHAT CONSUMES IT — every field below is READ by a run, and this list says by whom:
 *
 *   - [[SpatialAnalysis]]: `maxNodes`, `histQueries`, `reduceRounds`, and — through
 *     [[SpatialAnalysis.narrow]] — `shapeDepth`/`shapeWidth`.
 *   - `SpatialTyping.shapeWith`: `nodeBudget`, `termDepth`, `fixpointRounds`, `fixpointWiden`.
 *   - `SpatialType.reduce`: `reduceRounds`.
 *   - `SpatialFacts` (through [[facts]], which `SpatialAnnotations.factConfig` returns):
 *     `profileDepth`, `unrollDepth`, `unrollNodes`, `prefixLength`.
 *   - `SpatialRecursion` (through [[recursion]], which `SpatialAnnotations.limits` returns):
 *     `summaryKeys`, `summaryUpdates`, `summaryWiden`, `summaryRounds`, `unroll`.
 *   - [[SpatialLaws]] (through [[SpatialAnalysis]]' recorder): `laws`, `lawQueries`.
 *
 *  ==THE ONE HONEST CAVEAT: `shapeDepth`/`shapeWidth` NARROW, THEY DO NOT WIDEN==
 *  `Shape.MaxDepth`/`MaxHeads` are `val`s of the CARRIER, initialised from
 *  `SpatialConfig.default.shapeDepth`/`shapeWidth`.  They have to be domain-wide: a `Shape` built
 *  under one cap is compared, joined and met with one built under another, so the cap belongs to the
 *  domain rather than to a call.  What a per-analysis value can therefore do is only ever WEAKEN a
 *  shape further, and that is what [[SpatialAnalysis.narrow]] does — it caps the depth
 *  ([[Shape.capDepth]]) and spills the excess tracked heads into `others`/`otherTail` on every shape
 *  the decorated traversal records and hands to its parent.  So:
 *
 *   - `shapeDepth`/`shapeWidth` BELOW the carrier's caps really do change the run (cheaper, weaker);
 *   - values AT or ABOVE them are a no-op, and the analysis says so in its `notes` — a config cannot
 *     deepen the trie the transfers build.
 *
 *  ==WHAT IS NOT HERE==
 *  `SpatialCost.MaxInline` (the cost analysis' call-inlining cap) has no channel: `SpatialCost.Env`
 *  takes no budget argument, so a field mirroring it would be decoration.  It was one
 *  (`SpatialConfig.inline`) and is deleted rather than left unconsumed; see the report's API request. */
final case class SpatialConfig(
  /** trie levels this ANALYSIS keeps before collapsing to an untracked-head count.  Narrowing only —
   *  see the caveat above; `Shape.MaxDepth` is the domain-wide cap it cannot exceed. */
  shapeDepth: Int = 4,
  /** tracked heads per level this ANALYSIS keeps before spilling into `others`/`otherTail`.
   *  Narrowing only, against `Shape.MaxHeads`. */
  shapeWidth: Int = 12,
  /** UNTRACKED-HEAD NAMES kept in the disjointness certificate (`Shape.otherKeys`, channel (e),
   *  with the overflow interned into `Shape.headAtoms`, channel (f), rather than dropped)
   *  before it degrades to ⊤.  Far above `shapeWidth` on purpose — see `Shape.MaxSpillKeys`: this
   *  bounds NAMES (one reference, one set operation per lattice step), `shapeWidth` bounds tracked
   *  SUB-SHAPES.  This one is read only through `Shape.MaxSpillKeys`, i.e. it is a domain-wide cap
   *  like the other two, not a per-query knob. */
  spillKeys: Int = 4096,
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
  /** `SpatialFacts.Config.maxProfileDepth` */
  profileDepth: Int = 64,
  /** `SpatialFacts.Config.maxUnrollDepth` */
  unrollDepth: Int = 8,
  /** `SpatialFacts.Config.maxUnrollNodes` */
  unrollNodes: Long = 4096L,
  /** `SpatialFacts.Config.maxPrefixLength` */
  prefixLength: Int = 64,
  /** `SpatialRecursion.Limits.maxKeys` */
  summaryKeys: Int = 400,
  /** `SpatialRecursion.Limits.maxUpdates` */
  summaryUpdates: Int = 8,
  /** `SpatialRecursion.Limits.widenAfter` */
  summaryWiden: Int = 3,
  /** `SpatialRecursion.Limits.maxRounds` */
  summaryRounds: Int = 20000,
  /** `SpatialRecursion.Limits.maxUnroll` */
  unroll: Int = 32,
  /** THE SEMANTIC LAWS this run may meet into its per-node results (the review, [[SpatialLaws]]).
   *  Empty by default: a law is a soundness PREMISE with provenance, so it is opted into, never
   *  inherited.  Consumed by [[SpatialAnalysis]]' recorder at every visited occurrence. */
  laws: Vector[SpatialBoundLaw] = Vector.empty,
  /** APPLICABLE OCCURRENCES at which the decorated traversal will evaluate a law's `bound`.  Past it
   *  the laws stop firing and the analysis says so in its `notes` — a user-supplied law with an
   *  expensive `bound` (`SpatialLaws.restChainPointwise` runs a whole chain analysis) must not be able
   *  to turn a bounded analysis into an unbounded one.  Sites where no law is applicable cost only the
   *  `applies` predicates and are not counted; the ROOT is refined regardless of the budget, because
   *  the traversal is post-order and the root is the last occurrence visited. */
  lawQueries: Int = 4000,
):
  require(shapeDepth >= 1 && shapeWidth >= 1 && reduceRounds >= 1)
  /** add laws to this configuration (see [[SpatialLaws]] and `SpatialAnnotations.withLaws`) */
  def withLaws(ls: SpatialBoundLaw*): SpatialConfig = copy(laws = laws ++ ls)
  /** the fact/profile/candidate stage's budgets — the value `SpatialFacts` takes.  A `lazy val` and
   *  not a field so that constructing a `SpatialConfig` (which `Shape.MaxDepth` does, at class-load)
   *  cannot force `SpatialFacts`' own initialisation. */
  lazy val facts: SpatialFacts.Config =
    SpatialFacts.Config(maxProfileDepth = profileDepth, maxUnrollDepth = unrollDepth,
                        maxUnrollNodes = unrollNodes, maxPrefixLength = prefixLength)
  /** the recursion residualiser's budgets — the value `SpatialRecursion` takes */
  lazy val recursion: SpatialRecursion.Limits =
    SpatialRecursion.Limits(maxKeys = summaryKeys, maxUpdates = summaryUpdates,
                            widenAfter = summaryWiden, maxRounds = summaryRounds, maxUnroll = unroll)
  /** does this config narrow the trie below the carrier's own caps? (`false` ⇒ [[SpatialAnalysis]]
   *  skips the narrowing pass entirely, so the default path pays nothing for it) */
  def narrowsShapes: Boolean = shapeDepth < Shape.MaxDepth || shapeWidth < Shape.MaxHeads

object SpatialConfig:
  val default: SpatialConfig = SpatialConfig()
  /** THE CHEAP SETTING — the one a hook on a hot compilation path can afford (`SpatialHook`, which
   *  runs on every `Routine.optimized` call): no direct histogram queries, one reduction round, a trie
   *  narrowed to 2 levels × 6 heads, and — the field that actually bounds the price — a TRANSFER
   *  budget two orders of magnitude below the default.
   *
   *  `nodeBudget` is what makes the cost predictable, and it was chosen by measurement, not taste.
   *  With the default 200000 the analysis of n-queens `place(8)` (137 body nodes, but a term whose
   *  binder bodies are re-analysed per head group and whose `Call`s are inlined interprocedurally)
   *  added 4.4 SECONDS to one `optimized` call.  The measured worst case over the nine representative
   *  routines in `SpatialPipelineCheck`'s cost test:
   *
   *  {{{
   *  nodeBudget   worst added   n-queens place(8)   gol/nextStep
   *     200000      +4391 ms          +4391 ms          +129 ms
   *       8000       +123 ms            +81 ms          +123 ms
   *       2000        +11 ms             +8 ms           +11 ms
   *        500         +9 ms             +3 ms            +3 ms
   *  }}}
   *
   *  Exhausting it costs precision only: `SpatialTyping` degrades the remaining subterms to ⊤. */
  val cheap: SpatialConfig = SpatialConfig(shapeDepth = 2, shapeWidth = 6, nodeBudget = 2000,
                                           reduceRounds = 1, histQueries = 0, maxNodes = 2000)

/** THE LEXICAL IDENTITY of one occurrence: the child-index path from the root of the analysed term.
 *  `Vector()` is the root, `Vector(0, 1)` the second child of the first child.  Two structurally
 *  identical subterms in different positions therefore have DIFFERENT ids, which is the whole point
 *: `Fact.from(SpatialTyping.infer(subterm))` cannot tell them apart, and an optimizer
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
                              facts: Vector[Fact],
                              /** WHICH SEMANTIC LAW TIGHTENED WHAT, HERE.  `result` and
                               *  `facts` above are already law-refined; this is the audit trail that
                               *  says by which law, on what evidence, and from what to what.  Empty
                               *  unless [[SpatialConfig.laws]] is non-empty. */
                              laws: Vector[LawApplication] = Vector.empty):
  def isJoined: Boolean = observations.size > 1
  /** laws that actually moved this node's answer */
  def tightenedBy: Vector[LawApplication] = laws.filter(_.tightened)
  def show: String =
    s"${id.show} ${expression.show.take(60)} :: ${result.show}" +
    (if tightenedBy.isEmpty then "" else tightenedBy.map(a => s"\n      ⊓ ${a.show}").mkString)

/** THE DECORATED ANALYSIS — one traversal, per-node results with lexical provenance.
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
 *      `SpatialTypes.infer` call per BINDER OBSERVATION and MEETS the two answers, under
 *      [[SpatialConfig.histQueries]].  (Per observation, not per binder: a binder inside a 16-level
 *      nest is analysed once per enclosing head group, and each of those has its own environment, so
 *      one cached answer would be an answer to a different question.  Measured on `puzzle15`: 1279
 *      direct queries, 0.21 s of a 1.33 s analysis.)
 *
 *  ==WHY THE RECORDER IS LINEAR IN THE OBSERVATIONS==
 *  A position's published `result` is the JOIN over its observations, and `stubHist` reads a child's
 *  result once per PARENT visit.  Recomputing that join (and its `Fact.from` projection) per lookup is
 *  quadratic in the observation count, and on `puzzle15` — 295 positions, 13725 observations — it was
 *  34.1 s of a 35.6 s analysis.  The join is therefore maintained INCREMENTALLY (one `SpatialType.join`
 *  per observation, the same left fold, the same value) and facts are derived exactly once per
 *  position, at the end.  Measured: 35.6 s -> 1.33 s, identical root type, identical node count.
 *
 *  ==SEMANTIC LAWS==
 *  [[SpatialConfig.laws]] carries [[SpatialBoundLaw]]s; the recorder MEETS every applicable law's bound
 *  into the per-node result at the occurrence where it applies and keeps the provenance on the node
 *  ([[NodeAnalysis.laws]]).  Because the refined child is what the parent transfer consumes, a law at a
 *  child changes the parent's answer, the routine's facts, its specialisation candidates, and — through
 *  `SpatialPipeline`'s per-node elimination — its RESIDUAL and the residual's cost.  See
 *  [[SpatialLaws]] for the safety argument (the channel is a meet, so a law cannot widen).
 *
 *  ==NO EVALUATION==
 *  Nothing here calls `eval`/`evalI`/`evalT`/`exec*`.  Every number comes from the transfers, the
 *  declared input types, the term's syntax and the declared laws; grounded functions stay ⊤. */
final case class SpatialAnalysis(root: SpatialType,
                                 nodes: Vector[NodeAnalysis],
                                 config: SpatialConfig,
                                 notes: Vector[String]):
  /** the index the review asks for: O(1) per lookup instead of a fresh inference */
  val index: Map[NodeId, NodeAnalysis] = nodes.iterator.map(n => n.id -> n).toMap
  def at(id: NodeId): Option[NodeAnalysis] = index.get(id)
  def rootNode: Option[NodeAnalysis] = at(NodeId(Vector.empty))
  /** facts as a PROJECTION of the decorated analysis, not a second inference */
  def factsAt(id: NodeId): Vector[Fact] = index.get(id).map(_.facts).getOrElse(Vector.empty)
  def rootFacts: Vector[Fact] = rootNode.map(_.facts).getOrElse(Fact.from(root))
  /** every occurrence of a subterm, by position — two identical subterms come back separately */
  def occurrencesOf(s: Space): Vector[NodeAnalysis] = nodes.filter(_.expression == s)
  /** the nodes the analysis PROVED empty: the elimination candidates, with their positions */
  def provablyEmpty: Vector[NodeAnalysis] = nodes.filter(_.result.isProvablyEmpty)

  // ---- THE LAW CHANNEL'S AUDIT TRAIL ----------------------------------------------
  /** every law application at every occurrence */
  def lawApplications: Vector[LawApplication] = nodes.flatMap(_.laws)
  /** the ones that MOVED an answer — the honest measure of what the laws bought */
  def tightenedBy: Vector[LawApplication] = nodes.flatMap(_.tightenedBy)
  /** the law applications at ONE occurrence: "which law tightened WHAT, here" */
  def lawsAt(id: NodeId): Vector[LawApplication] = index.get(id).map(_.laws).getOrElse(Vector.empty)
  /** laws that tightened an answer WITHOUT a discharged proof obligation.  A consumer that must not
   *  rest on an undischarged axiom reads this and refuses. */
  def assumedLaws: Vector[String] = tightenedBy.filter(_.assumed).map(_.law).distinct
  /** laws whose bound contradicted the transfers and were therefore DROPPED */
  def contradictedLaws: Vector[LawApplication] =
    lawApplications.filter(_.outcome == LawOutcome.Contradicted)
  /** how many observations the traversal made in total (parents are re-analysed per head group, so
   *  this is the quantity the latency budget is really about, not `nodes.size`) */
  def observationCount: Int = nodes.iterator.map(_.observations.size).sum

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
   *  prefix query on, so `Fact.PrefixAbsent` becomes a fact somebody actually obtains. */
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

  // ------------------------------------------------------------------------------------------------
  // THE PER-ANALYSIS TRIE CAPS — what makes `shapeDepth`/`shapeWidth` a knob and not a comment
  // ------------------------------------------------------------------------------------------------

  /** WEAKEN `sh` to this analysis' own trie caps.  Applied to every shape the decorated traversal
   *  records AND hands back to its parent transfer, so a narrower config really does produce a
   *  cheaper, weaker run rather than an identical one.
   *
   *  ==WHY IT CAN ONLY WEAKEN==
   *  `Shape.MaxDepth`/`MaxHeads` are properties of the CARRIER (see [[SpatialConfig]]), so the deepest
   *  trie any transfer will build is fixed process-wide.  Both directions of this function are
   *  therefore downward: [[Shape.capDepth]] collapses everything below `shapeDepth` into an
   *  untracked-head COUNT, and [[capWidth]] moves the excess tracked heads into `others`/`otherTail`.
   *
   *  ==WHY IT IS SOUND==
   *  Both operations only ADD values to γ, and the decorated analysis' soundness argument is exactly
   *  γ-based, never monotonicity-based: the concrete value of a subterm is in γ of the shape recorded
   *  for it, and every transfer is sound for every value in γ of its operands' declared types.  So a
   *  parent transfer fed the widened child stays sound, the recorded node stays sound, and the only
   *  thing lost is precision.  (`SpatialType.reduce` may still tighten it back through the histogram
   *  half — that is the reduced product doing its job, not the cap being ignored.) */
  def narrow(sh: Shape, cfg: SpatialConfig): Shape =
    if !cfg.narrowsShapes then sh else Shape.capDepth(capWidth(sh, cfg.shapeWidth), cfg.shapeDepth)

  /** keep at most `k` tracked heads per level; the rest become untracked, exactly the way
   *  `Shape`'s own normalising constructor spills them (`SpatialShape.scala:340-348`) — the count
   *  channel absorbs how many they were (`lo` counts the ones that are FORCED present, `hi` all of
   *  them) and the `otherTail` summary absorbs their tails, WEAKENED so no must claim survives into a
   *  channel that is a may-only summary by definition. */
  private def capWidth(sh: Shape, k: Int): Shape =
    if sh.definitelyEmpty then sh
    else
      val kids = sh.heads.iterator.map((h, t) => h -> capWidth(t, k)).toVector
      val ot = sh.otherTail.map(t => Shape.weaken(capWidth(t, k)))
      if kids.size <= k then Shape(sh.eps, SortedMap.from(kids), sh.others, ot, sh.otherKeys, sh.headAtoms)
      else
        val keep = kids.take(k)
        val spill = kids.drop(k)
        val base: Shape = if sh.others.hi == 0 then Shape.empty else ot.getOrElse(Shape.top)
        val tail = spill.foldLeft(Shape.weaken(base))((a, kv) => Shape.unionTransfer(a, Shape.weaken(kv._2)))
        val cnt = Ivl(Ivl.add(sh.others.lo, spill.count((_, t) => t.definitelyNonEmpty).toLong),
                      Ivl.add(sh.others.hi, spill.size.toLong))
        // THE CONFIG'S OWN WIDTH SPILL keeps the untracked-head NAMES too (channel (e)), exactly as
        // `Shape.mk` does — otherwise a narrowed config would silently reintroduce the
        // discontinuity this channel exists to remove, and `SpatialConfig.cheap` (shapeWidth = 6)
        // would predict a different GROWTH CLASS from the default (12) on the same program.
        Shape(sh.eps, SortedMap.from(keep), cnt,
              if tail.isTop then None else Some(Shape.weaken(tail)),
              Shape.spillKeysOf(sh.possibleHeads, keep.iterator.map(_._1).toSet))

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
               "annotations are unsatisfiable, or one of the two transfers is unsound" +
               (if cfg.laws.isEmpty then ""
                else s"; ${cfg.laws.size} law(s) were in effect (${cfg.laws.map(_.show).mkString(", ")}) " +
                     "and a law's bound is a soundness PREMISE, so suspect it first"))
      else Vector.empty
    val nodes = rec.nodes(root)
    // a law that MOVED an answer is reported, and one that rests on an undischarged axiom is reported
    // loudly: a consumer must be able to see that a rewrite was licensed by an assumption.
    val lawNotes =
      val tightened = nodes.flatMap(_.tightenedBy)
      val dropped = nodes.flatMap(_.laws).filter(_.outcome == LawOutcome.Contradicted)
      tightened.groupBy(_.law).toVector.sortBy(_._1).map((n, as) =>
        s"law $n tightened ${as.size} occurrence(s) [${as.head.evidence.show}]") ++
      dropped.groupBy(_.law).toVector.sortBy(_._1).map((n, as) =>
        s"law $n CONTRADICTED the transfers at ${as.size} occurrence(s) and was DROPPED: ${as.head.why}") ++
      (if tightened.exists(_.assumed) then
         Vector("this result rests on ASSUMED law(s): " +
                tightened.filter(_.assumed).map(_.law).distinct.mkString(", ") +
                " — no proof obligation was discharged for their bounds")
       else Vector.empty)
    // a config may only NARROW the trie (see `narrow`); say so rather than let a caller believe a
    // bigger `shapeDepth` bought a deeper one
    val caps =
      if cfg.shapeDepth > Shape.MaxDepth || cfg.shapeWidth > Shape.MaxHeads then
        Vector(s"shapeDepth=${cfg.shapeDepth}/shapeWidth=${cfg.shapeWidth} exceed the carrier's own " +
               s"caps (${Shape.MaxDepth}/${Shape.MaxHeads}): a config narrows the trie, it cannot " +
               "deepen or widen it, so those two values had no effect")
      else Vector.empty
    SpatialAnalysis(root, nodes, cfg, contradiction ++ caps ++ lawNotes ++ rec.noteList)

  /** facts for one occurrence, straight out of the decorated analysis */
  def factsAt(s: Space, env: SpatialTyping.Env, id: NodeId): Vector[Fact] = of(s, env).factsAt(id)

  // ------------------------------------------------------------------------------------------------
  // the recorder: the ShapeVisitor that turns the one shape traversal into a decorated analysis
  // ------------------------------------------------------------------------------------------------
  private final class Recorder(cfg: SpatialConfig, probes: Vector[List[PathItem]])
      extends SpatialTyping.ShapeVisitor:
    private val obs = collection.mutable.LinkedHashMap.empty[Vector[Int], Vector[SpatialObservation]]
    private val exprs = collection.mutable.HashMap.empty[Vector[Int], Space]
    /** THE INCREMENTALLY MAINTAINED JOIN over a position's observations — the same value the fold
     *  `vs.map(_.result).reduce(SpatialType.join)` produces, in the same left-to-right order, but
     *  updated ONCE PER OBSERVATION instead of recomputed on every lookup.  That is what makes the
     *  decorated traversal linear in the number of observations rather than quadratic: `stubHist`
     *  reads a child's result once per PARENT visit, and a binder body under a 16-level iteration nest
     *  has thousands of observations (measured on `puzzle15`: 13725 visits over 295 positions, 11487
     *  child lookups, 34.1 s of the 35.6 s total spent re-joining and re-deriving facts). */
    private val joined = collection.mutable.HashMap.empty[Vector[Int], SpatialType]
    /** the law audit trail per position, merged over observations ([[LawApplication.occurrences]]) */
    private val lawLog = collection.mutable.HashMap.empty[Vector[Int], Vector[LawApplication]]
    private var queries = cfg.histQueries
    private var lawBudget = cfg.lawQueries
    private var dropped = 0
    private val notes = collection.mutable.LinkedHashSet.empty[String]
    /** `nodes` may add a note, so read this AFTER it */
    def noteList: Vector[String] = notes.toVector

    def result(id: NodeId): Option[NodeAnalysis] = node(id.position)

    /** POST-ORDER: children are visited before their parent, so their histograms are already here. */
    def visit(pos: Vector[Int], s: Space, env: SpatialTyping.Env, sh: Shape, cause: String): Shape =
      // ONE construction of the length environment per visit.  `env.lengths` rebuilds three maps, and
      // the direct query, the stub query and the leaf fallback all want the same value.
      lazy val lenv = env.lengths
      val lens = histOf(pos, s, env, lenv)
      // THIS ANALYSIS' OWN trie caps, applied before the reduction so the reducer works on the shape
      // this run is willing to keep (see `SpatialAnalysis.narrow` — narrowing only, always sound)
      val reduced = SpatialType.reduce(SpatialType(narrow(sh, cfg), lens), cfg)
      // ---- THE LAW CHANNEL: meet every applicable law's bound in, HERE, and keep the
      // provenance on the node.  A law can only narrow (the channel is a meet), and with no laws
      // configured this costs one `isEmpty` test and returns the value the transfers produced.
      val refined =
        // THE ROOT IS NEVER STARVED.  The traversal is POST-ORDER, so the root is the LAST occurrence
        // visited; a budget spent on the way up would silently skip the one node every consumer reads.
        // It is exactly one extra site, so the exception costs a bounded amount.
        if cfg.laws.isEmpty then reduced
        else if lawBudget <= 0 && pos.nonEmpty then
          notes += s"law refinements exhausted (${cfg.lawQueries} applicable occurrences); later " +
                   "occurrences use the transfers alone — sound, less precise (the ROOT is always " +
                   "refined regardless of this budget)"
          reduced
        else
          val (r, apps) = SpatialLaws.refine(cfg.laws, LawSite(NodeId(pos), s, env, reduced))
          if apps.nonEmpty then
            // the budget counts APPLICABLE sites, which is what the expensive half (`bound`) costs.
            // `applies` is required to be cheap and is not budgeted — see `SpatialBoundLaw`.
            lawBudget -= 1
            lawLog(pos) = SpatialLaws.mergeApplications(lawLog.getOrElse(pos, Vector.empty), apps)
          r
      if obs.size >= cfg.maxNodes && !obs.contains(pos) then
        dropped += 1
        refined.shape
      else
        exprs(pos) = s
        obs(pos) = obs.getOrElse(pos, Vector.empty) :+ SpatialObservation(cause, env, refined)
        joined(pos) = joined.get(pos) match
          case Some(prev) => SpatialType.join(prev, refined)
          case None => refined
        // the TIGHTENED child is what the parent transfer sees — the part a root-only reduction
        // cannot do, and the part that lets a law at a child change a PARENT's answer
        refined.shape

    /** the compositional histogram for one node, plus a direct query where composition is weak */
    private def histOf(pos: Vector[Int], s: Space, env: SpatialTyping.Env, lenv: => SpatialEnv): SpaceType =
      val kids = childrenOf(s)
      val direct = s match
        case Space.Iteration(_, _, _, _) | Space.Fold(_, _, _, _, _, _, _) | Space.Fixpoint(_, _, _) =>
          if queries > 0 then { queries -= 1; Some(SpatialTypes.infer(s, lenv)) }
          else { notes += s"direct histogram queries exhausted (${cfg.histQueries}); binder nodes " +
                          "past that point use the compositional bound only"; None }
        case _ => None
      val stub = stubHist(pos, s, kids, lenv)
      (stub, direct) match
        case (Some(a), Some(b)) => SpatialGamma.meetSpace(a, b).getOrElse(a)
        case (Some(a), None) => a
        case (None, Some(b)) => b
        // a leaf, or a child whose record was dropped: ask the transfer directly on the node itself
        case (None, None) =>
          if kids.isEmpty then SpatialTypes.infer(s, lenv)
          else if queries > 0 then { queries -= 1; SpatialTypes.infer(s, lenv) }
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
                         lenv: => SpatialEnv): Option[SpaceType] =
      if kids.isEmpty then None
      else
        val childTypes = kids.indices.map(i => joinedAt(pos :+ i).map(_.lens))
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
          val le = lenv
          if le.spaces.keysIterator.exists(_.s.startsWith(StubPrefix)) then None
          else Some(SpatialTypes.infer(rebuild(s, stubs), le.copy(spaces = le.spaces ++ bind)))

    /** THE HOT LOOKUP — the join over a position's observations, in O(1).  `stubHist` calls it once
     *  per operand per parent visit, so it must not derive facts (that is `node`'s job, and it happens
     *  exactly once per POSITION, at the end). */
    private def joinedAt(pos: Vector[Int]): Option[SpatialType] = joined.get(pos)

    private def node(pos: Vector[Int]): Option[NodeAnalysis] =
      for
        vs <- obs.get(pos)
        e <- exprs.get(pos)
        j <- joined.get(pos)
      yield NodeAnalysis(NodeId(pos), e, j, vs.head.bindings, vs, Fact.from(j, probes),
                         lawLog.getOrElse(pos, Vector.empty))

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
