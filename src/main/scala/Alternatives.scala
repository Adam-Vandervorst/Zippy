package morkl

import scala.collection.mutable

/** ==============================================================================================
 *  RESIDUAL ALTERNATIVES (tasks.md B1).
 *
 *  The supercompiler used to COMMIT: one law table, fold-first, one residual.  Whether the fused
 *  loop or the two loops, the hoisted invariant or the per-head recomputation, the pushed restriction
 *  or the restriction of the union is the cheaper program depends on the inputs and on the backend —
 *  and none of those decisions is made where the costs are known.  This module makes the choices
 *  EXPLICIT: an [[Alternative]] is a residual program together with everything a later decision needs
 *  — its semantic proof trace (C3), the spatial input assumptions it was priced under, its resource
 *  certificate per backend (A4/A5) and its provenance (which choice produced it) — and a [[Frontier]]
 *  is the set of alternatives that survived hash-consing, subsumption and the widening budget, with
 *  EVERY pruned alternative and the reason recorded.
 *
 *  ==WHERE ALTERNATIVES COME FROM==
 *  [[explore]] drives the same configuration under several `SC.Config`s:
 *
 *   - LAW FAMILIES ([[Family]]): the ordinary table, then the table with one family disabled —
 *     FUSION (`iter-setop-merge`, `wrap-merge`, `unwrap-merge`, `unwrap-fuse-const`), SHARING
 *     (`iter-union-indep`, `iter-comp-right-hoist`: the invariant is computed once and shared, or once
 *     per head), PREFIX RESTRICTION (`restriction-push`, `raffination-push`, `unwrap-push`,
 *     `raff-restrict-algebra`, `restrict-raff-wrap-both`), RANGE REDUCTION (`range-singleton`),
 *     MATERIALIZATION (`comp-lit-to-wraps`: a composition, or the right operand materialised under each
 *     literal prefix).  Two
 *     tables reach two normal forms of the same program; each normal form's law chain is its trace.
 *   - UNFOLD/FOLD (`SC.Config.unroll`): a configuration the fold-first driver would fold is unfolded
 *     once more before folding.  A definitional step (Drive.lean `unfold_step`), recorded as an
 *     `Unfold` node; the fold happens one level deeper.
 *   - BACKEND TRANSLATION: every alternative carries one certificate PER backend; the backend is a
 *     dimension of the choice, not a separate alternative, because the trace is the same and the
 *     translation's own theorem (the refinement/graph cells of the pipeline) is what the pipeline
 *     certifies.
 *
 *  MATERIALIZATION is NOT created here: at the term level it is literal folding (`constant-ops`,
 *  `literal-space-ops`), which EVALUATES, and the exploration is evaluation-free by construction
 *  (`groundFree`: the GROUND laws are removed from every table; `AlternativesCheck` counts executor
 *  events across the whole exploration and requires zero).  The backend-side materialization choice
 *  (the zipper's `materialize` boundary) is priced as the zipper backend's certificate.
 *
 *  ==HASH-CONSING AND MERGING==
 *  Two alternatives are the SAME residual when their programs are alpha-equivalent AFTER the residual
 *  routine names are canonicalised (names carry a run counter; two runs of the same program name their
 *  nodes differently).  They are MERGED — one alternative, the other recorded as pruned — only when
 *  both the semantic assumptions (the fact scope the trace is valid under) and the resource assumptions
 *  (the `CostSem.Inputs` the certificate was computed over) are equal; otherwise both are kept and the
 *  frontier says so.  An alternative whose residual equals another's but whose semantic scope is
 *  conditional while the other's is unconditional is SUBSUMED (same program, fewer inputs).
 *
 *  ==WIDENING==
 *  The frontier keeps at most `budget` alternatives; past it the largest residual is dropped and the
 *  drop is recorded as a widening with the budget named.  Nothing is silently lost.
 *
 *  Everything here is deterministic: ids are digests of the canonical residual and the assumptions,
 *  rows are sorted by id, and the rendering carries no counters, hashes of closures or timings.
 *  ============================================================================================== */
object Alternatives:

  /** the choice families tasks.md B1 names */
  enum Choice:
    case Unfold, Fold, Fusion, Sharing, PrefixRestriction, RangeReduction, Materialization, BackendTranslation
    def slug: String = toString

  /** a law family whose laws can be switched off together to expose the choice they make */
  final case class Family(choice: Choice, laws: Set[String]):
    def describe: String = s"${choice.slug}: ${laws.toVector.sorted.mkString(",")}"
  val families: Vector[Family] = Vector(
    Family(Choice.Fusion, Set("iter-setop-merge", "wrap-merge", "unwrap-merge", "unwrap-fuse-const")),
    Family(Choice.Sharing, Set("iter-union-indep", "iter-comp-right-hoist")),
    Family(Choice.PrefixRestriction, Set("restriction-push", "raffination-push", "unwrap-push", "raff-restrict-algebra", "restrict-raff-wrap-both")),
    Family(Choice.RangeReduction, Set("range-singleton")),
    // `comp-lit-to-wraps` trades a composition for a union of wraps: the right operand is MATERIALISED
    // once per literal path instead of attached under the literal's prefixes in one pass
    Family(Choice.Materialization, Set("comp-lit-to-wraps")))

  /** one recorded decision on the way to an alternative */
  final case class Provenance(choice: Choice, detail: String):
    def show: String = s"${choice.slug}[$detail]"

  /** THE RESIDUAL-ALTERNATIVE NODE. */
  final case class Alternative(
      /** digest of the canonical residual + the assumptions; the identity everything else keys on */
      id: String,
      residual: Residual,
      /** the parameters of the configuration (what the residual is a function of) */
      refs: Vector[PathRef], mentions: Vector[SpaceMention],
      /** C3: configuration → residual top */
      trace: ProofTrace.Dag,
      /** C3: one unfold of each residual node's configuration → its body */
      nodeTraces: Map[RoutinePtr, ProofTrace.Dag],
      /** the residual nodes (configuration and parameters), what the fold steps are checked against */
      nodes: ProofTrace.NodeTable,
      /** the semantic scope the trace is valid under (law/definitional steps: every input) */
      scope: FactScope,
      /** the spatial input assumptions the certificate was computed under */
      assumptions: CostSem.Inputs,
      /** A4/A5: the resource certificate per backend */
      certificate: Map[Backend, CostReport],
      provenance: Vector[Provenance],
      /** the supercompiler's own account of the run */
      folds: Int, unfoldings: Int, unrolls: Int, generalizations: Int):
    def top: Space = residual.top
    def size: Int = SCStats.of(top).total + residual.routines.values.map(r => SCStats.of(r.body).total).sum
    def canonKey: String = canonResidual(residual)
    def laws: Vector[String] = (trace.nodes ++ nodeTraces.values.flatMap(_.nodes)).collect { case ProofTrace.Node.LawInstance(l, _, _, _, _) => l }.distinct.sorted
    def kinds: Vector[String] = (trace.nodes ++ nodeTraces.values.flatMap(_.nodes)).map(_.kind).distinct.sorted
    def certified: Boolean = certificate.values.forall(_.certified)
    def interval(b: Backend, c: EffortComponent): Ivl = certificate(b).component(c)
    def row: String =
      val cells = Backend.values.toVector.map(b => s"${b.slug}:" + EffortEvent.calibratedComponents.map(c => s"${c.toString.toLowerCase}=${interval(b, c).show}").mkString(","))
      Vector(id, provenance.map(_.show).mkString(" "), scope.show, size.toString, residual.routines.size.toString,
             s"folds=$folds unfold=$unfoldings unroll=$unrolls gen=$generalizations", if certified then "CERTIFIED" else "UNCERTIFIED",
             laws.mkString(","), cells.mkString(" ")).mkString("\t")

  /** why an alternative is not on the frontier */
  enum Pruned:
    case Merged(into: String)
    case Subsumed(by: String)
    case Widened(budget: Int)
    case Refused(why: String)
    def show: String = this match
      case Merged(i) => s"MERGED into $i: alpha-equivalent canonical residual under equal semantic and resource assumptions"
      case Subsumed(b) => s"SUBSUMED by $b: same residual, valid on fewer inputs"
      case Widened(n) => s"WIDENED: frontier budget $n exceeded, the largest residual dropped"
      case Refused(w) => s"REFUSED: $w"

  /** THE FRONTIER: what survived, and everything that did not with its reason. */
  final case class Frontier(alternatives: Vector[Alternative], pruned: Vector[(Alternative, Pruned)],
                            refused: Vector[(Vector[Provenance], String)], budget: Int, notes: Vector[String]):
    def apply(id: String): Alternative = alternatives.find(_.id == id).getOrElse(sys.error(s"no alternative $id"))
    def byProvenance(c: Choice): Vector[Alternative] = alternatives.filter(_.provenance.exists(_.choice == c))
    /** deterministic TSV: the alternatives, the pruned ones, the refused variants */
    def render: String =
      val sb = new StringBuilder
      sb ++= "# RESIDUAL ALTERNATIVES (tasks.md B1) — one row per alternative on the frontier; every column is\n"
      sb ++= "# derived from the residual, its trace and its certificate (no timings, no counters, no hashes of closures).\n"
      sb ++= s"# budget\t$budget\n"
      sb ++= "# id\tprovenance\tscope\tsize\troutines\tdriver\tcertified\tlaws\tintervals\n"
      for a <- alternatives.sortBy(_.id) do sb ++= "A\t" ++= a.row ++= "\n"
      for (a, why) <- pruned.sortBy(_._1.id) do sb ++= s"P\t${a.id}\t${a.provenance.map(_.show).mkString(" ")}\t${why.show}\n"
      for (pv, why) <- refused.sortBy(_._1.map(_.show).mkString) do sb ++= s"R\t${pv.map(_.show).mkString(" ")}\t$why\n"
      for n <- notes do sb ++= s"# $n\n"
      sb.result()
    /** trace serialization: every alternative's top trace and node traces, by id */
    def renderTraces: Map[String, String] =
      alternatives.map(a => a.id -> (a.trace.render + a.nodeTraces.toVector.sortBy(_._1.s).map((g, d) => s"\n## node ${g.s}\n" + d.render).mkString)).toMap

  // ------------------------------------------------------------------------------------------------
  // canonical identity
  // ------------------------------------------------------------------------------------------------

  /** the residual with its routine names replaced by their order of first appearance from the top, and
   *  every term alpha-canonical — the string two runs of the same program agree on */
  def canonResidual(res: Residual): String =
    val order = mutable.LinkedHashMap.empty[RoutinePtr, String]
    val queue = mutable.Queue.empty[RoutinePtr]
    def note(s: Space): Unit =
      for rp <- collect(s)({ case Space.Call(r, _, _) => r })._1.map(_._2) if res.routines.contains(rp) && !order.contains(rp) do
        order(rp) = s"#r${order.size}"; queue += rp
    note(res.top)
    while queue.nonEmpty do note(res.routines(queue.dequeue()).body)
    // routines unreachable from the top (none, in a residual the driver produced) come last, by name
    for rp <- res.routines.keys.toVector.sortBy(_.s) if !order.contains(rp) do order(rp) = s"#r${order.size}"
    def rename(s: Space): Space = subs(s)(spost = { case Space.Call(r, refs, ms) if order.contains(r) => Space.Call(RoutinePtr(order(r)), refs, ms) })
    val top = Matching.canon(rename(res.top)).toString
    val rs = order.toVector.map { (rp, nm) =>
      val r = res.routines(rp)
      s"$nm(${r.refs.map(_.s).mkString(",")};${r.mentions.map(_.s).mkString(",")})=${Matching.canon(rename(r.body)).toString}"
    }
    (top +: rs).mkString("\n")

  def digest(text: String): String =
    val md = java.security.MessageDigest.getInstance("SHA-256").digest(text.getBytes("UTF-8"))
    md.take(8).map(b => f"${b & 0xff}%02x").mkString

  /** a deterministic rendering of the resource assumptions (sorted, no Map iteration order) */
  def renderInputs(in: CostSem.Inputs): String =
    (in.values.toVector.sortBy(_._1.s).map((m, v) => s"${m.s}=${v.show}") ++
     in.summaries.toVector.sortBy(_._1.s).map((m, t) => s"${m.s}:${t.toString}") ++
     in.paths.toVector.sortBy(_._1.s).map((p, v) => s"${p.s}=${v.show}") ++
     in.pathLens.toVector.sortBy(_._1.s).map((p, k) => s"${p.s}:[${k.lo},${k.hi}]")).mkString(";")

  // ------------------------------------------------------------------------------------------------
  // the frontier builder: hash-consing, subsumption, widening
  // ------------------------------------------------------------------------------------------------

  final class Builder(val budget: Int):
    private val alts = mutable.ArrayBuffer.empty[Alternative]
    private val pruned = mutable.ArrayBuffer.empty[(Alternative, Pruned)]
    private val refused = mutable.ArrayBuffer.empty[(Vector[Provenance], String)]
    private val notes = mutable.ArrayBuffer.empty[String]
    private val byKey = mutable.Map.empty[String, mutable.ArrayBuffer[Alternative]]

    def refuse(pv: Vector[Provenance], why: String): Unit = refused += ((pv, why))

    /** compatible: the same resource assumptions and the same semantic scope */
    private def compatible(a: Alternative, b: Alternative): Boolean = a.assumptions == b.assumptions && a.scope == b.scope
    private def subsumes(a: Alternative, b: Alternative): Boolean =
      a.assumptions == b.assumptions && a.scope == FactScope.Unconditional && b.scope != FactScope.Unconditional

    /** add an alternative; returns the id it is represented by on the frontier (its own or the one it
     *  merged into), or None when it was subsumed */
    def add(a: Alternative): Option[String] =
      val key = a.canonKey
      val same = byKey.getOrElseUpdate(key, mutable.ArrayBuffer.empty)
      same.find(o => compatible(o, a)) match
        case Some(o) => pruned += ((a, Pruned.Merged(o.id))); Some(o.id)
        case None =>
          same.find(o => subsumes(o, a)) match
            case Some(o) => pruned += ((a, Pruned.Subsumed(o.id))); None
            case None =>
              // the new one may subsume existing conditional twins
              for o <- same.toVector if subsumes(a, o) do
                same -= o; alts -= o; pruned += ((o, Pruned.Subsumed(a.id)))
              if same.nonEmpty then notes += s"${a.id} and ${same.map(_.id).mkString(",")} are the same residual under different assumptions: both kept"
              same += a; alts += a
              widen()
              Some(a.id)

    private def widen(): Unit =
      while alts.length > budget do
        val victim = alts.maxBy(x => (x.size, x.id))
        alts -= victim; byKey.get(victim.canonKey).foreach(_ -= victim)
        pruned += ((victim, Pruned.Widened(budget)))

    def result: Frontier = Frontier(alts.toVector.sortBy(_.id), pruned.toVector, refused.toVector, budget, notes.toVector)

  // ------------------------------------------------------------------------------------------------
  // exploration
  // ------------------------------------------------------------------------------------------------

  final case class Options(
      /** unfold-before-fold depths to try, on top of the fold-first driver */
      unrolls: Vector[Int] = Vector(1),
      /** the law families to switch off, one at a time */
      families: Vector[Family] = Alternatives.families,
      /** also try every PAIR of disabled families */
      pairs: Boolean = true,
      /** never drive with a GROUND law: the exploration is evaluation-free */
      groundFree: Boolean = true,
      budget: Int = 32,
      sc: SC.Config = SC.Config())

  /** price a residual over the inputs, per backend; the residual's own routine table answers its calls */
  def certify(res: Residual, refs: Vector[PathRef], mentions: Vector[SpaceMention], inputs: CostSem.Inputs): Map[Backend, CostReport] =
    val r = Routine(RoutinePtr("#alternative"), refs, mentions, res.top)
    Backend.values.iterator.map(b => b -> SpatialPipeline.priceInputs(r, inputs, res.routines, b)).toMap

  /** one driven variant → an alternative (or the reason it was refused) */
  def variant(conf: Space, defs: PartialFunction[RoutinePtr, Routine], inputs: CostSem.Inputs,
              cfg: SC.Config, provenance: Vector[Provenance]): Either[String, Alternative] =
    val (refs, ments) = (Matching.freeRefsV(conf), Matching.freeMentionsV(conf))
    try
      val (res, st, _) = SC.run(conf, defs, cfg.copy(trace = true))
      if !st.converged then Left("compile budget exceeded: the driver fell back to the original program")
      else
        val top = st.topTraceDag.getOrElse(return Left("no top trace was recorded"))
        val nodeTraces = st.traces.toVector.map((g, tid) => g -> st.traceBuilder.dag(tid)).toMap
        val cert = certify(res, refs, ments, inputs)
        val key = canonResidual(res)
        val id = digest(key + "\n@" + renderInputs(inputs))
        Right(Alternative(id, res, refs, ments, top, nodeTraces, st.nodeTable, FactScope.Unconditional, inputs, cert, provenance,
                          st.folds, st.unfoldings, st.unrolls, st.generalizations))
    catch case scala.util.control.NonFatal(e) => Left(s"${e.getClass.getSimpleName}: ${Option(e.getMessage).getOrElse("").take(200)}")

  /** THE EXPLORATION: the fold-first driver over every law table, then the unrolled drivers */
  def explore(conf: Space, defs: PartialFunction[RoutinePtr, Routine], inputs: CostSem.Inputs,
              opts: Options = Options()): Frontier =
    val b = new Builder(opts.budget)
    val ground = if opts.groundFree then SC.groundLaws else Set.empty[String]
    val tables: Vector[(Vector[Provenance], Set[String])] =
      Vector((Vector(Provenance(Choice.Fold, "fold-first driver, every law")), Set.empty[String])) ++
      opts.families.map(f => (Vector(Provenance(f.choice, s"disabled ${f.laws.toVector.sorted.mkString(",")}")), f.laws)) ++
      (if opts.pairs then
         for i <- opts.families.indices.toVector; j <- (i + 1) until opts.families.length yield
           val (f, g) = (opts.families(i), opts.families(j))
           (Vector(Provenance(f.choice, s"disabled ${f.laws.toVector.sorted.mkString(",")}"), Provenance(g.choice, s"disabled ${g.laws.toVector.sorted.mkString(",")}")), f.laws ++ g.laws)
       else Vector.empty)
    val unrolls = Vector(0) ++ opts.unrolls.filter(_ > 0).distinct.sorted
    for (pv0, off) <- tables; u <- unrolls do
      val pv = if u == 0 then pv0 else pv0 :+ Provenance(Choice.Unfold, s"unrolled $u time(s) before each fold")
      val cfg = opts.sc.copy(laws = SC.lawsWithout(ground ++ off), unroll = u)
      variant(conf, defs, inputs, cfg, pv) match
        case Right(a) => b.add(a)
        case Left(why) => b.refuse(pv, why)
    b.result

  /** the alternatives of a routine called on its own parameters */
  def exploreRoutine(r: Routine, defs: PartialFunction[RoutinePtr, Routine], inputs: CostSem.Inputs,
                     opts: Options = Options()): Frontier =
    explore(Space.Call(r.name, r.refs.map(Path.Deref(_)), r.mentions.map(Space.Mention(_))), defs, inputs, opts)
