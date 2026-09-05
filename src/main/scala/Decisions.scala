package morkl

import scala.collection.mutable

/** ==============================================================================================
 *  DECISION CASES: choices a scalar estimator cannot make safely.
 *
 *  A decision case is one symbolic program with a stated input PRECONDITION, explored into its
 *  residual alternatives (B1), selected from under a declared objective (B2), and then RUN: every
 *  alternative's counted resources on every executor are recorded next to the predicted intervals.
 *  Beside the certified choice, two SCALAR predictors are evaluated on the same frontier — the two an
 *  ordinary optimizer has:
 *
 *   - LOCAL REWRITE COUNT: prefer the residual with the fewest nodes, ties to the one more law steps
 *     produced (the "smaller program after more rewrites is the better program" heuristic);
 *   - OUTPUT CARDINALITY: prefer the residual whose result has fewer paths — which, over semantically
 *     equivalent alternatives, is EVERY alternative: the predictor cannot separate them and falls back
 *     to the first by id.  It is here because a cardinality estimator is what "cost-based" optimizers
 *     usually mean, and the point of this file is that equal cardinality says nothing about cost.
 *
 *  A case is DIFFERENTIATED when the scalar predictor's winner is not the certified choice and the
 *  counted run confirms the certified choice: its counted value of the objective's component is at most
 *  the scalar winner's.  A case whose certified choice coincides with the scalar one is recorded as
 *  AGREES — that is a result too, and the acceptance asks for at least one differentiated case per
 *  transformation family, not for every case to differentiate.
 *
 *  Every number in the generated tables is either an interval of a certificate, a counted event total,
 *  or a node count; nothing is timed.  `docs/DECISIONS.md` and the `proofs/decisions` certificates are generated
 *  by `DecisionsCheck` through `ArtifactSink` (regenerate under ZIPPY_REGENERATE=1, verify otherwise).
 *  ============================================================================================== */
object Decisions:

  /** one decision case: the program, its precondition, the concrete inputs the counted run uses */
  final case class Case(
      name: String,
      /** the transformation family  names */
      family: String,
      /** the symbolic input precondition, as a sentence a reader can check against `values` */
      precondition: String,
      routine: Routine,
      defs: PartialFunction[RoutinePtr, Routine],
      values: Map[SpaceMention, SpaceValue],
      objective: Pareto.Objective,
      opts: Alternatives.Options = Alternatives.Options(),
      /** what the case is about, one paragraph for the document */
      story: String)

  /** the counted run of one residual on one backend; None when the backend cannot run it */
  def counted(res: Residual, backend: Backend, values: Map[SpaceMention, SpaceValue]): Option[Events] =
    val pc = PathContextMap(Map.empty); val sc = SpaceContextMap(values); val rc = res.env
    // the input tries are built BEFORE the counted region (building them is not the program's work), and
    // every executor runs once uncounted first so interning is not charged to the run — the same
    // discipline as the gate suites' `counted`
    val ic = values.map((m, v) => m -> ITrie.fromSpaceValue(v))
    try backend match
      case Backend.Reference => eval(res.top)(using pc, sc, rc); Some(EffortSink.events(eval(res.top)(using pc, sc, rc)))
      case Backend.Trie => evalI(res.top)(using pc, ic, rc); Some(EffortSink.events(evalI(res.top)(using pc, ic, rc)))
      case Backend.Zipper => execZ(res.top)(using pc, ic, rc); Some(EffortSink.events(execZ(res.top)(using pc, ic, rc)))
      case Backend.Graph =>
        // the operation-graph executor has no stabilised-argument Call rule: a routine that reaches itself is
        // run only through the IR's fixpoint lowering (the pipeline's graph cells), not here — not counted
        def reaches(from: RoutinePtr, seen: Set[RoutinePtr]): Boolean =
          res.routines.get(from).exists { rt =>
            val callees = collect(rt.body)({ case Space.Call(q, _, _) => q })._1.map(_._2).toSet
            callees.contains(from) || callees.exists(q => !seen(q) && reaches(q, seen + q))
          }
        val tops = collect(res.top)({ case Space.Call(q, _, _) => q })._1.map(_._2).toSet
        if tops.exists(q => reaches(q, Set(q))) then return None
        val r = Routine(RoutinePtr("#decision"), Vector.empty, values.keys.toVector.sortBy(_.s), res.top)
        val g = morkl.optimize(transpile(r))
        val memo = mutable.HashMap.empty[String, Option[RecursiveOpGraph]]
        val index: PartialFunction[String, RecursiveOpGraph] = new PartialFunction[String, RecursiveOpGraph]:
          private def get(n: String) = memo.getOrElseUpdate(n, res.routines.get(RoutinePtr(n)).flatMap(rt => try Some(transpile(rt)) catch case scala.util.control.NonFatal(_) => None))
          def isDefinedAt(n: String) = get(n).isDefined
          def apply(n: String) = get(n).get
        val ments = ic.map((k, v) => k.s -> v)
        runGraphT(g, Map.empty, ments, index)
        Some(EffortSink.events(runGraphT(g, Map.empty, ments, index)))
    catch case scala.util.control.NonFatal(_) => None

  /** a scalar predictor's verdict on a frontier */
  final case class ScalarVerdict(name: String, winner: String, why: String)

  def rewriteCountWinner(f: Alternatives.Frontier): ScalarVerdict =
    val laws = (a: Alternatives.Alternative) => (a.trace.nodes ++ a.nodeTraces.values.flatMap(_.nodes)).count(_.kind == "LawInstance")
    val w = f.alternatives.minBy(a => (a.size, -laws(a), a.id))
    ScalarVerdict("rewrite-count", w.id, s"fewest residual nodes (${w.size}), then most law steps (${laws(w)})")

  def cardinalityWinner(f: Alternatives.Frontier, values: Map[SpaceMention, SpaceValue]): ScalarVerdict =
    val card = f.alternatives.map(a => a.id -> eval(a.top)(using PathContextMap(Map.empty), SpaceContextMap(values), a.residual.env).paths.size).toMap
    val w = f.alternatives.minBy(a => (card(a.id), a.id))
    val distinct = card.values.toSet.size
    ScalarVerdict("output-cardinality", w.id, if distinct == 1 then s"every alternative yields ${card(w.id)} paths: the predictor cannot separate them, first by id" else s"fewest output paths (${card(w.id)})")

  /** THE RESULT OF ONE CASE */
  final case class Outcome(c: Case, frontier: Alternatives.Frontier, selection: Pareto.Selection,
                           counted: Map[(String, Backend), Events], scalar: Vector[ScalarVerdict]):
    def selected: Pareto.Candidate = selection.selected.getOrElse(sys.error(s"${c.name}: nothing selected"))
    def component: EffortComponent = c.objective.priority.head
    def alt(id: String): Alternatives.Alternative = frontier(id)
    def countedOf(id: String, b: Backend): Option[Long] = counted.get((id, b)).map(_.component(component))
    /** the selected candidate's counted value lies in its predicted interval on every component */
    def contained: Vector[String] =
      counted.get((selected.alt, selected.backend)).toVector.flatMap(ev => alt(selected.alt).certificate(selected.backend).bounds.violations(ev))
    /** a scalar predictor's winner on the SELECTED backend, compared by the counted objective component */
    def verdictOn(v: ScalarVerdict): (String, Option[Long], Option[Long]) =
      val mine = countedOf(selected.alt, selected.backend); val theirs = countedOf(v.winner, selected.backend)
      val tag =
        if v.winner == selected.alt then "AGREES"
        else (mine, theirs) match
          case (Some(m), Some(t)) if m <= t => "DIFFERENTIATED"
          case (Some(m), Some(t)) => "CONTRADICTED"
          case _ => "UNCOUNTED"
      (tag, mine, theirs)
    def differentiated: Boolean = scalar.exists(v => verdictOn(v)._1 == "DIFFERENTIATED")

    /** one row of proofs/decisions/DECISIONS.tsv */
    def row: String =
      val sel = selected
      val iv = alt(sel.alt).certificate(sel.backend).component(component)
      val cnt = countedOf(sel.alt, sel.backend).map(_.toString).getOrElse("-")
      val sv = scalar.map { v => val (tag, _, t) = verdictOn(v); s"${v.name}=${v.winner}:${tag}:${t.map(_.toString).getOrElse("-")}" }.mkString(";")
      Vector(c.name, c.family, c.precondition, c.objective.name, frontier.alternatives.length.toString, s"${sel.alt}/${sel.backend.slug}",
             Pareto.slug(component), iv.show, cnt, sv, if differentiated then "DIFFERENTIATED" else "AGREES").mkString("\t")

    /** the section of docs/DECISIONS.md */
    def markdown: String =
      val sb = new StringBuilder
      val sel = selected
      sb ++= s"### ${c.name} — ${c.family}\n\n"
      sb ++= c.story ++= "\n\n"
      sb ++= s"**Precondition.** ${c.precondition}\n\n"
      sb ++= s"**Objective.** ${c.objective.show}.\n\n"
      sb ++= s"**Program.** `${c.routine.body.show.replace("\n", " ").replaceAll("\\s+", " ").take(400)}`\n\n"
      sb ++= s"**Alternatives.** ${frontier.alternatives.length} on the frontier (${frontier.pruned.length} pruned, ${frontier.refused.length} refused); every trace closed, every certificate certified.\n\n"
      sb ++= "| alternative | provenance | nodes | laws in trace | " + Backend.values.map(b => s"${b.slug} ${Pareto.slug(component)} predicted | counted").mkString(" | ") + " |\n"
      sb ++= "|---|---|---|---|" + Backend.values.map(_ => "---|---").mkString("|") + "|\n"
      for a <- frontier.alternatives.sortBy(_.id) do
        val cells = Backend.values.toVector.map { b =>
          val iv = a.certificate(b).component(component)
          val cnt = countedOf(a.id, b).map(_.toString).getOrElse("—")
          val mark = if a.id == sel.alt && b == sel.backend then " **selected**" else ""
          s"${iv.show}$mark | $cnt"
        }
        sb ++= s"| `${a.id}` | ${a.provenance.map(_.show).mkString("<br>")} | ${a.size} | ${a.laws.mkString(", ")} | ${cells.mkString(" | ")} |\n"
      sb ++= "\n"
      sb ++= s"**Selected.** `${sel.key}`: predicted ${Pareto.slug(component)} ${alt(sel.alt).certificate(sel.backend).component(component).show}, counted ${countedOf(sel.alt, sel.backend).map(_.toString).getOrElse("—")}"
      sb ++= (if contained.isEmpty then "; the counted run lies inside every predicted component.\n\n" else s"; VIOLATIONS: ${contained.mkString("; ")}\n\n")
      sb ++= s"**Rejections.** ${selection.rejected.length} (${selection.rejected.count(_._2.isInstanceOf[Pareto.Rejection.Dominated])} dominated); ${selection.kept.length} incomparable survivors kept. Certificate: `proofs/decisions/${c.name}-${c.objective.name}.tsv`.\n\n"
      sb ++= "**Scalar predictors on the same frontier.**\n\n| predictor | its winner | why | counted " + Pareto.slug(component) + s" on ${sel.backend.slug} (winner / selected) | verdict |\n|---|---|---|---|---|\n"
      for v <- scalar do
        val (tag, mine, theirs) = verdictOn(v)
        sb ++= s"| ${v.name} | `${v.winner}` | ${v.why} | ${theirs.map(_.toString).getOrElse("—")} / ${mine.map(_.toString).getOrElse("—")} | **$tag** |\n"
      sb ++= "\n"
      sb ++= "**Traces.** " + frontier.alternatives.sortBy(_.id).map(a => s"`${a.id}`: ${a.kinds.mkString("/")} (${a.trace.size} nodes)").mkString("; ") + ".\n\n"
      sb.result()

  def run(c: Case): Outcome =
    val inputs = CostSem.Inputs(values = c.values)
    val f = Alternatives.exploreRoutine(c.routine, c.defs, inputs, c.opts)
    val sel = Pareto.select(f, c.objective)
    val counted = (for a <- f.alternatives; b <- Backend.values.toVector; ev <- Decisions.counted(a.residual, b, c.values) yield (a.id, b) -> ev).toMap
    Outcome(c, f, sel, counted, Vector(rewriteCountWinner(f), cardinalityWinner(f, c.values)))

  val indexHeader: String =
    "# DECISION CASES — one row per case; generated by DecisionsCheck, replayed by scripts/check_selection.py\n" +
    "# case\tfamily\tprecondition\tobjective\talternatives\tselected\tcomponent\tpredicted\tcounted\tscalar-predictors(name=winner:verdict:counted)\tverdict\n"

  def document(outcomes: Vector[Outcome]): String =
    val sb = new StringBuilder
    sb ++= "# Decisions the certified frontier makes and a scalar estimator cannot\n\n"
    sb ++= "<!-- GENERATED by `ZIPPY_REGENERATE=1 sbt --server 'testOnly morkl.DecisionsCheck'`; a verify run fails on drift. -->\n\n"
    sb ++= "Every case below is one symbolic program under a stated input precondition. Its residual alternatives are\n"
    sb ++= "produced by the supercompiler under several law tables and unroll depths (`Alternatives`), each\n"
    sb ++= "with a typed proof trace that has CLOSED (every law step certified, every unfold/fold mechanized) and a\n"
    sb ++= "resource certificate per backend (`CostSem`). The choice is made by `Pareto.select`: admission,\n"
    sb ++= "constraints proved by the upper bound, dominance over interval-valued work/alloc/rounds/touch, and the declared\n"
    sb ++= "tie rule among incomparable survivors. Every alternative is then RUN on every executor that can run it and the\n"
    sb ++= "counted events are printed next to the predicted intervals. Two scalar predictors — fewest residual nodes after\n"
    sb ++= "the most rewrites, and output cardinality — are evaluated on the same frontier; a case is DIFFERENTIATED when a\n"
    sb ++= "scalar predictor names a different winner and the counted run confirms the certified choice.\n\n"
    sb ++= "Nothing here is timed; no measured performance enters a choice. The machine-readable form is\n"
    sb ++= "`proofs/decisions/DECISIONS.tsv` plus one selection certificate per case, each replayed independently by\n"
    sb ++= "`scripts/check_selection.py`.\n\n"
    sb ++= "## Summary\n\n| case | family | objective | alternatives | selected | predicted | counted | verdict |\n|---|---|---|---|---|---|---|---|\n"
    for o <- outcomes do
      val sel = o.selected
      sb ++= s"| ${o.c.name} | ${o.c.family} | ${o.c.objective.name} | ${o.frontier.alternatives.length} | `${sel.key}` | ${o.alt(sel.alt).certificate(sel.backend).component(o.component).show} | ${o.countedOf(sel.alt, sel.backend).map(_.toString).getOrElse("—")} | ${if o.differentiated then "DIFFERENTIATED" else "AGREES"} |\n"
    sb ++= "\n## Cases\n\n"
    for o <- outcomes do sb ++= o.markdown
    sb ++= "## What a case does not show\n\n"
    sb ++= "The trie, zipper and graph intervals are the must/may envelopes of the abstract interpretation; they are\n"
    sb ++= "sound and often wide, so dominance across backends is rarely provable and the tie rule (least upper bound) decides\n"
    sb ++= "among incomparable survivors — the certificate says which survivors overlap the selected one. The reference\n"
    sb ++= "evaluator's `touch` has no counted oracle and is never compared. A case marked AGREES is one where the scalar\n"
    sb ++= "predictor happened to name the certified choice; it is recorded, not hidden.\n"
    sb.result()
