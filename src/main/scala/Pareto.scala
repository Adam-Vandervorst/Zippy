package morkl

import scala.collection.mutable

/** ==============================================================================================
 *  SELECTION FROM A CERTIFIED PARETO FRONTIER (tasks.md B2).
 *
 *  A [[Alternatives.Frontier]] holds semantically equivalent residuals with interval-valued resource
 *  certificates per backend.  This module CHOOSES among them — and the whole point is what a choice
 *  is allowed to rest on:
 *
 *   - ADMISSION.  A candidate (alternative × backend) enters the certified frontier only when its
 *     spatial derivation is certified (every A6 transfer rule it used is PROVED or a stated premise —
 *     `CostReport.certified`) AND its semantic trace has closed (`TraceClosure`: every law step has a
 *     PROVED certificate, every unfold/fold rests on a MECHANIZED registry entry).  Anything else is
 *     rejected as NOT-ADMITTED with the reason, never silently priced.
 *   - CONSTRAINTS.  `component ≤ cap` is satisfied only when the UPPER bound proves it; a candidate
 *     whose lower bound already exceeds the cap is INFEASIBLE, one whose interval straddles the cap is
 *     UNPROVEN — both rejected, both with the numbers.
 *   - DOMINANCE over interval-valued `Work`, `Alloc`, `Rounds`, `Touch`: `x` dominates `y` iff on every
 *     dominance component `x.hi ≤ y.lo`, on at least one `x.hi < y.lo`, and no `x.hi` is infinite.
 *     Overlapping intervals are INCOMPARABLE — a result, not a failure; a widened or unbounded upper
 *     bound can never be used to win (it is sound, so it may still lose).  The reference evaluator's
 *     `touch` is a model with no counted oracle: it is taken as `[0, inf]`, so the reference can neither
 *     win nor be beaten on `touch`.
 *   - SELECTION among the incomparable survivors is by the objective's DECLARED tie rule — the
 *     lexicographic order of (upper, lower) bounds over the objective's priority components, then the
 *     alternative id, then the backend — and the certificate says so: a survivor ranked below the
 *     selected one is KEPT and reported with the components on which it overlaps.  Nothing measured
 *     enters: the API takes no timings, and the certificate is a pure function of the intervals.
 *
 *  Every removal is a row of the [[Selection]] certificate with the numbers that justify it, and
 *  `scripts/check_selection.py` recomputes the whole decision from the candidate rows alone.
 *  ============================================================================================== */
object Pareto:

  final case class Constraint(component: EffortComponent, cap: Long):
    def show: String = s"${slug(component)}<=$cap"

  /** WHAT THE CALLER IS PAYING FOR. */
  final case class Objective(
      name: String,
      /** the priority order the tie rule ranks by (first component first) */
      priority: Vector[EffortComponent],
      /** the components dominance is decided over (default: all four calibrated components) */
      dominance: Vector[EffortComponent] = EffortEvent.calibratedComponents,
      constraints: Vector[Constraint] = Vector.empty,
      /** the backends the caller can run */
      backends: Vector[Backend] = Backend.values.toVector):
    def show: String = s"$name: minimise ${priority.map(slug).mkString(" then ")}" +
      (if constraints.isEmpty then "" else s" subject to ${constraints.map(_.show).mkString(",")}") +
      s" over ${backends.map(_.slug).mkString(",")}"
  object Objective:
    def minimise(c: EffortComponent, backends: Vector[Backend] = Backend.values.toVector): Objective =
      Objective(slug(c), Vector(c) ++ EffortEvent.calibratedComponents.filterNot(_ == c), backends = backends)

  def slug(c: EffortComponent): String = c.toString.toLowerCase
  def component(s: String): EffortComponent = EffortEvent.calibratedComponents.find(c => slug(c) == s).getOrElse(sys.error(s"no component $s"))
  private def n(x: Long): String = if x >= Ivl.INF then "inf" else x.toString

  /** one alternative on one backend, with its EFFECTIVE bounds (the reference's `touch` unknown) */
  final case class Candidate(alt: String, backend: Backend, bounds: Map[EffortComponent, Ivl], certified: Boolean, closure: TraceClosure.Status):
    def key: String = s"$alt/${backend.slug}"
    def lo(c: EffortComponent): Long = bounds(c).lo
    def hi(c: EffortComponent): Long = bounds(c).hi
    def admitted: Boolean = certified && closure.closed
    /** the components this backend has NO counted oracle for (the reference's `touch`): unknown, [0, inf] */
    def unknown: Set[EffortComponent] = if backend == Backend.Reference then Set(EffortComponent.Touch) else Set.empty
    def row: String = (Vector("C", alt, backend.slug) ++ EffortEvent.calibratedComponents.flatMap(c => Vector(n(lo(c)), n(hi(c)))) ++
                       Vector(if certified then "CERTIFIED" else "UNCERTIFIED", closure.render)).mkString("\t")
  object Candidate:
    def of(a: Alternatives.Alternative, b: Backend): Candidate =
      val rep = a.certificate(b)
      val bounds = EffortEvent.calibratedComponents.map { c =>
        val i = rep.component(c)
        c -> (if b == Backend.Reference && c == EffortComponent.Touch then Ivl(0, Ivl.INF) else i)
      }.toMap
      Candidate(a.id, b, bounds, rep.certified, TraceClosure.of(a.trace +: a.nodeTraces.values.toVector))
    /** deterministic order: alternative id, then backend */
    given Ordering[Candidate] = Ordering.by(c => (c.alt, c.backend.ordinal))

  enum Rejection:
    case NotAdmitted(why: String)
    case Infeasible(c: EffortComponent, lo: Long, cap: Long)
    case Unproven(c: EffortComponent, hi: Long, cap: Long)
    case Dominated(by: Candidate, evidence: Vector[(EffortComponent, Long, Long)])
    def kind: String = this match
      case _: NotAdmitted => "NOT-ADMITTED"; case _: Infeasible => "INFEASIBLE"; case _: Unproven => "UNPROVEN"; case _: Dominated => "DOMINATED"
    def detail: String = this match
      case NotAdmitted(w) => w
      case Infeasible(c, lo, cap) => s"${slug(c)} lo=${n(lo)} > cap=$cap"
      case Unproven(c, hi, cap) => s"${slug(c)} hi=${n(hi)} > cap=$cap"
      case Dominated(by, ev) => s"by ${by.key}: " + ev.map((c, xhi, ylo) => s"${slug(c)} ${n(xhi)}<=${n(ylo)}").mkString(" ")

  /** THE SELECTION CERTIFICATE. */
  final case class Selection(objective: Objective, candidates: Vector[Candidate], rejected: Vector[(Candidate, Rejection)],
                             selected: Option[Candidate], kept: Vector[(Candidate, Vector[EffortComponent])]):
    def survivors: Vector[Candidate] = selected.toVector ++ kept.map(_._1)
    /** the trusted-base entries the selected candidate's trace rests on (empty when CLOSED) */
    def restsOn: Set[String] = selected.map(_.closure).collect { case TraceClosure.Status.Conditional(t) => t }.getOrElse(Set.empty)
    def render: String =
      val sb = new StringBuilder
      sb ++= "# SELECTION CERTIFICATE (tasks.md B2) — a pure function of the C rows and the objective; replay:\n"
      sb ++= "# scripts/check_selection.py (independent), morkl.Pareto.replay (in-process).\n"
      sb ++= s"# objective\t${objective.name}\n"
      sb ++= s"# priority\t${objective.priority.map(slug).mkString(",")}\n"
      sb ++= s"# dominance\t${objective.dominance.map(slug).mkString(",")}\n"
      sb ++= s"# constraints\t${if objective.constraints.isEmpty then "-" else objective.constraints.map(_.show).mkString(",")}\n"
      sb ++= s"# backends\t${objective.backends.map(_.slug).mkString(",")}\n"
      sb ++= "# tie-rule\tlexicographic (hi, lo) over the priority components, then alternative id, then backend order reference,trie,graph,zipper\n"
      sb ++= "# reference-touch\tmodelled, no counted oracle: taken as [0, inf]; not compared between two reference candidates\n"
      sb ++= ("# columns\tC\talt\tbackend\t" + EffortEvent.calibratedComponents.flatMap(c => Vector(s"${slug(c)}.lo", s"${slug(c)}.hi")).mkString("\t") + "\tcertified\tclosure\n")
      for c <- candidates.sorted do sb ++= c.row ++= "\n"
      for (c, r) <- rejected.sortBy(_._1) do sb ++= s"X\t${c.alt}\t${c.backend.slug}\t${r.kind}\t${r.detail}\n"
      for s <- selected do sb ++= s"S\t${s.alt}\t${s.backend.slug}\t${if kept.isEmpty then "unique survivor" else "ranked first by the tie rule among " + (kept.length + 1) + " incomparable survivors"}\n"
      for (c, ov) <- kept.sortBy(_._1) do sb ++= s"K\t${c.alt}\t${c.backend.slug}\tINCOMPARABLE with the selected: overlaps on ${ov.map(slug).mkString(",")}\n"
      sb.result()
    def report: String =
      val lines = Vector.newBuilder[String]
      lines += s"objective ${objective.show}"
      selected match
        case Some(s) => lines += s"  SELECTED ${s.key}  " + EffortEvent.calibratedComponents.map(c => s"${slug(c)}=${s.bounds(c).show}").mkString(" ") + (if restsOn.nonEmpty then s"  (rests on ${restsOn.toVector.sorted.mkString(",")})" else "")
        case None => lines += "  NOTHING SELECTED: no candidate is admitted and feasible"
      for (c, ov) <- kept do lines += s"  kept ${c.key}: incomparable (overlaps on ${ov.map(slug).mkString(",")})"
      for (c, r) <- rejected do lines += s"  rejected ${c.key}: ${r.kind} ${r.detail}"
      lines.result().mkString("\n")

  /** x dominates y on the components: every upper of x at or below the lower of y, one strictly, none infinite */
  def dominates(x: Candidate, y: Candidate, comps0: Vector[EffortComponent]): Option[Vector[(EffortComponent, Long, Long)]] =
    if x.key == y.key then None
    else
      // a component neither backend counts (both unknown) is not compared: two reference candidates are
      // decided on work/alloc/rounds; across backends an unknown side is [0, inf] and blocks both directions
      val comps = comps0.filterNot(c => x.unknown(c) && y.unknown(c))
      val ev = comps.map(c => (c, x.hi(c), y.lo(c)))
      if ev.forall((_, xhi, ylo) => xhi < Ivl.INF && xhi <= ylo) && ev.exists((_, xhi, ylo) => xhi < ylo) then Some(ev) else None

  def overlaps(x: Candidate, y: Candidate, comps: Vector[EffortComponent]): Vector[EffortComponent] =
    comps.filter(c => !(x.hi(c) < y.lo(c) || y.hi(c) < x.lo(c)))

  /** the tie rule: (hi, lo) per priority component, then id, then backend */
  def rank(o: Objective)(c: Candidate): (Vector[Long], String, Int) = (o.priority.flatMap(k => Vector(c.hi(k), c.lo(k))), c.alt, c.backend.ordinal)
  given Ordering[Vector[Long]] = (a, b) =>
    val n = a.length min b.length
    var i = 0; var r = 0
    while i < n && r == 0 do { r = java.lang.Long.compare(a(i), b(i)); i += 1 }
    if r != 0 then r else Integer.compare(a.length, b.length)

  /** THE DECISION over already-built candidates — the function `replay` re-runs on a parsed certificate */
  def decide(o: Objective, candidates: Vector[Candidate]): Selection =
    val sorted = candidates.sorted
    val rejected = Vector.newBuilder[(Candidate, Rejection)]
    // 1. admission
    val admitted = sorted.filter { c =>
      if c.admitted then true
      else
        val why = (if !c.certified then Vector("spatial derivation not certified (an A6 rule is OPEN or the status table is absent)") else Vector.empty) ++
                  (c.closure match { case TraceClosure.Status.Open(rs) => Vector("trace closure OPEN: " + rs.mkString("; ")); case _ => Vector.empty })
        rejected += ((c, Rejection.NotAdmitted(why.mkString("; ")))); false
    }
    // 2. constraints: proved by the upper bound, or rejected
    val feasible = admitted.filter { c =>
      o.constraints.iterator.map { k =>
        if c.lo(k.component) > k.cap then Some(Rejection.Infeasible(k.component, c.lo(k.component), k.cap))
        else if c.hi(k.component) > k.cap then Some(Rejection.Unproven(k.component, c.hi(k.component), k.cap))
        else None
      }.collectFirst { case Some(r) => r } match
        case Some(r) => rejected += ((c, r)); false
        case None => true
    }
    // 3. dominance: the first dominator in candidate order is the recorded winner
    val survivors = feasible.filter { y =>
      feasible.iterator.map(x => dominates(x, y, o.dominance).map(ev => (x, ev))).collectFirst { case Some(p) => p } match
        case Some((x, ev)) => rejected += ((y, Rejection.Dominated(x, ev))); false
        case None => true
    }
    // 4. the tie rule
    val ranked = survivors.sortBy(rank(o))(Ordering.Tuple3(summon[Ordering[Vector[Long]]], Ordering.String, Ordering.Int))
    val selected = ranked.headOption
    val kept = ranked.drop(1).map(c => c -> overlaps(selected.get, c, o.dominance))
    Selection(o, sorted, rejected.result(), selected, kept)

  /** select from a frontier under an objective */
  def select(f: Alternatives.Frontier, o: Objective): Selection =
    decide(o, for a <- f.alternatives; b <- o.backends yield Candidate.of(a, b))

  // ------------------------------------------------------------------------------------------------
  // replay: parse a rendered certificate and re-decide; the differences are the failures
  // ------------------------------------------------------------------------------------------------

  def parse(text: String): (Objective, Vector[Candidate], Vector[String], Option[String], Vector[String]) =
    val hdr = mutable.Map.empty[String, String]
    val cands = Vector.newBuilder[Candidate]; val xs = Vector.newBuilder[String]; var sel: Option[String] = None; val ks = Vector.newBuilder[String]
    for line <- text.linesIterator if line.nonEmpty do
      val cols = line.split("\t", -1).toVector
      if line.startsWith("# ") && cols.length >= 2 then hdr(cols(0).stripPrefix("# ")) = cols(1)
      else cols(0) match
        case "C" =>
          val bs = EffortEvent.calibratedComponents.zipWithIndex.map((c, i) => c -> Ivl(num(cols(3 + 2 * i)), num(cols(4 + 2 * i)))).toMap
          val cl = cols(12) match
            case "CLOSED" => TraceClosure.Status.Closed
            case s if s.startsWith("CONDITIONAL:") => TraceClosure.Status.Conditional(s.stripPrefix("CONDITIONAL:").split(",").toSet)
            case s => TraceClosure.Status.Open(Vector(s.stripPrefix("OPEN:")))
          cands += Candidate(cols(1), Backend.values.find(_.slug == cols(2)).get, bs, cols(11) == "CERTIFIED", cl)
        case "X" => xs += line
        case "S" => sel = Some(s"${cols(1)}/${cols(2)}")
        case "K" => ks += line
        case _ => ()
    val cons = hdr("constraints") match
      case "-" => Vector.empty
      case s => s.split(",").toVector.map { k => val Array(c, cap) = k.split("<="); Constraint(component(c), cap.toLong) }
    val o = Objective(hdr("objective"), hdr("priority").split(",").toVector.map(component), hdr("dominance").split(",").toVector.map(component), cons,
                      hdr("backends").split(",").toVector.map(s => Backend.values.find(_.slug == s).get))
    (o, cands.result(), xs.result(), sel, ks.result())
  private def num(s: String): Long = if s == "inf" then Ivl.INF else s.toLong

  /** re-decide from the certificate's own rows; empty = the certificate is exactly what the rows imply */
  def replay(text: String): Vector[String] =
    val (o, cands, xs, sel, ks) = parse(text)
    val again = decide(o, cands)
    val bad = Vector.newBuilder[String]
    val rx = again.rejected.sortBy(_._1).map((c, r) => s"X\t${c.alt}\t${c.backend.slug}\t${r.kind}\t${r.detail}")
    if rx != xs then bad += s"rejections differ:\n  certificate: ${xs.mkString(" | ")}\n  replay:      ${rx.mkString(" | ")}"
    if again.selected.map(_.key) != sel then bad += s"selected differs: certificate $sel, replay ${again.selected.map(_.key)}"
    val rk = again.kept.sortBy(_._1).map((c, ov) => s"K\t${c.alt}\t${c.backend.slug}\tINCOMPARABLE with the selected: overlaps on ${ov.map(slug).mkString(",")}")
    if rk != ks then bad += s"kept rows differ:\n  certificate: ${ks.mkString(" | ")}\n  replay:      ${rk.mkString(" | ")}"
    bad.result()
