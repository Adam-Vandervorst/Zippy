package morkl

import scala.collection.mutable

/** ==============================================================================================
 *  THE DEPENDENCY CLOSURE OF A PROOF TRACE, IN SCALA ( → B2).
 *
 *  `scripts/proof_closure.py check_trace_closure` is the INDEPENDENT checker of the committed traces.
 *  This is the same resolution, in the process that has to make a decision: an alternative may enter
 *  the certified Pareto frontier (B2) only when its semantic trace has CLOSED — every leaf resolves to
 *  a PROVED certificate, a MECHANIZED registry entry or a trusted-base entry it names.  It reads the
 *  same three tables the Python reads and nothing else:
 *
 *   - `proofs/laws/REGISTRY.tsv`  law → kind, certificate files (wildcards are families);
 *   - `proofs/STATUS.tsv`         certificate → verdict (`PROVED`, `PROVED (MECHANIZED …)`,
 *                                 `PROVED-MODULO T…`, anything else is not a proof);
 *   - `terminating/REGISTRY.tsv`  obligation id → kind (`MECHANIZED …` discharges it).
 *
 *  Definitional steps rest on registry entries: an `Unfold` on O6a (substitution) and O12a (unfolding),
 *  a `Fold` on O12b (repeated folding), a `Generalization` on O6a (its holes are substituted back).  A
 *  `GraphOptimizerNoOp` rests on the trusted entry T4 (the egglog `expand` step is trusted, not proved)
 *  — CONDITIONAL, never CLOSED.  A `BackendRefinement` resolves through its artifact's status row.
 *  ============================================================================================== */
object TraceClosure:

  enum Status:
    /** every dependency discharged */
    case Closed
    /** discharged modulo these trusted-base entries (`docs/TRUSTED.md` ids) */
    case Conditional(trusted: Set[String])
    /** at least one dependency is not discharged; the reasons */
    case Open(reasons: Vector[String])
    def closed: Boolean = this match { case Open(_) => false; case _ => true }
    def render: String = this match
      case Closed => "CLOSED"
      case Conditional(t) => s"CONDITIONAL:${t.toVector.sorted.mkString(",")}"
      case Open(rs) => s"OPEN:${rs.mkString("; ")}"

  private def rows(path: String): Vector[Vector[String]] =
    val f = java.nio.file.Paths.get(path)
    if !java.nio.file.Files.exists(f) then Vector.empty
    else scala.io.Source.fromFile(f.toFile).getLines().filterNot(l => l.trim.isEmpty || l.startsWith("#")).map(_.split("\t").toVector).toVector

  /** law → certificate patterns (basenames without extension; a trailing `*` is a prefix family) */
  lazy val lawCertificates: Map[String, (String, Vector[String])] =
    rows("proofs/laws/REGISTRY.tsv").filter(_.length >= 3).map { c =>
      val certs = c(2).split(",").toVector.map(_.trim).filter(x => x.nonEmpty && x != "-").map(x => x.split("/").last.stripSuffix(".smt2").stripSuffix(".p").stripSuffix(".egg"))
      c(0).trim -> (c(1).trim, certs)
    }.toMap

  /** certificate basename → verdict */
  lazy val verdicts: Map[String, String] =
    rows("proofs/STATUS.tsv").filter(_.length >= 2).map { c =>
      var n = c(0).trim.split("/").last
      for ext <- Vector(".smt2", ".p", ".egg") do n = n.stripSuffix(ext)
      n -> c.last.trim
    }.toMap

  /** obligation id → kind column */
  lazy val obligations: Map[String, String] =
    (rows("terminating/REGISTRY.tsv") ++ rows("proofs/unbounded/REGISTRY.tsv")).filter(_.length >= 2).map(c => c(0).trim -> c(1).trim).toMap

  private def verdictStatus(v: String, what: String): Status =
    if v.startsWith("PROVED-MODULO") then
      val ts = v.stripPrefix("PROVED-MODULO").trim.split("[ ,]").toVector.map(_.trim).filter(_.nonEmpty)
      val (trusted, gaps) = ts.partition(_.matches("T\\d+"))
      if gaps.nonEmpty then Status.Open(Vector(s"$what: $v")) else Status.Conditional(trusted.toSet)
    else if v.startsWith("PROVED") then Status.Closed
    else Status.Open(Vector(s"$what: $v"))

  def lawStatus(law: String): Status =
    lawCertificates.get(law) match
      case None => Status.Open(Vector(s"law $law: not in proofs/laws/REGISTRY.tsv"))
      case Some((kind, certs)) if kind == "DEFINITIONAL" && certs.isEmpty => Status.Closed   // a representation change: nothing to prove
      case Some((_, certs)) if certs.isEmpty => Status.Open(Vector(s"law $law: no certificate"))
      case Some((_, certs)) =>
        val parts = certs.map { pat =>
          val wild = pat.endsWith("*"); val stem = pat.stripSuffix("*")
          val matches = verdicts.filter((k, _) => if wild then k.startsWith(stem) else k == stem).toVector.sortBy(_._1)
          if matches.isEmpty then Status.Open(Vector(s"law $law: $pat: no status row"))
          else combine(matches.map((k, v) => verdictStatus(v, s"law $law: $k")))
        }
        combine(parts)

  def obligationStatus(id: String): Status =
    obligations.get(id) match
      case None => Status.Open(Vector(s"$id: not in a registry"))
      case Some(kind) if kind.startsWith("MECHANIZED") => Status.Closed
      case Some(kind) => Status.Open(Vector(s"$id: $kind"))

  /** pipeline cell artifact → verdict (proofs/pipeline/STATUS.tsv: file, z3, vampire, verdict).  Read on every
   *  call, not cached: the pipeline suite rewrites this table while it runs and reads closures in between. */
  def cellVerdicts: Map[String, String] =
    rows("proofs/pipeline/STATUS.tsv").filter(_.length >= 2).map { c =>
      var n = c(0).trim.split("/").last
      for ext <- Vector(".smt2", ".p", ".egg") do n = n.stripSuffix(ext)
      n -> c.last.trim
    }.toMap

  def artifactStatus(path: String): Status =
    var n = path.split("/").last
    for ext <- Vector(".smt2", ".p", ".egg") do n = n.stripSuffix(ext)
    if path.startsWith("proofs/pipeline/") then
      // the same reading as proof_closure.py: a PROVED or LAW-JUSTIFIED cell discharges; PROVED-MODULO /
      // LAW-JUSTIFIED-… are conditional; a marker cited as an obligation is conditional on itself
      cellVerdicts.get(n) match
        case None => Status.Open(Vector(s"artifact $path: no status row"))
        case Some(v) if v == "LAW-JUSTIFIED" => Status.Closed
        case Some(v) if v.startsWith("PROVED") && !v.contains("MODULO") => Status.Closed
        case Some(v) if v.startsWith("PROVED-MODULO") || v.startsWith("LAW-JUSTIFIED") => verdictStatus(v.replace("LAW-JUSTIFIED", "PROVED"), s"artifact $path")
        case Some(v) if v == "TRIVIAL" || v == "IDENTICAL-STRUCTURE" => Status.Conditional(Set(s"marker:$n"))
        case Some(v) => Status.Open(Vector(s"artifact $path: $v"))
    else
      verdicts.get(n) match
        case None => Status.Open(Vector(s"artifact $path: no status row"))
        case Some(v) => verdictStatus(v, s"artifact $path")

  def combine(ss: Iterable[Status]): Status =
    val opens = ss.collect { case Status.Open(r) => r }.flatten.toVector
    if opens.nonEmpty then Status.Open(opens.distinct)
    else
      val ts = ss.collect { case Status.Conditional(t) => t }.flatten.toSet
      if ts.isEmpty then Status.Closed else Status.Conditional(ts)

  /** the dependencies of one node, resolved */
  def nodeStatus(n: ProofTrace.Node): Status = n match
    case ProofTrace.Node.LawInstance(law, _, _, _, _) => lawStatus(law)
    case _: ProofTrace.Node.Unfold => combine(Vector(obligationStatus("O6a"), obligationStatus("O12a")))
    case _: ProofTrace.Node.Fold => obligationStatus("O12b")
    case _: ProofTrace.Node.Generalization => obligationStatus("O6a")
    case ProofTrace.Node.BackendRefinement(_, _, artifact, _, _, _) => artifactStatus(artifact)
    case _: ProofTrace.Node.GraphOptimizerNoOp => Status.Conditional(Set("T4"))
    case _: ProofTrace.Node.OptimizerNoOp | _: ProofTrace.Node.AlphaEquivalence | _: ProofTrace.Node.Positional | _: ProofTrace.Node.Compose => Status.Closed

  def of(dag: ProofTrace.Dag): Status = combine(dag.nodes.map(nodeStatus))
  def of(dags: Iterable[ProofTrace.Dag]): Status = combine(dags.map(of))
