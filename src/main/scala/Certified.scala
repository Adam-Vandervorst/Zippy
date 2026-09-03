package morkl

/** ==================================================================================================
 *  THE CERTIFIED LANGUAGE BOUNDARY, AND THE ONE FORMAT ITEMS 4 AND 8 BOTH READ.
 *
 *  ==THE CYCLE THIS BREAKS==
 *  Review item 4 (cornerstone coverage) has to record, per emitted artifact, WHAT ITS CLAIM RESTS ON:
 *  a cell whose two sides were brought together by an admitted law or by a term outside the certified
 *  algebra is not the same kind of evidence as one discharged by a prover on the bare denotation, and
 *  an audit that cannot tell them apart measures nothing.  Review item 8 (the proof closure) has to
 *  know what each artifact CLAIMS in order to decide whether an unqualified `PROVED` anywhere in the
 *  six status tables is honest.  Each therefore needs the other's output — which is the only real
 *  cycle in plan.md's dependency graph, and the reason 0.8 exists BEFORE either item builds.
 *
 *  It is broken by fixing the FORMAT first, in one place, with no consumer yet:
 *
 *    1. `; TRUSTS:` — the artifact header line.  Item 4's emitters WRITE it, item 8's readers
 *       (`scripts/proof_closure.py`) CONSUME it.  Spec: [[trustsHeader]] and `docs/TRUSTED.md`.
 *    2. [[Certified.boundary]] — the decision "is this term inside the certified language?", which is
 *       what an emitter has to ask in order to write an honest `; TRUSTS:` line at all.
 *    3. `proofs/pipeline/CLAIMS.tsv`'s `trusts` column — the DECLARATION, written before anything is
 *       built (2A.1), so the audit measures the emitted artifacts against a claim rather than against
 *       whatever came out.
 *
 *  ==WHAT IS AND IS NOT HERE (0.8 is a stub, and says so)==
 *  The FORMAT and the BOUNDARY PREDICATE are here and are checked (`CertifiedFormatCheck`).  The
 *  ENFORCEMENT is 2E.5's: "a term outside the certified language cannot enter a fully proved claim",
 *  enforced in the API and by `proof_closure.py` and the marker audit.  Nothing in the tree calls
 *  [[boundary]] yet, and that is deliberate — a mechanism with no consumer reported as progress is
 *  exactly the failure plan.md's opening paragraph names.  What 0.8 delivers is that when 2A.2's
 *  emitters and 2E.4's readers arrive, they agree, because they were written against this file.
 *
 *  ==THE DUAL OF `% MECHANIZED-IN:`==
 *  `% MECHANIZED-IN:` (see `scripts/check_lean.sh`) DISCHARGES a trusted entry: it says "the
 *  principle this file rests on is a Lean-checked theorem".  `; TRUSTS:` DECLARES one: it says "this
 *  artifact's claim rests on these entries".  A cell with an empty `; TRUSTS:` list and no reached
 *  axiom is unconditionally certified; every other cell's verdict is qualified by exactly the union
 *  of the two.  Keeping them as separate markers is what makes the two directions auditable
 *  independently — a discharge that silently deleted a declaration would be unfalsifiable.
 *  ================================================================================================== */
object Certified:

  /** ------------------------------------------------------------------------------------------------
   *  THE VOCABULARY OF THINGS AN ARTIFACT CAN TRUST.
   *
   *  A `; TRUSTS:` entry is one of these, and nothing else — an unrecognised token is a HARD FAILURE
   *  in the reader rather than an ignored comment, because a typo that silently drops a dependency is
   *  the precise defect the whole marker exists to prevent.
   *  ------------------------------------------------------------------------------------------------ */
  enum Trust:
    /** an entry of `docs/TRUSTED.md`'s trusted base, by id: `T1` … `T7`. */
    case Base(id: String)
    /** an OPEN obligation row of `terminating/REGISTRY.tsv` or `proofs/unbounded/REGISTRY.tsv`,
     *  by row id: `O6a`, `O10b`, `O12b`, `O12d`.  An open row is NOT a trusted assumption — it is a
     *  gap — and `docs/TRUSTED.md` says so; an artifact that leans on one is reporting a gap, and
     *  that is strictly worse than reporting an assumption.  It is in the vocabulary so that it can
     *  be SAID, not to make it acceptable. */
    case Open(id: String)
    /** a law of the optimiser's certified set, by its registry name (`proofs/laws/REGISTRY.tsv`).
     *  This is the LAW-JUSTIFIED case: the pair is an instance of a ∀-certified law, so the
     *  universal certificate is the proof and the per-program obligation is not needed. */
    case Law(name: String)
    /** a term outside the certified algebra, named by the boundary case that put it there.  This is
     *  what [[boundary]] returns, and the honest thing for an emitter to write when it has erased
     *  structure it could not render. */
    case Outside(reason: String)

    def render: String = this match
      case Base(id)    => id
      case Open(id)    => id
      case Law(n)      => s"law:$n"
      case Outside(r)  => s"outside:$r"

  object Trust:
    /** parse one token of a `; TRUSTS:` list.  `None` is a MALFORMED token, and every reader must
     *  treat it as a failure rather than skipping it. */
    def parse(tok: String): Option[Trust] =
      val t = tok.trim
      if t.isEmpty || t == "-" then None
      else if t.startsWith("law:") then Some(Law(t.stripPrefix("law:")))
      else if t.startsWith("outside:") then Some(Outside(t.stripPrefix("outside:")))
      else if t.matches("T\\d+") then Some(Base(t))
      else if t.matches("O\\d+[a-z]?") then Some(Open(t))
      else None

  /** ------------------------------------------------------------------------------------------------
   *  THE HEADER LINE.
   *
   *  Written as the FIRST line of an emitted artifact's header block, in the comment syntax of its
   *  format — `;` for SMT-LIB and for egglog, `%` for TPTP — so one regex reads all three:
   *
   *      ; TRUSTS: -
   *      ; TRUSTS: T4, law:unwrap-merge
   *      ; TRUSTS: O10b, outside:Range
   *
   *  `-` is REQUIRED for an artifact that trusts nothing, and an artifact with NO `; TRUSTS:` line at
   *  all is a failure in the reader.  Those are not the same thing and the difference is the point:
   *  "this cell depends on nothing" is a claim someone made, and "nobody said" is a claim nobody
   *  made.  An emitter that forgets the line would otherwise be indistinguishable from one that
   *  asserted the strongest possible statement.
   *  ------------------------------------------------------------------------------------------------ */
  val HeaderKey = "TRUSTS"

  /** the header line for a set of trusts, in the comment syntax `comment` (`";"` or `"%"`) */
  def trustsHeader(trusts: Seq[Trust], comment: String = ";"): String =
    val body = if trusts.isEmpty then "-" else trusts.map(_.render).distinct.sorted.mkString(", ")
    s"$comment $HeaderKey: $body\n"

  /** the regex both readers use.  Anchored at line start, comment character either `;` or `%`. */
  val HeaderPattern: scala.util.matching.Regex = raw"(?m)^\s*[;%]\s*$HeaderKey:\s*(.*)$$".r

  /** Read an artifact's declared trusts.
   *
   *  `Left` is a MALFORMED or MISSING header, with the reason — never an empty success.  A reader
   *  that returned "trusts nothing" for a file with no header would let an emitter bug read as the
   *  strongest claim in the tree. */
  def readTrusts(artifact: String): Either[String, Vector[Trust]] =
    HeaderPattern.findFirstMatchIn(artifact) match
      case None => Left(s"no `$HeaderKey:` header — an artifact must SAY what it trusts, and `-` " +
                        "(trusts nothing) is a claim someone made where a missing line is not")
      case Some(m) =>
        val raw = m.group(1).trim
        if raw == "-" then Right(Vector.empty)
        else
          val toks = raw.split(",").iterator.map(_.trim).filter(_.nonEmpty).toVector
          val parsed = toks.map(t => t -> Trust.parse(t))
          val bad = parsed.collect { case (t, None) => t }
          if bad.nonEmpty then
            Left(s"unrecognised `$HeaderKey` token(s): ${bad.mkString(", ")} — the vocabulary is " +
                 "`T<n>`, `O<n><letter?>`, `law:<registry name>`, `outside:<boundary case>`, or `-`. " +
                 "A token a reader cannot parse must never be skipped: that is a dropped dependency.")
          else Right(parsed.flatMap(_._2))

  /** ------------------------------------------------------------------------------------------------
   *  THE BOUNDARY.
   *
   *  `boundary(s)` is the list of reasons `s` is OUTSIDE the certified path-set algebra — empty when
   *  it is inside.  It is a list rather than a boolean because an emitter that has to write
   *  `outside:…` needs to name WHICH construct, and because a term can leave the algebra for more
   *  than one reason at once.
   *
   *  ==WHAT PUTS A TERM OUTSIDE, AND WHERE EACH IS ALREADY RECORDED==
   *  Nothing here is a new judgement; every case is a boundary the tree already declares, gathered
   *  into one predicate so an emitter asks once instead of each renderer deciding for itself (which
   *  is how `AgSmt.denRaw` and `renderZ` came to throw on `Call` while `formalOf` erased it).
   *
   *    `Range`        — `docs/TRUSTED.md` T5: outside the certified pointwise algebra.  Its window
   *                     semantics is a positional statement about a SET, which the path-set algebra
   *                     has no vocabulary for.
   *    `GroundedPS` / `GroundedSS` / `Path.GroundedPP` / `Path.GroundedSP`
   *                   — T6: an opaque Scala closure.  The only property assumed of it is
   *                     determinism, and no certificate can say more.
   *    `Call`         — O6a: beta-soundness of capture-avoiding inlining is OPEN.  A `Call` that has
   *                     been inlined is fine; a `Call` still standing in a term whose claim is
   *                     "these two sides are equal" carries O6a with it.
   *    `Fixpoint`     — O10b: the pipeline establishes k-unrolling equivalence for k = 1 and 2, and
   *                     the step from "for all k" to "the least fixpoints agree" needs the
   *                     antecedent it does not have.
   *
   *  `Mention` is deliberately NOT a boundary case: a free space variable is what the ∀-inputs legs
   *  quantify over, and treating it as outside would put the strongest artifacts in the tree outside
   *  the algebra.
   *  ------------------------------------------------------------------------------------------------ */
  def boundary(s: Space): Vector[Trust] =
    val out = scala.collection.mutable.LinkedHashSet.empty[Trust]
    def gp(x: Path): Unit = x match
      case Path.Deref(_) | Path.Constant(_) => ()
      case Path.Concat(l, r) => gp(l); gp(r)
      case Path.GroundedPP(q, _) => out += Trust.Base("T6"); gp(q)
      case Path.GroundedSP(q, _) => out += Trust.Base("T6"); go(q)
    def go(x: Space): Unit = x match
      case Space.Empty | Space.Literal(_) | Space.Mention(_) => ()
      case Space.Singleton(q) => gp(q)
      case Space.Union(a, b) => go(a); go(b)
      case Space.Intersection(a, b) => go(a); go(b)
      case Space.Subtraction(a, b) => go(a); go(b)
      case Space.Restriction(a, b) => go(a); go(b)
      case Space.Raffination(a, b) => go(a); go(b)
      case Space.Composition(a, b) => go(a); go(b)
      case Space.Wrap(a, q) => go(a); gp(q)
      case Space.Unwrap(a, q) => go(a); gp(q)
      case Space.TailsUnion(a) => go(a)
      case Space.TailsIntersection(a) => go(a)
      case Space.Iteration(src, _, _, b) => go(src); go(b)
      case Space.Fold(src, ini, _, _, _, t, u) => go(src); gp(ini); go(t); gp(u)
      case Space.Range(a, _, _) => out += Trust.Base("T5"); go(a)
      case Space.Call(_, refs, ms) => out += Trust.Open("O6a"); refs.foreach(gp); ms.foreach(go)
      case Space.Fixpoint(i, _, b) => out += Trust.Open("O10b"); go(i); go(b)
      case Space.GroundedPS(q, _) => out += Trust.Base("T6"); gp(q)
      case Space.GroundedSS(q, _) => out += Trust.Base("T6"); go(q)
    go(s)
    out.toVector

  /** is `s` inside the certified language?  The predicate 2E.5 enforces in the API. */
  def isCertified(s: Space): Boolean = boundary(s).isEmpty

  /** ------------------------------------------------------------------------------------------------
   *  `proofs/pipeline/CLAIMS.tsv`'S SCHEMA.
   *
   *  Declared here, in code, rather than only in the file's own header comment, so the emitter (2A.1
   *  writes the rows; 2A.6 adds the coverage columns) and the readers (`audit_pipeline_markers.py`,
   *  `proof_closure.py`) cannot disagree about the column order.  The file is a DECLARATION written
   *  BEFORE the artifacts exist — plan.md 2A.1: "one row per cornerstone x boundary, declared before
   *  anything is built, so the audit measures against a claim rather than against whatever was
   *  emitted."
   *  ------------------------------------------------------------------------------------------------ */
  val ClaimsColumns: Vector[String] = Vector(
    // the cell's identity: which cornerstone, and which of the pipeline's boundaries it crosses
    "cornerstone",   // aunt | datalog-sn | gol | puzzle15 | temperature | nqueens | puzzle3-full
    "boundary",      // space | zipper | graph  (the three stages), or a named sub-boundary
    "form",          // instance | agnostic — a ground input, or inputs universally quantified
    // what is claimed, and what it may rest on
    "claim",         // one line: the equivalence this cell asserts
    "trusts",        // the `; TRUSTS:` list this cell is ALLOWED to carry, same vocabulary
    // where the evidence is
    "artifact",      // repo-relative path of the emitted obligation
    "expected-kind", // REAL | LAW-JUSTIFIED | IDENT | TRIVIAL — the DECLARED_KIND vocabulary
  )
end Certified
