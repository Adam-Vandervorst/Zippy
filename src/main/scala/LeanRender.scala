package morkl

/** ==================================================================================================
 *  THE CORRESPONDENCE RENDERER (plan.md 1E.2).
 *
 *  `1E.2`: "Correspondence to the executable: a Lean-checked TRACE of the production substitutions —
 *  `LeanRender` emits each `(term, substitution, result)` the Scala performed, Lean re-checks it.
 *  Not a citation."
 *
 *  ==WHY A TRACE AND NOT A CITATION==
 *  `proofs/lean/Zippy/Subst.lean` defines a substitution and proves things about it.  On its own that
 *  says nothing whatever about `src/main/scala/Subst.scala`: two functions can both be
 *  capture-avoiding and simultaneous and still disagree, and a comment saying "this mirrors the
 *  Scala" is exactly the kind of claim this tree keeps finding to be false.  What ties them together
 *  is a trace: the Scala runs the real pipeline, records every distinct `(term, σ, result)` it
 *  actually performed, and Lean is asked to CONFIRM each result by evaluating its own definition on
 *  the same input.  A disagreement is a failing `lake build`, on real terms.
 *
 *  ==THE ONE DELIBERATE DIFFERENCE THE TRACE DISCHARGES==
 *  At a capturing binder the Scala does TWO passes over the body (rename, then substitute) while the
 *  Lean merges the rename into the substitution map and does ONE — which is what makes the Lean
 *  definition structurally recursive.  `Subst.lean`'s header argues they agree and says explicitly
 *  that the argument is an OBLIGATION discharged here rather than an assumption.  Every class-A
 *  triple in the emitted file is an instance of that agreement.
 *
 *  ==WHAT IS EMITTED, AND WHAT IS NOT ASSERTED==
 *  `Subst.Trace`'s header sets out the two classes.  Class A (no fresh name minted) is emitted as an
 *  `example : substS … = <result> := by native_decide`-style EQUATION and is the strong check.  Class
 *  B (a capture was avoided) cannot be checked by equality against any Lean `FreshSupply`, because
 *  the Scala's naming is a stateful counter and a `FreshSupply` is a function of the avoid set; those
 *  triples are emitted as COMMENTS carrying their minted names, so the count is visible in the
 *  artifact and the case cannot be silently dropped.
 *
 *  ==THE RENDERING IS TOTAL OVER THE SYNTAX==
 *  Every `Space` and `Path` constructor has an arm, with no catch-all: an unrenderable term is a
 *  COMPILE error here rather than a silently skipped triple, because a trace that quietly omits the
 *  constructors it cannot print would report a correspondence over a fragment while looking complete.
 *  Two constructors cannot be rendered faithfully and are REFUSED rather than approximated:
 *  `Space.Literal` and `Path.Constant` carry `PathItem` values, which is fine, but the four
 *  `Grounded*` forms carry an opaque Scala closure whose identity Lean models as a `Name` — so they
 *  are rendered with a STABLE SYNTHETIC name derived from the closure's identity hash, and
 *  `Trace.Entry`s containing one are dropped with a reported count, since two runs can disagree on
 *  that hash and the artifact must be reproducible.
 *  ================================================================================================== */
object LeanRender:

  /** how many triples the emitted file may carry.  A cap, not a target: the artifact is a golden
   *  file that `lake build` elaborates on every gate run, and elaboration is linear in the term
   *  size, so an unbounded trace would put minutes of Lean into a 30-second gate. */
  val DefaultLimit = 400

  // ------------------------------------------------------------------------------------------------
  // Rendering, total over both sorts
  // ------------------------------------------------------------------------------------------------

  private def str(s: String): String = "\"" + s.replace("\\", "\\\\").replace("\"", "\\\"") + "\""

  private def items(p: PathValue): String = p.items.map(i => str(i.toString)).mkString("[", ", ", "]")

  /** `true` when `s` mentions a grounded form, whose Lean rendering would need the closure's identity
   *  — not reproducible across runs, so such a triple is dropped rather than approximated. */
  def hasGrounded(s: Space): Boolean =
    var found = false
    def gp(x: Path): Unit = x match
      case Path.Deref(_) | Path.Constant(_) => ()
      case Path.Concat(l, r) => gp(l); gp(r)
      case Path.GroundedPP(_, _) | Path.GroundedSP(_, _) => found = true
    def go(x: Space): Unit = x match
      case Space.Empty | Space.Literal(_) | Space.Mention(_) => ()
      case Space.Singleton(p) => gp(p)
      case Space.Union(a, b) => go(a); go(b)
      case Space.Intersection(a, b) => go(a); go(b)
      case Space.Subtraction(a, b) => go(a); go(b)
      case Space.Restriction(a, b) => go(a); go(b)
      case Space.Raffination(a, b) => go(a); go(b)
      case Space.Composition(a, b) => go(a); go(b)
      case Space.Wrap(a, p) => go(a); gp(p)
      case Space.Unwrap(a, p) => go(a); gp(p)
      case Space.TailsUnion(a) => go(a)
      case Space.TailsIntersection(a) => go(a)
      case Space.Range(a, _, _) => go(a)
      case Space.Call(_, refs, ms) => refs.foreach(gp); ms.foreach(go)
      case Space.Iteration(src, _, _, b) => go(src); go(b)
      case Space.Fixpoint(i, _, b) => go(i); go(b)
      case Space.Fold(src, ini, _, _, _, t, u) => go(src); gp(ini); go(t); gp(u)
      case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) => found = true
    go(s)
    found

  /** a `Path` as Lean.  Total; the grounded arms are unreachable for a triple that passed
   *  [[hasGrounded]], and raise rather than printing something Lean would accept. */
  def path(p: Path): String = p match
    case Path.Deref(pr) => s"(.deref ${str(pr.s)})"
    case Path.Constant(pv) => s"(.const ${items(pv)})"
    case Path.Concat(l, r) => s"(.concat ${path(l)} ${path(r)})"
    case Path.GroundedPP(_, _) | Path.GroundedSP(_, _) =>
      throw new IllegalArgumentException(
        "LeanRender.path: a grounded path reached the renderer.  Its Lean model needs the closure's " +
        "IDENTITY, which is not reproducible across runs, so such a triple must be dropped by " +
        "`hasGrounded` before it gets here — an artifact that is not reproducible is not a golden file.")

  /** a `Space` as Lean.  Total, no catch-all: a new constructor is a compile error here. */
  def space(s: Space): String = s match
    case Space.Empty => "(.empty)"
    case Space.Literal(v) =>
      // the path set, in a DETERMINISTIC order.  `SpaceValue.paths` is a `Set`, whose iteration
      // order is not stable across runs for anything but the smallest sizes, and a golden artifact
      // whose line order moves is a diff on every run.
      val ps = v.paths.toVector.map(_.items.map(_.toString)).sorted
      "(.lit " + ps.map(is => is.map(str).mkString("[", ", ", "]")).mkString("[", ", ", "]") + ")"
    case Space.Mention(m) => s"(.mention ${str(m.s)})"
    case Space.Singleton(p) => s"(.singleton ${path(p)})"
    case Space.Union(a, b) => s"(.union ${space(a)} ${space(b)})"
    case Space.Intersection(a, b) => s"(.inter ${space(a)} ${space(b)})"
    case Space.Subtraction(a, b) => s"(.sub ${space(a)} ${space(b)})"
    case Space.Restriction(a, b) => s"(.restriction ${space(a)} ${space(b)})"
    case Space.Raffination(a, b) => s"(.raffination ${space(a)} ${space(b)})"
    case Space.Composition(a, b) => s"(.composition ${space(a)} ${space(b)})"
    case Space.Wrap(a, p) => s"(.wrap ${space(a)} ${path(p)})"
    case Space.Unwrap(a, p) => s"(.unwrap ${space(a)} ${path(p)})"
    case Space.TailsUnion(a) => s"(.tailsUnion ${space(a)})"
    case Space.TailsIntersection(a) => s"(.tailsInter ${space(a)})"
    case Space.Range(a, lo, hi) => s"(.range ${space(a)} ($lo) ($hi))"
    case Space.Call(rp, refs, ms) =>
      s"(.call ${str(rp.s)} ${refs.map(path).mkString("[", ", ", "]")} ${ms.map(space).mkString("[", ", ", "]")})"
    case Space.Iteration(src, sym, rest, b) =>
      s"(.iteration ${space(src)} ${str(sym.s)} ${str(rest.s)} ${space(b)})"
    case Space.Fixpoint(i, rec, b) => s"(.fixpoint ${space(i)} ${str(rec.s)} ${space(b)})"
    case Space.Fold(src, ini, acc, sym, rest, t, u) =>
      s"(.fold ${space(src)} ${path(ini)} ${str(acc.s)} ${str(sym.s)} ${str(rest.s)} ${space(t)} ${path(u)})"
    case Space.GroundedPS(_, _) | Space.GroundedSS(_, _) =>
      throw new IllegalArgumentException(
        "LeanRender.space: a grounded space reached the renderer; see LeanRender.path for why such " +
        "a triple must be dropped rather than approximated.")

  // ------------------------------------------------------------------------------------------------
  // The file
  // ------------------------------------------------------------------------------------------------

  /** Emit the whole trace as a Lean module.
   *
   *  `origin` names what produced it, so a reader of the artifact knows which run it describes. */
  def render(entries: Vector[Subst.Trace.Entry], dropped: Int, origin: String): String =
    val renderable = entries.filter(e =>
      !hasGrounded(e.term) && !hasGrounded(e.result) &&
      e.mentions.forall((_, t) => !hasGrounded(t)) &&
      e.paths.forall((_, t) => !hasGrounded(Space.Singleton(t))))
    val groundedDropped = entries.length - renderable.length
    val classA = renderable.filter(_.exactlyCheckable)
    val classB = renderable.filterNot(_.exactlyCheckable)
    val sb = new StringBuilder
    sb.append(s"""/-
==================================================================================================
GENERATED — the correspondence trace (plan.md 1E.2).  DO NOT EDIT.

Regenerate with `ZIPPY_REGENERATE=1 sbt --server 'testOnly morkl.SubstTrace'`; without the flag the suite
writes to `target/artifact-scratch` and DIFFS against this file, so a drift in EITHER
implementation fails.  `src/main/scala/LeanRender.scala` is the emitter and explains the design.

WHAT THIS FILE IS.  Each `example` below is a substitution `src/main/scala/Subst.scala` ACTUALLY
PERFORMED while running $origin, re-checked against `Zippy.substS` — the Lean definition
`Zippy/Subst.lean` proves its hygiene theorems about.  A disagreement between the two
implementations is a failing `lake build` on a real term, not a comment claiming they agree.

It is also what DISCHARGES the one deliberate difference between them: at a capturing binder the
Scala does two passes over the body (rename, then substitute) and the Lean merges the rename into
the map and does one.  `Zippy/Subst.lean`'s header states that as an obligation for this file.

  triples recorded          ${entries.length}
  emitted as EQUATIONS      ${classA.length}   (class A: no fresh name minted, so the result is
                                 independent of the naming policy and equality is checkable)
  emitted as COMMENTS       ${classB.length}   (class B: a capture WAS avoided; the Scala's naming is
                                 a stateful counter and no Lean `FreshSupply` reproduces it, so
                                 equality is not asserted.  `SubstCapture` and `substS_keeps_freeM`
                                 are what cover this class instead)
  dropped, grounded         $groundedDropped   (a `Grounded*` closure's Lean identity is not
                                 reproducible across runs, so the artifact would not be a golden file)
  dropped, over the cap     $dropped   (LeanRender.DefaultLimit; repeats of one triple are
                                 deduplicated before the cap applies)
==================================================================================================
-/
import Zippy.Subst

namespace Zippy.Trace

/-- the supply the equations below are checked under.  Class-A triples mint no name, so `gen` is
never called and the choice cannot matter — which is exactly what makes the class checkable. -/
private def F : FreshSupply := FreshSupply.byLength

""")
    if classA.isEmpty then
      sb.append("-- NO CLASS-A TRIPLE WAS RECORDED.  That is a failure of the trace, not a pass: the\n")
      sb.append("-- correspondence check would be vacuous.  `SubstTrace` asserts against it.\n")
    for (e, i) <- classA.zipWithIndex do
      sb.append(s"/-- triple ${i + 1} -/\n")
      sb.append(s"example : substS F\n")
      sb.append(s"    ${leanMentions(e.mentions)}\n")
      sb.append(s"    ${leanPaths(e.paths)}\n")
      sb.append(s"    ${space(e.term)}\n")
      sb.append(s"  = ${space(e.result)} := by rfl\n\n")
    if classB.nonEmpty then
      sb.append("/-\nCLASS B — a capture was avoided, so equality is not asserted here.  Recorded so the\n")
      sb.append("count is visible in the artifact rather than being a silent omission.\n\n")
      for (e, i) <- classB.zipWithIndex do
        sb.append(s"  ${i + 1}. minted ${e.fresh.mkString(", ")}\n")
        sb.append(s"     term   ${space(e.term).take(160)}\n")
      sb.append("-/\n\n")
    sb.append("end Zippy.Trace\n")
    sb.toString

  private def leanMentions(ms: Vector[(String, Space)]): String =
    if ms.isEmpty then "[]"
    else ms.map((n, t) => s"(${str(n)}, ${space(t)})").mkString("[", ", ", "]")

  private def leanPaths(ps: Vector[(String, Path)]): String =
    if ps.isEmpty then "[]"
    else ps.map((n, t) => s"(${str(n)}, ${path(t)})").mkString("[", ", ", "]")

  /** `proofs/lean/Zippy/WhistleTrace.lean` (plan.md 2E.3): one `example` per recorded whistle comparison,
   *  re-decided by `Zippy.Whistle.embedsB` on the label trees `Matching.toLabel` renders. */
  def renderWhistle(entries: Vector[Matching.WhistleTrace.Entry], dropped: Int, origin: String): String =
    val sb = new StringBuilder
    val emitted = entries.filter(_.renderable)
    val skipped = entries.length - emitted.length
    sb.append("/-\n")
    sb.append("==================================================================================================\n")
    sb.append("GENERATED — the whistle correspondence trace (plan.md 2E.3).  DO NOT EDIT.\n\n")
    sb.append("Regenerate with `ZIPPY_REGENERATE=1 sbt --server 'testOnly morkl.WhistleTrace'`; without the flag the suite\n")
    sb.append("writes to `target/artifact-scratch` and DIFFS against this file.\n\n")
    sb.append("WHAT THIS FILE IS.  Each `example` below is a pair of configurations `Matching.embeds` ACTUALLY\n")
    sb.append(s"compared while running $origin, rendered as label trees by `Matching.toLabel` (the alphabet\n")
    sb.append("`Matching.labelOf` fixes), with the verdict the Scala returned.  `Zippy.Whistle.embedsB` re-decides\n")
    sb.append("each one; `embedsB_iff` proves `embedsB` IS the relation `kruskal` shows to be a well-quasi-order,\n")
    sb.append("so an agreeing trace is what makes that theorem a statement about the implemented whistle.\n\n")
    sb.append(s"  pairs recorded            ${entries.length}\n")
    sb.append(s"  emitted as EXAMPLES       ${emitted.length}\n")
    sb.append(s"  dropped, grounded         $skipped   (a Grounded* closure's identity is not reproducible)\n")
    sb.append(s"  dropped, over the cap     $dropped\n")
    sb.append("==================================================================================================\n-/\n")
    sb.append("import Zippy.Whistle\n\nnamespace Zippy.WhistleTrace\nopen Zippy.Whistle\n\n")
    for (e, i) <- emitted.zipWithIndex do
      sb.append(s"/-- pair ${i + 1} (litAtoms = ${e.litAtoms}) -/\n")
      sb.append(s"example : embedsB\n    ${Matching.toLabel(e.a, e.litAtoms)}\n    ${Matching.toLabel(e.b, e.litAtoms)}\n")
      sb.append(s"  = ${e.verdict} := by simp [embedsB, zipAll]\n\n")
    sb.append("end Zippy.WhistleTrace\n")
    sb.toString

end LeanRender
