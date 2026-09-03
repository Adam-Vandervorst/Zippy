package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==================================================================================================
 *  `SmtDiff.alphaNorm` IS TOTAL, AND EVERY CLAUSE IS CHECKED (plan.md 0.6).
 *
 *  ==WHY THIS SUITE EXISTS==
 *  `alphaNorm` is a DECISION PROCEDURE, not a convenience.  Three consumers act on its verdict:
 *
 *    1. `EquivPipelineTest`'s cell classification -- `alphaNorm(a) == alphaNorm(b)` emits an
 *       `IDENTICAL-STRUCTURE-NO-EQUIVALENCE-OBLIGATION` marker, i.e. NO PROVER OBLIGATION AT ALL;
 *    2. `SmtDiff.partition` -- it normalises both sides before the structural diff, so a wrong
 *       answer turns a real difference into a reflexive obligation or vice versa;
 *    3. `CanonicalId.ofCut` -- residual-cut identity, so two different cuts could share an id.
 *
 *  Both of its matches used to end in `case other => other`, which swallowed six constructors that
 *  DO need descent: `Call`, `Fold`, `GroundedPS`, `GroundedSS`, `Path.GroundedPP`,
 *  `Path.GroundedSP`.  That is unsound in the direction that matters -- a `Mention` inside an
 *  un-descended subterm keeps the name an ENCLOSING binder already renamed, so the result carries
 *  one variable under two names, and two terms mis-normalised the same way compare EQUAL.  A cell
 *  can then be recorded as needing no obligation on the strength of a renaming never applied.
 *
 *  ==WHAT IS CHECKED==
 *   A. CONSTRUCTOR COVERAGE, read from `MORKL.scala` itself.  Every `case` of `enum Space` and
 *      `enum Path` must appear in this suite's covered set, so ADDING A CONSTRUCTOR FAILS THIS TEST
 *      rather than silently getting the identity clause.  (Scala's exhaustivity check is a WARNING
 *      in this build -- build.log records the pre-existing warning volume -- so the compiler is not
 *      the gate here; this is.)
 *   B. DESCENT, per constructor: a renamable occurrence placed UNDER each constructor, inside a
 *      binder, must come out renamed.  This is the property the catch-all violated.
 *   C. ALPHA-EQUIVALENCE, per binding form, including `Fold`'s THREE binders.
 *   D. NON-EQUIVALENCE -- the negative control.  Terms that are not alpha-equivalent must not
 *      normalise equal; a normaliser that erased names instead of renaming them would pass A-C.
 *   E. IDEMPOTENCE, and
 *   F. SEMANTIC PRESERVATION: `eval(alphaNorm(t)) == eval(t)` on closed terms, through all three
 *      executors -- the actual soundness statement, not a syntactic proxy.
 *  ================================================================================================== */
class AlphaNormCheck extends FunSuite:
  import Space.*

  def p(items: String*): PathValue = PathValue(items.toList)
  def lit(ps: PathValue*): Space = Literal(SpaceValue(ps.toSet))
  val K: Path = Path.Constant(p("k"))

  /** every binder name a source term below uses; none may survive normalisation under a binder */
  val sourceBinderNames = Set("y", "rest", "rec", "acc", "sym", "r2")

  /** the free names of a normalised term, as they appear in its rendering */
  def namesIn(s: Space): Set[String] =
    val out = scala.collection.mutable.Set.empty[String]
    def gp(x: Path): Unit = x match
      case Path.Deref(pr) => out += pr.s
      case Path.Concat(l, r) => gp(l); gp(r)
      case Path.Constant(_) => ()
      case Path.GroundedPP(q, _) => gp(q)
      case Path.GroundedSP(q, _) => go(q)
    def go(x: Space): Unit = x match
      case Empty | Literal(_) => ()
      case Mention(m) => out += m.s
      case Singleton(q) => gp(q)
      case Union(a, b) => go(a); go(b)
      case Intersection(a, b) => go(a); go(b)
      case Subtraction(a, b) => go(a); go(b)
      case Restriction(a, b) => go(a); go(b)
      case Raffination(a, b) => go(a); go(b)
      case Composition(a, b) => go(a); go(b)
      case Wrap(a, q) => go(a); gp(q)
      case Unwrap(a, q) => go(a); gp(q)
      case TailsUnion(a) => go(a)
      case TailsIntersection(a) => go(a)
      case Range(a, _, _) => go(a)
      case Call(_, refs, ms) => refs.foreach(gp); ms.foreach(go)
      case Iteration(src, sym, rest, b) => go(src); out += sym.s; out += rest.s; go(b)
      case Fixpoint(i, rec, b) => go(i); out += rec.s; go(b)
      case Fold(src, ini, acc, sym, rest, t, u) =>
        go(src); gp(ini); out += acc.s; out += sym.s; out += rest.s; go(t); gp(u)
      case GroundedPS(q, _) => gp(q)
      case GroundedSS(q, _) => go(q)
    go(s)
    out.toSet

  // ------------------------------------------------------------------------------------------------
  // B. DESCENT, per constructor.  Each case wraps `Mention("rest")` (or `Deref("y")`) in the
  // constructor under test and puts the whole thing under an `Iteration` that binds those names.  A
  // constructor `alphaNorm` does not descend leaves the source name in the output.
  // ------------------------------------------------------------------------------------------------
  val RP: Path = Path.Deref(PathRef("y"))
  val M: Space = Mention(SpaceMention("rest"))

  /** (constructor name, a term placing a renamable occurrence under that constructor) */
  val descentCases: Vector[(String, Space)] = Vector(
    "Empty"             -> Union(M, Empty),
    "Literal"           -> Union(M, lit(p("a"))),
    "Mention"           -> M,
    "Singleton"         -> Singleton(RP),
    "Union"             -> Union(M, M),
    "Intersection"      -> Intersection(M, M),
    "Subtraction"       -> Subtraction(M, M),
    "Restriction"       -> Restriction(M, M),
    "Raffination"       -> Raffination(M, M),
    "Composition"       -> Composition(M, M),
    "Wrap"              -> Wrap(M, RP),
    "Unwrap"            -> Unwrap(M, RP),
    "TailsUnion"        -> TailsUnion(M),
    "TailsIntersection" -> TailsIntersection(M),
    "Range"             -> Range(M, 0, 1),
    // THE SIX THE CATCH-ALL LOST.  `Call`'s `mentions` are precisely where a renamed outer binder is
    // handed to a routine, and `Fold`'s body sees three binders of its own.
    "Call"              -> Call(RoutinePtr("f"), Vector(RP), Vector(M)),
    "Fold"              -> Fold(M, K, PathRef("acc"), PathRef("sym"), SpaceMention("r2"),
                                Union(M, Singleton(RP)), Path.Deref(PathRef("acc"))),
    "GroundedPS"        -> GroundedPS(RP, (_: PathValue) => SpaceValue(Set(p("g")))),
    "GroundedSS"        -> GroundedSS(M, (v: SpaceValue) => v),
    // the binding forms themselves
    "Iteration"         -> Iteration(M, PathRef("sym"), SpaceMention("r2"), Union(M, Singleton(RP))),
    "Fixpoint"          -> Fixpoint(M, SpaceMention("rec"), Union(M, Mention(SpaceMention("rec")))),
  )

  /** (Path constructor name, a term placing a renamable occurrence under it) */
  val pathDescentCases: Vector[(String, Path)] = Vector(
    "Deref"      -> RP,
    "Constant"   -> Path.Concat(K, RP),
    "Concat"     -> Path.Concat(RP, K),
    "GroundedPP" -> Path.GroundedPP(RP, (v: PathValue) => v),
    "GroundedSP" -> Path.GroundedSP(M, (_: SpaceValue) => p("g")),
  )

  test("B. every Space constructor is DESCENDED: no source binder name survives normalisation") {
    for (label, inner) <- descentCases do
      // bind `y` and `rest` outside, so both must be renamed wherever they occur inside
      val t = Iteration(lit(p("s")), PathRef("y"), SpaceMention("rest"), inner)
      val leaked = namesIn(SmtDiff.alphaNorm(t)) intersect sourceBinderNames
      assertEquals(leaked, Set.empty[String],
        s"alphaNorm does not descend `$label`: the source name(s) ${leaked.mkString(", ")} survived, " +
        s"so an occurrence bound by the enclosing Iteration kept the name the binder renamed.  " +
        s"That is how one variable ends up with two names and two mis-normalised terms compare equal.")
  }

  test("B'. every Path constructor is DESCENDED") {
    for (label, inner) <- pathDescentCases do
      val t = Iteration(lit(p("s")), PathRef("y"), SpaceMention("rest"), Singleton(inner))
      val leaked = namesIn(SmtDiff.alphaNorm(t)) intersect sourceBinderNames
      assertEquals(leaked, Set.empty[String], s"alphaNorm does not descend `Path.$label`")
  }

  // ------------------------------------------------------------------------------------------------
  // A. CONSTRUCTOR COVERAGE, read from the source of truth.
  // ------------------------------------------------------------------------------------------------
  // The `enum` case reader is `AlphaNormReflect.enumCases` (CertifiedFormatCheck.scala):
  // `CertifiedFormatCheck` needs the same "every constructor MORKL.scala declares" list for
  // `Certified.boundary`, and two copies of a parser for one file is two things to drift.
  def enumCases(enumName: String): Vector[String] = AlphaNormReflect.enumCases(enumName)

  test("A. this suite covers EVERY Space and Path constructor MORKL.scala declares") {
    val declaredS = enumCases("Space")
    val declaredP = enumCases("Path")
    assert(declaredS.length >= 21, s"only ${declaredS.length} Space cases parsed — the reader broke")
    assert(declaredP.length >= 5, s"only ${declaredP.length} Path cases parsed — the reader broke")
    val coveredS = descentCases.map(_._1).toSet
    val coveredP = pathDescentCases.map(_._1).toSet
    assertEquals(declaredS.filterNot(coveredS), Vector.empty[String],
      "a `Space` constructor exists that this suite does not place under a binder.  `alphaNorm`'s " +
      "match is exhaustive, so the new case compiles — but whether it DESCENDS is exactly what the " +
      "catch-all used to get wrong, and an unlisted constructor is an unchecked clause.")
    assertEquals(declaredP.filterNot(coveredP), Vector.empty[String],
      "a `Path` constructor exists that this suite does not place under a binder")
    println(s"ALPHANORM: covered ${declaredS.length} Space + ${declaredP.length} Path constructors")
  }

  // ------------------------------------------------------------------------------------------------
  // C. ALPHA-EQUIVALENCE, per binding form.
  // ------------------------------------------------------------------------------------------------
  test("C. terms differing only in binder names normalise EQUAL, for all three binding forms") {
    val src = lit(p("a"), p("b"))
    // Iteration
    val i1 = Iteration(src, PathRef("y"), SpaceMention("rest"),
                       Union(Mention(SpaceMention("rest")), Singleton(Path.Deref(PathRef("y")))))
    val i2 = Iteration(src, PathRef("q"), SpaceMention("tl"),
                       Union(Mention(SpaceMention("tl")), Singleton(Path.Deref(PathRef("q")))))
    assertEquals(SmtDiff.alphaNorm(i1), SmtDiff.alphaNorm(i2), "Iteration binders are not canonical")
    // Fixpoint
    val f1 = Fixpoint(src, SpaceMention("rec"), Union(Mention(SpaceMention("rec")), src))
    val f2 = Fixpoint(src, SpaceMention("z"), Union(Mention(SpaceMention("z")), src))
    assertEquals(SmtDiff.alphaNorm(f1), SmtDiff.alphaNorm(f2), "Fixpoint binder is not canonical")
    // Fold — ALL THREE binders at once, which the catch-all could not do at all
    def fold(acc: String, sym: String, rest: String) =
      Fold(src, K, PathRef(acc), PathRef(sym), SpaceMention(rest),
           Union(Mention(SpaceMention(rest)), Singleton(Path.Deref(PathRef(sym)))),
           Path.Concat(Path.Deref(PathRef(acc)), Path.Deref(PathRef(sym))))
    assertEquals(SmtDiff.alphaNorm(fold("acc", "sym", "rest")),
                 SmtDiff.alphaNorm(fold("a2", "s2", "r2")),
                 "Fold's three binders are not canonical")
  }

  // ------------------------------------------------------------------------------------------------
  // D. THE NEGATIVE CONTROL.
  // ------------------------------------------------------------------------------------------------
  test("D. terms that are NOT alpha-equivalent must NOT normalise equal") {
    val src = lit(p("a"), p("b"))
    // Fold with `acc` and `sym` SWAPPED in the update: a different function of the same binders.
    def fold(u: Path) =
      Fold(src, K, PathRef("acc"), PathRef("sym"), SpaceMention("rest"),
           Mention(SpaceMention("rest")), u)
    val accSym = fold(Path.Concat(Path.Deref(PathRef("acc")), Path.Deref(PathRef("sym"))))
    val symAcc = fold(Path.Concat(Path.Deref(PathRef("sym")), Path.Deref(PathRef("acc"))))
    assertNotEquals(SmtDiff.alphaNorm(accSym), SmtDiff.alphaNorm(symAcc),
      "alphaNorm equated two Folds whose updates use their binders in the OPPOSITE order — it is " +
      "erasing names rather than renaming them, and every IDENTICAL-STRUCTURE classification built " +
      "on it would be worthless")
    // a Call to a DIFFERENT routine is a different term: `r` is a global name, not a binder
    assertNotEquals(SmtDiff.alphaNorm(Call(RoutinePtr("f"), Vector(K), Vector(src))),
                    SmtDiff.alphaNorm(Call(RoutinePtr("g"), Vector(K), Vector(src))),
      "alphaNorm renamed a RoutinePtr, which is a global name and not a binder")
    // a FREE name is not a binder either and must be preserved
    val free = Union(Mention(SpaceMention("free1")), src)
    assertEquals(namesIn(SmtDiff.alphaNorm(free)), Set("free1"),
      "alphaNorm renamed a FREE mention; only binder-bound occurrences may be canonicalised")
  }

  // ------------------------------------------------------------------------------------------------
  // E. IDEMPOTENCE.
  // ------------------------------------------------------------------------------------------------
  test("E. alphaNorm is idempotent on every descent case") {
    for (label, inner) <- descentCases do
      val t = Iteration(lit(p("s")), PathRef("y"), SpaceMention("rest"), inner)
      val once = SmtDiff.alphaNorm(t)
      assertEquals(SmtDiff.alphaNorm(once), once, s"alphaNorm is not idempotent at `$label`")
  }

  // ------------------------------------------------------------------------------------------------
  // F. SEMANTIC PRESERVATION — the actual soundness statement.
  // ------------------------------------------------------------------------------------------------
  test("F. alphaNorm preserves the denotation, through all three executors") {
    given PathContext = PathContextMap(Map.empty)
    given SpaceContext = SpaceContextMap(Map.empty)
    given PartialFunction[RoutinePtr, Routine] = PartialFunction.empty
    val closed: Vector[(String, Space)] = Vector(
      "iteration" -> Iteration(lit(p("a", "1"), p("b", "2")), PathRef("y"), SpaceMention("rest"),
                               Union(Mention(SpaceMention("rest")), Singleton(Path.Deref(PathRef("y"))))),
      "fixpoint"  -> Fixpoint(lit(p("a")), SpaceMention("rec"),
                              Union(Mention(SpaceMention("rec")), lit(p("b")))),
      "fold"      -> Fold(lit(p("a"), p("b")), K, PathRef("acc"), PathRef("sym"),
                          SpaceMention("rest"), Mention(SpaceMention("rest")),
                          Path.Concat(Path.Deref(PathRef("acc")), Path.Deref(PathRef("sym")))),
      "nested"    -> Iteration(lit(p("a", "1")), PathRef("y"), SpaceMention("rest"),
                               Wrap(TailsUnion(Mention(SpaceMention("rest"))), Path.Deref(PathRef("y")))),
    )
    for (label, t) <- closed do
      val n = SmtDiff.alphaNorm(t)
      assertEquals(eval(n), eval(t), s"$label: alphaNorm changed the reference denotation")
      assertEquals(evalI(n).toSpaceValue, evalI(t).toSpaceValue, s"$label: alphaNorm changed evalI")
      assertEquals(execZ(n).toSpaceValue, execZ(t).toSpaceValue, s"$label: alphaNorm changed execZ")
  }
end AlphaNormCheck
