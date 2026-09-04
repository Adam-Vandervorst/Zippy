package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions

/** ==================================================================================================
 *  THE ITEM 4 <-> ITEM 8 INTERFACE, CHECKED (plan.md 0.8).
 *
 *  0.8's acceptance sentence is "both items' emitters and readers agree on one format".  Agreement is
 *  not something a specification document can establish — `docs/TRUSTED.md` describing a header and
 *  `Certified.scala` implementing a different one is exactly the drift that a spec-only task
 *  produces.  So the agreement is checked, in four places:
 *
 *   1. ROUND TRIP.  Everything `trustsHeader` writes, `readTrusts` reads back identically, in all
 *      three comment syntaxes the corpora use.
 *   2. THE TWO FAILURE MODES ARE DISTINCT AND BOTH FAIL.  A MISSING header and a MALFORMED token are
 *      both `Left`, and neither may be reported as "trusts nothing".  This is the property the whole
 *      marker rests on: if a reader silently returned the empty set for a file with no header, an
 *      emitter that forgot the line would be indistinguishable from one asserting the strongest
 *      claim in the tree.
 *   3. THE BOUNDARY IS TOTAL, and each case reports the entry `docs/TRUSTED.md` says it should.
 *      Constructor coverage is read from `MORKL.scala`, as in `AlphaNormCheck`, so a NEW constructor
 *      fails this test rather than silently defaulting to "inside the certified algebra" — which is
 *      the dangerous default, because it is the one that licenses an unqualified claim.
 *   4. THE SCHEMA MATCHES THE FILE.  `proofs/pipeline/CLAIMS.tsv`'s declared header row is exactly
 *      `Certified.ClaimsColumns`, so the table and the code cannot disagree about column order.
 *
 *  There is no consumer of any of this yet, and that is deliberate: 2A.2's emitters and 2E.4's
 *  readers are the consumers, and 0.8 exists so that when they are written they are written against
 *  one format.  What this suite prevents is the format drifting in the interval.
 *  ================================================================================================== */
class CertifiedFormatCheck extends FunSuite:
  import Certified.*
  import Certified.Trust.*

  def p(items: String*): PathValue = PathValue(items.toList)
  def lit(ps: PathValue*): Space = Space.Literal(SpaceValue(ps.toSet))

  // ------------------------------------------------------------------------------------------------
  // 1. ROUND TRIP
  // ------------------------------------------------------------------------------------------------
  val sample: Vector[Vector[Trust]] = Vector(
    Vector.empty,
    Vector(Base("T4")),
    Vector(Base("T5"), Base("T6")),
    Vector(Open("O6a")),
    Vector(Open("O10b"), Open("O12d")),
    Vector(Law("unwrap-merge")),
    Vector(Law("iter-transpose-semijoin"), Law("wrap-iter")),
    Vector(Outside("Range")),
    Vector(Base("T4"), Open("O10b"), Law("unwrap-merge"), Outside("Fixpoint")),
  )

  test("1. every trusts list round-trips through the header, in all three comment syntaxes") {
    for ts <- sample; comment <- Vector(";", "%") do
      val hdr = trustsHeader(ts, comment)
      assert(hdr.startsWith(comment), s"header does not use the requested comment syntax: $hdr")
      readTrusts(hdr) match
        case Left(why) => fail(s"could not read back `${hdr.trim}`: $why")
        case Right(got) =>
          assertEquals(got.map(_.render).sorted, ts.map(_.render).distinct.sorted,
            s"round trip lost or altered an entry: wrote `${hdr.trim}`")
  }

  test("1'. the header is found inside a realistic artifact preamble, not only alone") {
    val artifact =
      "; AUTO-GENERATED pipeline graph (aunt) — DATA-AGNOSTIC.\n" +
      trustsHeader(Vector(Base("T4"), Law("unwrap-merge"))) +
      "; PROVER LOG (both provers are run on every obligation)\n" +
      "(set-logic ALL)\n(check-sat)\n"
    assertEquals(readTrusts(artifact).map(_.map(_.render).sorted),
                 Right(Vector("T4", "law:unwrap-merge")))
  }

  test("1''. `-` means TRUSTS NOTHING and reads back as the empty list") {
    assertEquals(readTrusts("; TRUSTS: -\n"), Right(Vector.empty[Trust]))
    assertEquals(trustsHeader(Vector.empty), "; TRUSTS: -\n")
  }

  // ------------------------------------------------------------------------------------------------
  // 2. THE TWO FAILURE MODES
  // ------------------------------------------------------------------------------------------------
  test("2. a MISSING header is a failure, never an empty trusts list") {
    val noHeader = "; AUTO-GENERATED — aunt stage 1\n(set-logic ALL)\n(check-sat)\n"
    readTrusts(noHeader) match
      case Right(v) =>
        fail(s"an artifact with NO `TRUSTS:` header read back as $v.  `-` is a claim someone made " +
             "and a missing line is a claim nobody made; conflating them lets an emitter bug read " +
             "as the strongest claim in the tree.")
      case Left(why) => assert(why.contains("no `TRUSTS:` header"), s"unhelpful reason: $why")
  }

  test("2'. an UNRECOGNISED token is a failure, and is NAMED — never skipped") {
    for bad <- Vector("T", "Tx", "X1", "law", "outside", "T1.5", "law :x", "junk") do
      readTrusts(s"; TRUSTS: T4, $bad\n") match
        case Right(v) =>
          fail(s"the token `$bad` was accepted or SKIPPED (read back as ${v.map(_.render)}).  A " +
               "token a reader cannot parse must never be dropped: that is a dependency dropped.")
        case Left(why) =>
          assert(why.contains(bad), s"the failure does not name the offending token `$bad`: $why")
  }

  test("2''. Trust.parse and Trust.render are inverse on every form") {
    for ts <- sample; t <- ts do
      assertEquals(Trust.parse(t.render), Some(t), s"parse(render(${t.render})) != ${t.render}")
  }

  // ------------------------------------------------------------------------------------------------
  // 3. THE BOUNDARY
  // ------------------------------------------------------------------------------------------------
  val K: Path = Path.Constant(p("k"))
  val L: Space = lit(p("a"))

  /** (constructor name, a term containing it, the trusts `boundary` must report for it) */
  val boundaryCases: Vector[(String, Space, Set[String])] = Vector(
    // inside the certified algebra: nothing reported
    ("Empty",              Space.Empty, Set.empty),
    ("Literal",            L, Set.empty),
    ("Mention",            Space.Mention(SpaceMention("m")), Set.empty),
    ("Singleton",          Space.Singleton(K), Set.empty),
    ("Union",              Space.Union(L, L), Set.empty),
    ("Intersection",       Space.Intersection(L, L), Set.empty),
    ("Subtraction",        Space.Subtraction(L, L), Set.empty),
    ("Restriction",        Space.Restriction(L, L), Set.empty),
    ("Raffination",        Space.Raffination(L, L), Set.empty),
    ("Composition",        Space.Composition(L, L), Set.empty),
    ("Wrap",               Space.Wrap(L, K), Set.empty),
    ("Unwrap",             Space.Unwrap(L, K), Set.empty),
    ("TailsUnion",         Space.TailsUnion(L), Set.empty),
    ("TailsIntersection",  Space.TailsIntersection(L), Set.empty),
    ("Iteration",          Space.Iteration(L, PathRef("y"), SpaceMention("r"), L), Set.empty),
    ("Fold",               Space.Fold(L, K, PathRef("a"), PathRef("y"), SpaceMention("r"), L, K),
                            Set.empty),
    // outside, each with the entry docs/TRUSTED.md names for it
    ("Range",              Space.Range(L, 0, 1), Set("T5")),
    ("Call",               Space.Call(RoutinePtr("f"), Vector(K), Vector(L)), Set("O6a")),
    // 2E.1: a POSITIVE body is inside the algebra (Positive.lean#fixpoint_is_lfp); nothing to trust
    ("Fixpoint",           Space.Fixpoint(L, SpaceMention("rec"), L), Set()),
    ("GroundedPS",         Space.GroundedPS(K, (_: PathValue) => SpaceValue(Set(p("g")))), Set("T6")),
    ("GroundedSS",         Space.GroundedSS(L, (v: SpaceValue) => v), Set("T6")),
  )

  val pathBoundaryCases: Vector[(String, Path, Set[String])] = Vector(
    ("Deref",       Path.Deref(PathRef("y")), Set.empty),
    ("Constant",    K, Set.empty),
    ("Concat",      Path.Concat(K, K), Set.empty),
    ("GroundedPP",  Path.GroundedPP(K, (v: PathValue) => v), Set("T6")),
    ("GroundedSP",  Path.GroundedSP(L, (_: SpaceValue) => p("g")), Set("T6")),
  )

  test("3. Certified.boundary reports exactly the declared entry, per constructor") {
    for (label, t, want) <- boundaryCases do
      assertEquals(boundary(t).map(_.render).toSet, want,
        s"boundary($label) disagrees with docs/TRUSTED.md.  Reporting nothing where an entry is due " +
        "is the dangerous direction: it licenses an unqualified claim over a term the algebra does " +
        "not certify.")
      assertEquals(isCertified(t), want.isEmpty, s"isCertified($label) disagrees with boundary")
    for (label, q, want) <- pathBoundaryCases do
      assertEquals(boundary(Space.Singleton(q)).map(_.render).toSet, want,
        s"boundary(Path.$label) disagrees with docs/TRUSTED.md")
  }

  test("3'. boundary is transitive through every container, and accumulates") {
    val bad = Space.Range(Space.Call(RoutinePtr("f"), Vector(K), Vector(L)), 0, 1)
    assertEquals(boundary(bad).map(_.render).toSet, Set("T5", "O6a"),
      "boundary did not accumulate both reasons; a term can leave the algebra more than once")
    // buried arbitrarily deep, and under every binder
    // a fixpoint whose body is NOT positive in its recursion variable (the variable under a
    // complement) is outside the algebra — and it is reported from under every binder
    val nonPositive = Space.Fixpoint(L, SpaceMention("z"), Space.Subtraction(L, Space.Mention(SpaceMention("z"))))
    val deep = Space.Iteration(L, PathRef("y"), SpaceMention("r"),
                 Space.Fold(L, K, PathRef("a"), PathRef("v"), SpaceMention("q"),
                   Space.Wrap(Space.TailsUnion(nonPositive), K), K))
    assertEquals(boundary(deep).map(_.render).toSet, Set("outside:Fixpoint"),
      "boundary does not descend through binders and containers — a non-positive `Fixpoint` buried " +
      "under an Iteration/Fold/Wrap/TailsUnion nest went unreported")
    // and the SAME nest around a positive fixpoint reports nothing: 2E.1 moved it inside
    val deepOk = Space.Iteration(L, PathRef("y"), SpaceMention("r"),
                 Space.Fold(L, K, PathRef("a"), PathRef("v"), SpaceMention("q"),
                   Space.Wrap(Space.TailsUnion(Space.Fixpoint(L, SpaceMention("z"), L)), K), K))
    assertEquals(boundary(deepOk).map(_.render).toSet, Set(),
      "a positive Fixpoint is inside the certified algebra since Positive.lean; nothing to trust")
  }

  test("3''. this suite covers EVERY Space and Path constructor MORKL.scala declares") {
    // Same reader as AlphaNormCheck's, and for the same reason: the compiler's exhaustivity check is
    // a warning in this build, and the default for an unlisted constructor here is "certified",
    // which is the direction that licenses a claim.
    val declaredS = AlphaNormReflect.enumCases("Space")
    val declaredP = AlphaNormReflect.enumCases("Path")
    assertEquals(declaredS.filterNot(boundaryCases.map(_._1).toSet), Vector.empty[String],
      "a `Space` constructor exists that Certified.boundary is not exercised on — and an unexercised " +
      "constructor defaults to INSIDE the certified algebra, which is the claim-licensing direction")
    assertEquals(declaredP.filterNot(pathBoundaryCases.map(_._1).toSet), Vector.empty[String],
      "a `Path` constructor exists that Certified.boundary is not exercised on")
    println(s"CERTIFIED: boundary exercised on ${declaredS.length} Space + ${declaredP.length} Path " +
            "constructors")
  }

  // ------------------------------------------------------------------------------------------------
  // 4. THE SCHEMA
  // ------------------------------------------------------------------------------------------------
  test("4. proofs/pipeline/CLAIMS.tsv's header row is exactly Certified.ClaimsColumns") {
    val f = new java.io.File(Loaders.repoRoot, "proofs/pipeline/CLAIMS.tsv")
    assert(f.isFile, s"${f.getPath} does not exist — 0.8 declares the FORMAT, so the file must exist " +
                     "even with no data rows")
    val lines = scala.io.Source.fromFile(f).getLines().toVector
    // the schema line is the LAST comment line: `# col<TAB>col<TAB>...`
    val schema = lines.filter(_.startsWith("#")).lastOption
      .getOrElse(fail("CLAIMS.tsv has no comment lines at all"))
    val cols = schema.stripPrefix("#").trim.split("\t").iterator.map(_.trim).filter(_.nonEmpty).toVector
    assertEquals(cols, Certified.ClaimsColumns,
      "CLAIMS.tsv's declared header row and `Certified.ClaimsColumns` disagree.  They are the SAME " +
      "declaration in two places on purpose — the table is what a human writes and the vector is " +
      "what the emitter and the two readers use — so a difference means one of the three is about " +
      "to read the wrong column.")
    val data = lines.filterNot(l => l.startsWith("#") || l.isBlank)
    println(s"CERTIFIED: CLAIMS.tsv schema = ${cols.mkString(", ")} (${data.length} declared row(s); " +
            "0.8 fixes the format, 2A.1 declares the rows)")
    // every data row, once 2A.1 writes them, must have the right arity and a parseable `trusts` cell
    for (row, i) <- data.zipWithIndex do
      val cells = row.split("\t", -1)
      assertEquals(cells.length, cols.length, s"CLAIMS.tsv row ${i + 1} has ${cells.length} cells, " +
                                              s"not ${cols.length}: $row")
      val trusts = cells(cols.indexOf("trusts"))
      assert(readTrusts(s"; TRUSTS: $trusts\n").isRight,
        s"CLAIMS.tsv row ${i + 1}'s `trusts` cell is not in Certified.Trust's vocabulary: `$trusts`")
  }
end CertifiedFormatCheck

/** The `enum` case reader, shared with [[AlphaNormCheck]].
 *
 *  It lives in its own object rather than being duplicated: both suites need "every constructor
 *  `MORKL.scala` declares", both need it to FAIL when a constructor is added, and two copies of a
 *  parser for the same file is two things to drift.  The parsing subtleties it encodes were both
 *  found by running it (see the comments): the enum body's own `def show ... this match` arms read as
 *  declarations, and `GroundedPS`/`GroundedSS` have function TYPES in their parameter lists. */
object AlphaNormReflect:
  def enumCases(enumName: String): Vector[String] =
    val src = new java.io.File(Loaders.repoRoot, "src/main/scala/MORKL.scala")
    val lines = scala.io.Source.fromFile(src).getLines().toVector
    val start = lines.indexWhere(_.trim == s"enum $enumName:")
    assert(start >= 0, s"could not find `enum $enumName:` in ${src.getPath}")
    val stop = Set("def ", "val ", "var ", "end ", "object ", "given ", "private ", "inline ")
    val body = lines.drop(start + 1)
      .takeWhile(l => l.isBlank || l.startsWith(" ") || l.startsWith("\t"))
      .takeWhile(l => !stop.exists(l.trim.startsWith))
    def arrowAtTopLevel(t: String): Boolean =
      var depth = 0; var i = 0; var hit = false
      while i < t.length do
        t.charAt(i) match
          case '(' | '[' => depth += 1
          case ')' | ']' => depth -= 1
          case '=' if depth == 0 && i + 1 < t.length && t.charAt(i + 1) == '>' => hit = true
          case _ => ()
        i += 1
      hit
    body.flatMap { l =>
      val t = l.trim
      if t.startsWith("case ") && !arrowAtTopLevel(t) then
        Some(t.stripPrefix("case ").takeWhile(c => c.isLetterOrDigit))
      else None
    }.filter(_.nonEmpty).distinct
end AlphaNormReflect
