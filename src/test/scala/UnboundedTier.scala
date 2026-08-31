package morkl

import munit.FunSuite
import scala.io.Source

/** ==============================================================================================
 *  TIER 3 — THE UNBOUNDED TIER, as a gate.
 *
 *  ==The three tiers==
 *
 *  {{{
 *  tier-1  Lower.sizeBounds / Lower.lenBounds   syntactic interval propagation, ONE AST
 *  tier-2  SizeZ3 / LenZ3                       ground SMT, one `(declare-const n<i> Int)`
 *                                               per AST node of ONE AST
 *  tier-3  the .p corpus under proofs/unbounded  first-order operator LAWS, over ALL
 *                                               spaces, ALL paths and ALL bodies, run by vampire
 *  }}}
 *
 *  Tier-1 and tier-2 answer "what is the size of THIS term".  Neither can even write down "for
 *  all spaces A, B: |A u B| =< |A| + |B|" — tier-1 has no quantifiers and tier-2 has a finite
 *  supply of ground integer constants, one per node.  That transfer function is nevertheless the
 *  thing whose soundness everything downstream rests on, and until now it was checked only
 *  empirically, by the corpus differential gate.  Tier 3 states and proves it.
 *
 *  ==What this suite does==
 *
 *    1. reads `proofs/unbounded/STATUS.tsv` (written by `proofs/unbounded/run.sh`) and FAILS on a
 *       countermodel, a contradictory/vacuous axiom set, an unexpected OPEN, or a NEGATIVE
 *       CONTROL that got proved;
 *    2. asserts `proofs/unbounded/REGISTRY.tsv` is in sync with the `.p` files on disk, in both
 *       directions, and that every registry row has a verdict;
 *    3. prints the tier-1 / tier-2 / tier-3 table for the cornerstones, so the three tiers are
 *       reported together instead of in three unrelated places.
 *
 *  This suite does NOT run vampire: a full `run.sh` is ~20 minutes (the vacuity probe alone is 53
 *  extra prover calls).  It gates on the recorded verdicts, exactly as `scripts/check_obligations.py`
 *  gates on `proofs/STATUS.tsv`.  If vampire is absent the corpus cannot be re-derived at all, and
 *  the suite says so LOUDLY and skips rather than passing quietly (docs/traps.md 3).
 *  ============================================================================================== */
class UnboundedTier extends FunSuite:
  import Space.*
  import Lower.{LenBounds, SizeBounds}

  private val dir = new java.io.File(Loaders.repoRoot, "proofs/unbounded")
  private val statusFile = new java.io.File(dir, "STATUS.tsv")
  private val registryFile = new java.io.File(dir, "REGISTRY.tsv")

  /** the admitted-unproved list, MIRRORED from `proofs/unbounded/run.sh`'s EXPECTED_OPEN.  Each
   *  entry carries its attempt log in its own `.p` header; an OPEN outside this list is a
   *  regression and fails the suite. */
  private val expectedOpen = Set("mon_cancel")

  private case class Row(file: String, vampire: String, probe: String, verdict: String)

  private lazy val rows: Vector[Row] =
    val s = Source.fromFile(statusFile)
    try
      s.getLines().filter(_.nonEmpty).map(_.split("\t", -1)).collect {
        case Array(f, v, p, d) => Row(f, v, p, d)
      }.toVector
    finally s.close()

  private def loud(msg: String): Unit =
    println("!" * 100); println(msg); println("!" * 100)

  // ---------------------------------------------------------------------------- 1. the gate
  test("tier-3 corpus: no countermodel, no vacuous axiom set, no unexpected OPEN") {
    if !Tools.vampire.isAvailable then
      loud(s"SKIPPED — ${Tools.vampire.missing}\n" +
           "  proofs/unbounded/STATUS.tsv cannot be re-derived without vampire, so this gate is\n" +
           "  NOT being enforced on this machine.  Nothing below was checked.")
      assume(false, "vampire absent")
    assert(statusFile.exists,
      s"$statusFile is missing — run `sh proofs/unbounded/run.sh` (about 20 min) to produce it")
    assert(rows.nonEmpty, s"$statusFile is empty — rerun proofs/unbounded/run.sh")

    val vacuous = rows.filter(_.probe == "VACUOUS")
    assert(vacuous.isEmpty,
      "VACUOUS AXIOM SET — the axioms alone were refuted, so every verdict from these files is " +
      s"void (see _nat.p's header for why this probe exists): ${vacuous.map(_.file).mkString(", ")}")

    val bad = rows.filter(r => r.verdict.startsWith("COUNTERMODEL") || r.verdict.startsWith("CONTRADICTORY"))
    assert(bad.isEmpty, s"COUNTERMODEL / CONTRADICTORY obligations: ${bad.map(_.file).mkString(", ")}")

    val negBroken = rows.filter(r => r.file.startsWith("negative/") && r.verdict.contains("BROKEN"))
    assert(negBroken.isEmpty,
      "A NEGATIVE CONTROL WAS PROVED — the encoding proves too much and every verdict in the " +
      s"corpus is void: ${negBroken.map(_.file).mkString(", ")}")

    val (theorems, negatives) = rows.partition(!_.file.startsWith("negative/"))
    val opens = theorems.filter(_.verdict.startsWith("OPEN")).map(_.file).toSet
    val unexpected = opens -- expectedOpen
    assert(unexpected.isEmpty,
      s"OPEN obligations not in EXPECTED_OPEN (proofs/unbounded/run.sh): ${unexpected.mkString(", ")}")
    val shrunk = expectedOpen -- opens
    if shrunk.nonEmpty then
      loud(s"EXPECTED_OPEN can be shrunk — now PROVED: ${shrunk.mkString(", ")}")

    val proved = theorems.count(_.verdict.startsWith("PROVED"))
    println(f"\n### tier-3 (proofs/unbounded): $proved%d/${theorems.size}%d schematic obligations PROVED, " +
            f"${opens.size}%d admitted OPEN (${expectedOpen.mkString(",")})")
    println(f"    negative controls held: ${negatives.count(_.verdict.startsWith("NOT-PROVED"))}%d/${negatives.size}%d " +
            "(FALSE conjectures that must not be provable)")
    println(f"    vacuity probes clean:   ${theorems.count(_.probe == "ok")}%d/${theorems.size}%d " +
            "(axioms alone must not be refutable)")
  }

  // ---------------------------------------------------------------------------- 2. registry sync
  test("tier-3 registry is in sync with the files on disk and with STATUS.tsv") {
    assert(registryFile.exists, s"$registryFile is missing")
    val reg: Vector[Array[String]] =
      val s = Source.fromFile(registryFile)
      try s.getLines().filterNot(l => l.startsWith("#") || l.isEmpty).map(_.split("\t", -1)).toVector
      finally s.close()

    for r <- reg do
      assert(r.length == 5, s"REGISTRY.tsv row must have 5 columns (id/file/operator/statement/generalises): ${r.mkString("|")}")
      assert(r(3).nonEmpty && r(4).nonEmpty, s"REGISTRY.tsv row ${r(0)} has an empty statement or generalises column")
    assertEquals(reg.map(_(0)).distinct.size, reg.size, "duplicate ids in REGISTRY.tsv")

    val registered = reg.map(_(1)).toSet
    def ps(d: java.io.File, prefix: String): Set[String] =
      Option(d.listFiles()).toVector.flatten
        // `_*.p` are axiom modules (no conjecture, so no registry row) and a DOTFILE is a scratch
        // artifact — `run.sh`'s vacuity probe writes `.probe.p` next to the corpus — neither is an
        // obligation, and treating a leftover temp file as a registry desync is a false alarm.
        .map(_.getName).filter(n => n.endsWith(".p") && !n.startsWith("_") && !n.startsWith("."))
        .map(prefix + _).toSet
    val onDisk = ps(dir, "") ++ ps(new java.io.File(dir, "negative"), "negative/")

    assertEquals(registered -- onDisk, Set.empty[String], "REGISTRY.tsv names files that do not exist")
    assertEquals(onDisk -- registered, Set.empty[String], ".p files with no REGISTRY.tsv row")

    if statusFile.exists && rows.nonEmpty then
      val scored = rows.map(_.file + ".p").toSet
      assertEquals(registered -- scored, Set.empty[String], "registry rows with no verdict in STATUS.tsv")
    println(s"\n### tier-3 registry: ${reg.size} obligations, all present on disk and scored")
  }

  // ---------------------------------------------------------------------------- 3. the joint table
  /** the algebra constructors a term actually uses — the key into the tier-3 registry */
  private def operators(s: Space): Set[String] = s match
    case Empty | Literal(_) | Mention(_) | Singleton(_) => Set.empty
    case Union(a, b) => Set("union") ++ operators(a) ++ operators(b)
    case Intersection(a, b) => Set("intersection") ++ operators(a) ++ operators(b)
    case Subtraction(a, b) => Set("subtraction") ++ operators(a) ++ operators(b)
    case Restriction(a, b) => Set("restriction") ++ operators(a) ++ operators(b)
    case Raffination(a, b) => Set("raffination") ++ operators(a) ++ operators(b)
    case Composition(a, b) => Set("composition") ++ operators(a) ++ operators(b)
    case Wrap(a, _) => Set("wrap") ++ operators(a)
    case Unwrap(a, _) => Set("unwrap") ++ operators(a)
    case TailsUnion(a) => Set("tails-union") ++ operators(a)
    case TailsIntersection(a) => Set("tails-intersection") ++ operators(a)
    case Iteration(src, _, _, t) => Set("iteration") ++ operators(src) ++ operators(t)
    case Fixpoint(i, _, b) => Set("fixpoint") ++ operators(i) ++ operators(b)
    case Fold(src, _, _, _, _, t, _) => Set("iteration") ++ operators(src) ++ operators(t)
    case Range(x, _, _) => operators(x)
    case Call(_, _, ms) => ms.iterator.flatMap(operators).toSet
    case GroundedPS(_, _) => Set.empty
    case GroundedSS(p, _) => operators(p)

  private lazy val byOperator: Map[String, Vector[(String, String)]] =
    if !registryFile.exists then Map.empty
    else
      val s = Source.fromFile(registryFile)
      val reg = try s.getLines().filterNot(l => l.startsWith("#") || l.isEmpty).map(_.split("\t", -1)).toVector
                finally s.close()
      val verdict = rows.map(r => (r.file + ".p") -> r.verdict).toMap
      reg.filterNot(_(0).startsWith("N"))
        .flatMap(r => r(2).split(" / ").map(op => op.trim -> (r(0), verdict.getOrElse(r(1), "unscored"))))
        .groupMap(_._1)(_._2)

  private def fs(b: SizeBounds): String = s"[${b.lo}, ${if b.hi == SizeBounds.INF then "inf" else b.hi}]"
  private def fl(b: LenBounds): String =
    if b.isEmpty then "EMPTY" else s"[${b.lo}, ${if b.hi == LenBounds.INF then "inf" else b.hi}]"

  private def tierRow(name: String, prog: Space, rc: PartialFunction[RoutinePtr, Routine]): Unit =
    val sb = Lower.sizeBounds(prog, rc)
    val lb = Lower.lenBounds(prog, rc)
    val zs = if SizeZ3.available then Some(SizeZ3.boundsWithStatus(prog, timeoutSec = 8, rc)) else None
    val zl = if LenZ3.available then Some(LenZ3.boundsWithStatus(prog, timeoutSec = 8, rc)) else None
    def statusOf(o: Option[(?, SizeZ3.Status)]): String = o match
      case None => "no-z3"
      case Some((_, SizeZ3.Status.Solved)) => "solved"
      case Some((_, SizeZ3.Status.ScopeLimited(r))) => s"scope-limited(${r.take(30)})"
      case Some((_, SizeZ3.Status.PartiallySolved(d))) => s"PARTIAL($d)"
      case Some((_, SizeZ3.Status.SolverFailed(d))) => s"solver-failed($d)"
      case Some((_, SizeZ3.Status.NoSolver)) => "no-z3"
    val ops = operators(prog).toVector.sorted
    val cover = ops.map { op =>
      val hits = byOperator.getOrElse(op, Vector.empty)
      val open = hits.count(!_._2.startsWith("PROVED"))
      s"$op:${hits.size}${if open == 0 then "" else s"(${open} open)"}"
    }
    println(f"\n### $name%-14s")
    println(f"    tier-1  size ${fs(sb)}%-18s length ${fl(lb)}%-18s  (syntactic interval, THIS term)")
    println(f"    tier-2  size ${zs.map((z, _) => fs(z)).getOrElse("no-z3")}%-18s " +
            f"length ${zl.map((z, _) => fl(z)).getOrElse("no-z3")}%-18s  (ground SMT, one var per node of THIS term)")
    println(f"            z3 size ${statusOf(zs)}, z3 length ${statusOf(zl)}")
    println(f"    tier-3  ${cover.mkString("  ")}")
    println(f"            schematic laws covering the operators this term uses - for ALL inputs")
    for op <- ops do
      val hits = byOperator.getOrElse(op, Vector.empty)
      assert(hits.nonEmpty, s"$name uses `$op` but the tier-3 registry has no obligation for it")

  test("tier-1 / tier-2 / tier-3 side by side on the cornerstones") {
    if !statusFile.exists then
      loud("SKIPPED — proofs/unbounded/STATUS.tsv is missing; run `sh proofs/unbounded/run.sh`.")
      assume(false, "no STATUS.tsv")
    println("=" * 100)
    println("THE THREE TIERS OF SIZE/LENGTH REASONING, PER CORNERSTONE")
    println("  tier-1/tier-2 answer for ONE term; tier-3 is the operator law, for ALL terms")
    println("=" * 100)

    // 1. aunt — union / composition / restriction / iteration over the family trie
    tierRow("aunt", Routines.aunt_query_routine.body, PartialFunction.empty)

    // 2. temperature — two prefix-range (cylinder) restrictions unioned
    locally {
      val world = Mention(SpaceMention("world"))
      val q = Union(Restriction(world, Literal(NOAA.interval(0, 4, 4))),
                    Restriction(world, Literal(NOAA.interval(12, 16, 4))))
      tierRow("temperature", q, PartialFunction.empty)
    }

    // 3. n-queens — nested placement iterations
    locally {
      val b = NQueens.board(4)
      tierRow("nqueens", b.program, b.defs)
    }

    // 4. a union-saturating Fixpoint over an Iteration body — the control-flow pair, so the table
    //    exercises the two operators the equivalence pipeline has to EXPAND before it can prove
    //    anything, and which tier-2 answers with `n >= n_init, hi = inf`.
    locally {
      val rec = SpaceMention("r")
      val step = Space.Iteration(Space.Mention(rec), PathRef("h"), SpaceMention("t"),
                                 Space.Wrap(Space.Mention(SpaceMention("t")), Path.Deref(PathRef("h"))))
      val prog = Space.Fixpoint(Space.Mention(SpaceMention("seed")), rec,
                                Space.Union(Space.Mention(rec), step))
      tierRow("fixpoint-iter", prog, PartialFunction.empty)
    }

    // 5. the raffination/tails pair the fuzzer used to omit (plan.md item 6) — the operators with
    //    the fewest instance-tier obligations and therefore the most to gain from a schematic law.
    locally {
      val x = Mention(SpaceMention("x")); val y = Mention(SpaceMention("y"))
      val prog = Union(Raffination(x, y), TailsIntersection(TailsUnion(x)))
      tierRow("raff-tails", prog, PartialFunction.empty)
    }
    println("\n" + "=" * 100)
  }
end UnboundedTier
