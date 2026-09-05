package morkl

import munit.FunSuite
import morkl.Syntax.{*, given}
import scala.language.implicitConversions
import morkl.Space.*
import morkl.EffortComponent.*

/** tasks.md B3 — DECISIONS EXISTING OPTIMIZERS CANNOT MAKE SAFELY.
 *
 *  Acceptance: every selected alternative is semantically certified (closed trace, certified derivation);
 *  its counted resources lie in the predicted intervals; at least one case per transformation family is
 *  DIFFERENTIATED — a scalar predictor (rewrite count or output cardinality) names a different winner and
 *  the counted run confirms the certified choice.  The suite generates `docs/DECISIONS.md` and
 *  the `proofs/decisions` certificates through `ArtifactSink` (regenerate under ZIPPY_REGENERATE=1; a verify run fails
 *  on drift) and replays every certificate with `scripts/check_selection.py`. */
class DecisionsCheck extends FunSuite:
  override val munitTimeout = scala.concurrent.duration.Duration(40, "min")

  def p(items: String*): PathValue = PathValue(items.toList)
  def sv(ps: PathValue*): SpaceValue = SpaceValue(ps.toSet)
  val s = SpaceMention("s"); val k = SpaceMention("k"); val h = PathRef("h"); val r = SpaceMention("r"); val m = SpaceMention("m")

  // ---- 1. DISJOINT VERSUS OVERLAPPING N-ARY TAILS -----------------------------------------------------
  val tailsBody: Space =
    Union(Iteration(TailsUnion(Union(Mention(s), Mention(k))), h, r, Wrap(Intersection(Mention(r), Mention(k)), Path.Deref(h))),
          Union(Iteration(TailsUnion(Union(Mention(s), Mention(k))), h, r, Wrap(TailsUnion(Mention(r)), Path.Deref(h))),
                Iteration(Mention(s), h, r, Union(Wrap(Subtraction(Mention(r), Mention(k)), Path.Deref(h)), TailsUnion(Mention(k))))))
  val tails = Routine(RoutinePtr("tails"), Vector.empty, Vector(s, k), tailsBody)
  val disjointS = sv(p("a", "x", "1"), p("a", "y", "2"), p("b", "x", "3"), p("b", "z", "4"), p("a", "x", "5"))
  val disjointK = sv(p("c", "x", "1"), p("c", "y", "2"), p("d", "x", "3"), p("d", "w", "4"))
  val overlapS = disjointS
  val overlapK = sv(p("a", "x", "1"), p("a", "y", "9"), p("b", "x", "3"), p("b", "w", "4"))

  // ---- 2. FIRST/LAST RANGE AFTER A CALL ------------------------------------------------------------------
  val n = SpaceMention("n")
  val f = Routine(RoutinePtr("f"), Vector.empty, Vector(m, n),
                  Union(Iteration(Mention(m), h, r, Union(Wrap(Intersection(Mention(r), Mention(n)), Path.Deref(h)), TailsUnion(TailsUnion(Mention(n))))),
                        Iteration(Mention(m), h, r, Wrap(TailsUnion(Mention(r)), Path.Deref(h)))))
  val rangeBody: Space = Union(Range(Call(f.name, Vector.empty, Vector(Mention(s), Mention(k))), 0, 2),
                               Range(Call(f.name, Vector.empty, Vector(Union(Mention(s), Mention(k)), Mention(k))), 0, 1))
  val range = Routine(RoutinePtr("range"), Vector.empty, Vector(s, k), rangeBody)

  // ---- 3. FUSION THAT TRADES ALLOCATION FOR WORK ----------------------------------------------------------
  val fusionBody: Space =
    Union(
      Union(Iteration(Mention(s), h, r, Wrap(Intersection(Mention(r), Mention(k)), Path.Deref(h))),
            Iteration(Mention(s), h, r, Wrap(TailsUnion(Mention(r)), Path.Deref(h)))),
      Union(Iteration(Mention(s), h, r, Union(Wrap(Subtraction(Mention(r), Mention(k)), Path.Deref(h)), Mention(k))),
            Restriction(Union(Mention(s), TailsUnion(Mention(k))), Literal(sv(p("a"), p("b"))))))
  val fusion = Routine(RoutinePtr("fusion"), Vector.empty, Vector(s, k), fusionBody)

  // ---- 4. POINTER-PRESERVING REBUILD: restriction pushed to the operands, or of the materialized union ----
  val rebuildBody: Space =
    Restriction(Union(Union(Wrap(Mention(k), Path.Constant(p("a"))), Mention(s)), Union(TailsUnion(Mention(k)), Wrap(Mention(s), Path.Constant(p("b"))))),
                Union(Literal(sv(p("a"))), Literal(sv(p("b", "x")))))
  val rebuild = Routine(RoutinePtr("rebuild"), Vector.empty, Vector(s, k), rebuildBody)
  val bigS = sv((for i <- 0 until 12; j <- 0 until 3 yield p(if i % 3 == 0 then "a" else if i % 3 == 1 then "b" else "c", s"x$i", s"y$j"))*)
  val smallK = sv(p("x", "1"), p("y", "2"), p("b", "x", "3"))

  // ---- 5. PUZZLE15 PROJECTION / MATERIALIZATION -----------------------------------------------------------
  val puzzle = Sliding.puzzle(4, 4)
  val frontier = SpaceMention("frontier")
  val p15 = Routine(RoutinePtr("expand"), Vector.empty, Vector(frontier), puzzle.expandStep(Mention(frontier)))

  val sVal = sv(p("a", "x"), p("a", "y", "z"), p("b", "x"), p("c", "q", "r", "t"), p("b"), p("a", "x", "w"))
  val kVal = sv(p("x"), p("y", "z"), p("q", "r"), p("a", "x"), p("b"))

  val cases: Vector[Decisions.Case] = Vector(
    Decisions.Case("tails-disjoint", "n-ary tails", "s and k have DISJOINT head sets ({a,b} against {c,d}); every path has length 3",
      tails, Map(tails.name -> tails), Map(s -> disjointS, k -> disjointK), Pareto.Objective.minimise(Alloc),
      story = "The n-ary tails-union of `s ∪ k` is iterated twice (fusable) beside a loop over `s` with a loop-invariant `tails(k)` (hoistable). With disjoint heads the union of the two inputs is a pointer attach and the tails-union's children are accepted whole; which residual allocates least depends on how many times the merged tails are rebuilt, not on how many paths come out."),
    Decisions.Case("tails-overlap", "n-ary tails", "s and k have the SAME head set ({a,b}); their depth-2 prefixes overlap on a.x and b.x",
      tails, Map(tails.name -> tails), Map(s -> overlapS, k -> overlapK), Pareto.Objective.minimise(Alloc),
      story = "The same program as `tails-disjoint` under the overlapping precondition: now every merge descends and rebuilds. The output cardinality barely moves; the allocation profile of the alternatives does, and the certified choice may change with it."),
    Decisions.Case("range-after-call", "first/last range", "s has 6 paths over heads {a,b,c}, k has 5; the ranges keep at most 2 and 1 result paths",
      range, Map(range.name -> range, f.name -> f), Map(s -> sVal, k -> kVal), Pareto.Objective.minimise(Work),
      story = "A `Range` keeps the first one or two paths of a call's result. An output-cardinality estimator sees one or two paths and calls every alternative cheap; the work is in building the call's result before ranging, and the alternatives differ in how the callee's two loops and its invariant are composed after inlining."),
    Decisions.Case("fusion-alloc-work", "fusion", "s has 6 paths over heads {a,b,c}, k has 5 paths over {x,y,q,a,b}",
      fusion, Map(fusion.name -> fusion), Map(s -> sVal, k -> kVal), Pareto.Objective.minimise(Alloc),
      story = "Two same-source loops fuse into one (one pass, one loop entry per head) and an invariant branch hoists out of a third loop. Fusion saves loop entries and dispatches but merges two bodies' allocations; hoisting saves allocation but adds a guard composition. Neither trade is visible to a node count."),
    Decisions.Case("fusion-work-trie", "fusion", "the same inputs as fusion-alloc-work; the caller can only run the trie executor",
      fusion, Map(fusion.name -> fusion), Map(s -> sVal, k -> kVal), Pareto.Objective("work-on-trie", Vector(Work, Alloc, Rounds, Touch), backends = Vector(Backend.Trie)),
      story = "The same frontier under the other half of the trade: minimise trie work. Fusing the two loops saves allocation (one accumulator instead of two and a merged wrap per head) but the fused body does more dispatch work per head on the trie; the unfused residual — larger, fewer rewrites — has the tighter work bound and the smaller counted work. A rewrite count picks the fused one."),
    Decisions.Case("pointer-rebuild", "pointer-preserving rebuild", "s has 36 paths of length 3 under heads {a,b,c}; k has 3 paths; the restriction prefixes are {a, b.x}",
      rebuild, Map(rebuild.name -> rebuild), Map(s -> bigS, k -> smallK), Pareto.Objective.minimise(Alloc),
      story = "Restricting a four-way union by two prefixes: pushed to the operands, each restriction accepts or rejects whole subtries by pointer and the small operands are rebuilt cheaply; applied to the materialized union, the union itself is built first. The residuals have different node counts and the smaller one is not the one that allocates less."),
    Decisions.Case("puzzle15-expand", "puzzle15 projection/materialization", "the frontier is the single initial board (blank at c0, tiles 1..15 in order); one BFS expansion",
      p15, puzzle.defs.orElse(Map(p15.name -> p15)), Map(frontier -> sv(puzzle.initial)), Pareto.Objective.minimise(Work),
      Alternatives.Options(pairs = false, unrolls = Vector.empty),
      story = "One BFS expansion of the 15-puzzle on every backend: the board is superposed into per-cell projections, moves are applied, and the result is collapsed back. The materialization choice is `comp-lit-to-wraps`: the literal move table composed with the projected board is either kept as one composition (attached under each move prefix in one pass) or MATERIALISED as a union of wraps, one copy of the projection per literal path. The materialised residual is smaller after more rewrites, and a rewrite count prefers it; keeping the composition does less work, which the certified intervals predict and the counted run confirms. The backends differ in what they materialise (the zipper walks, the trie shares subtries by pointer, the graph runs the operation DAG). Over every backend the graph executor wins and it happens to prefer the materialised residual, so the rewrite count agrees here; the companion case restricts the backend and the agreement ends."),
    Decisions.Case("puzzle15-expand-reference", "puzzle15 projection/materialization", "the same frontier; the caller runs the reference (set-based) evaluator",
      p15, puzzle.defs.orElse(Map(p15.name -> p15)), Map(frontier -> sv(puzzle.initial)),
      Pareto.Objective("work-on-reference", Vector(Work, Alloc, Rounds, Touch), backends = Vector(Backend.Reference)),
      Alternatives.Options(pairs = false, unrolls = Vector.empty),
      story = "The same four residuals of the 15-puzzle expansion, priced for the reference evaluator only. Here materialising the projection under each move prefix (`comp-lit-to-wraps`) COSTS work — every copy is re-evaluated — so the residual that keeps the composition, larger and reached by fewer rewrites, is the certified choice; the rewrite count picks the materialised one. Which residual is cheaper depends on the backend, which is exactly what a backend-blind heuristic cannot express and a per-backend certificate can."))

  lazy val outcomes: Vector[Decisions.Outcome] =
    cases.map { c =>
      val t0 = System.nanoTime()
      val o = Decisions.run(c)
      println(f"B3 ${c.name}%-26s ${o.frontier.alternatives.length} alternatives, selected ${o.selected.key}, ${(System.nanoTime() - t0) / 1e9}%.1fs")
      o
    }

  val decDir = new java.io.File("proofs/decisions")

  test("EVERY SELECTED ALTERNATIVE is semantically certified and its counted run lies in the predicted intervals") {
    for o <- outcomes do
      val a = o.alt(o.selected.alt)
      assert(a.certified, s"${o.c.name}: derivation not certified")
      val cl = TraceClosure.of(a.trace +: a.nodeTraces.values.toVector)
      assert(cl.closed, s"${o.c.name}: trace closure ${cl.render}")
      val bad = ProofTrace.Checker.check(a.trace, o.c.defs, a.nodes)
      assert(bad.isEmpty, s"${o.c.name}: ${bad.mkString("; ")}")
      assert(o.counted.contains((o.selected.alt, o.selected.backend)), s"${o.c.name}: the selected backend ${o.selected.backend.slug} did not run")
      assert(o.contained.isEmpty, s"${o.c.name}: ${o.contained.mkString("; ")}")
      // every alternative's counted run is inside its own certificate on every backend that ran it
      for a2 <- o.frontier.alternatives; b <- Backend.values; ev <- o.counted.get((a2.id, b)) do
        val v = a2.certificate(b).bounds.violations(ev)
        assert(v.isEmpty, s"${o.c.name}/${a2.id}/${b.slug}: ${v.mkString("; ")}\n  residual: ${a2.top.show.replace("\n", " ")}\n" +
                          a2.certificate(b).derivation.render().linesIterator.take(80).mkString("\n"))
      // semantically equivalent on the concrete inputs
      val vals = o.frontier.alternatives.map(a2 => eval(a2.top)(using PathContextMap(Map.empty), SpaceContextMap(o.c.values), a2.residual.env))
      assertEquals(vals.distinct.length, 1, s"${o.c.name}: alternatives disagree")
      println(s"B3 ${o.c.name}: ${o.scalar.map(v => s"${v.name}→${v.winner} ${o.verdictOn(v)._1}").mkString(", ")}")
  }

  test("AT LEAST ONE DIFFERENTIATED CASE PER FAMILY: a scalar predictor names a different winner and the counted run confirms the certified choice") {
    val byFamily = outcomes.groupBy(_.c.family)
    for (fam, os) <- byFamily.toVector.sortBy(_._1) do
      val diff = os.filter(_.differentiated)
      println(s"B3 family $fam: ${diff.length}/${os.length} differentiated" + os.map(o => s" ${o.c.name}=${o.scalar.map(v => o.verdictOn(v)._1).mkString("/")}").mkString)
      assert(diff.nonEmpty, s"family $fam: no differentiated case — " + os.map(o => s"${o.c.name}: ${o.scalar.map(v => s"${v.name}→${v.winner}:${o.verdictOn(v)}").mkString(", ")} selected ${o.selected.key}").mkString("; "))
    // no case is CONTRADICTED: a scalar winner never beats the certified choice on the counted objective component
    for o <- outcomes; v <- o.scalar do assert(o.verdictOn(v)._1 != "CONTRADICTED", s"${o.c.name}/${v.name}: the counted run contradicts the certified choice: ${o.verdictOn(v)}")
  }

  test("ARTIFACTS: certificates, the index and docs/DECISIONS.md are written through the sink and replay independently") {
    for o <- outcomes do
      ArtifactSink.write(new java.io.File(decDir, s"${o.c.name}-${o.c.objective.name}.tsv"), o.selection.render)
      // the frontier itself, so the alternatives named by the certificate are on record
      ArtifactSink.write(new java.io.File(decDir, s"${o.c.name}.frontier.tsv"), o.frontier.render)
    ArtifactSink.write(new java.io.File(decDir, "DECISIONS.tsv"), Decisions.indexHeader + outcomes.map(_.row).mkString("\n") + "\n")
    ArtifactSink.write(new java.io.File("docs/DECISIONS.md"), Decisions.document(outcomes))
    // the produced certificates (committed or scratch twins) replay under the independent checker
    val produced = ArtifactSink.produced.filter(p => p.startsWith("proofs/decisions/") && p.endsWith(".tsv") && !p.endsWith("DECISIONS.tsv") && !p.endsWith(".frontier.tsv"))
    assert(produced.nonEmpty)
    val files = produced.map(p => if ArtifactSink.regenerating then p else new java.io.File(ArtifactSink.scratchRoot, p).getPath)
    val proc = new ProcessBuilder(("python3" +: "scripts/check_selection.py" +: files)*).redirectErrorStream(true).start()
    val out = scala.io.Source.fromInputStream(proc.getInputStream).mkString
    assertEquals(proc.waitFor(), 0, out)
    println(out.linesIterator.toVector.last)
  }

  test("every committed decision artifact matches what this suite produces") {
    ArtifactSink.assertClean("morkl.DecisionsCheck")
  }
