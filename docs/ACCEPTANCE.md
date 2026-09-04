# Acceptance status — plan.md's successor

`plan.md` sequenced the work against the acceptance review; this file is what it says it must be
succeeded by (task 3.3): **one row per review item, each assigned only by its acceptance sentence and
the gate command that decides it**, with the measured verdict on 2026-09-04 at the tree this file was
written in. Nothing here is a claim of progress; a row is green when its command exits 0 and red
otherwise, and the command is the row.

Run the whole list with `sbt check` (which runs `python3 scripts/gates.py --run`; `--scripts-only`
skips the four Scala suites). `python3 scripts/publish_benchmarks.py --dry-run` runs the same gates
and says what blocks publication.

| item | acceptance sentence | gate command | verdict 2026-09-04 |
|---|---|---|---|
| 1 — cost model | the four measuring suites are green under the per-suite JVM, with the ledger empty of any entry whose subject no longer fails | `target/test-runtime/run-suite.sh morkl.SpatialCostCheck` / `…SpatialEventsCheck` / `…SpatialScaleCheck` / `…SpatialPipelineCheck` | **RED** — 1 / 2 / 1 / 1 requirement(s) fail per suite; the puzzle15 bound above 1e12 (plan.md 1B.5, the named single point of failure) and 2 of 3000 counted values outside a predicted interval. 0 `STALE FIGURE` rows: every recorded ledger figure is within 2% of this run (0.7, 3.3). |
| 2 — calls and ranges | `CrossFunctionCheck`, `RangeRankCheck`, `RangeOrderCheck`, `RangeCardCheck`, `SpatialRecursionCheck` green | `sbt 'testOnly morkl.CrossFunctionCheck morkl.RangeRankCheck morkl.RangeOrderCheck morkl.RangeCardCheck morkl.SpatialRecursionCheck'` | green at the Phase 1 commit (build.log, 1D); not re-measured in Phase 2/3, which did not touch Track D. |
| 3 — substitution and mechanization | `SubstConformance`, `SubstCapture`, `AlphaNormCheck` green; `check_lean.sh` green with every `PROVED-MODULO T1/T2` row lifted | `sbt 'testOnly morkl.SubstConformance morkl.SubstCapture morkl.AlphaNormCheck'` · `scripts/check_lean.sh` · `python3 scripts/proof_closure.py --check` | **GREEN** — 347 theorems, axioms exactly `propext`, `Quot.sound`, `Classical.choice`; T1, T2, T3, T8 discharged; O6a's semantic substitution lemma is the one premise still parametric (`terminating/REGISTRY.tsv`). |
| 4 — cornerstone coverage | every declared cell REAL or checked LAW-JUSTIFIED/TRIVIAL; 0 SINGLE-SIDE, 0 marker chains, 0 BUDGET; every cell holds to its CLAIMS.tsv row and coverage row | `python3 scripts/audit_pipeline_markers.py --run --accept` | **GREEN** — 42 of 42 cells accepted; REAL 1, LAW-JUSTIFIED 25, TRIVIAL 16; 0 BUDGET / SINGLE-SIDE / IDENT / BOUNDED; 104 coverage rows each backed by the artifact it names. |
| 5 — certificate tier | the six certificate suites green | `sbt 'testOnly morkl.SpatialCertCheck morkl.SpatialCertBudgetCheck morkl.SpatialFrontierCheck morkl.SpatialShapeCheck morkl.SpatialLawCheck morkl.SpatialSoundnessHunt'` | green at the Phase 1 commit (build.log, 1C); not re-measured in Phase 2/3. |
| 6 — publication | `publish_benchmarks.py` completes, and `publish_benchmarks.py --reproduce` exits 0 at the artifact commit | `python3 scripts/publish_benchmarks.py` then `python3 scripts/publish_benchmarks.py --reproduce` | **RED, blocked by item 1** — the publisher refuses at step 2 while the four item-1 suites are red (by design: a red gate blocks publication). The four committed outputs still name `9b818f3-dirty`, which no one can check out, and `--reproduce` says exactly that. The mode itself (worktree checkout, the commit's own gates, generation under its manifest, structural diff) is implemented and reaches its refusal at step 0. |
| 7 — references | `check_references.py --snapshot=index --strict` reports 0 dangling and every exception used; the self-test covers the named regressions plus a `resolves()` test against an in-memory name set | `python3 scripts/check_references.py --fresh --strict` · `python3 scripts/check_references.py --selftest` | **GREEN** — 0 dangling, 52 of 52 exceptions used; self-test PASS including (e), the in-memory name set with the filesystem disagreeing; vocabulary widened to `.lean`; `.gitignore` is no longer a whole-file skip. |
| 8 — proof closure | every `PROVED` across the six status tables depends only on Lean-checked theorems, checked correspondence and discharged cells; `check_lean.sh` lists the axioms each theorem uses and they are exactly Lean's | `python3 scripts/check_asserts.py` · `python3 scripts/proof_closure.py --check` · `scripts/check_lean.sh` | **GREEN** — 1686 SMT asserts classified, 0 unclassified; closure computed for TPTP (includes) and SMT (markers + `; TRUSTS:`); the rows that still rest on T7 (the counting axioms, not dischargeable — a model is given instead) say `PROVED-MODULO T7`. |

## What separates this tree from full acceptance

Two rows are red and they are one cause. Item 1's gate is the puzzle15 cost bound (`plan.md` 1B.5: "the
single point of failure of the whole plan") plus a two-value soundness miss in `SpatialEventsCheck`;
item 6 is red only because item 1 is. Nothing in Phases 2 and 3 changed either suite, and the ledger
check confirms no recorded figure has drifted (0 `STALE FIGURE`), so what remains is the domain work
Track B's record in `build.log` describes, not a measurement or plumbing gap.

## How the verdicts were taken

Each command above was run on this host on 2026-09-04 with the toolchain README.md pins (JDK 21, sbt
2.0.8, z3 5.1.0, Vampire 5.1.0, egglog 3.0.0, Lean 4.33.1 with Mathlib v4.33.1). The Scala suites were
run through the in-tree runner `target/test-runtime/run-suite.sh` (`sbt exportTestRuntime`), one JVM
per suite. `build.log` holds the per-phase records with the measurements behind every row.
