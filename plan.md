# plan.md — addressing the acceptance review in full

> **Successor:** `docs/ACCEPTANCE.md` (task 3.3) — one row per review item, assigned only by its
> acceptance sentence and gate command, with the measured verdict.  This file is the plan; that file is
> the status.

The review is deliberately untracked (`review.md`, see `.gitignore`): it is an input. This file is the
plan against it. Sequenced by **dependency**, not by tractability. Every task names its files and
the command that proves it done; every item is done when its own "Acceptance requires …" sentence
holds and nothing else.

## Why the previous round failed, in one paragraph

It sized nothing against the acceptance sentences, built declarative mechanisms with no consumer and
reported them as progress, quoted measurements that lived outside the repository, discovered every
cross-item dependency after the work instead of before it, and never started the Lean development
that two items make a precondition of any unqualified `PROVED`. Fixing three unsound bounds it found
was correct and raised every upper endpoint, so its one gated item moved *away* from acceptance. This
plan is built so that none of those can recur: no task without a gate command, no phase without a
dependency check, no measurement outside the tree.

## Five corrections to the obvious sequencing

1. **Item 1 does not need item 5.** `TailsFacts.of` (`SpatialCost.scala`) already computes per-child
   head sets before flattening them to a count; `tails-*` closes by keeping them.
2. **puzzle15's astronomical bounds are item 1's**, not item 5's: `groupTailType` and
   `ChainCost.leafEnv` install `Shape.top` for every `rest` mention.
3. **Substitution is worse than reported.** `substMention`/`substPathRef` are shadow-aware, not
   capture-avoiding; only `Matching.subst` is; there are four implementations plus blind `subs` in
   three `Lower` rules; `Lower.inline`'s one-parameter-at-a-time loop is unsound for `g(y,x)`; and
   `SubstConformance` substitutes closed `Literal`s only, so it cannot see capture.
4. **Item 4's honest baseline is ~8 REAL cells, not 19.** Eleven of the twelve REAL `.egg` cells
   compare one program against `Reflect(tnodeOf(resT))` — the executor's own output.
5. **`PricingTarget` is a prerequisite**, not a peer task: `SpatialCost.go`'s fallback swaps the
   whole model, so any trie-side must-count lands in zipper totals where `materialize` allocates
   strictly less.

---

## Phase 0 — Foundations

**Gate:** `sbt check` green (all script gates) · `scripts/check_determinism.sh` exits 0 · after
`sbt test`, `git status --porcelain proofs/ zipper-egg-tests/ terminating/` is empty.

| id | task | files | proves done |
|---|---|---|---|
| 0.1 | **Atomic status writers, first.** `proofs/run.sh` and `proofs/unbounded/run.sh` write `STATUS.tsv.tmp` and rename. (`proofs/STATUS.tsv` is truncated in the working tree by a live run today; the index is intact.) | `proofs/run.sh`, `proofs/unbounded/run.sh`, `terminating/run.sh` | a killed run leaves the committed table untouched |
| 0.2 | **One forked JVM per suite** (`Test / testGrouping`), so `testOnly X` ≡ `sbt test` and counted values stop depending on suite order. Print `Interner.size`/`HeadAtoms.count` at the start of each measuring suite; `check_determinism.sh` runs a gate suite twice and diffs every `CALIBRATION:` line. If the probe is identical while counts differ, the id-drift hypothesis is wrong — record the next candidate before "fixing". | `build.sbt`, `scripts/check_determinism.sh`, the three measuring suites | two runs byte-identical on counted lines |
| 0.3 | **Proof artifacts get a golden-file regenerate mode** (`ZIPPY_REGENERATE=1`), distinct from the benchmark manifest: one `ArtifactSink` for every writer in `EquivPipelineTest`, `ZipperEggTest`, `TierThreeConformance`, `FixpointSemantics`, `DatalogShowTest`. Without the flag, write to scratch and **diff against the committed file**; a difference fails. | those suites, `src/main/scala/ArtifactSink.scala` | `sbt test` leaves the tree clean; a stale artifact fails a test |
| 0.4 | **In-tree runner and one gate list.** sbt task `exportTestRuntime` writes the test classpath; `scripts/gates.py` holds `GATE_SUITES` + `GATE_SCRIPTS`; `sbt check` and `publish_benchmarks.py` both import it. | `build.sbt`, `scripts/gates.py`, `scripts/publish_benchmarks.py` | `sbt check` runs all ten gates with no environment variables |
| 0.5 | **Lean scaffold, once:** `proofs/lean/` with Mathlib pinned to the installed toolchain, `[lake]` in `toolchain.conf` (no absolute paths), `scripts/check_lean.sh`, `Space`/`Path` inductives with denotational semantics, one theorem. Defines the `% MECHANIZED-IN:` marker `proof_closure.py` will honour. | `proofs/lean/**`, `toolchain.conf`, `scripts/check_lean.sh`, `scripts/proof_closure.py` | `lake build` green inside `sbt check` |
| 0.6 | **`alphaNorm` total** over every constructor (`Fold` binds `acc`/`sym`/`rest`; `Call`, grounded, `Range`, `Singleton`, `Literal` descended), delegating to the one substitution of 1A.1. | `src/main/scala/EquivPipeline.scala`, `src/test/scala/AlphaNormCheck.scala` | `AlphaNormCheck` green; pipeline cell classifications re-derived and the diff read |
| 0.7 | **Ledger figures become a check.** In `ProductGate.report`, a red row whose `recorded` figure differs from the measured value by more than 2% fails as `STALE FIGURE`. | `src/test/scala/SpatialScaleCheck.scala` | no `recorded` figure can drift silently |
| 0.8 | **Spec the item 4 ↔ 8 interface** before either builds: the `; TRUSTS:` artifact header, `Certified.boundary`, the registry `trusts` column. Breaks the only real cycle in the graph. | `docs/TRUSTED.md`, `proofs/pipeline/CLAIMS.tsv` (format), `src/main/scala/Certified.scala` (stub) | both items' emitters and readers agree on one format |

---

## Phase 1 — Independent tracks, in parallel

### Track A — one substitution (item 3, Scala half)

*Hard because four implementations disagree and no existing test can see capture.*

- **1A.1** `Subst.apply(s, mentions, paths)`: simultaneous, capture-avoiding (alpha-rename via
  `Matching.subst`'s mechanism). `Lower.inline`, `substMention`, `substPathRef`, `unrollControl`,
  `SpatialRecursion` residualisation, and the blind `subs` in `IterateLiteral_Union`,
  `IterateSingleton_Deref`, `asFixpointGeneral` all delegate. Files: new `src/main/scala/Subst.scala`,
  `MORKL.scala`, `EquivPipeline.scala`, `Supercompiler.scala`, `SpatialRecursion.scala`.
- **1A.2** `SubstCapture` suite with **open** replacements (a free name meeting an inner binder), the
  `g(y,x)` simultaneity case, and shadowing under `Iteration`/`Fixpoint`/`Fold`.
- **Gate:** `sbt 'testOnly morkl.SubstConformance morkl.SubstCapture morkl.AlphaNormCheck'`.

### Track B — the cost model (item 1)

*Hard because every zipper-side lower endpoint is unsound until 1B.1 lands, and 1B.5 is the single
point of failure of the whole plan.*

- **1B.1** Wire `PricingTarget`: a delegating `CostModel` at `go`'s `controlFlowFallback` arm that
  overrides `profile` with `pricingFor(outer.backend)`; every must-count checks `claimsFloor`.
  `BackendProfileCheck` pins the semantics. Prerequisite for every task below.
- **1B.2** `TailsFacts.childKeySets`: keep the per-child head sets `TailsFacts.of` already computes; derive
  the PKD descent price from the key layout → `tails-{union,inter}` Work/Alloc on trie, graph, zipper.
- **1B.3** Price the rest-chain nest **per level** from the prefix profile — `Σ_d K_{d−1}` joins of
  fan-out arity over single-path operands, not one join over all leaves with `nd(leaf)` each (the
  quadratic `LIM-12` exposes) → the 33 undiagnosed `rest-chain/nest` rows.
- **1B.4** Fixpoint `Touch`: price the accumulating merge against the union tower's non-recursive
  residue, licensed by `pointerPreservingRebuild` (declared, never read; `unionR`'s `a eq b` returns
  untouched subtrees by pointer). Do **not** take the `R − 1` multiplicity; it is false on
  `Fixpoint(a, r, Union(b, Mention(r)))`.
- **1B.5** puzzle15 at its source: `groupTailType`/`ChainCost.leafEnv` install `Shape.weaken` with the
  per-prefix fiber bound instead of `Shape.top`, so `Unwrap(state, o)` is bounded by one tile per
  cell, not `|state|`. **If the 16-cell state's spill past `shapeWidth` leaves the per-factor bound
  above 6, this task needs item 5's retained per-head tails** — and `SpatialPipelineCheck` is both
  this item's gate and the publisher's, so failure here blocks items 1 and 6 outright.
- **1B.6** Decorated-program integration: the per-node decorated type must be at least as strong as a
  fresh single-node inference, so `refine` stops re-inferring; `SpatialPipelineCheck`'s ITEM 8 gate
  moves from `improved ≥ 1` to `improved == 8 of 8`.
- **1B.7** Cornerstone Work/Alloc/Touch rows (`aunt`, `datalog-sn`, `gol`, `puzzle15`) re-measured after
  1B.2–1B.5; each residual either closes or gets an entry with its measurement.
- **1B.8** Retire the ledger to **empty**, then re-derive every remaining `Limitation` from the
  implementation. Any entry whose subject no longer fails is deleted, not kept.
- **Gate:** the four suites green under the per-suite JVM. *This is the acceptance sentence.*

### Track C — the certificate tier (item 5)

*Hard because it swaps the `Shape` carrier that every lattice operation recurses over — the domain
where a smaller change previously produced three γ-regressions. Run the γ and law suites after each
spill site, not at the end.*

- **1C.1** Certificate as an **immutable hash-consed prefix-trie value**; a per-analysis arena that is
  only a cache. Not generation-stamped ids: shapes are consumed after the analysis returns
  (`SpatialPipeline` reads a stored `SpatialAnalysis`), so identity must be a value.
- **1C.2** Replace channels (e)+(f) (`otherKeys`, `headAtoms`) with one certificate channel; delete
  `object HeadAtoms`.
- **1C.3** Route all **three** ⊤-degrading sites — `Shape.of` at depth ≤ 0, `sub` at d ≤ 0,
  `SpatialAnalysis.capWidth` — plus `capDepth` and `mk`'s width spill through one owner that keeps
  sub-structure.
- **1C.4** The relational frontier walk consumes certificates below a collapsed `otherTail`
  (`Frame` gains a certificate); delete the `SpatialFrontier` `maxKeys` cliff.
- **1C.5** Budgets in `SpatialConfig` for certificate size and depth; a widening rule; every
  degradation **recorded in the result** and justified by the rule.
- **1C.6** `SpatialCertBudgetCheck`: deep and wide key-disjoint families on both sides of every
  budget, asserting exact disjointness below and recorded degradation above, and the predicted
  growth class unchanged across the crossing. Fix the vacuous `SpatialFrontierCheck` test (it
  inspects a closed root where the certificate is trivially defined).
- **1C.7** Price certificate construction, lookup, intersection and retained memory in
  `FrontierSummary.notes`.
- **Gate:** `sbt 'testOnly morkl.SpatialCertCheck morkl.SpatialCertBudgetCheck morkl.SpatialFrontierCheck morkl.SpatialShapeCheck morkl.SpatialLawCheck morkl.SpatialSoundnessHunt'`.

### Track D — calls and ranges (item 2)

- **1D.1** Production consumer of the certified summaries: `SpatialTypeSystem`/`SpatialTypes` call
  `SpatialRecursion.summarise(…).at(Key)` for a recursive callee instead of returning ⊤. New
  `CrossFunctionCheck`: γ-soundness of a summary over **varying path arguments** and a result that
  depends on them (today the path is fixed to `"a"`).
- **1D.2** Rank abstraction on the **Shape** tier: `Shape.orderMin`/`orderMax` (ε if `eps.mustBe`, else
  the least/greatest head's recursion), a `Fact` for the selected path of `Range(x,0,1)`/`(x,−1,0)`,
  extended to wider slices where a bound follows. New `RangeRankCheck`, differential against all
  seven executors.
- **1D.3** One `normalize`: `Lower.sizeBounds`' `Range` arm computes through `SpatialTyping.windowCard`
  rather than a third copy of the arithmetic; certify the optimiser's `range-singleton` law
  (`proofs/laws/law_range_singleton.smt2`); pin the comparator `IntTrie` slices by against
  `pathValueOrdering` on randomised tries, not only the outputs.
- **1D.4** Turn the binder census into a gate: `EquivPipelineTest` asserts `binderFallback == 0`.
- **Optional — `Call` preserved rather than erased (1D.5–1D.7).** `Call` arms in all three renderers
  (`formalOf`, `renderZ`, `AgSmt.denRaw` — the last two throw today) with routine sorts in
  `formal.egg` and `prelude.egg`. The review permits erasing structure when the artifact records and
  checks the justifying law; item 4's 2A.2 does exactly that (U63 + the substitution premise), so
  these are the *stronger* reading and are deferred unless preserved structure is wanted for its own
  sake.
- **Gate:** `sbt 'testOnly morkl.CrossFunctionCheck morkl.RangeRankCheck morkl.RangeOrderCheck morkl.RangeCardCheck morkl.SpatialRecursionCheck'`.

### Track E — Lean, part 1 (items 3 and 8)

Depends on 0.5.

- **1E.1** `Subst.lean`: the substitution function mirroring 1A.1, the capture-avoidance theorem, and
  `seq_subst_eq_simul` (the `g(y,x)` fact).
- **1E.2** Correspondence to the executable: a Lean-checked **trace** of the production
  substitutions — `LeanRender` emits each `(term, substitution, result)` the Scala performed, Lean
  re-checks it. Not a citation.
- **1E.3** T1 (structural induction over `path`) and T2 (the four bridging inductions of
  `fixpoint_is_lfp.smt2`) mechanized; `proof_closure.py` lifts `PROVED-MODULO T1/T2` only when the
  named `.lean` file builds.
- **Gate:** `scripts/check_lean.sh` green; `proof_closure.py --check` reports `mon_cancel`,
  `wrap_roundtrip`, `card_wrap`, `fixpoint_is_lfp` unqualified.

---

## Phase 2 — Consumers

### Track A′ — cornerstone coverage (item 4)

Depends on 0.3, 0.6, 0.8; on Track D only for `datalog-sn` (the other cornerstones' calls are
acyclic). *Hard because the honest baseline is ~8 cells and no proof trace exists at all.*

- **2A.1** `CLAIMS.tsv`: one row per cornerstone × boundary, declared before anything is built, so the
  audit measures against a claim rather than against whatever was emitted.
- **2A.2** Independent construction: both sides symbolic before any evaluation. `expandKeepBinders`
  inlines acyclic calls via 1A.1 and **records** U63 + the substitution premise as the justifying law;
  `datalog-sn`'s `sn_tc` waits on 1D.5 or a generalised `asFixpointGeneral`. Delete the `-lit`/`-impl`
  single-side emission — this removes the 8 SINGLE-SIDE cells and the 12 marker-to-marker chains at
  their source.
- **2A.3** `SC.reduceTraced`: per-step `(law, before, after)`; each edge discharged by a checked law
  instance (matcher + instantiation) or a backend obligation; edges composed into the end-to-end
  claim and emitted into the artifact.
- **2A.4** Universal `SpaceZipper` refinement theorem over the syntax (`proofs/zipper_refinement.smt2`)
  plus an opaque source so `transpileZ` runs data-agnostically; the stage-2 cells instantiate it.
- **2A.5** BUDGET cells closed by **decomposition through the trace**, never by budget; a timeout is an
  unresolved cell and the audit says so.
- **2A.6** `COVERAGE.tsv` per cornerstone — every `Space`/`Path` constructor, binder, call pattern,
  optimizer law, recursive transformation and backend boundary exercised must appear in a checked
  chain; the audit fails on any that does not.
- **Gate:** `python3 scripts/audit_pipeline_markers.py --run --accept` → 0 SINGLE-SIDE, 0 chains,
  0 BUDGET, every declared cell REAL or checked IDENT/LAW-JUSTIFIED.

### Track E′ — Lean, part 2 (items 3 and 8) — the critical path

- **2E.1** `Positive.lean`: the positive fragment as a decision procedure; monotonicity **and**
  ω-continuity per constructor; closure under composition and calls; the all-`k` approximant theorem.
  Its consumer wired at the same time: the pipeline cells that emit `k = 1, 2` today cite it.
- **2E.2** `Supercompile.lean`: folding preserves the least-fixpoint denotation — configuration
  matching, renaming/instantiation, generalization, residual routine creation, recursive references,
  composed folds. Parametric in `LawOK` so it lands before item 4 finishes; every implementation
  premise becomes an executable invariant in `Supercompiler.scala`. **The largest single task in the
  plan.**
- **2E.3** The whistle: `Matching.labelOf` fixes the finite alphabet of the *exact* `coupledS`/`coupledP`
  embedding (it couples `Call` by `RoutinePtr`, `Mention`/`Deref` by canonical name, `Range` by bounds,
  `Literal`/`Constant` by value — decide and engineer each). `Whistle.lean`: the WQO over that exact
  relation (Kruskal via Higman from Mathlib — **verify present at task start**; if absent, prove it
  from Higman) and termination of the implemented transition system. `Matching.toLabel` connects the
  executable to the definition.
- **2E.4** Assert-level closure for the five SMT status tables: every top-level `(assert …)` that is
  not a definition is either derived in-corpus or names a `TRUSTED-ENTRY`.
- **2E.5** `object Certified` — the certified language boundary, enforced in the API (a term outside it
  cannot enter a fully proved claim) and by `proof_closure.py` and the marker audit.
- **2E.6** `REGISTRY.tsv` O6a/O10b/O12b/O12d from `ADMITTED`/open to `MECHANIZED (proofs/lean/…)`;
  `docs/TRUSTED.md` T1/T2/T3 become checked theorems.
- **Gate:** every `PROVED` across the six tables depends only on Lean-checked theorems, checked
  correspondence and discharged cells; `scripts/check_lean.sh` lists the axioms each theorem uses and
  they are exactly Lean's.

---

## Phase 3 — Closure

- **3.1** Item 6: first end-to-end publication. Then `publish_benchmarks.py --reproduce`: check out the
  one commit all four outputs name in a worktree, re-run gates and generation, diff. **Gate:** exit 0
  at the artifact commit — *this is the acceptance sentence.*
- **3.2** Item 7 residual: a `resolves()` unit test against an in-memory name set with the filesystem
  deliberately disagreeing (so the test discriminates the checker from Linux), and a per-token
  `.gitignore` exception instead of a whole-file skip. Widen the reference vocabulary to `.lean`.
- **3.3** Final: every claim in this file's successor assigned **only** by acceptance sentence and gate
  command; every `recorded` figure re-derived by 0.7's check.

---

## Dependencies, critical path, risks

```
0.1 → 0.5 → 1E.1 → 2E.1 → 2E.2            (Lean; the critical path)
0.6 → 1A.1 → 2A.2 → 2A.3 → 2A.5 → 2A.6     (coverage)
1B.1 → 1B.2..1B.6 → 1B.7 → 1B.8 → 3.1      (cost model → publication)
1C.1 → 1C.2 → 1C.3 → 1C.4 → 1C.5 → 1C.6    (certificate tier; no external dependency)
1D.1 → 1D.2                                (item 2; 1D.2 after 1C.2 if it reads the certificate)
```

- **Single point of failure: 1B.5.** `SpatialPipelineCheck` is item 1's gate *and* the publisher's;
  if puzzle15 does not drop below `1e12` from the fiber bound alone, items 1 and 6 both stay red and
  item 5's per-head tails join the critical path.
- **Largest task: 2E.2.** If the fold theorem does not go through for the exact implementation, items
  3, 4 and 8 stay conditional. Mitigation: parametric in `LawOK`; 2A.3's trace makes the
  implementation-side premises *checked*, shrinking what Lean must assume.
- **Riskiest change: 1C.2.** Touches every lattice operation. γ and law suites in the loop per spill
  site.
- **Toolchain risk: Kruskal in Mathlib.** Verify before 2E.3; the fallback is proving it from Higman.

## What is already true

Item 7's acceptance sentence holds on `--snapshot=index --strict` (0 dangling, every exception used)
and its self-test covers the four named regressions. `scripts/proof_closure.py` enumerates all six
status tables, follows include and `DISCHARGED-BY` edges, enforces `TRUSTED-ENTRY` markers, and
annotates eight conditional verdicts. `scripts/publish_benchmarks.py` refuses correctly at preflight
and at the gates. `OperandShape.DistinctSingleKey` closed the operator table's `iteration` rows with
the measurement now committed in `BackendProfileCheck`. Three unsound bounds and two false-passing
negative controls are fixed, with containment at 100% in both declared configurations. None of that
is an acceptance sentence.
