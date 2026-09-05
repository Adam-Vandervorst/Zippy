# Tasks — certified resource-aware supercompilation

## Objective

Make Zippy choose among semantically equivalent residual programs using sound, useful, compositional
predictions of their operational resource use.  Every accepted choice must carry:

1. a checked semantic-equivalence trace;
2. sound lower and upper bounds for `Work`, `Alloc`, `Touch`, and `Rounds`;
3. the assumptions and precision losses used to derive those bounds; and
4. clean, reproducible cornerstone evidence from the commit that makes the claim.

The work below starts from the current implementation.  Existing call/range analysis, certificate
values, Lean positive-fragment development, snapshot reference checking, and passing regression
suites are foundations to preserve, not tasks to recreate.

The central implementation object is a **stratified delta-fixpoint IR**.  It represents signed
dependencies, positive mutually recursive SCCs, frozen lower-stratum inputs, the accumulated value
and current delta, and a shared operational-provenance/event DAG.  Concrete execution, correlated
resource analysis, transformation proofs, and residual selection must all consume this IR.  Its
delta, stratification, and iteration laws are part of the Lean proof boundary.

All compilation, tests, proof builds, benchmarks, and publication runs must execute on a provisioned
`cpu-small` or larger Symba node.  Local work on the current machine is limited to reading and editing
files.

## Completion rule

A task is complete only when its named artifacts exist, its acceptance checks pass from a clean Git
snapshot, and every theorem or result it exposes as unconditional has a transitively discharged
dependency closure.  A timeout, sampled test, open registry entry, undocumented widening, or
single-side observation is not completion.

---

## A. Authoritative operational resource semantics

### A1. Specify counted executions and resource events

**Outcome:** one semantics defines what every backend and the counted oracle mean by resource use.

**Work:**

- Define a backend-parameterized event algebra for node visits, operand probes, allocation,
  retained sharing, key comparisons, materialization, and fixpoint rounds.
- Give compositional event semantics to every certified `Space` constructor, including `Call`,
  `Iteration`, `Fixpoint`, `Range`, `TailsUnion`, and `TailsIntersection`.
- Specify n-ary execution in terms of ordered live frontiers, including when an operand is retired,
  revisited, aliased, or reused.
- Specify graph, trie, and zipper behavior explicitly; backend differences must be parameters of the
  same semantics rather than alternate fallback models.
- Make `SpatialEvents` the counted interpreter of this semantics.  Remove independent expected-cost
  formulae that can drift from it.
- Record the unit, inclusion rule, and sharing convention for each of `Work`, `Alloc`, `Touch`, and
  `Rounds` in `docs/SPATIAL_SEMANTICS.md`.

**Artifacts:** `SpatialEvents.scala`, a small shared event-semantics module, backend profiles, and
`docs/SPATIAL_SEMANTICS.md`.

**Acceptance:** differential tests show that instrumented executions and `SpatialEvents` produce the
same event multiset for every constructor and backend; the test corpus includes empty, singleton,
aliased, disjoint, deeply shared, recursive, and n-ary cases.

**Depends on:** nothing.

### A2. Introduce the stratified delta-fixpoint IR

**Outcome:** every certified `Fixpoint` and recursive call component has one explicit recursive
representation shared by execution, analysis, proof, and residual generation.

**Work:**

- Build a dependency graph over bound space mentions, routine parameters, and `Call` edges.  Label
  every dependency `+` (monotone), `-` (antitone), or `0` (unknown/nonmonotone) by compositional
  variance analysis of the actual constructors.
- Collapse the positive call/dependency graph into SCCs.  A recursive SCC is certified only when
  every dependency internal to it is positive; negative and unknown dependencies must point to a
  completed lower stratum.  Reject the term at the certified-language boundary otherwise.
- Represent each positive SCC as a simultaneous least-post-fixpoint system; make unary
  `Space.Fixpoint` the one-equation case.  Treat lower-stratum values as frozen parameters.
- Give the IR explicit accumulator, current delta, round, routine environment, backend schedule,
  and symbolic provenance/event outputs.
- Define the reference recurrence `A(0) = init`, `new(n+1) = F(A(n)) \\ A(n)`, and
  `A(n+1) = A(n) union new(n+1)`.  Define a compositional differential transfer for every positive
  constructor and call summary.  For nonlinear bodies, enumerate or symbolically share every term
  containing at least one changed argument; do not replace all recursive occurrences by the delta.
- Require the differential transfer to prove the step equation
  `A union deltaStep(F,A,lastDelta) = A union F(A)` under its stated invariant.  Deduplication and
  backend scheduling may change work, never the accumulated denotation.
- Preserve stratum, SCC, accumulator/delta, and provenance identities through lowering and
  residualization.  Do not reconstruct this information heuristically from the lowered graph.
- Mechanize the variance composition, stratum-order soundness, simultaneous/unary fixpoint
  correspondence, delta-step equation, and accumulated delta/full-iteration equivalence in Lean.

**Artifacts:** a recursive IR module, variance and stratification pass, delta transfer module,
lowering from `Space`/routine tables, Lean development under `proofs/lean/Zippy/`, and a readable IR
renderer.

**Acceptance:** positive mutual recursion and negative dependencies on lower strata are accepted;
cycles containing a negative or unknown edge are rejected; naive and delta execution produce the
same accumulator at every round boundary and the same stationary result; recursive `Call` SCCs and
explicit `Fixpoint` lower to the same IR when extensionally equivalent; every accepted IR instance
carries replayable Lean-backed stratification and delta premises.

**Depends on:** A1.

### A3. Replace independent scalar widening with correlated resource facts

**Outcome:** the abstract state preserves the relationships that determine operational cost.

**Work:**

- Add facts for distinct live operands, may/must aliasing, proven reuse, ordered frontier position,
  per-prefix fan-out, per-prefix fibre cardinality, and pointer-preserving sharing.
- Represent finite symbolic alternatives using an immutable hash-consed prefix trie, BDD-like
  decision sharing, or a deliberate composition of the two.
- Use the same hash-consed structure as an operational-provenance DAG: retain alternative causes,
  shared prefix decisions, accumulator membership, the round/delta that introduced a fact, and the
  backend event sites that consumed it.  Denotational and resource interpretations must share nodes
  without conflating their meanings.
- Keep two explicit tiers: an exact symbolic tier and a summarized tier.  Define the abstraction,
  concretization, join, meet, projection, and widening of both tiers.
- Preserve correlations between cardinality, key layout, order extrema, and prefix fibres.  Do not
  project them to unrelated intervals before resource transfer.
- Retain exact `min`/`max` information for nonempty ordered sets and use it for
  `Range(x, 0, 1)` and `Range(x, -1, 0)`.  General slices may summarize, but must retain sound lower
  and upper cardinalities after normalization.
- Scope all hash-consing and caches to one analysis.  The returned certificate must be an immutable
  value with no semantic dependence on process history.
- Make every budget crossing return a named widening reason and the before/after facts.  It may lose
  precision but may not silently change a must fact or growth class.

**Artifacts:** `SpatialShape.scala`, `SpatialCert.scala`, `SpatialFacts.scala`, `SpatialFrontier.scala`,
`SpatialTypes.scala`, and a documented domain specification in `docs/SPATIAL_DOMAIN.md`.

**Acceptance:** lattice and gamma checks pass; exact-tier disjointness and extrema survive depth and
width collapse; summarized results contain all counted outcomes; results are invariant under prior
analyses in the same JVM; every loss of precision is present in the returned analysis certificate.

**Depends on:** A1, A2.

### A4. Derive resource bounds by abstract interpretation of the event semantics

**Outcome:** lower and upper resource bounds are two abstractions of the same counted execution.

**Work:**

- Define an abstract transfer for every event-semantic rule from A1 over the correlated state from
  A3 and the recursive IR from A2.
- Derive lower bounds only from must facts and upper bounds only from may facts.  Remove backend or
  constructor special cases that bypass this rule.
- Price n-ary union/intersection from the ordered live frontier and key alternatives, not from a
  flattened operand count.
- Price rest-chain nesting per prefix level and preserve pointer-sharing facts through rebuilds.
- Interpret fixpoints over the IR accumulator/delta recurrence.  Charge only events actually
  scheduled for a delta while retaining sound costs for deduplication, old-state probes, nonlinear
  delta combinations, and the terminating empty-delta round.
- Bound puzzle15 state projections with per-cell/per-prefix fibres; no `Shape.top` may be introduced
  where the source type supplies a finite fibre constraint.
- Include certificate construction, lookup, intersection, widening, and retained memory in the
  applicable resource dimensions.
- Attach a derivation DAG to each reported interval: rule, input facts, backend parameter, widening
  event, and resulting bound.

**Artifacts:** `SpatialCost.scala`, `SpatialDemand.scala`, `SpatialAnalysis.scala`, derivation
certificate types, and a deterministic certificate renderer.

**Acceptance:** zero containment failures under exhaustive small-model checks and randomized
soundness hunts; the two known zipper counterexamples are covered as permanent regressions; all
four spatial cost suites pass without workload-specific exceptions or stale expected formulae.

**Depends on:** A1–A3.

### A5. Make calls and recursive components compositional in the resource domain

**Outcome:** analysis chains across functions without erasing call boundaries or evaluating callees.

**Work:**

- Give every routine a parametric summary over path arguments, space arguments, correlated result
  facts, and the four resource measures.
- Compose acyclic summaries at `Call` sites while preserving argument/result correlation and
  certificate provenance.
- Analyse the stratified IR's recursive SCCs as simultaneous abstract fixpoints.  Reuse its frozen
  lower-stratum values, delta transfer, and SCC identity rather than discovering recursion again.
  Record explicit convergence and widening certificates.
- Distinguish per-invocation cost, shared one-time cost, and recursive accumulated cost.
- Cache summaries by canonical routine identity and abstract input, never by a collision-prone
  residual integer alone.
- Preserve `Call` in source, residual, backend, and proof representations.  Inlining is a separate
  certified transformation, not an analysis implementation detail.

**Artifacts:** `SpatialRecursion.scala`, `SpatialTypeSystem.scala`, `SpatialTypes.scala`, canonical
routine identities, and call-summary certificate nodes.

**Acceptance:** cross-function tests include changing path arguments, mutually recursive routines,
summary reuse, range selection of call results, and calls below binders; composed bounds contain
counted executions and remain materially tighter than `top` on the cornerstone call chains.

**Depends on:** A2–A4.

### A6. Prove or check every abstract transfer

**Outcome:** spatial soundness is a property of the domain, not an empirical inference from the
benchmark corpus.

**Work:**

- State, for each transfer rule, that concretization of the abstract result contains every concrete
  event execution admitted by the abstract inputs.
- Mechanize the finite-domain, interval, order, range-normalization, and widening lemmas in Lean
  where practical.
- Connect the abstract recursive transfer to A2's Lean delta and stratification theorems: one
  post-fixpoint certificate must cover the simultaneous SCC, and its projection must soundly cover
  each routine and explicit `Fixpoint` result.
- For representation-heavy certificate operations, use a small independently implemented checker
  and exhaustive finite-model enumeration, with a written mathematical argument connecting the
  checker to the general rule.
- Prove that lower-bound rules use only universal must properties and upper-bound rules cover every
  may alternative.
- Connect backend pricing parameters to the counted event semantics with checked differential
  obligations.
- Register every remaining premise explicitly; no spatial result may be labelled certified while
  depending on an open soundness premise.

**Artifacts:** `proofs/lean/Zippy/Spatial*.lean`, checker inputs/outputs under `proofs/spatial/`, and
registry rows for the exact implementation-correspondence boundary.

**Acceptance:** all transfer rules are either Lean-checked or accepted by the independent checker
under a documented universal argument; `proof_closure.py` rejects a certified cost result if any
transfer dependency is open.

**Depends on:** A1–A5.

---

## B. Make resource knowledge drive supercompilation

### B1. Represent residual alternatives explicitly

**Outcome:** the supercompiler exposes meaningful choices instead of committing before costs are
known.

**Work:**

- Introduce a residual-alternative node containing the residual program, semantic proof trace,
  spatial input assumptions, resource certificate, and provenance.
- Retain alternatives created by unfolding, folding, fusion, prefix restriction, range reduction,
  materialization, backend translation, and sharing choices.
- Hash-cons alpha-equivalent residuals and merge only when both semantic and resource assumptions
  are compatible.
- Bound search with explicit subsumption and widening; record every pruned alternative and reason.

**Artifacts:** alternative/frontier types in the supercompiler, deterministic rendering, and trace
serialization.

**Acceptance:** a deterministic test fixture exposes at least three non-equivalent-cost but
semantically equivalent residual choices, with no ground evaluation used to create or merge them.

**Depends on:** A4, A5; C2 for unconditional proof labels.

### B2. Select from a certified Pareto frontier

**Outcome:** transformation choice is justified by proved equivalence and sound resource dominance.

**Work:**

- Define dominance over interval-valued `Work`, `Alloc`, `Touch`, and `Rounds`, including the policy
  for incomparable and widened bounds.
- Discard an alternative as dominated only when the upper/lower relationship proves dominance under
  the declared input assumptions.
- Keep incomparable alternatives and allow the caller to choose an objective or constraint vector.
- Return the selected residual together with the rejected alternatives and checkable reason for each
  rejection.
- Never use measured cornerstone performance as an unrecorded tie-breaker.

**Artifacts:** Pareto-frontier module, objective API, selection certificates, and CLI/report output.

**Acceptance:** selection is deterministic; every removal is replayable by an independent checker;
changing objectives selects the expected alternatives in fusion, prefix/range, call-composition,
sharing, and recursion fixtures.

**Depends on:** B1, A6, C4.

### B3. Demonstrate decisions that existing optimizers cannot make safely

**Outcome:** the ambitious work yields a differentiated capability rather than only green gates.

**Work:**

- Add decision cases where local rewrite count or output cardinality predicts the wrong winner but
  correlated operational analysis selects correctly.
- Include: disjoint versus overlapping n-ary tails; first/last range after a call; fusion that trades
  allocation for work; pointer-preserving recursive rebuild; and puzzle15 projection/materialization.
- For each case, state the symbolic input precondition, alternatives, proof traces, predicted
  intervals, selected objective, and counted result.

**Artifacts:** `docs/DECISIONS.md`, machine-readable decision fixtures, and generated comparison
tables.

**Acceptance:** every selected alternative is semantically certified, its counted resources lie in
the predicted intervals, and at least one case per transformation family requires correlation or
call composition unavailable to a scalar cardinality estimator.

**Depends on:** B2, D1.

---

## C. Close semantic correctness and trust dependencies

### C1. Prove semantic substitution for the production operation

**Outcome:** O6a is a theorem rather than differential evidence.

**Work:**

- State and prove denotational preservation of simultaneous, capture-avoiding path and space
  substitution for every constructor in the certified language, including `Call`, `Iteration`, and
  `Fixpoint`.
- Prove freshness, alpha-renaming, shadowing, and simultaneous-versus-sequential side conditions.
- Make Scala emit a canonical substitution trace containing the input term, substitutions,
  freshness decisions, alpha-renamings, and result.
- Check that trace with the Lean substitution function or a generated proof term.
- Route every production substitution and inlining path through this operation.

**Artifacts:** `Subst.scala`, `proofs/lean/Zippy/Subst.lean`, substitution trace format/checker, and
updated O6a registry evidence.

**Acceptance:** O6a is `MECHANIZED`, all substitution traces replay, capture regressions pass, and no
production call site implements independent substitution logic.

**Depends on:** nothing.

### C2. Discharge unfolding and repeated folding

**Outcome:** the complete recursive transformation chain is unconditional.

**Work:**

- Use C1 to close the unfold/beta half currently recorded as O12a.
- Prove that configuration matching, renaming/instantiation, generalization, residual routine
  creation, and recursive references preserve least-fixpoint denotation.
- Instantiate the existing parametric fold theorem with checked implementation invariants rather
  than an assumed `fix` premise.
- Prove composition for an arbitrary finite chain of unfold/fold steps.
- Replace residual identities with collision-safe canonical identities wherever proof composition
  depends on identity.

**Artifacts:** `proofs/lean/Zippy/Supercompile.lean`, executable invariant checks in
`Supercompiler.scala`, and closed O12a/O12b registry rows.

**Acceptance:** arbitrary positive-fragment transformation traces replay without open premises;
O12a and O12b are mechanized; no bounded-depth experiment is cited as theorem evidence.

**Depends on:** C1 and the existing positive-fragment theorem.

### C3. Make proof traces typed, compositional objects

**Outcome:** every residual alternative terminates directly in a replayable proof object.

**Work:**

- Define trace nodes for universal law instantiation, substitution, alpha-equivalence, unfold, fold,
  backend refinement, and transitive composition.
- Include exact matcher substitutions and side-condition evidence in law nodes.
- Construct source and optimized terms independently before ground evaluation.
- Reject marker-to-marker chains, single-side observations, and identity claims without independent
  pre-evaluation alpha-equivalence plus a verified optimizer no-op.
- Preserve binders, routine boundaries, and control structure unless an explicit checked trace node
  justifies erasure.

**Artifacts:** typed trace schema, Scala encoder, independent trace checker, and migrated pipeline
artifacts.

**Acceptance:** every accepted pipeline claim resolves to a finite trace DAG whose leaves are
checked universal theorems or direct backend obligations; mutation tests of a matcher, side
condition, before/after term, or dependency make replay fail.

**Depends on:** C1, C2.

### C4. Enforce transitive trust closure

**Outcome:** an open obligation can never support an unconditional result or cost-guided choice.

**Work:**

- Parse obligation identifiers in every trace and resolve them against `terminating/REGISTRY.tsv`.
- Traverse law, Lean theorem, implementation-correspondence, backend, cornerstone, and spatial
  transfer dependencies as one graph.
- Reject cycles without a separately checked inductive or fixpoint justification.
- Define the certified-language boundary in `Certified.scala`; refuse unconditional certification
  for terms outside it.
- Remove stale hard-coded trust descriptions, including the obsolete T3 `ADMITTED` wording.
- Emit a machine-readable closure and the minimal open dependency set for every conditional claim.

**Artifacts:** `scripts/proof_closure.py`, registry/schema updates, `Certified.scala`, and closure
reports consumed by both the proof and resource checkers.

**Acceptance:** injecting an open O6a-like dependency changes every transitive consumer to
conditional or failed; removing it restores the status; no unqualified `PROVED` or `CERTIFIED-COST`
result has an open leaf.

**Depends on:** C3, A6.

---

## D. Cornerstones as end-to-end acceptance evidence

### D1. Replace marker coverage with structural coverage

**Outcome:** the audit proves that claimed language and optimizer features occur inside checked
end-to-end chains.

**Work:**

- Replace substring coverage with identifiers emitted from parsed source/residual AST nodes and
  typed proof-trace nodes.
- Give every coverage row a nonempty feature identifier, artifact node, trace node, and discharged
  claim identifier.
- Check coverage of constructors, binders, call patterns, recursive transformations, optimizer
  laws, resource rules, and backend boundaries separately.
- Resolve every permitted trust through C4; a syntactically valid obligation name is insufficient.
- Report unsupported, exercised-but-unproved, proved-but-unexercised, and fully covered features as
  distinct states.

**Artifacts:** `proofs/pipeline/COVERAGE.tsv` schema, structured coverage emitter, and
`scripts/audit_pipeline_markers.py`.

**Acceptance:** empty items and unattached strings are rejected; deleting any relevant AST or trace
node removes its coverage; no accepted cell depends on an open registry entry.

**Depends on:** C3, C4.

### D2. Rebuild every cornerstone claim independently

**Outcome:** each claimed source/backend relation has semantic and resource evidence generated from
its actual symbolic program.

**Work:**

- Rebuild aunt, datalog semi-naive, Game of Life, n-queens, puzzle3-full, and puzzle15 source and
  optimized sides independently.
- Attach complete equivalence traces, call summaries, spatial derivations, and selection
  certificates where a choice is claimed.
- Prove and instantiate universal representation-boundary theorems for `SpaceZipper` translation,
  collapse, and every other claimed backend boundary.
- Decompose large proofs through trace nodes; a budget timeout remains unresolved rather than being
  accepted as a category.
- Correct declaration/content drift and remove claims that the artifact does not actually exercise.

**Artifacts:** regenerated cornerstone artifacts, `CLAIMS.tsv`, `COVERAGE.tsv`, proof traces, and
resource certificates.

**Acceptance:** every declared cell is independently constructed and has a replayable semantic
trace; every claimed resource result contains its counted run; there are no open, budget, chained,
or single-side acceptance cells.

**Depends on:** B2, C3, C4, D1.

### D3. Make puzzle15 a first-class stress theorem

**Outcome:** puzzle15 validates finite-fibre reasoning, sharing, composition, and useful bounds rather
than merely avoiding an astronomical number.

**Work:**

- State the board invariants and per-cell/per-prefix fibre constraints independently of the cost
  model.
- Prove that projection, unwrap, move generation, and residual transformations preserve those
  invariants.
- Feed the proved constraints through calls into the correlated spatial domain.
- Explain every interval contribution in the generated certificate and identify any widening.
- Compare materialized, trie, zipper, and graph alternatives under multiple objectives.

**Artifacts:** puzzle15 invariant proof/checker, trace, spatial certificate, decision fixture, and
human-readable derivation report.

**Acceptance:** no bound exceeds the finite maximum permitted by the proved state space; counted
resource use is contained; intervals satisfy the committed usefulness thresholds; at least one
backend/transformation choice is justified by the certificate rather than benchmark fitting.

**Depends on:** A6, B2, C4.

---

## E. Gates, publication, and acceptance status

### E1. Turn ambitious properties into discriminating gates

**Outcome:** tests reject plausible weaker implementations, not just known bugs.

**Work:**

- Keep deterministic containment, width, slope, integration, lattice, and proof checks as hard
  gates.
- Add mutation tests for dropped alias facts, reversed range order, erased calls, optimistic lower
  bounds, missing widening records, open proof dependencies, and forged coverage links.
- Generate adversarial families across depth, width, operand count, aliasing, prefix overlap,
  recursion depth, and certificate budgets.
- Separate soundness thresholds from usefulness thresholds: sound-but-wide is not unsound, but it
  cannot satisfy a published usefulness claim.
- Make every recorded expected figure derive from the current semantics or a versioned requirement;
  reject stale handwritten diagnoses.

**Artifacts:** strengthened spatial, proof-closure, pipeline-audit, and decision suites registered in
the single gate manifest.

**Acceptance:** each major requirement has at least one mutation that fails only when that property
is weakened; all gates pass twice with byte-identical counted and certificate output on a clean
remote snapshot.

**Depends on:** A6, B3, C4, D2.

### E2. Publish atomically from the accepted commit

**Outcome:** public numbers and claims reproduce from exactly the source that passed acceptance.

**Work:**

- Preflight tracked and relevant untracked inputs before writing an output.
- Run the full gate set, generate all tables and documentation sections, and validate the diff as
  one transaction.
- Record one commit, environment, toolchain, seed, workload, and configuration manifest in every
  output.
- Permit only declared generated files to change.
- Reproduce in a clean checkout of the named commit and byte-diff schema/data outputs, allowing only
  explicitly declared timing tolerances.

**Artifacts:** regenerated `corpus_runtimes.csv`, `expressivity.csv`, `prog_matrix.tsv`, generated
sections of `docs/BENCHMARKS.md`, and an environment manifest.

**Acceptance:** `publish_benchmarks.py --reproduce` succeeds from the clean accepted commit and no
artifact names a dirty or different tree.

**Depends on:** E1.

### E3. Derive repository status from evidence

**Outcome:** `docs/ACCEPTANCE.md` cannot become more optimistic than the gates and dependency graph.

**Work:**

- Generate each acceptance row from its acceptance sentence, named gates, and proof-closure result.
- Distinguish `GREEN`, `CONDITIONAL`, `UNSOUND`, `SOUND-BUT-NOT-USEFUL`, and `UNMEASURED`.
- Include the clean snapshot identity and links to semantic traces, spatial certificates, and
  cornerstone claims.
- Fail if prose status disagrees with machine-readable evidence.

**Artifacts:** generated acceptance data plus rendered `docs/ACCEPTANCE.md`.

**Acceptance:** deliberately opening a theorem, widening a cornerstone beyond its usefulness limit,
or dirtying a generated result changes the corresponding row away from `GREEN`.

**Depends on:** E1, E2.

---

## Required execution order

1. **Semantic spine:** A1 → A2 → A3 → A4 → A5 → A6.
2. **Proof spine:** C1 → C2 → C3 → C4.
3. **Decision layer:** B1 → B2, after A4/A5 and the applicable proof spine; then B3.
4. **Evidence:** D1 → D2, with D3 after A6/B2/C4.
5. **Closure:** E1 → E2 → E3.

A and C may proceed concurrently, but an alternative cannot enter the certified Pareto frontier
until both its spatial derivation and semantic trace have closed.  Publication cannot begin while
any required cornerstone is conditional, unsound, or outside its usefulness threshold.

## Milestones

### M1 — Sound operational analysis

A1–A6 complete.  Certified recursion lowers to the stratified delta-fixpoint IR; naive and delta
execution agree; no counted execution escapes a reported interval; calls and recursive SCCs
compose; every widening is explicit.  Wide intervals are allowed at this milestone but are
reported as not useful.

### M2 — Unconditional semantic transformations

C1–C4 complete.  O6a/O12a/O12b are closed; typed traces and transitive dependency closure are
enforced.

### M3 — Certified choice

B1–B3 complete.  Zippy exposes equivalent alternatives and selects only by certified resource
dominance under declared objectives and assumptions.

### M4 — Cornerstone usefulness

D1–D3 complete.  All cornerstone relations are independently proved, structurally covered, and
bounded tightly enough to support the claimed decisions.

### M5 — Reproducible acceptance

E1–E3 complete.  The full remote gate is deterministic and green, publication reproduces from the
named clean commit, and acceptance status is generated from the evidence.
