# Zipper Critique Audit

Date: 2026-07-02

This audits `pasted-text.txt` against the current workspace. Status labels:

- **Addressed**: implemented and covered by focused tests.
- **Partial**: important progress exists, but the critique is not fully closed.
- **Open**: not meaningfully addressed yet.

## Summary

Not everything in the pasted critique is addressed.

The largest concrete change since the critique is real executable zipper support in Scala:
`SpaceZipper.Cursor` / `CursorContext`, `PatchChild`, plug-invariance tests, virtual focus edits, exact observations, and exhaustive bounded oracle tests. This addresses the core "it is only a derivative, not a zipper" complaint for the Scala runtime path.

The formal/egg side is still behind, but the operational track is less toy-like now. `zipper-descend.egg` has relational key analyses, exact positive key witnesses, negative nullable hooks, bounded virtual movement via `PatchFrameCtx` / `PatchChildOp`, alphabet-free concrete suffix-closure rules, finite `tail-frontier` observations, and explicit `HeadZ` / `IterZ` / `FixpointZ` forms for the operational cases currently justified. The repo now also has a proof gate in `tools/proof_pipeline.py`: Scala (`morkl.ProofArtifactGeneratorMain`) generates every SMT2/TPTP proof artifact and manifest, Scala (`morkl.generateZipperEggTests`) generates the independent example egg files, and the Python runner invokes the configured Vampire command, Z3, and egglog. Vampire proves first-order equivalence obligations connecting path-set, eager-trie, zipper membership/child/terminal notions, and grouped-head Iteration materialization, while Z3 bounded-checks concrete finite-language laws with negative controls, including Iteration schemas and small puzzle/n-queens examples. It still does not provide a complete cost semantics, a unified operational egg prelude, a non-vacuous normal-form semantics for all ops, recursive global virtual cursor saturation, or Antimirov closure state for fully general virtual closures.

## Section 1: "It isn't a zipper"

Status: **Mostly addressed in Scala, partial in egg.**

- Focus + context:
  - Addressed in Scala by `TrieSpace.Zipper` and `SpaceZipper.Cursor`.
  - Evidence: `src/main/scala/TrieSpace.scala` has `ZipperContext` and `Zipper`; `src/main/scala/ZipperSpace.scala` has `CursorContext` and `Cursor`.
  - Egg has relational context movement (`plugged`, `down-move`, `up-move`) but not a globally saturating cursor model.

- `up`, `path`, `plug`, sibling movement, ordered child iteration:
  - Addressed in Scala.
  - Evidence: `path`, `pathValue`, `whole`, `up`, `toRoot`, `firstChild`, `nextSibling`, `previousSibling`, and ordered child tests exist.

- Plug-invariance from arbitrary focus:
  - Addressed in Scala for bounded concrete tries and operation-shaped virtual zippers.
  - Evidence: `ZipperDenotationOracleTest` checks every focus for bounded tries and virtual op roots.
  - Partial in egg: `plugged` relation exists, but path-observation over recursively generated virtual cursors is intentionally bounded to avoid blowup.

- Write half: insert/remove/graft:
  - Addressed in Scala for `graft`, `removeFocus`, `insertAtFocus`, and virtual lazy reconstruction via `PatchChild`.
  - Still missing: explicit `join-into` API and cost accounting for copy-on-write spine updates.

- Tries are sets, not maps:
  - Addressed for the production track. MORKL intentionally models finite path
    sets, and all enriched terminal-data work is sidecarred under `valued/`.
    The unit optimizer now exploits path-set-only laws such as subset
    absorption, restriction/raffination partition,
    `(A \ B) \/ (A /\ B) = A`, and `A \ (A \ B) = A /\ B` without importing
    side conditions from the sidecar.

## Section 2: Constant-time/local constraint

Status: **Partial, with major proof/cost gaps.**

- Equational rewriting erases cost:
  - Open. There is no formal cost semantics or step-counting model.
  - Runtime has local/lazy structures (`Memo`, `PatchChild`) but no proof that moves are bounded independent of trie size.

- Concrete trie modeled honestly:
  - Addressed in Scala: `TrieSpace` is an `IntMap` trie with child lookup.
  - Partial in egg: concrete spaces are still represented by `Empty` / `Singleton` / `Union`, not actual child maps.

- Observations hiding unbounded work:
  - Partial. Scala now exposes exact `SpaceZipper.Observation`; `Memo` caches child movement and materialization.
  - Egg now has relational `terminal`, `empty-focus`, `nonterminal`, `has-key`, and `nonempty-focus`.
  - Still open: no completeness proof for negative observations, no amortized memoization contract, and no cost tier checks.

- SuffixClosure / TailsClosure non-locality:
  - Partial in Scala: implementation uses actual child iterators, not a fixed alphabet.
  - Partial in egg: `zipper-descend.egg` no longer has hardcoded `a,b,c,d,x` structural closure/tails rules; it uses finite `tail-frontier` observations and alphabet-free concrete suffix-closure singleton/union laws. Still open: no Antimirov frontier-set state or memoized subset-construction model for fully general virtual closures.

- TailsUnion / TailsIntersection cost tier:
  - Open. No formal Tier A/B/C classification is encoded or tested with node-touch bounds.

## Section 3: Confirmed defects

### 3a. KeySet lattice collapse

Status: **Addressed in `zipper-descend.egg`.**

- `Keys` term rewrites were replaced by relational `keyset` facts.
- Permanent regressions exist:
  - `(fail (check (= (KEmpty) (KOne "a"))))`
  - `(fail (check (= (KOne "a") (KOne "b"))))`
- Exact positive key analysis was added separately via `has-key`.

### 3b. Vacuous `zipper.egg` checks

Status: **Partial / still a real problem.**

- Progress: `ZipperDenotationOracleTest` provides a non-vacuous executable oracle; `zipper-descend.egg` has operational movement checks.
- Still open: `zipper.egg` itself remains largely a materialization-congruence fixture. Many `check (materializes ...)` tests still pass because the relation states the congruence being checked.
- Missing: canonical normal forms, disjoint derivations of `materialize(Descend k z)` vs `Unwrap(materialize z,k)`, and full Space-level semantics for every op in egg.

### 3c. No negative information

Status: **Partial.**

- Addressed in Scala: `Observation(nullable, nonterminal, empty, childKeys)` makes nullable/nonterminal exact complements.
- Partial in egg: `nonterminal` relation allows subtraction terminal cases like epsilon minus a headed singleton, and regressions exist.
- Still open: egg negative info is monotone and incomplete; failed checks still mean underivability, not proof of falsity.

### 3d. Movement stuck on virtual operands

Status: **Partially addressed.**

- `zipper-descend.egg` now has `TerminalProductChild` rules that consult `terminal` / `nonterminal`.
- Regression for virtual terminal concat was added.
- Generated egg preludes still use the smaller shape-specific `TerminalProductChild` subset and do not include the full relational observation layer. This keeps cross-file divergence alive.

### 3e. Cross-file divergence

Status: **Open / only partially reduced.**

- Some divergence was fixed: generated prelude preserves `MemoZ` under child descent and uses generic nonlinear child rules.
- Still open:
  - `formal.egg` remains stale and has a different `PrefixZipper` / `ZPos` model.
  - Generated `zipper-egg-tests/*.egg` have a simpler descent prelude than `zipper-descend.egg`.
  - There is no single source-of-truth prelude emitted into every egg file.

### 3f. `formal.egg` zipper machinery dead code

Status: **Open.**

`formal.egg` still contains the old `ZPos` zipper model and materialization relation. It has not been rebuilt around the new context zipper.

### 3g. Alphabet expansion

Status: **Addressed for `zipper-descend.egg`, still divergent elsewhere.**

- Concrete hit/miss descent was generalized with nonlinear egg patterns and `!=` guards.
- Generated per-symbol concrete descent blocks were removed.
- Closure/tails structural rules in `zipper-descend.egg` no longer hardcode `a,b,c,d,x`; regressions now include a `z.q` path outside the old fixture alphabet.
- Still open: the generated `zipper-egg-tests` prelude remains simpler than `zipper-descend.egg`, and the old `formal.egg` / `zipper.egg` tracks are not generated from a single law table.

## Section 4: Missing trie ops

Status: **Mixed.**

- Movement:
  - Addressed: `up`, `path`, `toRoot`, ordered children, first child, next/previous sibling, child count via `childKeySize`.
  - Open: ordered DFS `to_next`, k-th child, and descend-until are not explicit APIs.

- Writes:
  - Addressed: graft, remove, insert at focus.
  - Open: explicit join-into and write cost accounting.

- Values:
  - Sidecarred. Enriched terminal data is present in `valued/`, but is
    deliberately not part of the production path-set zipper or proof gate.

- Fixpoint / Iter / Head / n-ary Join/Meet:
  - Partial in Scala: `JoinAll` / `MeetAll` are vector-based; `transpileZ` supports `Iteration` and `Fixpoint` at evaluator level.
  - Partial for egg/proof zipper formalism: `zipper-descend.egg` now has `HeadZ`, `IterZ`, and `FixpointZ`; `IterZ` is the identity-tail iterator, and `FixpointZ` is limited to the proved union-saturating tails-closure shape. The proof pipeline now models general grouped-head Iteration with head/rest bindings, proves canonical Iter templates, and bounded-checks puzzle/n-queens-shaped Iter examples. Still open: a generated binder table shared by Scala/egg/proofs, virtual semi-naive delta zipper theorem, general Fixpoint lowering, mutual recursion, and n-ary egg join/meet.

- Range:
  - Addressed in Scala runtime: ordered trie range and virtual range child traversal use path counts and ordered children.
  - Partial in egg: singleton border slices and nested border composition are now modeled and tested. Still open: a general ordered child/border-descent law over trie child maps.

- Pattern/transform:
  - Open if MORK-parity is in scope. No zipper-level variable query/substitution model exists.

## Section 5: Missed derivative-algebra framing

Status: **Partial.**

- Addressed informally/executably: tests name and check child movement as the Brzozowski derivative; Scala operations follow derivative-style child laws.
- Partial proof pipeline: Scala now owns the proof artifact source of truth. `morkl.ProofArtifactGeneratorMain` emits the SMT2 law files, TPTP Vampire obligations, and `proofs/proof_manifest.tsv`; `tools/proof_pipeline.py` only runs the checkers. Vampire proves first-order obligations that eager trie membership agrees with path-set membership, zipper membership agrees with eager trie membership, eager union/intersection/diff agree with path-set union/intersection/diff, eager Iteration agrees with grouped-head path-set Iteration, canonical Iter templates collapse to tails/head/headed source, and zipper base/union/intersection/diff/iteration materialization commutes with eager trie views. Z3 bounded-checks set algebra, restriction/raffination partition, Wrap/Unwrap, product and restriction derivative laws, tails/head, grouped-head Iteration, puzzle/n-queens-shaped Iter examples, closures, and Range subset/composition laws; negative-control laws must produce `sat`.
- Still open: no generated single source of truth for the committed operational egg prelude (`zipper-descend.egg` / `zipper.egg`), no proof of general Fixpoint/mutual-recursion laws, and no full Antimirov closure proof.

## Execution Plan Status

### Phase 0: One spec, one oracle

Status: **Mostly addressed, but not perfect.**

- Executable bounded oracle exists in `ZipperDenotationOracleTest`.
- It exhaustively checks bounded path sets over `{a,b}` and plug-invariance.
- Still missing: one centralized denotational spec used to generate both Scala runtime code and the committed operational egg prelude. The proof artifacts and example egg artifacts now come from Scala.

### Phase 1: Prove law table

Status: **Partial.**

Done:
- Added a Vampire/TPTP equivalence gate using the configured `--vampire`,
  `VAMPIRE`, or `PATH` command.
- Added `morkl.ProofArtifactGeneratorMain` as the Scala source of truth for reproducible TPTP obligations under `proofs/vampire/generated/`.
- Added the bounded SMT/Z3 law table to the same Scala source and generated reproducible SMT-LIB artifacts under `proofs/generated/`.
- Added `proofs/proof_manifest.tsv`, generated from Scala and consumed by the Python runner.
- Added `proofs/PROOF_REPORT.md` with the latest PASS report.
- Included negative controls for false rewrites such as commutative subtraction, nullable-missing restriction derivative, independent iteration without headed-source guard, and first-range-as-full.

Open:
- The law table is hand-coded in Scala rather than generated from the same table that defines the runtime and operational egg prelude.
- General `Fixpoint`, mutual recursion, a generated shared binder table, and Antimirov closure state are outside this first gate.

### Phase 2: Cost semantics

Status: **Open / partial runtime scaffolding only.**

The runtime now has a zipper interface and lazy patching, but there is no cost semantics, operation tier model, node-touch instrumentation, or memoization contract.

### Phase 3: Rebuild egglog harness

Status: **Partial.**

Done:
- Generic nonlinear concrete child rules.
- Relational keyset instead of rewrite-based analysis.
- Regression for key lattice collapse.
- Movement driven partly by `terminal` / `nonterminal`.

Open:
- One generated prelude.
- Non-vacuous `zipper.egg` semantics.
- Canonical path-set normal forms.
- Disjoint derivation/refinement theorem.
- Complete negative observation analysis.
- Shrinking/fuzz-generated egg checks as primary safety net.

### Phase 4: Close op gaps

Status: **Partial.**

Done:
- Context and `up` / `plug` laws in Scala.
- Graft/insert/remove in Scala.

Open:
- Values, merge lattices, join-into, cost accounting.
- General binder-aware `FixpointZ` / `IterZ` beyond the current tails-closure and identity-tail forms.
- Full ordered egg `Range` over child maps.
- n-ary egg join/meet.
- Pattern/transform zipper model.

### Phase 5: Land it

Status: **Partial.**

There is now a Vampire plus bounded-Z3 proof/test suite, short proof-pipeline README, and Scala-owned proof artifact generator. Still missing: one generated semantic table shared by Scala runtime code and the committed operational egg prelude, and a design writeup that treats the proof pipeline as normative.

## Recommended Next Work

1. Replace `zipper.egg` with a non-vacuous normal-form harness or retire it in favor of `zipper-descend.egg` plus generated oracle checks.
2. Extract one generated egg prelude shared by `zipper-descend.egg` and all `zipper-egg-tests`.
3. Finish closure/tails modeling by replacing the current finite `tail-frontier` relation with Antimirov-style frontier state and an explicit memoization contract.
4. Add cost instrumentation to `SpaceZipper.Cursor`, `PatchChild`, `Memo`, and observations; classify Tier A/B/C operations and test node-touch bounds.
5. Extend the bounded SMT/Z3 law gate to general Fixpoint lowering, mutual recursion lowering, and Antimirov closure state before expanding those egg rewrites.
6. Decide whether values/maps are in scope for MORKL. If yes, introduce payload merge semantics before claiming PathMap parity.
