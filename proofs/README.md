# MORKL Proof Pipeline

Run:

```sh
python3 tools/proof_pipeline.py
```

The pipeline is intentionally executable and counterexample-oriented.  Scala is
the source of truth for generated artifacts:

- `morkl.ProofArtifactGeneratorMain` generates TPTP files under
  `proofs/vampire/generated/`.
- The same Scala generator writes SMT-LIB files under `proofs/generated/`.
- The Scala generator also writes `proofs/proof_manifest.tsv`, which is the
  manifest consumed by the Python runner.
- Before running external solvers, the Python runner validates proof-shape
  invariants that must hold even in manifest-only runs.  In particular,
  bounded product derivative laws must use the generated `ProductClosed(X,Y)`
  guard for the principle "no concatenation escapes the bounded universe", and
  the unguarded mutated product law must remain a `sat` negative control.
  The same manifest-time gate also checks that each major algebra/proof family
  has live Z3 `sat` mutated negative controls, so a green run cannot silently
  lose the counterexample side of a law family.
  Symbol-sensitive bounded laws must also either include paired `a`/`b`
  representatives or provide an explicit symmetry artifact; this is checked
  before the expensive solver phases run.  Negative/key observations are
  likewise checked before solver execution: `absent-key` must flow through
  observed child emptiness, keyset facts must not collapse the lattice, and the
  generated `negative-key.egg` regression must stay in the transpiler suite.
  The same cheap gate rejects any `SuffixClosureOp`/`TailsClosureOp` rewrite
  that expands a concrete `TrieZ`; closure movement must stay expressed through
  frontier-state derivatives.  It also fails if the generated operational rule
  manifest contains any `UNPROVED` row.  The frontier algebra itself is also a
  manifest-time invariant: the runner checks both `zipper-descend.egg` and the
  generated `zipper-egg-tests/frontier-antimirov.egg` artifact for the required
  tail-frontier rules for intersection, diff, restriction, concat, wrap,
  suffix/tails closure, and scheduled frontier-state union reification.  Iter
  and Fixpoint have their own manifest-time acceptance invariant: binary
  `IterZ`/`FixpointZ` syntax, direct child movement, Kleene unfold witnesses,
  the semi-naive datalog `IterZ` projection over `complete.path`, and zipper-tier
  FOL materialization artifacts must all stay present.  Context movement is
  also guarded before solver execution: the runner requires the full
  `RootCtx`/`FrameCtx`/`TerminalFrameCtx`/`PatchFrameCtx` model, plug/path/up/down
  and sibling movement rules, generated patch-frame regression probes, and the
  first-order plug/graft/path/sibling artifacts.  A second executable-context
  gate checks that Scala's concrete and virtual zipper cursor APIs still expose
  path, plug, up/down, to-root, graft/remove/insert, and ordered sibling
  movement, and that the bounded denotational oracle tests cover every
  operation-shaped focus.  The former transform gap is guarded as a removal
  invariant: `Space.Transform` must remain absent, while the pure
  `Unification.T` pair-swap replacement keeps open-program SMT rows and
  SpaceValue/Trie graph backend regressions.  The value-payload experiment is
  intentionally sidecarred under `valued/`; the main proof pipeline remains a
  path-set pipeline so it can exploit the stronger unit/set laws.  Range has
  the same style of
  cheap acceptance gate: sentinel rewrites, ordered first/last/drop-last border
  state, scheduled `range-child-result`/`tail-frontier` movement, generated
  `range-observation`, `range-border-child`, and `range-border-operational`
  artifacts, and the first-order Range materialization/subset theorem family
  must stay present; generic eager `Child(Range*)` rewrites are rejected.
- `morkl.generateZipperEggTests` regenerates the independent
  `zipper-egg-tests/*.egg` artifacts.
- `morkl.generateCornerstoneProofArtifacts` regenerates exact-output SMT-LIB,
  TPTP, and egg certificates under `proofs/examples/` for aunt, semi-naive
  datalog, GOL, 15-puzzle, temperature, and n-queens.
- `morkl.generateOpenProgramProofArtifacts` regenerates symbolic open-program
  SMT-LIB obligations under `proofs/open/`, comparing expanded source, source
  optimization, raw graph round-trip, and optimized graph round-trip over
  bounded arbitrary input spaces.  It also emits structural full-program TPTP
  obligations under `proofs/open/vampire/` for the cornerstone programs and a
  dedicated full 24-state 2x2 puzzle step certificate.
- `tools/proof_pipeline.py` only orchestrates external checkers over the
  Scala-generated artifacts.
- It runs `/Applications/Vampire` in portfolio mode on first-order obligations proving that eager trie membership agrees with path-set membership, zipper membership agrees with eager trie membership, core zipper constructors commute with eager trie terminal/child observations, and the generated full-program structural backend certificates are valid.
- It asks Z3 for a bounded counterexample to each claimed law.
- Claimed laws pass when the negated equality is `unsat`.
- Negative-control laws pass when Z3 returns `sat`, proving the gate can catch false rewrites.
- It then runs `egglog` over `zipper-descend.egg`, `zipper.egg`, the generated
  `zipper-egg-tests/*.egg` artifacts, and the generated cornerstone egg
  certificates, plus the generated arbitrary-backend egg certificate.
- It writes the latest summary to `proofs/PROOF_REPORT.md`.

Current scope:

- Vampire obligations:
  - eager trie membership equals path-set membership through paths of depth 0..4 by recursive unfolding;
  - zipper membership equals eager trie membership through paths of depth 0..4 by recursive unfolding;
  - eager union/intersection/diff agree with path-set union/intersection/diff;
  - eager MORKL Iteration materializes to the path-set grouped-head iteration semantics;
  - the canonical Iteration templates for `tail`, `head`, and `head x tail` prove to `TailsUnion`, `Head`, and headed/non-empty source respectively;
  - ordered Range proves its full `0..0` sentinel, empty `1..1` slice, and eager-trie/path-set bridge through abstract rank-selection lemmas;
  - zipper base/union/intersection/diff terminal and child movements commute with eager trie terminal and child movements.
  - zipper `Iter` materialization commutes with eager trie iteration.
- Alphabet: `a,b`
- Maximum path length: `3`
- Space model: finite path sets encoded as bit-vectors
- Covered families: set algebra, restriction/raffination partition, wrap/unwrap, product derivatives, restriction derivatives, tails/head, grouped-head Iteration, small puzzle/n-queens Iteration examples, closures, and ordered range slices.
- Cornerstone example checks: for each of aunt, semi-naive datalog, GOL,
  15-puzzle, temperature, and n-queens, Scala checks and then emits solver
  certificates for trie eval vs reference eval, source-optimized Space/term vs
  original Space/term, zipper materialization vs Space/Trie evaluation, and
  graph `execT` vs Space/Trie evaluation.
- Open-program checks: Scala translates proof-sized MORKL programs and
  benchmark skeletons to the bounded path-set model, then Z3 proves source
  optimization, raw graph round-trip, and optimized graph round-trip equivalent
  for every symbolic input in that bounded universe.  The current corpus emits
  78 such Z3 obligations, including the full Aunt query at length 3 and a
  proof-sized full GOL helper expansion.
- Structural full-program checks: Scala emits expanded MORKL terms for Aunt,
  semi-naive Datalog, GOL, temperature, the arbitrary-input 2x2 sliding-puzzle
  transition, the complete 24-state 2x2 sliding-puzzle step, and 4-queens as
  first-order DAG terms.  Vampire proves source, optimized-source, trie, zipper,
  and graph backends equivalent with constructor-specific implementation lemmas
  over arbitrary interpretations of input spaces and path references.  `Iter`
  uses an explicit path/space binding environment; `Range` uses source
  membership plus ordered rank/count/bounds selection.
- Arbitrary-data backend checks: Vampire proves source/path-set, eager trie,
  zipper, and operation-graph constructors agree over symbolic input spaces
  rather than only over the cornerstone data.  The generated egg certificate
  rewrites symbolic source, optimized source, trie, zipper, and graph forms over
  arbitrary `X`, `Y`, and `F` inputs to one semantic normal form.
- Valued-map checks: the historical value-payload oracle, tests, and generated
  proof artifacts have been moved to `valued/`.  They are not part of the main
  proof gate; the main runtime and proof claims remain path-set-only.

Important limit:

Vampire proves the first-order equivalence obligations listed above, but not every optimizer rewrite directly from one generated semantic table. The Z3 algebraic law and open-program phases are still bounded finite-language refutation gates. Cornerstone example proofs are closed instantiated output-equivalence certificates over their generated inputs/contexts; the open-program SMT tier now covers proof-sized operator programs, benchmark skeletons, the full Aunt query over arbitrary bounded inputs, and a proof-sized full GOL expansion. DAG-shared SMT emission makes these obligations practical, but whole programs with very large literal domains are better handled by the structural FOL tier. That FOL tier now generates full-program arbitrary-data backend certificates for the six cornerstone examples plus a complete 24-state 2x2 sliding-puzzle step certificate. Its current lemmas are constructor-specific for backend equivalence and include concrete literal/path definitions. `Iter` now has explicit environment-stack semantics for bound path refs and rest spaces, including nested iteration capture; `Range` now exposes membership, rank, count, normalized bounds, and half-open interval selection. `Fixpoint` now exposes the union-saturating base-or-step equation in that same structural environment, while the proved tail-template form still lowers structurally to `TailsClosure`. `Fold` and grounded functions remain represented by shared operator semantic predicates. The next improvement is to unfold those remaining predicates into stronger op-specific FOL lemmas so Vampire proves deeper optimizer and graph-lowering structure. The Antimirov closure-state operators now have bounded SMT artifacts for frontier union, keyed frontier tails, nested frontier child movement, and suffix/tails closure child states. Mutual recursion, leastness/positivity obligations for general `Fixpoint`, and an unbounded FOL proof of the full Antimirov frontier-state construction remain outside this first pipeline. `zipper-descend.egg` and `zipper.egg` are still committed operational targets; the example egg artifacts and all SMT2/TPTP proof artifacts now come from Scala.
