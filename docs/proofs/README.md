# MORKL Proof Pipeline

Run:

```sh
env _JAVA_OPTIONS='-Xmx4g -Xss64m' \
  PYTHONPYCACHEPREFIX=/tmp/morkl_pycache \
python3 tools/proof_pipeline.py --solver-workers 1
```

The mandatory symbolic 2x2-puzzle full-open obligations use a focused width-125
universe containing exact translated witnesses for all four move directions:
`A -> {B,C}`, `B -> {A}`, and `C -> {A}`. This is deliberately not the complete
24-state transition relation; move-table constants outside the bound encode as
zero. Generation measured 4,582,176 KiB peak resident memory including JVM
overhead, so the proof-only command uses a 4 GiB heap while the ordinary Scala
suite can retain its 1.5 GiB bound. Use one solver worker unless the machine has
substantial spare memory: the largest focused puzzle row measured 61,854,736
KiB Z3 RSS, its graph rows about 7.7 GiB, and the exact witnesses about 3.9 GiB.

Vampire is resolved portably from `--vampire`, then the `VAMPIRE`
environment variable, then `PATH`; there is no machine-specific default. Use
`--long` to expand the default bounded universe from alphabet `a,b` through
length 3 to alphabet `a,b,c` through length 4. Explicit `--alphabet` and
`--max-len` values still take precedence. Independent solver obligations run
through the runner's worker pool (`--solver-workers`, defaulting to at most
four workers, or eight for `--long`). The generated report records a UTC
timestamp, Git SHA/dirty state, and portable tool-version strings.

Every normal run snapshots committed generated outputs, regenerates them in the
same process, and fails if they changed. After an intentional generator change,
review and commit the regenerated files, then rerun to establish a clean
freshness gate. Ignored `*_full_open_*.smt2` files are intentionally excluded
from that diff: they are regenerated and solved on every run, not committed.
`--no-freshness-check` exists for scratch runs into temporary output paths.
Every `--no-*-generation` flag is also recorded as a skipped/reused generator
in the report and makes the run ineligible for `PASS` or
`PASS_WITH_PROOF_DEBT`; solver success over reused artifacts is only a partial
run.

The pipeline is intentionally executable and counterexample-oriented.  Scala is
the source of truth for generated artifacts. Test-scope generators compile only
`src/main/scala` and `src/test/scala`; the isolated `valued/` sidecar is not on
their source path:

- `morkl.ProofArtifactGeneratorMain` generates TPTP files under
  `../../proofs/vampire/generated/`.
- The same Scala generator writes SMT-LIB files under `../../proofs/generated/`.
- The Scala generator also writes `../../proofs/proof_manifest.tsv`, which is the
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
  before the expensive solver phases run. The manifest gate also validates the
  exact kind, theorem expectation, and file identity of every structural
  full-program obligation, including 4x4 sliding puzzle and SCC, plus all three
  bounded symbolic relations for the named semi-naive-Datalog and 2x2-puzzle
  full-open cases and the puzzle's three exact-output non-vacuity witnesses
  covering all four directions. Structural invariants reject concrete closure
  expansion and require the frontier algebra, termination artifacts, and a
  zero-`UNPROVED` operational manifest. Executable behavior is covered by the
  Scala semantic and asymptotic test suites rather than redundant Python source
  string scanners. A manifest-ownership gate also rejects stale solver files
  left behind when a generator stops emitting an obligation; closed examples
  may contain only their manifest and executable parity report.
- `morkl.generateZipperEggTests` regenerates the independent
  `zipper-egg-tests/*.egg` artifacts.
- `morkl.generateCornerstoneProofArtifacts` executes independent reference,
  trie, source-optimizer, zipper, and graph evaluations for aunt, semi-naive
  Datalog, GOL, 15-puzzle, temperature, n-queens, and SCC, then writes a parity
  report. The old closed-output SMT-LIB, TPTP, and egg files merely encoded both
  sides as one precomputed answer, so they are no longer generated or committed.
- `morkl.generateOpenProgramProofArtifacts` regenerates symbolic open-program
  SMT-LIB obligations under `proofs/open/`, comparing expanded source, source
  optimization, raw graph round-trip, and optimized graph round-trip over
  bounded arbitrary input spaces.  It also emits structural full-program TPTP
  schema-consistency obligations under `proofs/open/vampire/` for the cornerstone programs,
  including an arbitrary-input 4x4 sliding-puzzle program and a dedicated full
  24-state 2x2 puzzle-step structural check. These FOL files axiomatize
  per-constructor backend/source agreement, so they check program-DAG and
  contract consistency rather than independently proving the implementations
  equivalent. The full-open SMT obligations are
  generated beneath `proofs/open/smt2/` and remain ignored/ephemeral.
- `tools/proof_pipeline.py` only orchestrates external checkers over the
  Scala-generated artifacts.
- It runs the configured Vampire command in portfolio mode by default on
  first-order obligations proving eager-trie/path-set and zipper/trie laws,
  plus the explicitly axiomatized full-program structural schema checks.
  Deliberately decomposed obligations may declare
  `vampire-strategy=plain` in their generated manifest note and use Vampire's
  plain saturation loop; the selected strategy is reported on failure. The
  full-program schema obligations validate only consistency under their
  backend/source agreement axioms.
- It asks Z3 for a bounded counterexample to each claimed law.
- Claimed laws pass when the negated equality is `unsat`.
- Negative-control laws pass when Z3 returns `sat`, proving the gate can catch false rewrites.
- It then runs `egglog` over `zipper-descend.egg`, `zipper.egg`, the generated
  `zipper-egg-tests/*.egg` artifacts, and the generated arbitrary-backend egg
  certificate.
- It writes the latest summary to `PROOF_REPORT.md`.

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
- Cornerstone example checks: for each of aunt, semi-naive Datalog, GOL,
  15-puzzle, temperature, n-queens, and SCC, Scala differentially checks trie
  evaluation against the independent reference, optimized source against the
  original term, zipper materialization against Space/Trie, and graph `execT`
  against Space/Trie. These are executable parity gates, not solver certificates.
- Open-program checks: Scala translates proof-sized MORKL programs and
  benchmark skeletons to the bounded path-set model, then Z3 proves source
  optimization, raw graph round-trip, and optimized graph round-trip equivalent
  for every symbolic input in that bounded universe. The corpus includes the
  full Aunt query, semi-naive-Datalog full-open program, a proof-sized full GOL
  expansion, and the 2x2-puzzle full-open program; the generated report is the
  source of truth for current counts and bounds.
- Structural full-program schema checks: Scala emits expanded MORKL terms for Aunt,
  semi-naive Datalog, GOL, temperature, arbitrary-input 2x2 and 4x4
  sliding-puzzle programs, the complete 24-state 2x2 sliding-puzzle step,
  4-queens, and SCC as first-order DAG terms. Vampire checks their well-formedness
  and consistency under constructor-specific axioms equating each backend's
  membership contract with source membership. This does not independently
  establish implementation equivalence. `Iter` uses an explicit path/space binding
  environment; `Range` uses source membership plus ordered rank/count/bounds
  selection. The SCC structural artifact retains the paper routine's pivot
  `Range`, representative emission, and three shrinking recursive partitions;
  masked reachability lowers to `Fixpoint`. Curated Vampire theorems prove the
  reachability value/decrease invariants and all three SCC branch decreases,
  alongside executable reference/trie/zipper/graph parity coverage.
- Arbitrary-data backend checks: bounded open-program SMT searches for
  counterexamples over symbolic input spaces, while the structural FOL files
  compose axiomatized contracts. The generated egg certificate
  rewrites symbolic source, optimized source, trie, zipper, and graph forms over
  arbitrary `X`, `Y`, and `F` inputs to one semantic normal form.
- Valued-map checks: the historical value-payload oracle, tests, and generated
  proof artifacts have been moved to `valued/`.  They are not part of the main
  proof gate; the main runtime and proof claims remain path-set-only.

Important limit:

Vampire proves the non-full-program first-order laws listed above, but not every optimizer rewrite directly from one generated semantic table. The Z3 algebraic law and open-program phases are bounded finite-language refutation gates. Closed cornerstone checks are differential Scala executions, not theorem-prover certificates; they and open symbolic SMT are the independent backend evidence. The structural FOL tier covers the seven cornerstone families, a 4x4 sliding-puzzle program, and a complete 24-state 2x2 step, but its backend/source agreement is axiomatized per constructor. It therefore checks structural DAG and contract consistency only. `Iter` has explicit environment-stack syntax for bound path refs and rest spaces; `Range` exposes membership, rank, count, normalized bounds, and half-open interval selection. `Fixpoint` exposes the union-saturating base-or-step equation in that same structural schema. `Fold` and grounded functions remain represented by shared operator semantic predicates. The Antimirov closure-state operators have bounded SMT artifacts for frontier union, keyed frontier tails, nested frontier child movement, and suffix/tails closure child states. Mutual recursion, leastness/positivity obligations for general `Fixpoint`, and an unbounded independent proof of the full Antimirov frontier-state construction remain outside this pipeline. `zipper-descend.egg` and `zipper.egg` remain committed operational targets; the proof generators do not emit closed-output cornerstone solver tautologies.
