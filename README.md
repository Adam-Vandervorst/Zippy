# Zippy

Zippy is a small algebra for programming with finite sets of structured paths — values like
`parent.Tom.Bob` or `Cell.2.1` are words in a free monoid, a *space* is a finite set of such
words, and a handful of set/monoid operators (union, intersection, subtraction, composition,
prefix restriction, wrap/unwrap, tails, iteration, recursion) express relational queries,
Datalog fixed points, graph algorithms, and trie-indexed search.

**Start with [ALGEBRA.md](docs/ALGEBRA.md)** — a self-contained functional-pearl-style paper that
develops the core algebra, relates it to semirings, Kleene algebras, complex-object query
languages, and trie automata, and works through five case studies. This repository is the
executable and machine-checked counterpart of that paper.

## What is here

| Area | Contents |
| --- | --- |
| `src/main/scala/` | The `Space` AST, reference evaluators (`eval`, `evalI`), compiled executors (`exec`, `execT`, the zipper executor `execZ`), hash-consed interned tries (`IntTrie`), the zipper runtime (`Zipper`), the positive supercompiler (`Supercompiler`), and the proof-emission pipeline (`EquivPipeline`). |
| `src/test/scala/` | The full test and benchmark suite: executors, algebraic-law property tests, the fuzzed 1000-program corpus, the seven-cornerstone equivalence pipeline, and the case studies from the paper. |
| `formal.egg`, `zipper.egg` | Illustrative, runnable egglog models: the core set language (eager set-of-paths semantics) and the zipper extension over the same prelude. |
| `zipper-spec.egg`, `zipper-impl.egg` | The certified rewrite systems: the zipper movement/observation spec and the eager-trie implementation recursion. Every rule carries a proof/definitional annotation. |
| `proofs/` | SMT-LIB proof obligations: per-law certificates (`laws/`, indexed by `laws/REGISTRY.tsv`), rule certifications, executor characterizations, and the machine-readable verdict table `STATUS.tsv`. |
| `terminating/` | The RECURSION CERTIFICATES: what a `Fixpoint` computes, what each lowering pass preserves, and why each recursion terminates. `terminating/REGISTRY.tsv` is the total map from the lowering surface to its obligations; `terminating/STATUS.tsv` carries the per-prover verdicts. |
| `zipper-egg-tests/` | Generated egglog artifacts: randomized spec/impl/reference differentials (`generated/`) and the per-program equivalence pipeline output (`pipeline/`). |
| `scripts/` | Generators and CI checkers (see below). |
| [`docs/SUPERCOMPILER.md`](docs/SUPERCOMPILER.md) | Design, guiding examples, and limitations of the supercompiler. |
| [`docs/BENCHMARKS.md`](docs/BENCHMARKS.md) | Executor, op-graph and zipper benchmark results, each stamped with the machine, toolchain and configuration it was produced on. |
| [`docs/residuals.md`](docs/residuals.md) | Why the residuated-division operators are omitted from the algebra. |
| [`docs/SPATIAL_SEMANTICS.md`](docs/SPATIAL_SEMANTICS.md) | The backend-parameterised event algebra and compositional event semantics of every certified constructor, checked against the counted executors. |
| [`docs/SPATIAL_DOMAIN.md`](docs/SPATIAL_DOMAIN.md) | The two-tier correlated spatial domain: exact hash-consed tries with alternatives, summaries, alias channel, and named widenings. |
| [`docs/SPATIAL_COST.md`](docs/SPATIAL_COST.md) | Resource bounds by abstract interpretation, parametric call summaries and recursive systems, and transfer certification (`proofs/spatial/`). |
| [`docs/DECISIONS.md`](docs/DECISIONS.md) | Generated decision cases with closed traces, per-backend certificates, certified Pareto selection, counted runs beside predicted intervals, and scalar predictors evaluated on the same frontier; machine-readable twin `proofs/decisions/`. |
| [`docs/ACCEPTANCE.md`](docs/ACCEPTANCE.md) | Generated acceptance status — GREEN / CONDITIONAL / UNSOUND / SOUND-BUT-NOT-USEFUL / UNMEASURED — derived from acceptance criteria, recorded gates, proof closures, and committed evidence; `--check` fails on drift. |
| [`proofs/puzzle15/REPORT.md`](proofs/puzzle15/REPORT.md) | Generated puzzle15 derivation report: state-space theorems, checked expansion, per-declaration/backend certificates, usefulness verdicts, and the source of symbolic imprecision. |
| [`docs/TRUSTED.md`](docs/TRUSTED.md) | **The complete trusted base**: every assumption a `PROVED` verdict rests on, and the three open obligations that are gaps rather than assumptions. |

## Requirements

| tool | version this tree is verified against | how it is found |
|---|---|---|
| JDK | 21 (`openjdk-21-jdk-headless`) | `JAVA_HOME` / `PATH` |
| sbt | 2.0.8 (pinned in `project/build.properties`; any 1.x/2.x launcher bootstraps it) | `PATH` |
| Scala | 3.8.1 (pinned in `build.sbt`; fetched by sbt) | — |
| [z3](https://github.com/Z3Prover/z3) | 5.1.0 | `$Z3`, then `$ZIPPY_TOOLS`, then `PATH` |
| [Vampire](https://vprover.github.io) | 5.1.0 | `$VAMPIRE`, then `$ZIPPY_TOOLS`, then `PATH` |
| [egglog](https://github.com/egraphs-good/egglog) | 3.0.0 | `$EGGLOG`, then `$ZIPPY_TOOLS`, then `PATH` |
| [Lean 4](https://lean-lang.org) via `elan` | `leanprover/lean4:v4.33.1` (`proofs/lean/lean-toolchain`), Mathlib `v4.33.1` (`proofs/lean/lake-manifest.json`) | `$LAKE`, then `$ZIPPY_TOOLS`, then `PATH`, then `${ELAN_HOME:-~/.elan}/bin` |

Library dependencies (munit, scala-collection-contrib) are resolved by sbt from `build.sbt`.
Every pipeline proof obligation must be discharged by **both** provers.

**Installing the three external tools.** There is nothing to bootstrap and no lock file to
check out — z3 and Vampire ship prebuilt Linux/macOS binaries and egglog builds from source:

```sh
# z3 5.1.0 and Vampire 5.1.0 — prebuilt release archives
curl -fsSLO https://github.com/Z3Prover/z3/releases/download/z3-5.1.0/z3-5.1.0-x64-glibc-2.39.zip
curl -fsSLO https://github.com/vprover/vampire/releases/download/v5.1.0/vampire-Linux-X64.zip
# egglog 3.0.0 — needs a Rust toolchain and a C linker (`apt-get install build-essential`)
cargo install --locked --git https://github.com/egraphs-good/egglog egglog
# Lean 4.33.1 + Mathlib (the mechanized theorems under proofs/lean; `scripts/check_lean.sh` is a gate)
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain leanprover/lean4:v4.33.1
~/.elan/bin/elan toolchain install leanprover/lean4:v4.33.1      # elan is lazy; pin it now
(cd proofs/lean && ~/.elan/bin/lake exe cache get && ~/.elan/bin/lake build)   # Mathlib oleans (~5 GB), then the package
```

Then point the tree at them, EITHER per tool or with one directory:

```sh
export Z3=/path/to/z3  VAMPIRE=/path/to/vampire  EGGLOG=/path/to/egglog
# or, if all three live in one directory:
export ZIPPY_TOOLS=/path/to/prover-bin
```

`toolchain.conf` at the repo root is the single resolution policy — the search order above, one
entry per tool — and `src/main/scala/Tools.scala`, `scripts/toolpath.sh` and `scripts/toolpath.py`
all read it, so a machine configured for one is configured for all. No install location is
hardcoded anywhere in the tree. To see what resolves:

```sh
python3 scripts/toolpath.py        # z3 / vampire / egglog -> resolved path, or ABSENT
```

A missing tool is a **named error** that says which variable to set, never a silent skip.

## Running

```sh
sbt 'testOnly morkl.*'            # full suite: executors, laws, corpus, case studies, and the
                                  # SEVEN-cornerstone equivalence pipeline.  ~1 h: EquivPipelineTest
                                  # runs z3 and Vampire on every emitted obligation and is most of
                                  # it.  (`sbt test` skips suites already run since the last change.)

egglog formal.egg                 # tour of the core set language (all checks pass)
egglog zipper.egg                 # tour of the zipper extension

proofs/run.sh                     # discharge every proof obligation with z3 AND Vampire, the
                                  # pipeline family included; writes proofs/STATUS.tsv
terminating/run.sh                # z3 AND vampire on the recursion corpus (pinned goal counts,
                                  # writes terminating/STATUS.tsv)
proofs/unbounded/run.sh           # TIER 3: the schematic FOL corpus, plus 8 negative controls and
                                  # a per-file vacuity probe; writes proofs/unbounded/STATUS.tsv
```

CI checkers (all exit non-zero on any problem):

```sh
python3 scripts/check_obligations.py     # every egg rule annotated; cited certificates live
                                         # (OPEN must be acknowledged, countermodels always fail)
python3 scripts/check_laws.py            # every optimiser law has a PROVED certificate;
                                         # the law registry is in sync with the Scala source
python3 scripts/audit_pipeline_markers.py# every pipeline artifact is REAL / TRIVIAL /
                                         # LAW-JUSTIFIED / BUDGET / IDENT — no vacuous checks
python3 scripts/check_references.py --snapshot=index --strict
                                         # every path a tracked file cites resolves, against ONE
                                         # git snapshot (names AND contents), case-exact.
                                         # `--selftest` builds throwaway repos for the four
                                         # regressions: uncommitted edit, deleted-but-tracked,
                                         # untracked target, case-only mismatch
python3 scripts/proof_closure.py --check # the transitive `include` closure of every reported
                                         # proof status, intersected with docs/TRUSTED.md: an
                                         # unqualified PROVED whose closure reaches a trusted
                                         # axiom is an error.  Also flags an include that
                                         # resolves only from the corpus root, which is how
                                         # three negative controls were unreadable for a round
python3 scripts/check_traces.py          # every typed proof trace (proofs/pipeline/traces) is a
                                         # well-formed DAG with certified leaves; every declared
                                         # CLAIMS.tsv cell has one
python3 scripts/proof_closure.py --inject-open O6a --expect-consumers 1
                                         # the trace closure is transitive: opening one registry
                                         # entry turns exactly its consumers OPEN
python3 scripts/check_selection.py       # every committed selection certificate (proofs/decisions)
                                         # re-derives from its candidate rows: admission, constraints,
                                         # interval dominance, and the declared tie rule
python3 scripts/check_coverage.py        # every feature row of
                                         # proofs/pipeline/COVERAGE.tsv is anchored to a trace term
                                         # or node and a discharged claim; the census of unsupported
                                         # constructors and unexercised laws is complete.
                                         # `--selftest` mutates copies and requires each to be caught
python3 scripts/check_puzzle15.py        # the committed puzzle15 expansion is a
                                         # legal BFS, every counted run inside its interval, no result
                                         # bound above the proved 4·|frontier|, the thresholds hold
python3 scripts/gen_acceptance.py --check# docs/ACCEPTANCE.md agrees with the recorded gate results, the
                                         # closures and the committed evidence; `--selftest` shows
                                         # that opening a theorem, failing a gate or dirtying a result
                                         # moves the corresponding row away from GREEN
python3 scripts/gen_bridge_tests.py      # regenerate the randomized differentials
python3 scripts/gen_law_obligations.py   # regenerate the per-law certificate corpus
```

Benchmark artifacts are **not** regenerated by any of the above, and not by `sbt test` either:

```sh
python3 scripts/publish_benchmarks.py --dry-run   # what blocks publication right now
python3 scripts/publish_benchmarks.py             # preflight -> gates -> capture -> generate
                                                  # -> validate -> report; commits nothing
```

Publication is one transaction: it aborts on a dirty tree or an untracked relevant input, runs the
acceptance gates *before* regenerating anything, captures **one** commit identity and **one**
environment record for all four outputs, permits only declared outputs to change, and validates
provenance, schema, row sets and the generated-section markers before it reports the diff. Outside
a publication every writer of a committed artifact refuses or skips, which is what makes a test run
read-only with respect to the repository. A failed gate reports the blocking property directly.

## Verification, in one paragraph

The algebra's laws are not asserted but certified: each is a small ∀-statement over the
set-of-paths denotation, proved by z3 and Vampire, with structural induction always explicit as
schema instances (`proofs/laws/`). Every rewrite rule in the three egglog systems is annotated
with its certificate, and checkers keep that mapping total and honest — admitted-open
obligations are machine-visible in `proofs/STATUS.tsv`, and a prover countermodel fails the
build. On top of the law corpus, an automated pipeline emits, for each of seven cornerstone
programs, three stages (the optimised term, the zipper program, the compiled operation graph)
against the reference semantics, in two tiers (equationally in egglog, denotationally in both
provers) and in two variants (this instance, and data-agnostic over free inputs) —
`puzzle3-full` being the one whose recursion is an unbounded `Space.Fixpoint`.

**Read `proofs/pipeline/STATUS.tsv` before believing anything about that matrix.** It is not a
full-support table, and the marker vocabulary is the point: a cell is `PROVED` only when a prover
discharged an actual equivalence goal. A `TRIVIAL` or `IDENTICAL-STRUCTURE` cell means the two
sides came out as the same term and there was **no obligation to discharge**; `LAW-JUSTIFIED`
means every differing pair was replayed as an instance of a certified law rather than proved per
program; `OPEN (prover budget exceeded)` means neither prover reached it, with the attempt log in
the file. And `BOUNDED-UNROLLING (k=…)` means the cell carries a real goal whose sides contain a
**residual cut** — a recursive call no lowering recognised, replaced past depth *k* by a fresh free
input — so its claim is about the *k*-unrollings at those depths and **not** about the recursion;
lifting it needs registry row O10b (all *k* plus omega-continuity), which is open. Only the first
counts as certified equivalence for that cell. As of this commit a
minority of the 42 cells are `PROVED`, and the reason most of the instance cells are markers is
recorded rather than hidden: `EquivPipeline.expand` evaluates control flow on **both** sides, so
the two renderings are literal-vs-literal. Cornerstone claims therefore require independently
constructed sides and a replayable relation between them. `scripts/audit_pipeline_markers.py` classifies every artifact,
executes them under `--run`, and fails on a marker that defers to another marker. `proofs/unbounded/` is a third tier: the same operator
laws stated SCHEMATICALLY, over all spaces and all paths, which neither the interval propagation nor
the ground SMT tier can express at all. The recursive case studies are certified in `terminating/` — what a `Fixpoint` computes, what each
lowering pass preserves, and why each recursion terminates — with every goal discharged by z3 and
re-run per goal under Vampire. Randomized
differentials (thousands of checks per run) ground the egg models and the Scala executors
against independent reference semantics.
