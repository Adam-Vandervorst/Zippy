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

## Requirements

- Scala 3.8 with [sbt](https://www.scala-sbt.org) (or `scala-cli`); dependencies: munit,
  scala-collection-contrib.
- [egglog](https://github.com/egraphs-good/egglog) for the equational models and differentials.
- [z3](https://github.com/Z3Prover/z3) and [Vampire](https://vprover.github.io) for the proof
  obligations (every pipeline obligation must be discharged by *both*).

## Running

```sh
source .tools/env.sh               # JDK 21, sbt, scala-cli, z3, Vampire, egglog on PATH.
                                  # Nothing below assumes a system install; every tool is also
                                  # resolvable from $Z3/$VAMPIRE/$EGGLOG (see src/main/scala/Tools.scala)

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
python3 scripts/gen_bridge_tests.py      # regenerate the randomized differentials
python3 scripts/gen_law_obligations.py   # regenerate the per-law certificate corpus
```

## Verification, in one paragraph

The algebra's laws are not asserted but certified: each is a small ∀-statement over the
set-of-paths denotation, proved by z3 and Vampire, with structural induction always explicit as
schema instances (`proofs/laws/`). Every rewrite rule in the three egglog systems is annotated
with its certificate, and checkers keep that mapping total and honest — admitted-open
obligations are machine-visible in `proofs/STATUS.tsv`, and a prover countermodel fails the
build. On top of the law corpus, an automated pipeline proves per program that the optimised
term, the zipper program, and the compiled operation graph are observationally equivalent to
the reference semantics (equationally in egglog, denotationally in both provers), on seven
cornerstone programs with data-agnostic variants — `puzzle3-full` being the one whose recursion is an
unbounded `Space.Fixpoint`. A cell no prover discharges is recorded as `PROVER-BUDGET-EXCEEDED` with
its attempt log and does NOT count as certified; optimiser rewrites are justified as instances
of the certified laws by syntactic replay. `proofs/unbounded/` is a third tier: the same operator
laws stated SCHEMATICALLY, over all spaces and all paths, which neither the interval propagation nor
the ground SMT tier can express at all. The recursive case studies are certified in `terminating/` — what a `Fixpoint` computes, what each
lowering pass preserves, and why each recursion terminates — with every goal discharged by z3 and
re-run per goal under Vampire. Randomized
differentials (thousands of checks per run) ground the egg models and the Scala executors
against independent reference semantics.
