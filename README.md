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
| `src/test/scala/` | The full test and benchmark suite: executors, algebraic-law property tests, the fuzzed 1000-program corpus, the six-cornerstone equivalence pipeline, and the case studies from the paper. |
| `formal.egg`, `zipper.egg` | Illustrative, runnable egglog models: the core set language (eager set-of-paths semantics) and the zipper extension over the same prelude. |
| `zipper-spec.egg`, `zipper-impl.egg` | The certified rewrite systems: the zipper movement/observation spec and the eager-trie implementation recursion. Every rule carries a proof/definitional annotation. |
| `proofs/` | SMT-LIB proof obligations: per-law certificates (`laws/`, indexed by `laws/REGISTRY.tsv`), rule certifications, executor characterizations, and the machine-readable verdict table `STATUS.tsv`. |
| `terminating/` | Termination proofs for the recursive case studies (TPTP + SMT-LIB twins): finite-universe measure arguments and the lexicographic semi-naive measure. |
| `zipper-egg-tests/` | Generated egglog artifacts: randomized spec/impl/reference differentials (`generated/`) and the per-program equivalence pipeline output (`pipeline/`). |
| `scripts/` | Generators and CI checkers (see below). |
| `SUPERCOMPILER.md` | Design, guiding examples, and limitations of the supercompiler. |
| `BENCHMARKS.md` | Executor and zipper benchmark results. |
| `residuals.md` | Why the residuated-division operators are omitted from the algebra. |

## Requirements

- Scala 3.8 with [sbt](https://www.scala-sbt.org) (or `scala-cli`); dependencies: munit,
  scala-collection-contrib.
- [egglog](https://github.com/egraphs-good/egglog) for the equational models and differentials.
- [z3](https://github.com/Z3Prover/z3) and [Vampire](https://vprover.github.io) for the proof
  obligations (every pipeline obligation must be discharged by *both*).

## Running

```sh
sbt test                          # full suite: executors, laws, corpus, case studies,
                                  # and the six-cornerstone equivalence pipeline

egglog formal.egg                 # tour of the core set language (all checks pass)
egglog zipper.egg                 # tour of the zipper extension

proofs/run.sh                     # discharge every proof obligation with z3 AND Vampire;
                                  # writes the machine-readable verdicts to proofs/STATUS.tsv
terminating/run.sh                # z3 on the termination twins (pinned goal counts)
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
the reference semantics (equationally in egglog, denotationally in both provers), on six
cornerstone programs with data-agnostic variants; optimiser rewrites are justified as instances
of the certified laws by syntactic replay. Termination of the recursive case studies is proved
by measure arguments in `terminating/`, cross-checked between TPTP and SMT-LIB. Randomized
differentials (thousands of checks per run) ground the egg models and the Scala executors
against independent reference semantics.
