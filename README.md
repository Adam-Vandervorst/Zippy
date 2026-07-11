# Zippy / MORKL

Zippy is the Scala implementation, optimizer, supercompiler, and verification
suite for **MORKL**, an algebra over finite sets of structured paths.

For the language itself, start with the functional pearl:

> **[Zippy: An Algebra for Path Sets](ALGEBRA.md)**

That paper introduces the algebra through family queries, graph algorithms,
Game of Life, semi-naive Datalog, and fuzzy temperature search. This README is
only the repository guide.

## Status

The project contains working implementations of:

- the direct `Set[PathValue]` reference semantics;
- an interned `IntMap` trie runtime;
- a virtual zipper evaluator with focus/context movement;
- recursive operation-graph lowering and direct trie execution;
- source optimization and positive supercompilation;
- generated egglog, Z3, and Vampire proof artifacts;
- dependent expression/space fuzzers and differential backend verification;
- benchmark suites for the cornerstone MORKL programs.

This is an active research codebase. Correctness gates are extensive, but the
proof report deliberately distinguishes bounded evidence from unbounded proofs.
See [Proof Status](#proof-status) and [`fallbacks.md`](fallbacks.md).

## Repository Layout

| Path | Purpose |
| --- | --- |
| `src/main/scala/MORKL.scala` | language syntax, reference evaluator, operation graphs, optimization, and `execT` |
| `src/main/scala/TrieSpace.scala` | interned trie representation and native algebra |
| `src/main/scala/ZipperSpace.scala` | virtual zipper operators, traversal, context, and `execZ` |
| `src/main/scala/SC.scala` | positive supercompiler and residualization |
| `src/main/scala/Fuzzer.scala` | reusable distribution and corpus machinery |
| `src/main/scala/ProofArtifacts.scala` | generated bounded and unbounded proof obligations |
| `src/test/scala/` | unit, differential, corpus, proof-generation, and benchmark suites |
| `formal.egg` | generated readable model of the core set language |
| `zipper.egg` | generated readable zipper extension using the same core prelude |
| `zipper-descend.egg` | comprehensive operational zipper model |
| `zipper-egg-tests/` | independently executable generated egg examples |
| `proofs/` | generated SMT2, TPTP, egg, manifests, and reports |
| `tools/proof_pipeline.py` | proof orchestration and reporting |
| `build.log` | append-only development and verification record |
| `valued/` | isolated experimental path-to-value track |

The production language is path-set based. The optional valued-map experiment
is kept separate so the main algebra retains unconditional set idempotence,
absorption, and ordinary difference.

## Requirements

- Scala CLI
- Scala 3.8.1 with `--source 3.3`
- egglog
- Z3
- Vampire at `/Applications/Vampire` for the full proof gate
- Python 3 for orchestration and dataset utilities

The commands below use bounded JVM memory because the complete proof and fuzz
suites are intentionally substantial.

## Build and Test

Run the Scala suite:

```bash
env _JAVA_OPTIONS='-Xmx1536m -Xss64m' \
scala-cli test src/main/scala src/test/scala \
  --server=false \
  --scala 3.8.1 \
  --source 3.3 \
  --dependency org.scalameta::munit:1.2.1 \
  --dependency org.scala-lang.modules::scala-collection-contrib:0.3.0
```

Run the three root egg models:

```bash
egglog formal.egg
egglog zipper.egg
egglog zipper-descend.egg
```

`formal.egg` and `zipper.egg` are generated together from
`IllustrativeEggArtifacts.scala`; a freshness test prevents the checked-in
artifacts from drifting from that source.

## Proof Pipeline

Run the complete proof gate with five minutes per Z3 or Vampire obligation:

```bash
env _JAVA_OPTIONS='-Xmx1536m -Xss64m' \
  PYTHONPYCACHEPREFIX=/tmp/morkl_pycache \
python3 tools/proof_pipeline.py \
  --alphabet a,b \
  --max-len 3 \
  --z3-time-limit 300 \
  --vampire-time-limit 300 \
  --solver-workers 1
```

Use a small worker count on memory-constrained machines. Some ordered `Range`
obligations are CPU-heavy, and excessive parallelism can turn contention into a
misleading wall-clock timeout.

### Proof Status

The current [`proofs/PROOF_REPORT.md`](proofs/PROOF_REPORT.md) status is
`PASS_WITH_PROOF_DEBT`.

The operational manifest contains:

- 582 mapped rows;
- 149 proved-unbounded rows;
- 433 proved-bounded rows;
- 0 axiom-elsewhere rows;
- 0 unproved rows.

The 433 bounded rows remain proof debt. Zero unproved rows is not presented as
a complete unbounded proof.

Generated obligations connect the path-set semantics to eager tries, virtual
zippers, optimized source programs, and operation graphs. Open-program checks
quantify over arbitrary inputs; cornerstone certificates cover Aunt queries,
semi-naive Datalog, pure Game of Life, the sliding puzzle, temperature queries,
and pure MORKL n-queens.

## Fuzzing

The fuzzer generates dependent programs and appropriate argument spaces,
rejects insensitive or degenerate candidates, records constructor-position
coverage, and shrinks failures. Saved corpora exercise calls, iteration,
closures, ranges, self recursion, mutual recursion, and every trie-native
operation.

Important entry points include:

```text
spaceFuzzerCorpusRun
zipperFuzzerShowcase
freeExpressionFuzzerCorpusRun
fullBackendVerifierRun
slowProgramScTimingRun
slowProgramDegeneracyRun
```

The slow differential gate runs a fresh-seed corpus of 1,000 programs against
1,000 appropriate input frames and compares every evaluator/executor backend.

## Benchmarks

Benchmark entry points include:

```text
trieBenchmarkReport
constantFoldExecutorReport
zipperAlgebraBenchmarkReport
zipperIterRangeTailMicroReport
zipperLargeBenchmarkReport
```

The benchmark suite covers:

- graph queries over `lot.metta` and `royal92_simple.metta`;
- semi-naive Datalog and carac-derived programs;
- pure Game of Life with parameterized and compiled-in grids;
- NOAA temperature/spatial queries;
- pure sliding-puzzle exploration;
- pure MORKL n-queens.

Reports include absolute runtime, relative runtime, compile time,
compile-plus-run time, compile/run ratio, graph size, trie size, result size,
pass attribution, and explicit fallback notes. Correctness is checked before a
row is timed.

See:

- [`TRIE_RUNTIME.md`](TRIE_RUNTIME.md)
- [`TRIE_BENCHMARKS.md`](TRIE_BENCHMARKS.md)
- [`ZIPPER_ALGEBRA_BENCHMARKS.md`](ZIPPER_ALGEBRA_BENCHMARKS.md)
- [`ZIPPER_LARGE_BENCHMARKS.md`](ZIPPER_LARGE_BENCHMARKS.md)
- [`SUPERCOMPILER.md`](SUPERCOMPILER.md)

## Datasets

Large external datasets are optional. Tests use deterministic fixtures when a
local source file is unavailable. Named benchmark inputs include:

- `lot.metta`
- `royal92_simple.metta`
- the NOAA gridded NetCDF dataset
- `fred.rle` from Hashlife tests
- additional carac examples

The repository also includes a reproducible NOAA slice under
`src/test/resources/` and extraction utilities under `tools/`.

## Honest Boundaries

- Grounded host callbacks are explicit semantic boundaries and are not portable
  graph constants.
- Calls whose recursion/fixed-point obligations are not proved remain visible
  calls and must appear in benchmark fallback notes.
- Some closure-frontier and ordered-range properties combine bounded evidence,
  focused egg models, and named first-order bridge theorems rather than one
  complete scheduler bisimulation.
- The main path-set track must compile with `valued/` removed.

The complete current inventory is maintained in [`fallbacks.md`](fallbacks.md).
