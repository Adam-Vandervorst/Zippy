# MORKL Supercompiler

This document describes the positive supercompiler for MORKL/Zippy's path-space
language. The implementation lives in `src/main/scala/Supercompiler.scala` and
is exposed through the public facade in `src/main/scala/MORKL.scala`.

MORKL programs compute finite sets of dotted paths. A space can be a relation,
a trie, a tagged database, or a sparse grid. The existing compiler machinery
already had an evaluator, source-level lowering laws, and an operation-graph
backend. That older path is still present as `Supercompiler.compile`: it is a
conservative normalizer/specializer plus graph compiler. It deliberately avoids
unfolding recursive self-calls.

The new process driver is `SC.supercompile` and the facade methods
`Supercompiler.supercompile` / `Supercompiler.specializeProgram`. It implements
the positive-supercompilation loop:

| Step | MORKL implementation |
|---|---|
| Driving | Reduce a configuration with the source laws, then unfold routine calls, including self-calls. |
| Folding | If the current configuration is an instance of an ancestor, emit a call to the ancestor's residual routine. |
| Whistle | If an ancestor homeomorphically embeds in a growing descendant, stop unfolding that branch. |
| Generalization | Compute the most-specific generalization (MSG) and continue with fresh residual parameters. |
| Residualization | Emit a `Residual(top, routines, report)` that can be evaluated with `residual.env`. |

## Architecture

`object Matching` is the term layer:

- `freeMentions` / `freeRefs` are binder-aware for `Iteration` and `Fold`.
- `subst` is simultaneous and capture-avoiding for space and path variables.
- `canon` and `alphaEqual` normalize bound names for matching.
- `renaming` and `instanceOf` provide the folding tests.
- `embeds` implements homeomorphic embedding. Literal leaves can be treated as
  exact values or as atoms through `SC.Config.literalEmbeddingPolicy`.
- `msg` computes anti-unification holes and the left/right substitutions that
  re-instantiate the skeleton.

`object SC` is the process-tree driver:

- `reduce` runs the same named source laws used by `Supercompiler.compile`, but
  with an explicit round cap.
- `drive` reduces a configuration and supercompiles routine-call subterms.
- `scCall` tries ancestor folding, then whistle/generalization, then unfolds.
- `makeNode` creates a residual routine and drives the unfolded body below it.
- `SCReport` records unfolds, folds, whistles, generalizations, and residual
  control statistics.

Ancestor-only folding is intentional. It keeps the first implementation easy to
audit and avoids global memoization accidentally folding through an unrelated
branch.

## Public API

For the conservative normalizing compiler:

```scala
val compiled = Supercompiler.compile(Routines.aunt_query_routine)
compiled.routine  // optimized source routine
compiled.graph    // operation graph when supported
compiled.report   // pass trace, convergence, backend status
```

For positive supercompilation of a configuration:

```scala
val call = R"aunts"(Literal(family), S"people")
val residual =
  Supercompiler.supercompile(
    call,
    mod(Routines.aunt_query_routine),
    SC.Config(maxNodes = 200, maxDepth = 80)
  )

val answer = eval(residual.top)(using PathContext.emptyMap, peopleContext, residual.env)
```

For specializing a recursive routine with known static arguments:

```scala
val residual =
  Supercompiler.specializeProgram(
    DatalogExample.semiNaiveTransitive,
    spaceArgs = Map(SpaceMention("edges") -> Literal(staticEdges))
  )
```

## Evidence

The default test suite keeps two kinds of evidence separate.

The process tests in `SupercompilerProcessTest.scala` check the core algorithm:

- semi-naive transitive closure supercompiles to a residual program and agrees
  with the original evaluator;
- disabling generalization on a growing symbolic reachability problem hits a
  cap, while enabling the whistle terminates and yields a self-recursive
  residual routine;
- residual control shape is independent of static graph size: routine count,
  AST nodes, calls, iterations, and literal-node count remain fixed while only
  the baked-in literal payload changes.

The independent reference tests in `ReferenceExamplesTest.scala` check the
examples against non-MORKL reference implementations:

- semi-naive Datalog closure vs. an independent transitive-closure loop;
- Game of Life vs. an independent B3/S23 neighbor counter;
- sliding puzzle one-step expansion for 3x3 and 4x4 boards, full 3x3
  reachability `9!/2 = 181440`, and bounded 4x4 expansion vs. direct BFS;
- NOAA spatial and temperature-first prefix queries vs. manual path filters;
- n-queens 8x8 through the MORKL graph backend vs. the known 92-solution
  count, plus an independent bit-recursive count table through 11x11.

The publication harness in `SupercompilerPublicationExamples` exercises the
public facade on the requested domains: Aunt/graph queries, carac-style
Datalog, Game of Life including random and RLE data, the committed NOAA slice,
sliding-puzzle generalizations, backend graph execution, and 9x9 n-queens.

The optimized trie runtime is documented separately in `TRIE_RUNTIME.md`.
`TrieSpaceTest` checks conversion and `evalTrie` agreement against the reference
set evaluator, including recursive and supercompiled residual programs.
`TRIE_BENCHMARKS.md` reports reference-vs-trie runtime measurements on the same
benchmark families and highlights where grounded host callbacks still dominate.

Run the verification with:

```bash
scala-cli test . --scala 3.8.1 --source 3.3 \
  --dependency org.scalameta::munit:1.2.1 \
  --dependency org.scala-lang.modules::scala-collection-contrib:0.3.0
```

Focused runs used during development:

```bash
scala-cli test . --test-only 'morkl.MatchingProcessTest' ...
scala-cli test . --test-only 'morkl.SupercompilerProcessTest' ...
scala-cli test . --test-only 'morkl.ReferenceExamplesTest' ...
scala-cli test . --test-only 'morkl.SupercompilerPublicationExamples' ...
```

## Data And Reproducibility

The suite is runnable in a small checkout. External datasets are used when they
are present, but deterministic fixtures keep the examples executable without a
large data download.

- `lot.metta`: parsed into `parent`, `child`, `female`, `male`, `person`, and
  `hasName`-backed name metadata for the Aunt query. A small family tree is used
  when the file is absent.
- `../carac`: parsed for `edge`, `parent`, `mother`, and `father` facts. A small
  acyclic parent graph is used when the directory is absent.
- `../hashlife/tests/fred.rle`: parsed as Conway RLE. A glider fixture is used
  when the file is absent.
- `src/test/resources/noaa_slice.txt`: a committed 2,592-cell NOAA GlobalTemp
  anomaly slice. The spatial encoding is `cell.latBits.lonBits.bucketBits.label`;
  the temperature-first encoding is `temp.label.bucket.lat.lon`.
- `tools/extract_noaa_slice.py`: extraction script for regenerating the NOAA
  slice from the original NetCDF/HDF5 file when `h5py` and the large source file
  are available.

## What It Does Not Claim

The current supercompiler preserves and specializes a semi-naive solver. It does
not derive semi-naive evaluation from a naive Datalog specification. That would
require a distillation-style transformation that discovers the accumulator and
delta split.

Fully static recursive examples may reduce to compile-time evaluation. That is
semantically useful, but the more interesting supercompilation claim is the
partially static case where the residual remains a compact recursive program.

The operation-graph backend is still separate from multi-routine residual
programs. `Supercompiler.compile` lowers single supported routines to the graph
backend; `SC.compileProgram` only attempts graph lowering for residuals with a
supported, routine-free top. Grounded host computations, `Fold`, and residual
routine environments remain source-level.

The matching layer handles `Fold` and grounded nodes structurally, but generated
names still use a reserved textual namespace. The tests cover capture avoidance,
alpha-equivalence, and grounded identity behavior; a future production system
should replace textual freshness with opaque binder identifiers.
