# Benchmarks

Executor, op-graph and zipper measurements for the Zippy runtime.

**Every section below is REGENERATED IN PLACE, not appended.** Each carries the machine, the
toolchain and the configuration it was produced on, because a timing table without them cannot be
reproduced, compared against a later run, or even read — "is 43.6 ms fast?" has no answer without
the CPU. This is [design_plan.md](design_plan.md) §7.4's reproducibility requirement made
mechanical: `RunEnvironment` (`src/main/scala/RunEnvironment.scala`) collects the provenance and
`BenchmarkReport` writes each section between stable `<!-- BEGIN benchmark:<slug> -->` markers.

> **This file used to be an append-only tape.** Five benchmarks each opened it with
> `new FileWriter(f, append = true)`, so about 28 near-identical replays of the same five sections
> had accumulated over 3,696 lines. The current numbers were indistinguishable from numbers
> produced months earlier by different code on a different machine, and no row said which machine.
> History belongs in git; this file holds the current run.

## What is measured

| section | slug | what it compares |
| --- | --- | --- |
| Executor scaling | `executor-scaling` | `eval` (the reference `Set[PathValue]` evaluator) vs `evalT` (TreeMap trie) vs `evalI` (interned `IntMap` trie), over the example domains at increasing scale. `evalI/eval` and `evalI/evalT` are speedups — higher means `evalI` is faster. |
| Op-graph backend | `op-graph-backend` | `execT` on the transpiled operation graph, raw vs optimised, plus the one-time compile cost accounted per pass with its improvement (`hoist` = nodes lifted out of loops, `cse` = duplicate nodes removed). |
| Loop-invariant subgraph hoisting | `subgraph-hoisting` | A/B on `push_out`'s `hoistSubgraphs` flag alone, with inline, CSE and executor held fixed. |
| Optimization across SC domains | `sc-domains` | `push_out` (LICM) + `optimize_sharing` (CSE) across the supercompiler's example domains, and the subgraph-hoisting contribution isolated. |
| Pipeline-stage ablation | `pipeline-ablation` | each example through five increasingly-compiled paths, from the `Set` reference to supercompile-then-graph-optimize. |

## How to regenerate

```bash
sbt 'testOnly morkl.TrieBench morkl.GraphBench morkl.SubgraphHoistBench morkl.SCOptBench morkl.AblationStages'
```

Each suite rewrites its own section and leaves the others untouched. The benchmarks are tagged
`Slow`; every one asserts all-backend agreement on a row **before** timing it, so a red row is a
correctness failure and not a slow one.

## How to read a row

- **Compile-vs-run is separated.** A program the optimiser residualises to a literal reports its
  compile cost plus a tiny run, never a runtime "speedup factor" ([design_plan.md](design_plan.md) §1.5).
- **The interner is WARM** within a run: `Interner` and the literal memo carry every id from earlier
  rows. Never compare a row against one taken after an unrelated large alphabet was interned.
- **Timings are best-of-N after warmup**, not single runs; the per-row `warm`/`reps` are in the
  benchmark source.
- A `*` on a program in the op-graph table means it was **optimised away** — the whole graph
  evaluated to a constant at compile time, so its "run" is a constant lookup.
- A `-1.0` or a `0.0x` in a generated cell means the row's operand was below the timer's resolution
  or the comparison was not applicable; it is not a measurement.

---

<!-- BEGIN benchmark:subgraph-hoisting -->
## Loop-invariant subgraph hoisting — A/B

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T16:47:09Z |
| git commit | f6832fc-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala | 3.8.1 |
| tuning | literalByRef=true patriciaOps=true |
| timing | best-of-N wall clock after warmup (see the per-row `warm`/`reps` in the source) |
| interner | WARM — `Interner` and the literal memo carry every id from earlier rows of the same run |
| seed | fixed per benchmark; the workloads are deterministic |

Runtime of `execT(optimize(g))` with push_out's subgraph hoisting OFF vs ON — the ONLY
difference between columns (inline/CSE/executor identical).  Synthetic: an invariant inner
iteration over a 60-path literal inside an outer loop of size N (with hoisting it runs once,
without it N times); plus sliding `expandStep` (the `all_moves` sub-iteration is invariant)
and n-queens place.  `depth` = max iteration-nesting depth: it drops when the hoisted loop
WAS the deepest (the synthetic case); sliding still wins ~4x at runtime even though its
overall max depth is fixed by a different branch; n-queens has no invariant inner loop.

| program | exec off ms | exec on ms | speedup | depth off | depth on |
|---|---:|---:|---:|---:|---:|
| invariant-inner N=150  |      0.07 |      0.03 |    2.4x |     2 |     1 |
| invariant-inner N=400  |      0.19 |      0.08 |    2.4x |     2 |     1 |
| sliding expandStep 3x3 |      0.29 |      0.09 |    3.4x |    17 |    17 |
| n-queens place(6)      |      1.62 |      1.59 |    1.0x |     7 |     7 |

<!-- END benchmark:subgraph-hoisting -->

<!-- BEGIN benchmark:sc-domains -->
## Optimization across all SC domains

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T16:47:37Z |
| git commit | f6832fc-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala | 3.8.1 |
| tuning | literalByRef=true patriciaOps=true |
| timing | best-of-N wall clock after warmup (see the per-row `warm`/`reps` in the source) |
| interner | WARM — `Interner` and the literal memo carry every id from earlier rows of the same run |
| seed | fixed per benchmark; the workloads are deterministic |

Each program is made Call-free by `lowerCalls` (acyclic calls inlined; union-saturating
recursion lowered to a Fixpoint), then `execT` is timed on the unoptimized vs `optimize`d
graph.  `opt speedup` = unopt/opt (the LICM+CSE win); `hoist` = optNoHoist/opt (the
loop-invariant SUBGRAPH-hoisting win in isolation).  GoL is now PURE (precomputed succ/
decr/idr number relations + `Range` counting), so it lowers and optimizes like the rest.

| domain | evalI ms | execT unopt ms | execT opt ms | opt speedup | execT opt(no-hoist) ms | hoist |
|---|---:|---:|---:|---:|---:|---:|
| aunt (lot.metta)   |     0.01 |      0.01 |      0.00 |    1.6x |      0.00 |   0.9x |
(royal92_simple.metta not found — aunt(royal92) row skipped)
| n-queens n=7       |    16.33 |     12.18 |      6.60 |    1.8x |      6.63 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    1.0x |      0.00 |   0.9x |
| datalog tc (n=80)  |    14.71 |     14.24 |     14.34 |    1.0x |     14.27 |   1.0x |
| sliding 3x3 step   |     1.93 |      0.39 |      0.08 |    5.0x |      0.31 |   3.9x |
| gol step 12x12     |     3.92 |      2.70 |      1.04 |    2.6x |      1.00 |   1.0x |

<!-- END benchmark:sc-domains -->

<!-- BEGIN benchmark:op-graph-backend -->
## Op-graph backend benchmark

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T16:46:35Z |
| git commit | f6832fc-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala | 3.8.1 |
| tuning | literalByRef=true patriciaOps=true |
| timing | best-of-N wall clock after warmup (see the per-row `warm`/`reps` in the source) |
| interner | WARM — `Interner` and the literal memo carry every id from earlier rows of the same run |
| seed | fixed per benchmark; the workloads are deterministic |

eval-based `exec` vs trie-native `execT`.  `execT` = transpiled graph; `execT(opt)` =
push_out(LICM)+optimize_sharing(CSE); `execT(inline+opt)` = all Calls inlined into the graph
then optimized (the executor-ready form — no Call dispatch, constants decoded once).  Last
column is execT(inline+opt)/evalI (<1.0 means the compiled graph beats the interpreter).
Game of Life is now pure (precomputed number relations + Range counting), so it is included.
Datalog's saturating recursion is LOWERED to a Fixpoint subgraph (so it transpiles Call-free);
for it execT(opt) is the executor-ready form.

| program | evalI ms | exec ms | execT ms | execT(opt) ms | execT(inline+opt) ms | vs evalI |
|---|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.9 |     26.5 |      0.5 |       0.3 |           0.4 |     0.49 |
| aunt n=400           |      0.9 |    240.4 |      0.9 |       0.6 |           0.6 |     0.67 |
| n-queens n=6         |      7.4 |     95.9 |     14.8 |       8.6 |           2.1 |     0.28 |
| n-queens n=7         |     22.0 |    261.3 |     25.7 |      26.6 |           9.2 |     0.42 |
| temperature 4096     |      0.0 |      1.2 |      0.0 |       0.0 |           0.0 |     1.36 |
| temperature 16384    |      0.0 |      3.5 |      0.0 |       0.0 |           0.0 |     1.00 |
| gol step 12x12       |      4.7 |     42.3 |     15.5 |       5.7 |           1.3 |     0.27 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 7.42 ms ONCE, run = 1.223 ms/step.  Amortized comp+run over K steps =
compile/K + run → 1.223 ms (vs the compiled-in literal, recompiled per grid: 8.64 ms each).

| union_iter           |      0.1 |      0.7 |      0.0 |       0.0 |           0.0 |     0.12 |
| datalog tc n=40        |      2.7 |        — |      1.2 |       1.1 |           1.1 |     0.41 |
| datalog tc n=80        |     27.7 |        — |     16.1 |      16.2 |          16.2 |     0.59 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.12 |     0.65 |       8 |      3.94 |       4 |     5.09 |      5.54 |
| aunt n=400           |      0.08 |     0.46 |       8 |      0.16 |       4 |     0.74 |      1.37 |
| n-queens n=6         |      1.29 |     1.34 |     184 |      0.72 |     200 |     3.58 |      5.67 |
| n-queens n=7         |      0.24 |     1.50 |     215 |      3.69 |     234 |     5.56 |     14.78 |
| temperature 4096     |      0.08 |     0.02 |       0 |      0.01 |       1 |     0.15 |      0.15 |
| temperature 16384    |      0.32 |     0.05 |       0 |      0.01 |       1 |     0.40 |      0.40 |
| gol step 12x12       |      2.26 |     0.83 |     102 |      0.27 |     221 |     3.47 |      4.74 |
| union_iter           |      0.01 |     0.05 |       2 |      0.02 |       0 |     0.08 |      0.09 |
| datalog tc n=40        |      0.02 |     0.03 |       0 |      0.01 |       0 |     0.05 |      1.18 |
| datalog tc n=80        |      0.02 |     0.01 |       0 |      0.01 |       0 |     0.04 |     16.24 |

**comp+run geomean = 1.790 ms ; run-only geomean = 0.270 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

<!-- END benchmark:op-graph-backend -->

<!-- BEGIN benchmark:executor-scaling -->
## Executor scaling: eval vs evalT vs evalI

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T16:48:15Z |
| git commit | f6832fc-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala | 3.8.1 |
| tuning | literalByRef=true patriciaOps=true |
| timing | best-of-N wall clock after warmup (see the per-row `warm`/`reps` in the source) |
| interner | WARM — `Interner` and the literal memo carry every id from earlier rows of the same run |
| seed | fixed per benchmark; the workloads are deterministic |

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       6.1 |       0.9 |       0.2 |    31.8x |    4.4x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      32.8 |       5.5 |       1.3 |    25.2x |    4.2x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     477.5 |      34.8 |       8.6 |    55.5x |    4.0x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    5836.5 |     157.4 |      32.5 |   179.5x |    4.8x |  |
| aunt-query       | family n=150         |      18.8 |       1.4 |       0.1 |   133.5x |    9.7x |  |
| aunt-query       | family n=400         |     154.8 |       5.2 |       0.7 |   228.0x |    7.7x |  |
| aunt-query       | family n=800         |     624.3 |      20.3 |       1.0 |   611.5x |   19.8x |  |
| aunt-query       | family n=1600        |    2738.0 |      94.8 |       3.8 |   724.3x |   25.1x |  |
| game-of-life     | 16x16 2 steps (68 live) |      28.7 |       9.4 |       6.1 |     4.7x |    1.5x |  |
| game-of-life     | 24x24 2 steps (193 live) |     114.1 |      24.1 |      15.9 |     7.2x |    1.5x |  |
| game-of-life     | 32x32 2 steps (321 live) |     301.8 |      43.5 |      28.7 |    10.5x |    1.5x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   321.0x |    3.3x |  |
| temperature      | 4096 cells (resident) |       0.5 |       0.0 |       0.0 |  1434.0x |    3.8x |  |
| temperature      | 16384 cells (resident) |       3.3 |       0.0 |       0.0 |  8079.6x |    3.8x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      28.6 |      14.3 |       9.9 |     2.9x |    1.4x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     141.7 |      53.2 |      39.1 |     3.6x |    1.4x |  |
| n-queens         | n=6 (4 sols, pure)   |      27.0 |       4.2 |       2.3 |    11.8x |    1.8x |  |
| n-queens         | n=7 (40 sols, pure)  |     162.8 |      18.9 |      10.4 |    15.6x |    1.8x |  |
| n-queens         | n=8 (92 sols, pure)  |     933.8 |      86.6 |      53.9 |    17.3x |    1.6x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     0.6x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.1 |      -1.0 |       0.2 |     0.3x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     1.2x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.7x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 59.2x vs the
reference Set, and 3.5x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is touched during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


<!-- END benchmark:executor-scaling -->

<!-- BEGIN benchmark:pipeline-ablation -->
## Pipeline-stage ablation

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T16:46:34Z |
| git commit | f6832fc-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala | 3.8.1 |
| tuning | literalByRef=true patriciaOps=true |
| timing | best-of-N wall clock after warmup (see the per-row `warm`/`reps` in the source) |
| interner | WARM — `Interner` and the literal memo carry every id from earlier rows of the same run |
| seed | fixed per benchmark; the workloads are deterministic |

Time to evaluate each example through five increasingly-compiled paths (ms, best of N; modest
inputs so the Set `eval` reference and supercompilation are feasible).  `eval(def)` = Set
reference; `evalI(def)` = interned-trie interpreter; `evalI(SC)` = interpret the supercompiled
residual; `execT(opt)` = lower→transpile→optimize op-graph; `execT(SC+opt)` = supercompile then
graph-optimize.  All stages verified equal to the reference.

| example | eval(def) | evalI(def) | evalI(SC) | execT(opt) | execT(SC+opt) |
|---|---:|---:|---:|---:|---:|
| aunt (lot)         |    0.062 |    0.021 |    0.216 |    0.207 |    0.202 |
| datalog tc (n=15)  |    1.506 |    0.878 |    0.023 |    0.901 |    0.057 |
| gol step (glider)  |    1.004 |    8.899 |    0.489 |    2.626 |    1.641 |
| sliding 3x3 step   |    7.410 |    4.428 |    0.064 |   53.956 |    1.231 |
| n-queens n=6       |   71.070 |   13.561 |    4.955 |    6.238 |    7.432 |
| temperature 1024   |    0.105 |    0.065 |    0.063 |    0.127 |    0.080 |

<!-- END benchmark:pipeline-ablation -->
