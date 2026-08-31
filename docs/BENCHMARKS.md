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
| timestamp (UTC) | 2026-08-31T15:00:41Z |
| git commit | 789b26d-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12.1 (Eclipse Adoptium) |
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
| invariant-inner N=150  |      0.07 |      0.03 |    2.3x |     2 |     1 |
| invariant-inner N=400  |      0.20 |      0.08 |    2.4x |     2 |     1 |
| sliding expandStep 3x3 |      0.32 |      0.09 |    3.4x |    17 |    17 |
| n-queens place(6)      |      1.61 |      1.60 |    1.0x |     7 |     7 |

<!-- END benchmark:subgraph-hoisting -->

<!-- BEGIN benchmark:sc-domains -->
## Optimization across all SC domains

| environment | value |
|---|---|
| timestamp (UTC) | 2026-08-31T15:01:11Z |
| git commit | 789b26d-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12.1 (Eclipse Adoptium) |
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
| aunt (lot.metta)   |     0.01 |      0.01 |      0.01 |    1.4x |      0.01 |   1.0x |
(royal92_simple.metta not found — aunt(royal92) row skipped)
| n-queens n=7       |    15.87 |     12.40 |      6.84 |    1.8x |      6.94 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    1.0x |      0.00 |   1.0x |
| datalog tc (n=80)  |    15.12 |     14.93 |     14.96 |    1.0x |     14.87 |   1.0x |
| sliding 3x3 step   |     1.96 |      0.41 |      0.10 |    4.3x |      0.32 |   3.3x |
| gol step 12x12     |     3.83 |      2.84 |      1.07 |    2.7x |      1.07 |   1.0x |

<!-- END benchmark:sc-domains -->

<!-- BEGIN benchmark:op-graph-backend -->
## Op-graph backend benchmark

| environment | value |
|---|---|
| timestamp (UTC) | 2026-08-31T15:00:14Z |
| git commit | 789b26d-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12.1 (Eclipse Adoptium) |
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
| aunt n=150           |      1.5 |     27.7 |      0.5 |       0.5 |           0.4 |     0.28 |
| aunt n=400           |      1.4 |    262.5 |      0.7 |       0.5 |           0.5 |     0.34 |
| n-queens n=6         |      4.5 |     44.9 |     32.0 |       8.6 |           2.3 |     0.50 |
| n-queens n=7         |     19.5 |    231.4 |     25.3 |      25.9 |           7.4 |     0.38 |
| temperature 4096     |      0.0 |      1.0 |      0.0 |       0.0 |           0.0 |     1.65 |
| temperature 16384    |      0.0 |      3.3 |      0.0 |       0.0 |           0.0 |     1.46 |
| gol step 12x12       |      4.6 |     45.6 |     10.5 |      10.7 |           1.5 |     0.31 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 8.35 ms ONCE, run = 1.413 ms/step.  Amortized comp+run over K steps =
compile/K + run → 1.413 ms (vs the compiled-in literal, recompiled per grid: 9.76 ms each).

| union_iter           |      0.0 |      0.6 |      0.0 |       0.0 |           0.0 |     0.43 |
| datalog tc n=40        |      1.7 |        — |      1.0 |       1.0 |           1.0 |     0.60 |
| datalog tc n=80        |     26.0 |        — |     15.7 |      11.1 |          11.1 |     0.43 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.15 |     1.08 |       8 |      0.44 |       4 |     4.38 |      4.82 |
| aunt n=400           |      0.08 |     0.87 |       8 |      0.25 |       4 |     1.23 |      1.70 |
| n-queens n=6         |      0.49 |     1.39 |     184 |      0.54 |     200 |     2.59 |      4.87 |
| n-queens n=7         |      0.25 |    10.57 |     215 |      0.56 |     234 |    16.28 |     23.68 |
| temperature 4096     |      0.08 |     0.03 |       0 |      0.01 |       1 |     0.16 |      0.16 |
| temperature 16384    |      0.36 |     0.05 |       0 |      0.01 |       1 |     0.44 |      0.44 |
| gol step 12x12       |      0.41 |     0.75 |     102 |      0.28 |     221 |     1.60 |      3.06 |
| union_iter           |      0.01 |     0.06 |       2 |      0.08 |       0 |     0.16 |      0.18 |
| datalog tc n=40        |      0.02 |     0.03 |       0 |      0.03 |       0 |     0.07 |      1.10 |
| datalog tc n=80        |      0.02 |     0.02 |       0 |      0.01 |       0 |     0.04 |     11.16 |

**comp+run geomean = 1.843 ms ; run-only geomean = 0.271 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

<!-- END benchmark:op-graph-backend -->

<!-- BEGIN benchmark:executor-scaling -->
## Executor scaling: eval vs evalT vs evalI

| environment | value |
|---|---|
| timestamp (UTC) | 2026-08-31T15:01:45Z |
| git commit | 789b26d-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12.1 (Eclipse Adoptium) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala | 3.8.1 |
| tuning | literalByRef=true patriciaOps=true |
| timing | best-of-N wall clock after warmup (see the per-row `warm`/`reps` in the source) |
| interner | WARM — `Interner` and the literal memo carry every id from earlier rows of the same run |
| seed | fixed per benchmark; the workloads are deterministic |

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       2.6 |       0.8 |       0.1 |    17.5x |    5.2x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      30.0 |       5.3 |       1.1 |    26.2x |    4.6x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     461.9 |      36.3 |       7.4 |    62.1x |    4.9x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    6387.5 |     283.9 |      54.9 |   116.3x |    5.2x |  |
| aunt-query       | family n=150         |      27.6 |       1.7 |       0.2 |   147.4x |    9.3x |  |
| aunt-query       | family n=400         |     140.9 |       7.7 |       0.6 |   228.3x |   12.5x |  |
| aunt-query       | family n=800         |     789.1 |      46.5 |       1.8 |   440.6x |   26.0x |  |
| aunt-query       | family n=1600        |    2976.9 |     109.8 |       2.8 |  1071.1x |   39.5x |  |
| game-of-life     | 16x16 2 steps (68 live) |      24.8 |       9.4 |       7.5 |     3.3x |    1.3x |  |
| game-of-life     | 24x24 2 steps (193 live) |     164.8 |      38.6 |      29.6 |     5.6x |    1.3x |  |
| game-of-life     | 32x32 2 steps (321 live) |     410.0 |      60.1 |      38.5 |    10.7x |    1.6x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   182.6x |    3.0x |  |
| temperature      | 4096 cells (resident) |       0.7 |       0.0 |       0.0 |   889.2x |    4.0x |  |
| temperature      | 16384 cells (resident) |       2.0 |       0.0 |       0.0 |  3350.0x |    3.2x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      27.1 |      13.7 |       9.5 |     2.8x |    1.4x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     159.5 |      59.2 |      37.6 |     4.2x |    1.6x |  |
| n-queens         | n=6 (4 sols, pure)   |      25.1 |       4.2 |       2.8 |     9.0x |    1.5x |  |
| n-queens         | n=7 (40 sols, pure)  |     148.4 |      19.6 |      11.8 |    12.6x |    1.7x |  |
| n-queens         | n=8 (92 sols, pure)  |     924.6 |      82.1 |      82.8 |    11.2x |    1.0x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.1 |     0.6x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.1 |      -1.0 |       0.3 |     0.3x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.7x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.4x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 47.9x vs the
reference Set, and 3.6x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is touched during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


<!-- END benchmark:executor-scaling -->

<!-- BEGIN benchmark:pipeline-ablation -->
## Pipeline-stage ablation

| environment | value |
|---|---|
| timestamp (UTC) | 2026-08-31T15:00:12Z |
| git commit | 789b26d-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12.1 (Eclipse Adoptium) |
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
| aunt (lot)         |    0.059 |    0.020 |    0.181 |    0.287 |    0.260 |
| datalog tc (n=15)  |    1.566 |    0.890 |    0.025 |    0.856 |    0.051 |
| gol step (glider)  |    0.969 |    0.947 |    0.447 |    2.279 |    1.867 |
| sliding 3x3 step   |    7.031 |    4.141 |    0.068 |   33.158 |    1.261 |
| n-queens n=6       |   42.608 |    9.287 |   10.270 |    9.433 |    7.734 |
| temperature 1024   |    0.152 |    0.063 |    0.061 |    0.120 |    0.075 |

<!-- END benchmark:pipeline-ablation -->
