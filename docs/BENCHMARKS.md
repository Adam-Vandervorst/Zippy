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
| timestamp (UTC) | 2026-09-02T19:55:17Z |
| git commit | 9b818f3-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala (runtime library) | 3.8.1 |
| build | sbt 2.0.8; scalac 3.8.1 -source:3.3 -feature -explain |
| external tools | z3=Z3 version 5.1.0 - 64 bit  vampire=Vampire 5.1.0 (Release build, commit 7b2f410 on 2026-08-13 10:17:34 +0200)  egglog=egglog 3.0.0_2026-09-02_e5dea2d5 |
| source tree | DIRTY — 103 modified path(s); `9b818f3-dirty` does NOT identify the code that produced these numbers |
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
| invariant-inner N=150  |      0.07 |      0.03 |    2.2x |     2 |     1 |
| invariant-inner N=400  |      0.20 |      0.08 |    2.4x |     2 |     1 |
| sliding expandStep 3x3 |      0.33 |      0.09 |    3.6x |    17 |    17 |
| n-queens place(6)      |      1.58 |      1.58 |    1.0x |     7 |     7 |

<!-- END benchmark:subgraph-hoisting -->

<!-- BEGIN benchmark:sc-domains -->
## Optimization across all SC domains

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T19:55:34Z |
| git commit | 9b818f3-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala (runtime library) | 3.8.1 |
| build | sbt 2.0.8; scalac 3.8.1 -source:3.3 -feature -explain |
| external tools | z3=Z3 version 5.1.0 - 64 bit  vampire=Vampire 5.1.0 (Release build, commit 7b2f410 on 2026-08-13 10:17:34 +0200)  egglog=egglog 3.0.0_2026-09-02_e5dea2d5 |
| source tree | DIRTY — 103 modified path(s); `9b818f3-dirty` does NOT identify the code that produced these numbers |
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
| aunt (lot.metta)   |     0.01 |      0.01 |      0.01 |    1.5x |      0.01 |   1.0x |
(royal92_simple.metta not found — aunt(royal92) row skipped)
| n-queens n=7       |    15.93 |     12.00 |      6.62 |    1.8x |      6.55 |   1.0x |
| temperature 4096   |     0.00 |      0.00 |      0.00 |    1.0x |      0.00 |   1.0x |
| datalog tc (n=80)  |    14.77 |     15.11 |     14.87 |    1.0x |     14.50 |   1.0x |
| sliding 3x3 step   |     1.85 |      0.42 |      0.09 |    4.7x |      0.31 |   3.5x |
| gol step 12x12     |     4.00 |      2.68 |      1.08 |    2.5x |      0.95 |   0.9x |

<!-- END benchmark:sc-domains -->

<!-- BEGIN benchmark:op-graph-backend -->
## Op-graph backend benchmark

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T19:54:20Z |
| git commit | 9b818f3-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala (runtime library) | 3.8.1 |
| build | sbt 2.0.8; scalac 3.8.1 -source:3.3 -feature -explain |
| external tools | z3=Z3 version 5.1.0 - 64 bit  vampire=Vampire 5.1.0 (Release build, commit 7b2f410 on 2026-08-13 10:17:34 +0200)  egglog=egglog 3.0.0_2026-09-02_e5dea2d5 |
| source tree | DIRTY — 103 modified path(s); `9b818f3-dirty` does NOT identify the code that produced these numbers |
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
| aunt n=150           |      0.7 |     25.7 |      0.4 |       0.4 |           0.3 |     0.43 |
| aunt n=400           |      0.7 |    202.7 |      0.9 |       0.6 |           0.8 |     1.05 |
| n-queens n=6         |      3.6 |     44.5 |      6.3 |       8.3 |          11.6 |     3.19 |
| n-queens n=7         |     27.1 |    236.6 |     22.8 |      22.2 |           6.6 |     0.25 |
| temperature 4096     |      0.0 |      1.2 |      0.0 |       0.0 |           0.0 |     1.53 |
| temperature 16384    |      0.0 |      4.5 |      0.0 |       0.0 |           0.0 |     1.65 |
| gol step 12x12       |      4.4 |     19.0 |      3.8 |       4.0 |           1.5 |     0.34 |

**GoL grid-as-argument** (field is a runtime input ⇒ one compiled graph runs any grid):
compile = 1.31 ms ONCE, run = 1.443 ms/step.  Amortized comp+run over K steps =
compile/K + run → 1.443 ms (vs the compiled-in literal, recompiled per grid: 2.75 ms each).

| union_iter           |      0.0 |      0.5 |      0.0 |       0.0 |           0.0 |     0.39 |
| datalog tc n=40        |      1.7 |        — |      1.4 |       1.4 |           1.4 |     0.84 |
| datalog tc n=80        |     26.9 |        — |     17.2 |      16.1 |          16.1 |     0.60 |

### Compile time + improvement per pass (executor-ready build)

One-time compile cost, bounded and accounted per pass with its IMPROVEMENT: push_out's `hoist`
= nodes lifted out of loops, optimize_sharing's `cse` = duplicate nodes removed.  `compile+run`
is the combined cost of one build plus one execT(inline+opt) run.  A `*` on a program above
means it was OPTIMIZED AWAY — the whole graph evaluated to a constant at compile time.

| program | transpile ms | push_out ms | hoist | optimize_sharing ms | cse | compile ms | compile+run ms |
|---|---:|---:|---:|---:|---:|---:|---:|
| aunt n=150           |      0.10 |     5.25 |       8 |      0.25 |       4 |     6.82 |      7.13 |
| aunt n=400           |      0.06 |     3.86 |       8 |      0.19 |       4 |     4.14 |      4.90 |
| n-queens n=6         |      0.37 |     1.31 |     184 |      1.37 |     200 |     3.22 |     14.77 |
| n-queens n=7         |      3.81 |     1.55 |     215 |      0.71 |     234 |     6.20 |     12.84 |
| temperature 4096     |      0.08 |     0.04 |       0 |      0.01 |       1 |     0.18 |      0.18 |
| temperature 16384    |      0.53 |     0.08 |       0 |      0.04 |       1 |     0.68 |      0.68 |
| gol step 12x12       |      0.36 |     1.03 |     102 |      0.45 |     221 |     2.03 |      3.52 |
| union_iter           |      0.01 |     0.06 |       2 |      0.02 |       0 |     0.10 |      0.11 |
| datalog tc n=40        |      0.02 |     0.10 |       0 |      0.01 |       0 |     0.14 |      1.57 |
| datalog tc n=80        |      0.02 |     0.03 |       0 |      0.01 |       0 |     0.07 |     16.17 |

**comp+run geomean = 2.464 ms ; run-only geomean = 0.316 ms** over 10 benchmarks (literalByRef=true patriciaOps=true).

<!-- END benchmark:op-graph-backend -->

<!-- BEGIN benchmark:executor-scaling -->
## Executor scaling: eval vs evalT vs evalI

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T19:56:15Z |
| git commit | 9b818f3-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala (runtime library) | 3.8.1 |
| build | sbt 2.0.8; scalac 3.8.1 -source:3.3 -feature -explain |
| external tools | z3=Z3 version 5.1.0 - 64 bit  vampire=Vampire 5.1.0 (Release build, commit 7b2f410 on 2026-08-13 10:17:34 +0200)  egglog=egglog 3.0.0_2026-09-02_e5dea2d5 |
| source tree | DIRTY — 103 modified path(s); `9b818f3-dirty` does NOT identify the code that produced these numbers |
| tuning | literalByRef=true patriciaOps=true |
| timing | best-of-N wall clock after warmup (see the per-row `warm`/`reps` in the source) |
| interner | WARM — `Interner` and the literal memo carry every id from earlier rows of the same run |
| seed | fixed per benchmark; the workloads are deterministic |

| domain | scale | eval ms | evalT ms | evalI ms | evalI/eval | evalI/evalT | note |
|---|---|---:|---:|---:|---:|---:|---|
| datalog-TC       | chain n=16 (|TC|=136) |       3.1 |       0.8 |       0.2 |    16.3x |    4.3x |  |
| datalog-TC       | chain n=32 (|TC|=528) |      31.8 |       5.0 |       1.2 |    26.2x |    4.1x |  |
| datalog-TC       | chain n=64 (|TC|=2080) |     431.9 |      32.5 |       7.8 |    55.6x |    4.2x |  |
| datalog-TC       | chain n=128 (|TC|=8256) |    5283.5 |     151.3 |      32.6 |   162.1x |    4.6x |  |
| aunt-query       | family n=150         |      17.4 |       1.5 |       0.1 |   124.5x |   10.9x |  |
| aunt-query       | family n=400         |     136.2 |      10.5 |       0.4 |   324.6x |   25.0x |  |
| aunt-query       | family n=800         |     591.4 |      41.7 |       1.1 |   554.0x |   39.1x |  |
| aunt-query       | family n=1600        |    2575.8 |     166.9 |       2.4 |  1078.1x |   69.9x |  |
| game-of-life     | 16x16 2 steps (68 live) |      26.8 |       9.5 |       6.4 |     4.2x |    1.5x |  |
| game-of-life     | 24x24 2 steps (193 live) |     107.1 |      24.0 |      16.4 |     6.5x |    1.5x |  |
| game-of-life     | 32x32 2 steps (321 live) |     279.6 |      43.1 |      29.9 |     9.4x |    1.4x |  |
| temperature      | 1024 cells (resident) |       0.1 |       0.0 |       0.0 |   321.9x |    3.5x |  |
| temperature      | 4096 cells (resident) |       0.5 |       0.0 |       0.0 |  1293.6x |    3.5x |  |
| temperature      | 16384 cells (resident) |       2.4 |       0.0 |       0.0 |  5355.7x |    3.3x |  |
| sliding-puzzle   | 2x2 depth 6 (pure)   |      28.8 |      13.6 |       9.5 |     3.0x |    1.4x |  |
| sliding-puzzle   | 3x3 depth 4 (pure)   |     139.9 |      51.2 |      38.8 |     3.6x |    1.3x |  |
| n-queens         | n=6 (4 sols, pure)   |      26.0 |       4.0 |       2.2 |    11.9x |    1.8x |  |
| n-queens         | n=7 (40 sols, pure)  |     155.6 |      17.8 |      10.0 |    15.6x |    1.8x |  |
| n-queens         | n=8 (92 sols, pure)  |     978.5 |      79.4 |      45.2 |    21.7x |    1.8x |  |
| join-all         | k=200 m=200          |       0.0 |      -1.0 |       0.0 |     0.8x |    0.0x | reduce(union) vs joinAll |
| join-all         | k=800 m=300          |       0.1 |      -1.0 |       0.2 |     0.3x |    0.0x | reduce(union) vs joinAll |
| meet-all         | k=40 core=400 +tiny  |       0.0 |      -1.0 |       0.0 |     0.7x |    0.0x | reduce(meet) vs meetAll |
| meet-all         | k=120 core=600 +tiny |       0.0 |      -1.0 |       0.0 |     0.4x |    0.0x | reduce(meet) vs meetAll |

Geometric-mean evalI speedup over the six example domains: 57.0x vs the
reference Set, and 4.1x vs the TreeMap trie (evalT). All six
domains are pure algebra; PathItems are interned to Ints before evaluation (no PathItem
is touched during evaluation), and the ring ops use IntMap's unionWith/intersectionWith.


<!-- END benchmark:executor-scaling -->

<!-- BEGIN benchmark:pipeline-ablation -->
## Pipeline-stage ablation

| environment | value |
|---|---|
| timestamp (UTC) | 2026-09-02T19:54:21Z |
| git commit | 9b818f3-dirty |
| cpu | Intel(R) Xeon(R) 6975P-C (16 logical cores) |
| memory | 247 GiB |
| os | Linux 6.17.0-1019-aws |
| jvm | OpenJDK 64-Bit Server VM 21.0.12 (Ubuntu) |
| jvm args | -Xmx24G -Xss16M -Dfile.encoding=UTF-8 |
| max heap | 24.0 GiB |
| scala (runtime library) | 3.8.1 |
| build | sbt 2.0.8; scalac 3.8.1 -source:3.3 -feature -explain |
| external tools | z3=Z3 version 5.1.0 - 64 bit  vampire=Vampire 5.1.0 (Release build, commit 7b2f410 on 2026-08-13 10:17:34 +0200)  egglog=egglog 3.0.0_2026-09-02_e5dea2d5 |
| source tree | DIRTY — 103 modified path(s); `9b818f3-dirty` does NOT identify the code that produced these numbers |
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
| aunt (lot)         |    0.058 |    0.020 |    0.117 |    0.183 |    0.159 |
| datalog tc (n=15)  |    1.679 |    0.666 |    0.027 |    0.484 |    0.042 |
| gol step (glider)  |    0.943 |    0.962 |    0.525 |    1.693 |    1.454 |
| sliding 3x3 step   |    7.380 |    4.310 |    0.073 |   47.786 |    1.556 |
| n-queens n=6       |   38.800 |    9.611 |    5.210 |    6.688 |    7.391 |
| temperature 1024   |    0.158 |    0.062 |    0.058 |    0.152 |    0.078 |

<!-- END benchmark:pipeline-ablation -->
